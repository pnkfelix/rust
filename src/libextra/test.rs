// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[doc(hidden)];

// Support code for rustc's built in test runner generator. Currently,
// none of this is meant for users. It is intended to support the
// simplest interface possible for representing and running tests
// while providing a base that other test frameworks may build off of.


use getopts;
use json::ToJson;
use json;
use serialize::Decodable;
use sort;
use stats::Stats;
use stats;
use term;
use time::precise_time_ns;
use treemap::TreeMap;

use std::comm::{stream, SharedChan};
use std::either;
use std::io;
use std::option;
use std::result;
use std::task;
use std::to_str::ToStr;
use std::u64;
use std::hashmap::HashMap;
use std::os;

pub mod rustrt {
    use std::libc::size_t;

    #[abi = "cdecl"]
    pub extern {
        pub unsafe fn rust_sched_threads() -> size_t;
    }
}

// The name of a test. By convention this follows the rules for rust
// paths; i.e. it should be a series of identifiers separated by double
// colons. This way if some test runner wants to arrange the tests
// hierarchically it may.

pub enum TestName {
    StaticTestName(&'static str),
    DynTestName(~str)
}
impl ToStr for TestName {
    fn to_str(&self) -> ~str {
        match copy *self {
            StaticTestName(s) => s.to_str(),
            DynTestName(s) => s.to_str()
        }
    }
}

// A function that runs a test. If the function returns successfully,
// the test succeeds; if the function fails then the test fails. We
// may need to come up with a more clever definition of test in order
// to support isolation of tests into tasks.
pub enum TestFn {
    StaticTestFn(extern fn()),
    StaticBenchFn(extern fn(&mut BenchHarness)),
    DynTestFn(~fn()),
    DynBenchFn(~fn(&mut BenchHarness))
}

// Structure passed to BenchFns
pub struct BenchHarness {
    iterations: u64,
    ns_start: u64,
    ns_end: u64,
    bytes: u64
}

// The definition of a single test. A test runner will run a list of
// these.
pub struct TestDesc {
    name: TestName,
    ignore: bool,
    should_fail: bool
}

pub struct TestDescAndFn {
    desc: TestDesc,
    testfn: TestFn,
}

#[deriving(Encodable,Decodable,Eq)]
pub struct Metric {
    value: f64,
    noise: f64
}

pub struct MetricMap(TreeMap<~str,Metric>);

/// Analysis of a single change in metric
pub enum MetricChange {
    LikelyNoise,
    MetricAdded,
    MetricRemoved,
    Improvement(f64),
    Regression(f64)
}

pub type MetricDiff = TreeMap<~str,MetricChange>;

// The default console test runner. It accepts the command line
// arguments and a vector of test_descs.
pub fn test_main(args: &[~str], tests: ~[TestDescAndFn]) {
    let opts =
        match parse_opts(args) {
          either::Left(o) => o,
          either::Right(m) => fail!(m)
        };
    if !run_tests_console(&opts, tests) { fail!("Some tests failed"); }
}

// A variant optimized for invocation with a static test vector.
// This will fail (intentionally) when fed any dynamic tests, because
// it is copying the static values out into a dynamic vector and cannot
// copy dynamic values. It is doing this because from this point on
// a ~[TestDescAndFn] is used in order to effect ownership-transfer
// semantics into parallel test runners, which in turn requires a ~[]
// rather than a &[].
pub fn test_main_static(args: &[~str], tests: &[TestDescAndFn]) {
    let owned_tests = do tests.map |t| {
        match t.testfn {
            StaticTestFn(f) =>
            TestDescAndFn { testfn: StaticTestFn(f), desc: copy t.desc },

            StaticBenchFn(f) =>
            TestDescAndFn { testfn: StaticBenchFn(f), desc: copy t.desc },

            _ => {
                fail!("non-static tests passed to test::test_main_static");
            }
        }
    };
    test_main(args, owned_tests)
}

pub struct TestOpts {
    filter: Option<~str>,
    run_ignored: bool,
    run_tests: bool,
    run_benchmarks: bool,
    ratchet_metrics: Option<Path>,
    save_metrics: Option<Path>,
    logfile: Option<Path>
}

type OptRes = Either<TestOpts, ~str>;

// Parses command line arguments into test options
pub fn parse_opts(args: &[~str]) -> OptRes {
    let args_ = args.tail();
    let opts = ~[getopts::optflag("ignored"),
                 getopts::optflag("test"),
                 getopts::optflag("bench"),
                 getopts::optopt("save-metrics"),
                 getopts::optopt("ratchet-metrics"),
                 getopts::optopt("logfile")];
    let matches =
        match getopts::getopts(args_, opts) {
          Ok(m) => m,
          Err(f) => return either::Right(getopts::fail_str(f))
        };

    let filter =
        if matches.free.len() > 0 {
            option::Some(copy (matches).free[0])
        } else { option::None };

    let run_ignored = getopts::opt_present(&matches, "ignored");

    let logfile = getopts::opt_maybe_str(&matches, "logfile");
    let logfile = logfile.map(|s| Path(*s));

    let run_benchmarks = getopts::opt_present(&matches, "bench");
    let run_tests = ! run_benchmarks ||
        getopts::opt_present(&matches, "test");

    let ratchet_metrics = getopts::opt_maybe_str(&matches, "ratchet-metrics");
    let ratchet_metrics = ratchet_metrics.map(|s| Path(*s));

    let save_metrics = getopts::opt_maybe_str(&matches, "save-metrics");
    let save_metrics = save_metrics.map(|s| Path(*s));

    let test_opts = TestOpts {
        filter: filter,
        run_ignored: run_ignored,
        run_tests: run_tests,
        run_benchmarks: run_benchmarks,
        ratchet_metrics: ratchet_metrics,
        save_metrics: save_metrics,
        logfile: logfile
    };

    either::Left(test_opts)
}

#[deriving(Eq)]
pub struct BenchSamples {
    ns_iter_summ: stats::Summary,
    mb_s: uint
}

#[deriving(Eq)]
pub enum TestResult { TrOk, TrFailed, TrIgnored, TrBench(BenchSamples) }

struct ConsoleTestState {
    out: @io::Writer,
    log_out: Option<@io::Writer>,
    term: Option<term::Terminal>,
    use_color: bool,
    total: uint,
    passed: uint,
    failed: uint,
    ignored: uint,
    benchmarked: uint,
    metrics: MetricMap,
    failures: ~[TestDesc]
}

impl ConsoleTestState {
    pub fn new(opts: &TestOpts) -> ConsoleTestState {
        let log_out = match opts.logfile {
            Some(ref path) => match io::file_writer(path,
                                                    [io::Create,
                                                     io::Truncate]) {
                result::Ok(w) => Some(w),
                result::Err(ref s) => {
                    fail!("can't open output file: %s", *s)
                }
            },
            None => None
        };
        let out = io::stdout();
        let term = match term::Terminal::new(out) {
            Err(_) => None,
            Ok(t) => Some(t)
        };
        ConsoleTestState {
            out: out,
            log_out: log_out,
            use_color: use_color(),
            term: term,
            total: 0u,
            passed: 0u,
            failed: 0u,
            ignored: 0u,
            benchmarked: 0u,
            metrics: MetricMap::new(),
            failures: ~[]
        }
    }

    pub fn write_ok(&self) {
        self.write_pretty("ok", term::color::GREEN);
    }

    pub fn write_failed(&self) {
        self.write_pretty("FAILED", term::color::RED);
    }

    pub fn write_ignored(&self) {
        self.write_pretty("ignored", term::color::YELLOW);
    }

    pub fn write_bench(&self) {
        self.write_pretty("bench", term::color::CYAN);
    }


    pub fn write_added(&self) {
        self.write_pretty("added", term::color::GREEN);
    }

    pub fn write_improved(&self) {
        self.write_pretty("improved", term::color::GREEN);
    }

    pub fn write_removed(&self) {
        self.write_pretty("removed", term::color::YELLOW);
    }

    pub fn write_regressed(&self) {
        self.write_pretty("regressed", term::color::RED);
    }

    pub fn write_pretty(&self,
                        word: &str,
                        color: term::color::Color) {
        match self.term {
            None => self.out.write_str(word),
            Some(ref t) => {
                if self.use_color {
                    t.fg(color);
                }
                self.out.write_str(word);
                if self.use_color {
                    t.reset();
                }
            }
        }
    }

    pub fn write_run_start(&mut self, len: uint) {
        self.total = len;
        let noun = if len != 1 { &"tests" } else { &"test" };
        self.out.write_line(fmt!("\nrunning %u %s", len, noun));
    }

    pub fn write_test_start(&self, test: &TestDesc) {
        self.out.write_str(fmt!("test %s ... ", test.name.to_str()));
    }

    pub fn write_result(&self, result: &TestResult) {
        match *result {
            TrOk => self.write_ok(),
            TrFailed => self.write_failed(),
            TrIgnored => self.write_ignored(),
            TrBench(ref bs) => {
                self.write_bench();
                self.out.write_str(": " + fmt_bench_samples(bs))
            }
        }
        self.out.write_str(&"\n");
    }

    pub fn write_log(&self, test: &TestDesc, result: &TestResult) {
        match self.log_out {
            None => (),
            Some(out) => {
                out.write_line(fmt!("%s %s",
                                    match *result {
                                        TrOk => ~"ok",
                                        TrFailed => ~"failed",
                                        TrIgnored => ~"ignored",
                                        TrBench(ref bs) => fmt_bench_samples(bs)
                                    }, test.name.to_str()));
            }
        }
    }

    pub fn write_failures(&self) {
        self.out.write_line("\nfailures:");
        let mut failures = ~[];
        for self.failures.iter().advance() |f| {
            failures.push(f.name.to_str());
        }
        sort::tim_sort(failures);
        for failures.iter().advance |name| {
            self.out.write_line(fmt!("    %s", name.to_str()));
        }
    }

    pub fn write_metric_diff(&self, diff: &MetricDiff) {
        let mut noise = 0;
        let mut improved = 0;
        let mut regressed = 0;
        let mut added = 0;
        let mut removed = 0;

        for diff.iter().advance() |(k, v)| {
            match *v {
                LikelyNoise => noise += 1,
                MetricAdded => {
                    added += 1;
                    self.write_added();
                    self.out.write_line(fmt!(": %s", *k));
                }
                MetricRemoved => {
                    removed += 1;
                    self.write_removed();
                    self.out.write_line(fmt!(": %s", *k));
                }
                Improvement(pct) => {
                    improved += 1;
                    self.out.write_str(*k);
                    self.out.write_str(": ");
                    self.write_improved();
                    self.out.write_line(fmt!(" by %.2f%%", pct as float))
                }
                Regression(pct) => {
                    regressed += 1;
                    self.out.write_str(*k);
                    self.out.write_str(": ");
                    self.write_regressed();
                    self.out.write_line(fmt!(" by %.2f%%", pct as float))
                }
            }
        }
        self.out.write_line(fmt!("result of ratchet: %u matrics added, %u removed, \
                                  %u improved, %u regressed, %u noise",
                                 added, removed, improved, regressed, noise));
        if regressed == 0 {
            self.out.write_line("updated ratchet file")
        } else {
            self.out.write_line("left ratchet file untouched")
        }
    }

    pub fn write_run_finish(&self, ratchet_metrics: &Option<Path>) -> bool {
        assert!(self.passed + self.failed + self.ignored + self.benchmarked == self.total);

        let ratchet_success = match *ratchet_metrics {
            None => true,
            Some(ref pth) => {
                self.out.write_str(fmt!("\nusing metrics ratchet: %s\n", pth.to_str()));
                let (diff, ok) = self.metrics.ratchet(pth);
                self.write_metric_diff(&diff);
                ok
            }
        };

        let test_success = self.failed == 0u;
        if !test_success {
            self.write_failures();
        }

        let success = ratchet_success && test_success;

        self.out.write_str("\ntest result: ");
        if success {
            // There's no parallelism at this point so it's safe to use color
            self.write_ok();
        } else {
            self.write_failed();
        }
        self.out.write_str(fmt!(". %u passed; %u failed; %u ignored, %u benchmarked\n\n",
                                self.passed, self.failed, self.ignored, self.benchmarked));
        return success;
    }
}

pub fn fmt_bench_samples(bs: &BenchSamples) -> ~str {
    if bs.mb_s != 0 {
        fmt!("%u ns/iter (+/- %u) = %u MB/s",
             bs.ns_iter_summ.median as uint,
             (bs.ns_iter_summ.max - bs.ns_iter_summ.min) as uint,
             bs.mb_s)
    } else {
        fmt!("%u ns/iter (+/- %u)",
             bs.ns_iter_summ.median as uint,
             (bs.ns_iter_summ.max - bs.ns_iter_summ.min) as uint)
    }
}

// A simple console test runner
pub fn run_tests_console(opts: &TestOpts,
                         tests: ~[TestDescAndFn]) -> bool {
    fn callback(event: &TestEvent, st: &mut ConsoleTestState) {
        debug!("callback(event=%?)", event);
        match copy *event {
            TeFiltered(ref filtered_tests) => st.write_run_start(filtered_tests.len()),
            TeWait(ref test) => st.write_test_start(test),
            TeResult(test, result) => {
                st.write_log(&test, &result);
                st.write_result(&result);
                match result {
                    TrOk => st.passed += 1,
                    TrIgnored => st.ignored += 1,
                    TrBench(bs) => {
                        st.metrics.insert_metric(test.name.to_str(),
                                                 bs.ns_iter_summ.median,
                                                 bs.ns_iter_summ.max - bs.ns_iter_summ.min);
                        st.benchmarked += 1
                    }
                    TrFailed => {
                        st.failed += 1;
                        st.failures.push(test);
                    }
                }
            }
        }
    }
    let st = @mut ConsoleTestState::new(opts);
    run_tests(opts, tests, |x| callback(&x, st));
    match opts.save_metrics {
        None => (),
        Some(ref pth) => {
            st.metrics.save(pth);
            st.out.write_str(fmt!("\nmetrics saved to: %s", pth.to_str()));
        }
    }
    return st.write_run_finish(&opts.ratchet_metrics);
}

#[test]
fn should_sort_failures_before_printing_them() {
    fn dummy() {}

    let s = do io::with_str_writer |wr| {
        let test_a = TestDesc {
            name: StaticTestName("a"),
            ignore: false,
            should_fail: false
        };

        let test_b = TestDesc {
            name: StaticTestName("b"),
            ignore: false,
            should_fail: false
        };

        let st = @ConsoleTestState {
            out: wr,
            log_out: option::None,
            use_color: false,
            total: 0u,
            passed: 0u,
            failed: 0u,
            ignored: 0u,
            benchmarked: 0u,
            metrics: MetricsMap::new(),
            failures: ~[test_b, test_a]
        };

        print_failures(st);
    };

    let apos = s.find_str("a").get();
    let bpos = s.find_str("b").get();
    assert!(apos < bpos);
}

fn use_color() -> bool { return get_concurrency() == 1; }

enum TestEvent {
    TeFiltered(~[TestDesc]),
    TeWait(TestDesc),
    TeResult(TestDesc, TestResult),
}

type MonitorMsg = (TestDesc, TestResult);

fn run_tests(opts: &TestOpts,
             tests: ~[TestDescAndFn],
             callback: &fn(e: TestEvent)) {

    let filtered_tests = filter_tests(opts, tests);
    let filtered_descs = filtered_tests.map(|t| copy t.desc);

    callback(TeFiltered(filtered_descs));

    let (filtered_tests, filtered_benchs) =
        do filtered_tests.partition |e| {
        match e.testfn {
            StaticTestFn(_) | DynTestFn(_) => true,
            StaticBenchFn(_) | DynBenchFn(_) => false
        }
    };

    // It's tempting to just spawn all the tests at once, but since we have
    // many tests that run in other processes we would be making a big mess.
    let concurrency = get_concurrency();
    debug!("using %u test tasks", concurrency);

    let mut remaining = filtered_tests;
    remaining.reverse();
    let mut pending = 0;

    let (p, ch) = stream();
    let ch = SharedChan::new(ch);

    while pending > 0 || !remaining.is_empty() {
        while pending < concurrency && !remaining.is_empty() {
            let test = remaining.pop();
            if concurrency == 1 {
                // We are doing one test at a time so we can print the name
                // of the test before we run it. Useful for debugging tests
                // that hang forever.
                callback(TeWait(copy test.desc));
            }
            run_test(!opts.run_tests, test, ch.clone());
            pending += 1;
        }

        let (desc, result) = p.recv();
        if concurrency != 1 {
            callback(TeWait(copy desc));
        }
        callback(TeResult(desc, result));
        pending -= 1;
    }

    // All benchmarks run at the end, in serial.
    for filtered_benchs.consume_iter().advance |b| {
        callback(TeWait(copy b.desc));
        run_test(!opts.run_benchmarks, b, ch.clone());
        let (test, result) = p.recv();
        callback(TeResult(test, result));
    }
}

// Windows tends to dislike being overloaded with threads.
#[cfg(windows)]
static SCHED_OVERCOMMIT : uint = 1;

#[cfg(unix)]
static SCHED_OVERCOMMIT : uint = 4u;

fn get_concurrency() -> uint {
    unsafe {
        let threads = rustrt::rust_sched_threads() as uint;
        if threads == 1 { 1 }
        else { threads * SCHED_OVERCOMMIT }
    }
}

#[allow(non_implicitly_copyable_typarams)]
pub fn filter_tests(
    opts: &TestOpts,
    tests: ~[TestDescAndFn]) -> ~[TestDescAndFn]
{
    let mut filtered = tests;

    // Remove tests that don't match the test filter
    filtered = if opts.filter.is_none() {
        filtered
    } else {
        let filter_str = match opts.filter {
          option::Some(ref f) => copy *f,
          option::None => ~""
        };

        fn filter_fn(test: TestDescAndFn, filter_str: &str) ->
            Option<TestDescAndFn> {
            if test.desc.name.to_str().contains(filter_str) {
                return option::Some(test);
            } else { return option::None; }
        }

        filtered.consume_iter().filter_map(|x| filter_fn(x, filter_str)).collect()
    };

    // Maybe pull out the ignored test and unignore them
    filtered = if !opts.run_ignored {
        filtered
    } else {
        fn filter(test: TestDescAndFn) -> Option<TestDescAndFn> {
            if test.desc.ignore {
                let TestDescAndFn {desc, testfn} = test;
                Some(TestDescAndFn {
                    desc: TestDesc {ignore: false, ..desc},
                    testfn: testfn
                })
            } else {
                None
            }
        };
        filtered.consume_iter().filter_map(|x| filter(x)).collect()
    };

    // Sort the tests alphabetically
    fn lteq(t1: &TestDescAndFn, t2: &TestDescAndFn) -> bool {
        t1.desc.name.to_str() < t2.desc.name.to_str()
    }
    sort::quick_sort(filtered, lteq);

    filtered
}

struct TestFuture {
    test: TestDesc,
    wait: @fn() -> TestResult,
}

pub fn run_test(force_ignore: bool,
                test: TestDescAndFn,
                monitor_ch: SharedChan<MonitorMsg>) {

    let TestDescAndFn {desc, testfn} = test;

    if force_ignore || desc.ignore {
        monitor_ch.send((desc, TrIgnored));
        return;
    }

    fn run_test_inner(desc: TestDesc,
                      monitor_ch: SharedChan<MonitorMsg>,
                      testfn: ~fn()) {
        let testfn_cell = ::std::cell::Cell::new(testfn);
        do task::spawn {
            let mut result_future = None; // task::future_result(builder);

            let mut task = task::task();
            task.unlinked();
            task.future_result(|r| { result_future = Some(r) });
            task.spawn(testfn_cell.take());

            let task_result = result_future.unwrap().recv();
            let test_result = calc_result(&desc,
                                          task_result == task::Success);
            monitor_ch.send((copy desc, test_result));
        }
    }

    match testfn {
        DynBenchFn(benchfn) => {
            let bs = ::test::bench::benchmark(benchfn);
            monitor_ch.send((desc, TrBench(bs)));
            return;
        }
        StaticBenchFn(benchfn) => {
            let bs = ::test::bench::benchmark(benchfn);
            monitor_ch.send((desc, TrBench(bs)));
            return;
        }
        DynTestFn(f) => run_test_inner(desc, monitor_ch, f),
        StaticTestFn(f) => run_test_inner(desc, monitor_ch, || f())
    }
}

fn calc_result(desc: &TestDesc, task_succeeded: bool) -> TestResult {
    if task_succeeded {
        if desc.should_fail { TrFailed }
        else { TrOk }
    } else {
        if desc.should_fail { TrOk }
        else { TrFailed }
    }
}


impl ToJson for Metric {
    fn to_json(&self) -> json::Json {
        let mut map = ~HashMap::new();
        map.insert(~"value", json::Number(self.value as float));
        map.insert(~"noise", json::Number(self.noise as float));
        json::Object(map)
    }
}

impl MetricMap {

    fn new() -> MetricMap {
        MetricMap(TreeMap::new())
    }

    /// Load MetricDiff from a file.
    fn load(p: &Path) -> MetricMap {
        assert!(os::path_exists(p));
        let f = io::file_reader(p).get();
        let mut decoder = json::Decoder(json::from_reader(f).get());
        MetricMap(Decodable::decode(&mut decoder))
    }

    /// Write MetricDiff to a file.
    pub fn save(&self, p: &Path) {
        let f = io::file_writer(p, [io::Create, io::Truncate]).get();
        json::to_pretty_writer(f, &self.to_json());
    }

    /// Compare against another MetricMap
    pub fn compare_to_old(&self, old: MetricMap) -> MetricDiff {
        let mut diff : MetricDiff = TreeMap::new();
        for old.iter().advance |(k, vold)| {
            let r = match self.find(k) {
                None => MetricRemoved,
                Some(v) => {
                    let delta = (v.value - vold.value);
                    if delta.abs() < vold.noise.abs() {
                        LikelyNoise
                    } else {
                        let pct = delta.abs() / v.value * 100.0;
                        if vold.noise < 0.0 {
                            // When 'noise' is negative, it means we want
                            // to see deltas that go up over time, and can
                            // only tolerate slight negative movement.
                            if delta < 0.0 {
                                Regression(pct)
                            } else {
                                Improvement(pct)
                            }
                        } else {
                            // When 'noise' is positive, it means we want
                            // to see deltas that go down over time, and
                            // can only tolerate slight positive movements.
                            if delta < 0.0 {
                                Improvement(pct)
                            } else {
                                Regression(pct)
                            }
                        }
                    }
                }
            };
            diff.insert(copy *k, r);
        }
        for self.iter().advance |(k, _)| {
            if !diff.contains_key(k) {
                diff.insert(copy *k, MetricAdded);
            }
        }
        diff
    }

    /// Insert a named `value` (+/- `noise`) metric into the map. The value
    /// must be non-negative. The `noise` indicates the uncertainty of the
    /// metric, which doubles as the "noise range" of acceptable
    /// pairwise-regressions on this named value, when comparing from one
    /// metric to the next using `compare_to_old`.
    ///
    /// If `noise` is positive, then it means this metric is of a value
    /// you want to see grow smaller, so a change larger than `noise` in the
    /// positive direction represents a regression.
    ///
    /// If `noise` is negative, then it means this metric is of a value
    /// you want to see grow larger, so a change larger than `noise` in the
    /// negative direction represents a regression.
    pub fn insert_metric(&mut self, name: &str, value: f64, noise: f64) {
        let m = Metric {
            value: value,
            noise: noise
        };
        self.insert(name.to_owned(), m);
    }

    /// Attempt to "ratchet" an external metric file. This involves loading
    /// metrics from a metric file (if it exists), comparing against
    /// the metrics in `self` using `compare_to_old`, and rewriting the
    /// file to contain the metrics in `self` if none of the
    /// `MetricChange`s are `Regression`. Returns the diff as well
    /// as a boolean indicating whether the ratchet succeeded.
    pub fn ratchet(&self, p: &Path) -> (MetricDiff, bool) {
        let old = if os::path_exists(p) {
            MetricMap::load(p)
        } else {
            MetricMap::new()
        };

        let diff : MetricDiff = self.compare_to_old(old);
        let ok = do diff.iter().all() |(_, v)| {
            match *v {
                Regression(_) => false,
                _ => true
            }
        };

        if ok {
            debug!("rewriting file '%s' with updated metrics");
            self.save(p);
        }
        return (diff, ok)
    }
}


// Benchmarking

impl BenchHarness {
    /// Callback for benchmark functions to run in their body.
    pub fn iter(&mut self, inner:&fn()) {
        self.ns_start = precise_time_ns();
        let k = self.iterations;
        for u64::range(0, k) |_| {
            inner();
        }
        self.ns_end = precise_time_ns();
    }

    pub fn ns_elapsed(&mut self) -> u64 {
        if self.ns_start == 0 || self.ns_end == 0 {
            0
        } else {
            self.ns_end - self.ns_start
        }
    }

    pub fn ns_per_iter(&mut self) -> u64 {
        if self.iterations == 0 {
            0
        } else {
            self.ns_elapsed() / self.iterations
        }
    }

    pub fn bench_n(&mut self, n: u64, f: &fn(&mut BenchHarness)) {
        self.iterations = n;
        debug!("running benchmark for %u iterations",
               n as uint);
        f(self);
    }

    // This is a more statistics-driven benchmark algorithm
    pub fn auto_bench(&mut self, f: &fn(&mut BenchHarness)) -> stats::Summary {

        // Initial bench run to get ballpark figure.
        let mut n = 1_u64;
        self.bench_n(n, |x| f(x));

        // Try to estimate iter count for 1ms falling back to 1m
        // iterations if first run took < 1ns.
        if self.ns_per_iter() == 0 {
            n = 1_000_000;
        } else {
            n = 1_000_000 / self.ns_per_iter();
        }

        let mut total_run = 0;
        let samples : &mut [f64] = [0.0_f64, ..50];
        loop {
            let loop_start = precise_time_ns();

            for samples.mut_iter().advance() |p| {
                self.bench_n(n as u64, |x| f(x));
                *p = self.ns_per_iter() as f64;
            };

            stats::winsorize(samples, 5.0);
            let summ = stats::Summary::new(samples);

            for samples.mut_iter().advance() |p| {
                self.bench_n(5 * n as u64, |x| f(x));
                *p = self.ns_per_iter() as f64;
            };

            stats::winsorize(samples, 5.0);
            let summ5 = stats::Summary::new(samples);

            debug!("%u samples, median %f, MAD=%f, MADP=%f",
                   samples.len(),
                   summ.median as float,
                   summ.median_abs_dev as float,
                   summ.median_abs_dev_pct as float);

            let now = precise_time_ns();
            let loop_run = now - loop_start;

            // If we've run for 100ms an seem to have converged to a
            // stable median.
            if loop_run > 100_000_000 &&
                summ.median_abs_dev_pct < 1.0 &&
                summ.median - summ5.median < summ5.median_abs_dev {
                return summ5;
            }

            total_run += loop_run;
            // Longest we ever run for is 10s.
            if total_run > 10_000_000_000 {
                return summ5;
            }

            n *= 2;
        }
    }




}

pub mod bench {
    use test::{BenchHarness, BenchSamples};

    pub fn benchmark(f: &fn(&mut BenchHarness)) -> BenchSamples {

        let mut bs = BenchHarness {
            iterations: 0,
            ns_start: 0,
            ns_end: 0,
            bytes: 0
        };

        let ns_iter_summ = bs.auto_bench(f);

        let iter_s = 1_000_000_000 / (ns_iter_summ.median as u64);
        let mb_s = (bs.bytes * iter_s) / 1_000_000;

        BenchSamples {
            ns_iter_summ: ns_iter_summ,
            mb_s: mb_s as uint
        }
    }
}

#[cfg(test)]
mod tests {
    use test::{TrFailed, TrIgnored, TrOk, filter_tests, parse_opts,
               TestDesc, TestDescAndFn,
               StaticTestName, DynTestName, DynTestFn};
    use test::{TestOpts, run_test};

    use std::either;
    use std::comm::{stream, SharedChan};
    use std::option;
    use std::vec;

    #[test]
    pub fn do_not_run_ignored_tests() {
        fn f() { fail!(); }
        let desc = TestDescAndFn {
            desc: TestDesc {
                name: StaticTestName("whatever"),
                ignore: true,
                should_fail: false
            },
            testfn: DynTestFn(|| f()),
        };
        let (p, ch) = stream();
        let ch = SharedChan::new(ch);
        run_test(false, desc, ch);
        let (_, res) = p.recv();
        assert!(res != TrOk);
    }

    #[test]
    pub fn ignored_tests_result_in_ignored() {
        fn f() { }
        let desc = TestDescAndFn {
            desc: TestDesc {
                name: StaticTestName("whatever"),
                ignore: true,
                should_fail: false
            },
            testfn: DynTestFn(|| f()),
        };
        let (p, ch) = stream();
        let ch = SharedChan::new(ch);
        run_test(false, desc, ch);
        let (_, res) = p.recv();
        assert_eq!(res, TrIgnored);
    }

    #[test]
    #[ignore(cfg(windows))]
    fn test_should_fail() {
        fn f() { fail!(); }
        let desc = TestDescAndFn {
            desc: TestDesc {
                name: StaticTestName("whatever"),
                ignore: false,
                should_fail: true
            },
            testfn: DynTestFn(|| f()),
        };
        let (p, ch) = stream();
        let ch = SharedChan::new(ch);
        run_test(false, desc, ch);
        let (_, res) = p.recv();
        assert_eq!(res, TrOk);
    }

    #[test]
    fn test_should_fail_but_succeeds() {
        fn f() { }
        let desc = TestDescAndFn {
            desc: TestDesc {
                name: StaticTestName("whatever"),
                ignore: false,
                should_fail: true
            },
            testfn: DynTestFn(|| f()),
        };
        let (p, ch) = stream();
        let ch = SharedChan::new(ch);
        run_test(false, desc, ch);
        let (_, res) = p.recv();
        assert_eq!(res, TrFailed);
    }

    #[test]
    fn first_free_arg_should_be_a_filter() {
        let args = ~[~"progname", ~"filter"];
        let opts = match parse_opts(args) {
          either::Left(o) => o,
          _ => fail!("Malformed arg in first_free_arg_should_be_a_filter")
        };
        assert!("filter" == (copy opts.filter).get());
    }

    #[test]
    fn parse_ignored_flag() {
        let args = ~[~"progname", ~"filter", ~"--ignored"];
        let opts = match parse_opts(args) {
          either::Left(o) => o,
          _ => fail!("Malformed arg in parse_ignored_flag")
        };
        assert!((opts.run_ignored));
    }

    #[test]
    pub fn filter_for_ignored_option() {
        fn dummy() {}

        // When we run ignored tests the test filter should filter out all the
        // unignored tests and flip the ignore flag on the rest to false

        let opts = TestOpts {
            filter: option::None,
            run_ignored: true,
            logfile: option::None,
            run_tests: true,
            run_benchmarks: false,
            ratchet: option::None,
        };

        let tests = ~[
            TestDescAndFn {
                desc: TestDesc {
                    name: StaticTestName("1"),
                    ignore: true,
                    should_fail: false,
                },
                testfn: DynTestFn(|| {}),
            },
            TestDescAndFn {
                desc: TestDesc {
                    name: StaticTestName("2"),
                    ignore: false,
                    should_fail: false
                },
                testfn: DynTestFn(|| {}),
            },
        ];
        let filtered = filter_tests(&opts, tests);

        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].desc.name.to_str(), ~"1");
        assert!(filtered[0].desc.ignore == false);
    }

    #[test]
    pub fn sort_tests() {
        let opts = TestOpts {
            filter: option::None,
            run_ignored: false,
            logfile: option::None,
            run_tests: true,
            run_benchmarks: false,
            ratchet_metrics: option::None,
            save_metrics: option::None,
        };

        let names =
            ~[~"sha1::test", ~"int::test_to_str", ~"int::test_pow",
             ~"test::do_not_run_ignored_tests",
             ~"test::ignored_tests_result_in_ignored",
             ~"test::first_free_arg_should_be_a_filter",
             ~"test::parse_ignored_flag", ~"test::filter_for_ignored_option",
             ~"test::sort_tests"];
        let tests =
        {
            fn testfn() { }
            let mut tests = ~[];
            for names.iter().advance |name| {
                let test = TestDescAndFn {
                    desc: TestDesc {
                        name: DynTestName(copy *name),
                        ignore: false,
                        should_fail: false
                    },
                    testfn: DynTestFn(copy testfn),
                };
                tests.push(test);
            }
            tests
        };
        let filtered = filter_tests(&opts, tests);

        let expected =
            ~[~"int::test_pow", ~"int::test_to_str", ~"sha1::test",
              ~"test::do_not_run_ignored_tests",
              ~"test::filter_for_ignored_option",
              ~"test::first_free_arg_should_be_a_filter",
              ~"test::ignored_tests_result_in_ignored",
              ~"test::parse_ignored_flag",
              ~"test::sort_tests"];

        let pairs = vec::zip(expected, filtered);

        for pairs.iter().advance |p| {
            match *p {
                (ref a, ref b) => {
                    assert!(*a == b.desc.name.to_str());
                }
            }
        }
    }
}
