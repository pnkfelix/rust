// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::os;
use std::str;
use std::io::process::{ProcessExit, Process, ProcessConfig, ProcessOutput};
use std::unstable::dynamic_lib::DynamicLibrary;

fn target_env(lib_path: &str, prog: &str) -> Vec<(~str,~str)> {
    let prog = if cfg!(windows) {prog.slice_to(prog.len() - 4)} else {prog};
    let aux_path = prog + ".libaux";

    // Need to be sure to put both the lib_path and the aux path in the dylib
    // search path for the child.
    let mut path = DynamicLibrary::search_path();
    path.insert(0, Path::new(aux_path));
    path.insert(0, Path::new(lib_path));

    // Remove the previous dylib search path var
    let var = DynamicLibrary::envvar();
    let mut env: Vec<(~str,~str)> = os::env().move_iter().collect();
    match env.iter().position(|&(ref k, _)| k.as_slice() == var) {
        Some(i) => { env.remove(i); }
        None => {}
    };

    // Add the new dylib search path var
    let newpath = DynamicLibrary::create_path(path.as_slice());
    env.push((var.to_owned(),
              str::from_utf8(newpath.as_slice()).unwrap().to_owned()));
    return env;
}

pub struct Result {pub status: ProcessExit, pub out: ~str, pub err: ~str}

pub fn run(lib_path: &str,
           prog: &str,
           args: &[~str],
           env: Vec<(~str, ~str)> ,
           input: Option<~str>) -> Option<Result> {

    let env = env.clone().append(target_env(lib_path, prog).as_slice());
    let mut opt_process = Process::configure(ProcessConfig {
        program: prog,
        args: args,
        env: Some(env.as_slice()),
        .. ProcessConfig::new()
    });

    match opt_process {
        Ok(ref mut process) => {
            for input in input.iter() {
                process.stdin.get_mut_ref().write(input.as_bytes()).unwrap();
            }
            let ProcessOutput { status, output, error } = process.wait_with_output();

            Some(Result {
                status: status,
                out: str::from_utf8(output.as_slice()).unwrap().to_owned(),
                err: str::from_utf8(error.as_slice()).unwrap().to_owned()
            })
        },
        Err(..) => None
    }
}

pub fn run_background(lib_path: &str,
           prog: &str,
           args: &[~str],
           env: Vec<(~str, ~str)> ,
           input: Option<~str>) -> Option<Process> {

    let env = env.clone().append(target_env(lib_path, prog).as_slice());
    let opt_process = Process::configure(ProcessConfig {
        program: prog,
        args: args,
        env: Some(env.as_slice()),
        .. ProcessConfig::new()
    });

    match opt_process {
        Ok(mut process) => {
            for input in input.iter() {
                process.stdin.get_mut_ref().write(input.as_bytes()).unwrap();
            }

            Some(process)
        },
        Err(..) => None
    }
}
