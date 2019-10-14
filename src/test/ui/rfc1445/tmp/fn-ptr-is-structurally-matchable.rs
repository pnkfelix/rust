// run-pass

// This file checks that fn ptrs are considered structurally matchable.
// See also rust-lang/rust#63479.

fn main() {
    let mut count = 0;

    // A type which is not structurally matchable:
    struct NotSM;

    // And one that is:
    #[derive(PartialEq, Eq)]
    struct SM;

    fn trivial() {}

    fn sm_to(_: SM) {}
    fn not_sm_to(_: NotSM) {}
    fn to_sm() -> SM { SM }
    fn to_not_sm() -> NotSM { NotSM }

    // To recreate the scenario of interest in #63479, we need to add
    // a ref-level-of-indirection so that we descend into the type.

    fn r_sm_to(_: &SM) {}
    fn r_not_sm_to(_: &NotSM) {}
    fn r_to_r_sm(_: &()) -> &SM { &SM }
    fn r_to_r_not_sm(_: &()) -> &NotSM { &NotSM }

    #[derive(PartialEq, Eq)]
    struct Wrap<T>(T);

    // Check that fn(&T) is #[structural_match] when T is too.
    const CFN6: Wrap<fn(&SM)> = Wrap(r_sm_to);
    let input: Wrap<fn(&SM)> = Wrap(r_sm_to);
    match Wrap(input) {
        Wrap(CFN6) => count += 1,
        Wrap(_) => {}
    };
}
