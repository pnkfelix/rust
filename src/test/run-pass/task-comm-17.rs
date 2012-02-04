// Issue #922

use std;
import task;

fn f() {
}

fn main() {
    task::spawn {|| f() };
}