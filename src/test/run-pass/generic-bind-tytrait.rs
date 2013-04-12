// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

trait Rait   { fn foo(&self) -> int; }
trait B3     { fn bar(&self) -> int; }
trait Raitor { fn foo(&self) -> int; }

struct FooIsOne();
struct FooIsTwo();
struct FooIsOneOrTwo();

impl Rait   for FooIsOne { fn foo(&self) -> int { 1 } }
impl Raitor for FooIsOne { fn foo(&self) -> int { 1 } }

impl Rait   for FooIsTwo { fn foo(&self) -> int { 2 } }
impl Raitor for FooIsTwo { fn foo(&self) -> int { 2 } }

impl Rait   for FooIsOneOrTwo { fn foo(&self) -> int { 1 } }
impl Raitor for FooIsOneOrTwo { fn foo(&self) -> int { 2 } }

impl B3 for FooIsOne      { fn bar(&self) -> int { 3 } }
impl B3 for FooIsTwo      { fn bar(&self) -> int { 3 } }
impl B3 for FooIsOneOrTwo { fn bar(&self) -> int { 3 } }

fn foo1<Y: Rait             >(y: Y) -> int { y.foo() }
fn foo2<Y: Rait + B3        >(y: Y) -> int { y.foo() }
fn bar2<Y: Rait + B3        >(y: Y) -> int { y.bar() }
fn foo3<Y: R = Rait         >(y: Y) -> int { y.foo() }
fn foo4<Y: Raitor           >(y: Y) -> int { y.foo() }

fn foo5<Y: R = Rait + Raitor>(y: Y) -> int { fail!() /* y.R::foo */ }
fn foo6<Y: Rait + R = Raitor>(y: Y) -> int { fail!() /* y.R::foo */ }
fn foo7<Y: R = Rait + B = B3>(y: Y) -> int { fail!() /* y.R::foo */ }

trait Left  { fn make() -> Self; }
trait Right { fn make() -> Self; }

pub fn main() {
    let is1    = FooIsOne;
    let is2    = FooIsTwo;
    let is1or2 = FooIsOneOrTwo;

    assert!(foo1(is1) == 1);
    assert!(foo2(is1) == 1);
    assert!(bar2(is1) == 3);
    assert!(foo3(is1) == 1);
    assert!(foo4(is1) == 1);

    assert!(foo1(is2) == 2);
    assert!(foo2(is2) == 2);
    assert!(bar2(is2) == 3);
    assert!(foo3(is2) == 2);
    assert!(foo4(is2) == 2);
}
