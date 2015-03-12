// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Tests for `checked_*` methods from `core::num::Int` trait.

use std::fmt;
use std::num::Int;
use std::ops::Neg;

fn main() {
    #![allow(overflowing_literals)]
    // To make the tests self-documenting, they include tests
    // referencing the boundary-condition constants MAX and MIN as
    // well as tests writtens in terms of some interesting cases in
    // the bit-level representations (especially when the handling of
    // signed versus unsigned differs)
    //
    // Some "interesting cases" are:
    //
    // - all-zeros:                             0x0000_0000 (aka `0`)
    // - all-ones expect two most sig bits:     0x3FFF_FFFF (aka `!(3 << N-2)`)
    // - all-zeros except 2nd most sig bit:     0x4000_0000 (aka `1 << N-2`)
    // - all-ones except most-significant bit:  0x7FFF_FFFF (aka `!(1 << N-1)`)
    // - all-zeros except most-significant bit: 0x8000_0000 (aka `1 << N-1`)
    // - all-ones:                              0xFFFF_FFFF (aka `!0`)

    type Inputs<T> = &'static [T];

    type Expected<T> = ((T, T),
                        //        input.method(.0.0)  input.method(.0.1)
                        &'static [(        Option<T>,          Option<T>)]);

    fn run_add_sub_tests<T:Int+Neg<Output=T>+fmt::Debug>(inputs: Inputs<T>,
                                                         for_add: Expected<T>) {
        assert_eq!(inputs.len(), for_add.1.len()); // confirm test is well-formed

        for (i, (n, &(p1, n1))) in inputs.iter().zip(for_add.1.iter()).enumerate() {
            let pos_one = (for_add.0).0;
            let neg_one = (for_add.0).1;
            assert_eq!((i, n.checked_add(pos_one)), (i, p1));
            assert_eq!((i, n.checked_add(neg_one)), (i, n1));

            assert_eq!((i, n.checked_sub(pos_one)), (i, n1));
            assert_eq!((i, n.checked_sub(neg_one)), (i, p1));
        }
    }

    fn run_mul_tests<T:Int+Neg<Output=T>+fmt::Debug>(inputs: Inputs<T>,
                                                     for_mul: Expected<T>) {
        assert_eq!(inputs.len(), for_mul.1.len()); // confirm test is well-formed

        for (i, (n, &(p1, n1))) in inputs.iter().zip(for_mul.1.iter()).enumerate() {
            let pos_one = (for_mul.0).0;
            let neg_one = (for_mul.0).1;
            assert_eq!((i, n.checked_mul(pos_one)), (i, p1));
            assert_eq!((i, n.checked_mul(neg_one)), (i, n1));
        }
    }

    fn run_div_tests<T:Int+Neg<Output=T>+fmt::Debug>(inputs: Inputs<T>,
                                                     for_div: Expected<T>) {
        assert_eq!(inputs.len(), for_div.1.len()); // confirm test is well-formed

        for (i, (n, &(p1, n1))) in inputs.iter().zip(for_div.1.iter()).enumerate() {
            let pos_one = (for_div.0).0;
            let neg_one = (for_div.0).1;
            assert_eq!((i, n.checked_div(pos_one)), (i, p1));
            assert_eq!((i, n.checked_div(neg_one)), (i, n1));
        }
    }

    {
        const NUMS: Inputs<i8> = &[0x00, 0x3F,
                                   0x40, 0x7F,
                                   0x80, 0xFF,
                                   std::i8::MIN, std::i8::MAX];

        const EXPECT_ADD: Expected<i8> = ((         1,         -1),     // RHS; below is LHS INPUT
                                          &[(Some(0x01), Some(0xFF)),    // 0x00
                                            (Some(0x40), Some(0x3E)),    // 0x3F
                                            (Some(0x41), Some(0x3F)),    // 0x40
                                            (None,       Some(0x7E)),    // 0x7F
                                            (Some(0x81), None),          // 0x80
                                            (Some(   0), Some(0xFE)),    // 0xFF
                                            (Some(0x81), None),          // MIN
                                            (None,       Some(0x7E))]);  // MAX

        const EXPECT_MUL: Expected<i8> = ((         2,          -1),    // RHS; below is LHS INPUT
                                          &[(Some(   0), Some(    0)),   // 0x00
                                            (Some(0x7E), Some(-0x3F)),   // 0x3F
                                            (None,       Some(-0x40)),   // 0x40
                                            (None,       Some(-0x7F)),   // 0x7F
                                            (None,       None),          // 0x80
                                            (Some(0xFE), Some(-0xFF)),   // 0xFF
                                            (None,       None),          // MIN
                                            (None,       Some(-0x7F))]); // MAX

        const EXPECT_DIV: Expected<i8> = ((         2,          -1),    // RHS; below is LHS INPUT
                                          &[(Some(   0), Some(    0)),   // 0x00
                                            (Some(0x1F), Some(-0x3F)),   // 0x3F
                                            (Some(0x20), Some(-0x40)),   // 0x40
                                            (Some(0x3F), Some(-0x7F)),   // 0x7F
                                            (Some(0xC0), None),          // 0x80
                                            (Some(   0), Some( 0x01)),   // 0xFF
                                            (Some(0xC0), None),          // MIN
                                            (Some(0x3F), Some(-0x7F))]); // MAX

        run_add_sub_tests(NUMS, EXPECT_ADD);
        run_mul_tests(NUMS, EXPECT_MUL);
        run_div_tests(NUMS, EXPECT_DIV);
    }

    {
        const NUMS: Inputs<i16> = &[0x0000, 0x3FFF,
                                    0x4000, 0x7FFF,
                                    0x8000, 0xFFFF,
                                    std::i16::MIN, std::i16::MAX];

        const EXPECT_ADD: Expected<i16> = ((           1,           -1),    // RHS; below is LHS INPUT
                                           &[(Some(0x0001), Some(0xFFFF)),   // 0x0000
                                             (Some(0x4000), Some(0x3FFE)),   // 0x3FFF
                                             (Some(0x4001), Some(0x3FFF)),   // 0x4000
                                             (None,         Some(0x7FFE)),   // 0x7FFF
                                             (Some(0x8001), None),           // 0x8000
                                             (Some(     0), Some(0xFFFE)),   // 0xFFFF
                                             (Some(0x8001), None),           // MIN
                                             (None,         Some(0x7FFE))]); // MAX

        const EXPECT_MUL: Expected<i16> = ((           2,           -1),    // RHS; below is LHS INPUT
                                          &[(Some(     0), Some(      0)),   // 0x0000
                                            (Some(0x7FFE), Some(-0x3FFF)),   // 0x3FFF
                                            (None,         Some(-0x4000)),   // 0x4000
                                            (None,         Some(-0x7FFF)),   // 0x7FFF
                                            (None,         None),            // 0x8000
                                            (Some(0xFFFE), Some(-0xFFFF)),   // 0xFFFF
                                            (None,         None),            // MIN
                                            (None,         Some(-0x7FFF))]); // MAX

        const EXPECT_DIV: Expected<i16> = ((           2,            -1),    // RHS; below is LHS INPUT
                                           &[(Some(     0), Some(      0)),   // 0x0000
                                             (Some(0x1FFF), Some(-0x3FFF)),   // 0x3FFF
                                             (Some(0x2000), Some(-0x4000)),   // 0x4000
                                             (Some(0x3FFF), Some(-0x7FFF)),   // 0x7FFF
                                             (Some(0xC000), None),            // 0x8000
                                             (Some(     0), Some( 0x0001)),   // 0xFFFF
                                             (Some(0xC000), None),            // MIN
                                             (Some(0x3FFF), Some(-0x7FFF))]); // MAX

        run_add_sub_tests(&NUMS, EXPECT_ADD);
        run_mul_tests(&NUMS, EXPECT_MUL);
        run_div_tests(&NUMS, EXPECT_DIV);

    }

    {
        const NUMS: Inputs<i32> = &[0x0000_0000, 0x3FFF_FFFF,
                                    0x4000_0000, 0x7FFF_FFFF,
                                    0x8000_0000, 0xFFFF_FFFF,
                                    std::i32::MIN, std::i32::MAX];

        const EXPECT_ADD: Expected<i32> = ((                1,                -1),
                                           &[(Some(0x0000_0001), Some(0xFFFF_FFFF)),
                                             (Some(0x4000_0000), Some(0x3FFF_FFFE)),
                                             (Some(0x4000_0001), Some(0x3FFF_FFFF)),
                                             (None,              Some(0x7FFF_FFFE)),
                                             (Some(0x8000_0001), None),
                                             (Some(          0), Some(0xFFFF_FFFE)),
                                             (Some(0x8000_0001), None),
                                             (None,              Some(0x7FFF_FFFE))]);

        const EXPECT_MUL: Expected<i32> = ((                2,                 -1),
                                           &[(Some(0x0000_0000), Some( 0x0000_0000)),
                                            (Some(0x7FFF_FFFE), Some(-0x3FFF_FFFF)),
                                             (None,              Some(-0x4000_0000)),
                                             (None,              Some(-0x7FFF_FFFF)),
                                             (None,              None),
                                             (Some(0xFFFF_FFFE), Some(-0xFFFF_FFFF)),
                                             (None,              None),
                                             (None,              Some(-0x7FFF_FFFF))]);

        const EXPECT_DIV: Expected<i32> = ((                2,                 -1),
                                           &[(Some(          0), Some(           0)),
                                             (Some(0x1FFF_FFFF), Some(-0x3FFF_FFFF)),
                                             (Some(0x2000_0000), Some(-0x4000_0000)),
                                             (Some(0x3FFF_FFFF), Some(-0x7FFF_FFFF)),
                                             (Some(0xC000_0000), None),
                                             (Some(          0), Some( 0x0000_0001)),
                                             (Some(0xC000_0000), None),
                                             (Some(0x3FFF_FFFF), Some(-0x7FFF_FFFF))]);

        run_add_sub_tests(NUMS, EXPECT_ADD);
        run_mul_tests(NUMS, EXPECT_MUL);
        run_div_tests(NUMS, EXPECT_DIV);
    }

    {
        const NUMS: Inputs<i64> = &[0x0000_0000_0000_0000, 0x3FFF_FFFF_FFFF_FFFF,
                                    0x4000_0000_0000_0000, 0x7FFF_FFFF_FFFF_FFFF,
                                    0x8000_0000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF,
                                    std::i64::MIN, std::i64::MAX];

        const EXPECT_ADD: Expected<i64> =
            ((                          1,                          -1),
             &[(Some(0x0000_0000_0000_0001), Some(0xFFFF_FFFF_FFFF_FFFF)),
               (Some(0x4000_0000_0000_0000), Some(0x3FFF_FFFF_FFFF_FFFE)),
               (Some(0x4000_0000_0000_0001), Some(0x3FFF_FFFF_FFFF_FFFF)),
               (None,                        Some(0x7FFF_FFFF_FFFF_FFFE)),
               (Some(0x8000_0000_0000_0001), None),
               (Some(0x0000_0000_0000_0000), Some(0xFFFF_FFFF_FFFF_FFFE)),
               (Some(0x8000_0000_0000_0001), None),
               (None,                        Some(0x7FFF_FFFF_FFFF_FFFE))]);

        const EXPECT_MUL: Expected<i64> =
            ((                          2,                           -1),
             &[(Some(0x0000_0000_0000_0000), Some( 0x0000_0000_0000_0000)),
               (Some(0x7FFF_FFFF_FFFF_FFFE), Some(-0x3FFF_FFFF_FFFF_FFFF)),
               (None,                        Some(-0x4000_0000_0000_0000)),
               (None,                        Some(-0x7FFF_FFFF_FFFF_FFFF)),
               (None,                        None),
               (Some(0xFFFF_FFFF_FFFF_FFFE), Some(-0xFFFF_FFFF_FFFF_FFFF)),
               (None,                        None),
               (None,                        Some(-0x7FFF_FFFF_FFFF_FFFF))]);

        const EXPECT_DIV: Expected<i64> =
            ((                          2,                           -1),
             &[(Some(                    0), Some(                     0)),
               (Some(0x1FFF_FFFF_FFFF_FFFF), Some(-0x3FFF_FFFF_FFFF_FFFF)),
               (Some(0x2000_0000_0000_0000), Some(-0x4000_0000_0000_0000)),
               (Some(0x3FFF_FFFF_FFFF_FFFF), Some(-0x7FFF_FFFF_FFFF_FFFF)),
               (Some(0xC000_0000_0000_0000), None),
               (Some(                    0), Some( 0x0000_0000_0000_0001)),
               (Some(0xC000_0000_0000_0000), None),
               (Some(0x3FFF_FFFF_FFFF_FFFF), Some(-0x7FFF_FFFF_FFFF_FFFF))]);

        run_add_sub_tests(NUMS, EXPECT_ADD);
        run_mul_tests(NUMS, EXPECT_MUL);
        run_div_tests(NUMS, EXPECT_DIV);
    }

    {
        #[cfg(target_pointer_width = "32")]
        const NUMS: Inputs<isize> = [0x0000_0000, 0x7FFF_FFFF,
                                     0x8000_0000, 0xFFFF_FFFF,
                                     std::isize::MIN, std::isize::MAX];

        #[cfg(target_pointer_width = "32")]
        const EXPECT_ADD: Expected<isize> =
            (                 1,                -1,
             [(Some(0x0000_0001), Some(0xFFFF_FFFF)),
              (None,              Some(0x7FFF_FFFE)),
              (Some(0x8000_0001), None),
              (Some(0x0000_0000), Some(0xFFFF_FFFE)),
              (Some(0x8000_0001), None),
              (None,              Some(0x7FFF_FFFE))]);

        #[cfg(target_pointer_width = "32")]
        const EXPECT_MUL: Expected<isize> =
            ((                2,                 -1),
             [(Some(0x0000_0000), Some( 0x0000_0000)),
              (Some(0x7FFF_FFFE), Some(-0x3FFF_FFFF)),
              (None,              Some(-0x4000_0000)),
              (None,              Some(-0x7FFF_FFFF)),
              (None,              None),
              (Some(0xFFFF_FFFE), Some(-0xFFFF_FFFF)),
              (None,              None),
              (None,              Some(-0x7FFF_FFFF))]);

        #[cfg(target_pointer_width = "32")]
        const EXPECT_DIV: Expected<isize> =
            ((                2,                 -1),
             [(Some(          0), Some(           0)),
              (Some(0x1FFF_FFFF), Some(-0x3FFF_FFFF)),
              (Some(0x2000_0000), Some(-0x4000_0000)),
              (Some(0x3FFF_FFFF), Some(-0x7FFF_FFFF)),
              (Some(0xC000_0000), None),
              (Some(          0), Some( 0x0000_0001)),
              (Some(0xC000_0000), None),
              (Some(0x3FFF_FFFF), Some(-0x7FFF_FFFF))]);


        #[cfg(target_pointer_width = "64")]
        const NUMS: Inputs<isize> = &[0x0000_0000_0000_0000, 0x3FFF_FFFF_FFFF_FFFF,
                                      0x4000_0000_0000_0000, 0x7FFF_FFFF_FFFF_FFFF,
                                      0x8000_0000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF,
                                      std::isize::MIN, std::isize::MAX];

        #[cfg(target_pointer_width = "64")]
        const EXPECT_ADD: Expected<isize> =
            ((                           1,                          -1),
             &[(Some(0x0000_0000_0000_0001), Some(0xFFFF_FFFF_FFFF_FFFF)),
               (Some(0x4000_0000_0000_0000), Some(0x3FFF_FFFF_FFFF_FFFE)),
               (Some(0x4000_0000_0000_0001), Some(0x3FFF_FFFF_FFFF_FFFF)),
               (None,                        Some(0x7FFF_FFFF_FFFF_FFFE)),
               (Some(0x8000_0000_0000_0001), None),
               (Some(0x0000_0000_0000_0000), Some(0xFFFF_FFFF_FFFF_FFFE)),
               (Some(0x8000_0000_0000_0001), None),
               (None,                        Some(0x7FFF_FFFF_FFFF_FFFE))]);

        #[cfg(target_pointer_width = "64")]
        const EXPECT_MUL: Expected<isize> =
            ((                          2,                           -1),
             &[(Some(0x0000_0000_0000_0000), Some( 0x0000_0000_0000_0000)),
               (Some(0x7FFF_FFFF_FFFF_FFFE), Some(-0x3FFF_FFFF_FFFF_FFFF)),
               (None,                        Some(-0x4000_0000_0000_0000)),
               (None,                        Some(-0x7FFF_FFFF_FFFF_FFFF)),
               (None,                        None),
               (Some(0xFFFF_FFFF_FFFF_FFFE), Some(-0xFFFF_FFFF_FFFF_FFFF)),
               (None,                        None),
               (None,                        Some(-0x7FFF_FFFF_FFFF_FFFF))]);

        #[cfg(target_pointer_width = "64")]
        const EXPECT_DIV: Expected<isize> =
            ((                          2,                           -1),
             &[(Some(                    0), Some(                     0)),
               (Some(0x1FFF_FFFF_FFFF_FFFF), Some(-0x3FFF_FFFF_FFFF_FFFF)),
               (Some(0x2000_0000_0000_0000), Some(-0x4000_0000_0000_0000)),
               (Some(0x3FFF_FFFF_FFFF_FFFF), Some(-0x7FFF_FFFF_FFFF_FFFF)),
               (Some(0xC000_0000_0000_0000), None),
               (Some(                    0), Some( 0x0000_0000_0000_0001)),
               (Some(0xC000_0000_0000_0000), None),
               (Some(0x3FFF_FFFF_FFFF_FFFF), Some(-0x7FFF_FFFF_FFFF_FFFF))]);

        run_add_sub_tests(NUMS, EXPECT_ADD);
        run_mul_tests(NUMS, EXPECT_MUL);
        run_div_tests(NUMS, EXPECT_DIV);
    }
}
