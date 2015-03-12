// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(checked_arith_ops)]
#![feature(checked_bit_ops)]

// Tests for `checked_*` methods from `core::num::Int` trait.

use std::fmt;
use std::num::Int;
use std::ops::Neg;

#[derive(PartialEq)]
enum IntType {
    I8   =  0b1,
    U8   =  0b10,
    I16  =  0b100,
    U16  =  0b1000,
    I32  =  0b10000,
    U32  =  0b100000,
    I64  =  0b1000000,
    U64  =  0b10000000,
    ISIZE = 0b100000000,
    USIZE = 0b1000000000,
}

const ALL_INT_TYPES: &'static [IntType] = {
    use self::IntType::*;
    &[I8, U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]
};

trait BlindAs {
    fn as_i8(&self) -> i8;
    fn as_i16(&self) -> i16;
    fn as_i32(&self) -> i32;
    fn as_i64(&self) -> i64;
    fn as_isize(&self) -> isize;
    fn as_u8(&self) -> u8;
    fn as_u16(&self) -> u16;
    fn as_u32(&self) -> u32;
    fn as_u64(&self) -> u64;
    fn as_usize(&self) -> usize;
}

macro_rules! impl_blind_as {
    ($($t:ty)*) => { $(
        impl BlindAs for $t {
            fn as_i8(&self) -> i8 { *self as i8 }
            fn as_i16(&self) -> i16 { *self as i16 }
            fn as_i32(&self) -> i32 { *self as i32 }
            fn as_i64(&self) -> i64 { *self as i64 }
            fn as_isize(&self) -> isize { *self as isize }
            fn as_u8(&self) -> u8 { *self as u8 }
            fn as_u16(&self) -> u16 { *self as u16 }
            fn as_u32(&self) -> u32 { *self as u32 }
            fn as_u64(&self) -> u64 { *self as u64 }
            fn as_usize(&self) -> usize { *self as usize }
        } )*
    }
}

impl_blind_as!(i8 i16 i32 i64 isize u8 u16 u32 u64 usize);

impl IntType {
    fn checked_is_none<T: Int+fmt::Debug>(&self, n: T) {
        use self::IntType::*;
        match *self {
            I8 => assert_eq!(n.checked_as_i8(), None),
            U8 => assert_eq!(n.checked_as_u8(), None),
            I16 => assert_eq!(n.checked_as_i16(), None),
            U16 => assert_eq!(n.checked_as_u16(), None),
            I32 => assert_eq!(n.checked_as_i16(), None),
            U32 => assert_eq!(n.checked_as_u16(), None),
            I64 => assert_eq!(n.checked_as_i64(), None),
            U64 => assert_eq!(n.checked_as_u64(), None),
            ISIZE => assert_eq!(n.checked_as_isize(), None),
            USIZE => assert_eq!(n.checked_as_usize(), None),
        }
    }

    fn checked_matches_blind<T: Int+fmt::Debug+BlindAs>(&self, n: T) {
        use self::IntType::*;
        println!("{:?}", n);
        match *self {
            I8 => assert_eq!(n.checked_as_i8(), Some(n.as_i8())),
            U8 => assert_eq!(n.checked_as_u8(), Some(n.as_u8())),
            I16 => assert_eq!(n.checked_as_i16(), Some(n.as_i16())),
            U16 => assert_eq!(n.checked_as_u16(), Some(n.as_u16())),
            I32 => assert_eq!(n.checked_as_i32(), Some(n.as_i32())),
            U32 => assert_eq!(n.checked_as_u32(), Some(n.as_u32())),
            I64 => assert_eq!(n.checked_as_i64(), Some(n.as_i64())),
            U64 => assert_eq!(n.checked_as_u64(), Some(n.as_u64())),
            ISIZE => assert_eq!(n.checked_as_isize(), Some(n.as_isize())),
            USIZE => assert_eq!(n.checked_as_usize(), Some(n.as_usize())),
        }
    }
}


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

    fn run_neg_tests<T:Int+fmt::Debug>(inputs: &[T], expect: &[Option<T>]) {
        assert_eq!(inputs.len(), expect.len()); // confirm test is well-formed

        for (i, (&n, &r)) in inputs.iter().zip(expect.iter()).enumerate() {
            assert_eq!((i, n.checked_neg()), (i, r));
        }
    }


    type CanConvertViaAs<'a> = &'a [IntType];

    fn run_as_tests<T:Int+fmt::Debug+BlindAs>(inputs: &[(T, &[IntType])]) {
        for &(n, n_can) in inputs.iter() {
            for t in ALL_INT_TYPES {
                if n_can.iter().any(|c| c == t) {
                    t.checked_matches_blind(n);
                } else {
                    t.checked_is_none(n);
                }
            }
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

        run_neg_tests(&[     0,        1,      -1,  std::i8::MAX, std::i8::MIN],
                      &[Some(0), Some(-1), Some(1), Some(-0x7F),          None]);

        const INPUTS_AS: Inputs<i8> = &[0, 0x1, 0x7F, 0x80, 0xFF];

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

        run_neg_tests(&[     0,        1,      -1,  std::i16::MAX, std::i16::MIN],
                      &[Some(0), Some(-1), Some(1), Some(-0x7FFF),          None]);

        const INPUTS_AS: Inputs<i16> = &[0, 0x1, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000, 0xFFFF];
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

        run_neg_tests(&[     0,        1,      -1,  std::i32::MAX,      std::i32::MIN],
                      &[Some(0), Some(-1), Some(1), Some(-0x7FFF_FFFF),          None]);

        const INPUTS_AS: Inputs<i32> = &[0, 0x1, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000, 0xFFFF,
                                         0x1_0000, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF];
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

        run_neg_tests(&[     0,        1,      -1,
                             std::i64::MAX,      std::i64::MIN],

                      &[Some(0), Some(-1), Some(1),
                        Some(-0x7FFF_FFFF_FFFF_FFFF),     None]);

        const INPUTS_AS: Inputs<i64> =
            &[0,
              0x1,           0x7F,                  0x80,                  0xFF,
              0x100,         0x7FFF,                0x8000,                0xFFFF,
              0x1_0000,      0x7FFF_FFFF,           0x8000_0000,           0xFFFF_FFFF,
              0x1_0000_0000, 0x7FFF_FFFF_FFFF_FFFF, 0x8000_0000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF];


        const GTE_8: &'static [IntType] = {
            use self::IntType::*;
            &[I8, U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE] };
        const GTE_16: &'static [IntType] = {
            use self::IntType::*;
            &[        I16, U16, I32, U32, I64, U64, ISIZE, USIZE] };
        const GTE_32: &'static [IntType] = {
            use self::IntType::*;
            &[                  I32, U32, I64, U64, ISIZE, USIZE] };
        #[cfg(target_pointer_width = "32")]
        const GTE_64: &'static [IntType] = {
            use self::IntType::*;
            &[                            I64, U64              ] };
        #[cfg(target_pointer_width = "64")]
        const GTE_64: &'static [IntType] = {
            use self::IntType::*;
            &[                            I64, U64, ISIZE, USIZE] };

        match true {
            #[cfg(target_pointer_width = "64")]
            true => {
                use self::IntType::*;

                run_as_tests(
                    &[(   0, &[I8, U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x01, &[I8, U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x7f, &[I8, U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x80, &[    U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0xFF, &[    U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x100, &[       I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x7FFF, &[      I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x8000, &[           U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0xFFFF, &[           U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x1_0000, &[              I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x7FFF_FFFF, &[           I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x8000_0000, &[                U32, I64, U64, ISIZE, USIZE]),
                      (0xFFFF_FFFF, &[                U32, I64, U64, ISIZE, USIZE]),
                      (0x1_0000_0000, &[                   I64, U64, ISIZE, USIZE]),
                      (0x7FFF_FFFF_FFFF_FFFF, &[           I64, U64, ISIZE, USIZE]),
                      (0x8000_0000_0000_0000, &[           I64, U64, ISIZE, USIZE]),
                      (0xFFFF_FFFF_FFFF_FFFF, &[           I64, U64, ISIZE, USIZE])]);
            }
            #[cfg(target_pointer_width = "32")]
            true => {
                use self::IntType::*;

                run_as_tests(
                    &[(   0, &[I8, U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x01, &[I8, U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x7f, &[I8, U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x80, &[    U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0xFF, &[    U8, I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x100, &[       I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x7FFF, &[      I16, U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x8000, &[           U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0xFFFF, &[           U16, I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x1_0000, &[              I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x7FFF_FFFF, &[           I32, U32, I64, U64, ISIZE, USIZE]),
                      (0x8000_0000, &[                U32, I64, U64, ISIZE, USIZE]),
                      (0xFFFF_FFFF, &[                U32, I64, U64, ISIZE, USIZE]),
                      (0x1_0000_0000, &[                   I64, U64 ]),
                      (0x7FFF_FFFF_FFFF_FFFF, &[           I64, U64 ]),
                      (0x8000_0000_0000_0000, &[           I64, U64 ]),
                      (0xFFFF_FFFF_FFFF_FFFF, &[           I64, U64 ])]);
            }

            _ => panic!("need case for other target_pointer_width"),
        }
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

        const INPUTS_NEG: Inputs<isize> =
            &[     0,        1,      -1,               std::isize::MAX, std::isize::MIN];

        #[cfg(target_pointer_width = "32")]
        const EXPECT_NEG: &'static [Option<isize>] =
            &[Some(0), Some(-1), Some(1), Some(-0x7FFF_FFFF),            None];

        #[cfg(target_pointer_width = "64")]
        const EXPECT_NEG: &'static [Option<isize>] =
            &[Some(0), Some(-1), Some(1), Some(-0x7FFF_FFFF_FFFF_FFFF),            None];

        run_neg_tests(INPUTS_NEG, EXPECT_NEG);
    }
}
