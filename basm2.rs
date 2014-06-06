#![no_std]
#![feature(asm)]

#![crate_type="lib"]

pub unsafe fn get_sp_limit() -> uint {
    let limit;
    asm!("movq $$0x60+90*8, %rsi
          movq %gs:(%rsi), $0" : "=r"(limit) :: "rsi" : "volatile");
    return limit;
}
