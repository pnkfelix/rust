// compile-flags: -Cno-prepopulate-passes

// Nevisions:x86_64 i686 aarch64-apple aarch64-windows aarch64-linux arm riscv
// Neds-llvm-components: aarch64 arm riscv

//[x86_64] compile-flags: --target x86_64-unknown-uefi
//[i686] compile-flags: --target i686-unknown-linux-musl
//[aarch64-windows] compile-flags: --target aarch64-unknown-none
//[aarch64-linux] compile-flags: --target aarch64-unknown-none
//[aarch64-apple] compile-flags: --target aarch64-apple-darwin
//[arm] compile-flags: --target armv7r-none-eabi
//[riscv] compile-flags: --target riscv64gc-unknown-none-elf

#![crate_type = "lib"]

