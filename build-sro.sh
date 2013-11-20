set -e

( cd ./objdir-dbgopt && make )
./objdir-dbgopt/x86_64-apple-darwin/stage2/bin/rustc \
    -Z debug-info -Z extra-debug-info                \
    sro-play.rs
