# Copyright 2014 The Rust Project Developers. See the COPYRIGHT
# file at the top-level directory of this distribution and at
# http://rust-lang.org/COPYRIGHT.
#
# Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
# http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
# <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
# option. This file may not be copied, modified, or distributed
# except according to those terms.
#
# ignore-tidy-linelength

DIR=$(dirname $0)
RUSTC_BIN=$DIR/bin/rustc

# FULL_LIB_SUFFIX=$(otool -L $RUSTC_BIN | grep librustc- | cut -f 1 -d ' ' | xargs dirname)
# LIB_SUFFIX_B1=$(basename $FULL_LIB_SUFFIX)
# LIB_SUFFIX_D1=$(dirname $FULL_LIB_SUFFIX)
# LIB_SUFFIX_B2=$(basename $LIB_SUFFIX_D1)
# LIB_SUFFIX_D2=$(dirname $LIB_SUFFIX_D1)
# LIB_SUFFIX_B3=$(basename $LIB_SUFFIX_D2)
# LIB_SUFFIX_D3=$(dirname $LIB_SUFFIX_D2)
# LIB_SUFFIX=$LIB_SUFFIX_B3/$LIB_SUFFIX_B2/$LIB_SUFFIX_B1
# CMD="DYLD_LIBRARY_PATH=$DIR/lib:$DIR/lib/$LIB_SUFFIX:$DYLD_LIBRARY_PATH $RUSTC_BIN $@"

CMD="DYLD_LIBRARY_PATH=$DIR/lib:$DYLD_LIBRARY_PATH $RUSTC_BIN $@"
echo $CMD
eval "$CMD"
