// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use integral::{int_ty_set};
use floating::{float_ty_set};
use unify::{VarValue, Redirect, Root};
use ty::{FnSig, FnTyBase};

pub trait InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str;
}

impl ty::t : InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str {
        ty_to_str(cx.tcx, self)
    }
}

impl FnMeta : InferStr {
    fn inf_str(_cx: @InferCtxt) -> ~str {
        fmt!("%?", self)
    }
}

impl FnSig : InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str {
        fmt!("(%s) -> %s",
             str::connect(self.inputs.map(|a| a.ty.inf_str(cx)), ", "),
             self.output.inf_str(cx))
    }
}

impl<M:InferStr> FnTyBase<M> : InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str {
        fmt!("%s%s", self.meta.inf_str(cx), self.sig.inf_str(cx))
    }
}

impl ty::mt : InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str {
        mt_to_str(cx.tcx, self)
    }
}

impl ty::Region : InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str {
        util::ppaux::region_to_str(cx.tcx, self)
    }
}

impl<V:InferStr> Bound<V> : InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str {
        match self {
          Some(ref v) => v.inf_str(cx),
          None => ~"none"
        }
    }
}

impl<T:InferStr> Bounds<T> : InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str {
        fmt!("{%s <: %s}",
             self.lb.inf_str(cx),
             self.ub.inf_str(cx))
    }
}

impl int_ty_set : InferStr {
    fn inf_str(_cx: @InferCtxt) -> ~str {
        match self {
          int_ty_set(v) => uint::to_str(v, 10u)
        }
    }
}

impl float_ty_set: InferStr {
    fn inf_str(_cx: @InferCtxt) -> ~str {
        match self {
          float_ty_set(v) => uint::to_str(v, 10u)
        }
    }
}

impl<V:Vid ToStr, T:InferStr> VarValue<V, T> : InferStr {
    fn inf_str(cx: @InferCtxt) -> ~str {
        match self {
          Redirect(ref vid) => fmt!("Redirect(%s)", vid.to_str()),
          Root(ref pt, rk) => fmt!("Root(%s, %s)", pt.inf_str(cx),
                               uint::to_str(rk, 10u))
        }
    }
}

