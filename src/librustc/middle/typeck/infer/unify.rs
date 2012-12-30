// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use combine::Combine;
use integral::*;
use floating::*;
use to_str::InferStr;
use std::smallintmap::SmallIntMap;

enum VarValue<V, T> {
    Redirect(V),
    Root(T, uint),
}

struct ValsAndBindings<V:Copy, T:Copy> {
    vals: SmallIntMap<VarValue<V, T>>,
    mut bindings: ~[(V, VarValue<V, T>)],
}

struct Node<V:Copy, T:Copy> {
    root: V,
    possible_types: T,
    rank: uint,
}

impl @InferCtxt {
    fn get<V:Copy Eq Vid, T:Copy>(
        vb: &ValsAndBindings<V, T>,
        vid: V)
        -> Node<V, T>
    {
        let vid_u = vid.to_uint();
        match vb.vals.find(vid_u) {
          None => {
            self.tcx.sess.bug(fmt!("failed lookup of vid `%u`", vid_u));
          }
          Some(ref var_val) => {
            match (*var_val) {
              Redirect(ref vid) => {
                let node = self.get(vb, (*vid));
                if node.root.ne(vid) {
                    // Path compression
                    vb.vals.insert(vid.to_uint(), Redirect(node.root));
                }
                node
              }
              Root(ref pt, rk) => {
                Node {root: vid, possible_types: *pt, rank: rk}
              }
            }
          }
        }
    }

    fn set<V:Copy Vid ToStr, T:Copy InferStr>(
        vb: &ValsAndBindings<V, T>,
        vid: V,
        +new_v: VarValue<V, T>)
    {
        let old_v = vb.vals.get(vid.to_uint());
        vb.bindings.push((vid, old_v));
        vb.vals.insert(vid.to_uint(), new_v);

        debug!("Updating variable %s from %s to %s",
               vid.to_str(), old_v.inf_str(self), new_v.inf_str(self));
    }

    fn unify<V:Copy Vid ToStr, T:Copy InferStr, R>(
        vb: &ValsAndBindings<V, T>,
        node_a: &Node<V, T>,
        node_b: &Node<V, T>,
        op: &fn(new_root: V, new_rank: uint) -> R
    ) -> R {
        // Rank optimization: if you don't know what it is, check
        // out <http://en.wikipedia.org/wiki/Disjoint-set_data_structure>

        debug!("unify(node_a(id=%?, rank=%?), \
                node_b(id=%?, rank=%?))",
               node_a.root, node_a.rank,
               node_b.root, node_b.rank);

        if node_a.rank > node_b.rank {
            // a has greater rank, so a should become b's parent,
            // i.e., b should redirect to a.
            self.set(vb, node_b.root, Redirect(node_a.root));
            op(node_a.root, node_a.rank)
        } else if node_a.rank < node_b.rank {
            // b has greater rank, so a should redirect to b.
            self.set(vb, node_a.root, Redirect(node_b.root));
            op(node_b.root, node_b.rank)
        } else {
            // If equal, redirect one to the other and increment the
            // other's rank.
            assert node_a.rank == node_b.rank;
            self.set(vb, node_b.root, Redirect(node_a.root));
            op(node_a.root, node_a.rank + 1)
        }
    }

}

// ______________________________________________________________________
// Integral variables

impl @InferCtxt {
    fn int_vars(a_id: ty::IntVid, b_id: ty::IntVid) -> ures {
        let vb = &self.int_var_bindings;

        let node_a = self.get(vb, a_id);
        let node_b = self.get(vb, b_id);
        let a_id = node_a.root;
        let b_id = node_b.root;
        let a_pt = node_a.possible_types;
        let b_pt = node_b.possible_types;

        // If we're already dealing with the same two variables,
        // there's nothing to do.
        if a_id == b_id { return uok(); }

        // Otherwise, take the intersection of the two sets of
        // possible types.
        let intersection = integral::intersection(a_pt, b_pt);
        if *intersection == INT_TY_SET_EMPTY {
            return Err(ty::terr_no_integral_type);
        }

        self.unify(vb, &node_a, &node_b, |new_root, new_rank| {
            self.set(vb, new_root, Root(intersection, new_rank));
        });

        uok()
    }

    fn int_var_sub_t(a_id: ty::IntVid, b: ty::t) -> ures {
        assert ty::type_is_integral(b);

        let vb = &self.int_var_bindings;
        let node_a = self.get(vb, a_id);
        let a_id = node_a.root;
        let a_pt = node_a.possible_types;

        let intersection =
            integral::intersection(a_pt,
                         convert_integral_ty_to_int_ty_set(self.tcx, b));
        if *intersection == INT_TY_SET_EMPTY {
            return Err(ty::terr_no_integral_type);
        }
        self.set(vb, a_id, Root(intersection, node_a.rank));
        uok()
    }

    fn t_sub_int_var(a: ty::t, b_id: ty::IntVid) -> ures {
        assert ty::type_is_integral(a);
        let vb = &self.int_var_bindings;

        let node_b = self.get(vb, b_id);
        let b_id = node_b.root;
        let b_pt = node_b.possible_types;

        let intersection =
            integral::intersection(b_pt,
                         convert_integral_ty_to_int_ty_set(self.tcx, a));
        if *intersection == INT_TY_SET_EMPTY {
            return Err(ty::terr_no_integral_type);
        }
        self.set(vb, b_id, Root(intersection, node_b.rank));
        uok()
    }


}

// ______________________________________________________________________
// Floating point variables

impl @InferCtxt {
    fn float_vars(a_id: ty::FloatVid, b_id: ty::FloatVid) -> ures {
        let vb = &self.float_var_bindings;

        let node_a = self.get(vb, a_id);
        let node_b = self.get(vb, b_id);
        let a_id = node_a.root;
        let b_id = node_b.root;
        let a_pt = node_a.possible_types;
        let b_pt = node_b.possible_types;

        // If we're already dealing with the same two variables,
        // there's nothing to do.
        if a_id == b_id { return uok(); }

        // Otherwise, take the intersection of the two sets of
        // possible types.
        let intersection = floating::intersection(a_pt, b_pt);
        if *intersection == FLOAT_TY_SET_EMPTY {
            return Err(ty::terr_no_floating_point_type);
        }

        self.unify(vb, &node_a, &node_b, |new_root, new_rank| {
            self.set(vb, new_root, Root(intersection, new_rank));
        });

        uok()
    }

    fn float_var_sub_t(a_id: ty::FloatVid, b: ty::t) -> ures {
        assert ty::type_is_fp(b);

        let vb = &self.float_var_bindings;
        let node_a = self.get(vb, a_id);
        let a_id = node_a.root;
        let a_pt = node_a.possible_types;

        let intersection =
            floating::intersection(
                a_pt,
                convert_floating_point_ty_to_float_ty_set(self.tcx, b));
        if *intersection == FLOAT_TY_SET_EMPTY {
            return Err(ty::terr_no_floating_point_type);
        }
        self.set(vb, a_id, Root(intersection, node_a.rank));
        uok()
    }

    fn t_sub_float_var(a: ty::t, b_id: ty::FloatVid) -> ures {
        assert ty::type_is_fp(a);
        let vb = &self.float_var_bindings;

        let node_b = self.get(vb, b_id);
        let b_id = node_b.root;
        let b_pt = node_b.possible_types;

        let intersection =
            floating::intersection(
                b_pt,
                convert_floating_point_ty_to_float_ty_set(self.tcx, a));
        if *intersection == FLOAT_TY_SET_EMPTY {
            return Err(ty::terr_no_floating_point_type);
        }
        self.set(vb, b_id, Root(intersection, node_b.rank));
        uok()
    }
}

