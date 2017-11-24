// Copyright 2012-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::mir::{self, Mir, Location, Place};
use rustc::ty::{self, TyCtxt};
use util::elaborate_drops::DropFlagState;

use super::indexes::MovePathIndex;
use super::move_paths::{MoveData, LookupResult, InitKind};

pub fn move_path_children_matching<'tcx, F>(move_data: &MoveData<'tcx>,
                                        path: MovePathIndex,
                                        mut cond: F)
                                        -> Option<MovePathIndex>
    where F: FnMut(&mir::PlaceProjection<'tcx>) -> bool
{
    let mut next_child = move_data.move_paths[path].first_child;
    while let Some(child_index) = next_child {
        match move_data.move_paths[child_index].place {
            Place::Projection(ref proj) => {
                if cond(proj) {
                    return Some(child_index)
                }
            }
            _ => {}
        }
        next_child = move_data.move_paths[child_index].next_sibling;
    }

    None
}

/// When enumerating the child fragments of a path, don't recurse into
/// paths (1.) past arrays, slices, and pointers, nor (2.) into a type
/// that implements `Drop`.
///
/// Places behind references or arrays are not tracked by elaboration
/// and are always assumed to be initialized when accessible. As
/// references and indexes can be reseated, trying to track them can
/// only lead to trouble.
///
/// Places behind ADT's with a Drop impl are not tracked by
/// elaboration since they can never have a drop-flag state that
/// differs from that of the parent with the Drop impl.
///
/// In both cases, the contents can only be accessed if and only if
/// their parents are initialized. This implies for example that there
/// is no need to maintain separate drop flags to track such state.
///
/// FIXME: we have to do something for moving slice patterns.
pub(crate) fn place_contents_drop_state_cannot_differ<'a, 'gcx, 'tcx>(
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    mir: &Mir<'tcx>,
    place: &Place<'tcx>) -> bool
{
    let ty = place.ty(mir, tcx).to_ty(tcx);
    match ty.sty {
        ty::TyArray(..) => {
            debug!("place_contents_drop_state_cannot_differ place: {:?} ty: {:?} => false",
                   place, ty);
            false
        }
        ty::TySlice(..) | ty::TyRef(..) | ty::TyRawPtr(..) => {
            debug!("place_contents_drop_state_cannot_differ place: {:?} ty: {:?} refd => true",
                   place, ty);
            true
        }
        ty::TyAdt(def, _) if (def.has_dtor(tcx) && !def.is_box()) || def.is_union() => {
            debug!("place_contents_drop_state_cannot_differ place: {:?} ty: {:?} Drop => true",
                   place, ty);
            true
        }
        _ => {
            false
        }
    }
}

pub(crate) fn place_needs_drop<'a, 'gcx, 'tcx>(tcx: TyCtxt<'a, 'gcx, 'tcx>,
                                                mir: &Mir<'tcx>,
                                                param_env: ty::ParamEnv<'gcx>,
                                                place: &Place<'tcx>)
                                                -> bool
{
    let ty = place.ty(mir, tcx).to_ty(tcx);
    // debug!("on_all_drop_children_bits({:?}, {:?} : {:?})", path, place, ty);

    let gcx = tcx.global_tcx();
    let erased_ty = gcx.lift(&tcx.erase_regions(&ty)).unwrap();
    erased_ty.needs_drop(gcx, param_env)
}

pub(crate) fn on_lookup_result_bits<'tcx, F, U>(move_data: &MoveData<'tcx>,
                                                lookup_result: LookupResult,
                                                has_uniform_drop_state: U,
                                                each_child: F)
    where F: FnMut(MovePathIndex), U: Fn(&Place<'tcx>) -> bool
{
    match lookup_result {
        LookupResult::Parent(..) => {
            // access to untracked value - do not touch children
        }
        LookupResult::Exact(e) => {
            on_all_children_bits(move_data, e, has_uniform_drop_state, each_child)
        }
    }
}

pub(crate) fn on_all_children_bits<'tcx, F, U>(move_data: &MoveData<'tcx>,
                                               move_path_index: MovePathIndex,
                                               has_uniform_drop_state: U,
                                               mut each_child: F)
    where F: FnMut(MovePathIndex), U: Fn(&Place<'tcx>) -> bool
{
    fn is_terminal_path<'tcx, U>(move_data: &MoveData<'tcx>,
                                 path: MovePathIndex,
                                 has_uniform_drop_state: U) -> bool
        where U: Fn(&Place<'tcx>) -> bool
    {
        // lvalue_contents_drop_state_cannot_differ
        has_uniform_drop_state(&move_data.move_paths[path].place)
    }

    fn on_all_children_bits<'tcx, F, U>(move_data: &MoveData<'tcx>,
                                        move_path_index: MovePathIndex,
                                        has_uniform_drop_state: &U,
                                        each_child: &mut F)
        where F: FnMut(MovePathIndex), U: Fn(&Place<'tcx>) -> bool
    {
        each_child(move_path_index);

        if is_terminal_path(move_data, move_path_index, has_uniform_drop_state) {
            return
        }

        let mut next_child_index = move_data.move_paths[move_path_index].first_child;
        while let Some(child_index) = next_child_index {
            on_all_children_bits(move_data, child_index, has_uniform_drop_state, each_child);
            next_child_index = move_data.move_paths[child_index].next_sibling;
        }
    }
    on_all_children_bits(move_data, move_path_index, &has_uniform_drop_state, &mut each_child);
}

pub(crate) fn on_all_drop_children_bits<'tcx, F, U, N>(move_data: &MoveData<'tcx>,
                                                       path: MovePathIndex,
                                                       has_uniform_drop_state: U,
                                                       needs_drop: N,
                                                       mut each_child: F)
    where F: FnMut(MovePathIndex),
          U: Fn(&Place<'tcx>) -> bool,
          N: Fn(&Place<'tcx>) -> bool,
{
    on_all_children_bits(move_data, path, has_uniform_drop_state, |child| {
        let place = &move_data.move_paths[path].place;
        // let ty = place.ty(mir, tcx).to_ty(tcx);
        // debug!("on_all_drop_children_bits({:?}, {:?} : {:?})", path, place, ty);

        // let gcx = tcx.global_tcx();
        // let erased_ty = gcx.lift(&tcx.erase_regions(&ty)).unwrap();
        // if erased_ty.needs_drop(gcx, ctxt.param_env) {
        if needs_drop(place) {
            each_child(child);
        } else {
            debug!("on_all_drop_children_bits - skipping")
        }
    })
}

pub(crate) fn drop_flag_effects_for_function_entry<'tcx, F, U>(
          mir: &Mir<'tcx>,
          move_data: &MoveData<'tcx>,
          has_uniform_drop_state: U,
          mut callback: F)
    where F: FnMut(MovePathIndex, DropFlagState), U: Fn(&Place<'tcx>) -> bool
{
    for arg in mir.args_iter() {
        let place = Place::Local(arg);
        let lookup_result = move_data.rev_lookup.find(&place);
        on_lookup_result_bits(move_data,
                              lookup_result,
                              &has_uniform_drop_state,
                              |mpi| callback(mpi, DropFlagState::Present));
    }
}

pub(crate) fn drop_flag_effects_for_location<'tcx, F, U>(move_data: &MoveData<'tcx>,
                                                         loc: Location,
                                                         has_uniform_drop_state: U,
                                                         mut callback: F)
    where F: FnMut(MovePathIndex, DropFlagState), U: Fn(&Place<'tcx>) -> bool
{
    debug!("drop_flag_effects_for_location({:?})", loc);

    // first, move out of the RHS
    for mi in &move_data.loc_map[loc] {
        let path = mi.move_path_index(move_data);
        debug!("moving out of path {:?}", move_data.move_paths[path]);

        on_all_children_bits(move_data,
                             path,
                             &has_uniform_drop_state,
                             |mpi| callback(mpi, DropFlagState::Absent))
    }

    debug!("drop_flag_effects: assignment for location({:?})", loc);

    for_location_inits(
        move_data,
        loc,
        has_uniform_drop_state,
        |mpi| callback(mpi, DropFlagState::Present)
    );
}

pub(crate) fn for_location_inits<'tcx, F, U>(
    move_data: &MoveData<'tcx>,
    loc: Location,
    has_uniform_drop_state: U,
    mut callback: F)
    where F: FnMut(MovePathIndex), U: Fn(&Place<'tcx>) -> bool
{
    for ii in &move_data.init_loc_map[loc] {
        let init = move_data.inits[*ii];
        match init.kind {
            InitKind::Deep => {
                let path = init.path;

                on_all_children_bits(move_data,
                                     path,
                                     &has_uniform_drop_state,
                                     &mut callback)
            },
            InitKind::Shallow => {
                let mpi = init.path;
                callback(mpi);
            }
            InitKind::NonPanicPathOnly => (),
        }
    }
}
