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
use rustc::ty::{self, TyCtxt, ParamEnv};
use util::elaborate_drops::DropFlagState;

use super::indexes::MovePathIndex;
use super::move_paths::{MoveData, LookupResult, InitKind};

pub(crate) trait PlaceOneDropFlag<'tcx> {
    fn place_contents_drop_state_cannot_differ(&self, &Place<'tcx>) -> bool;
}

pub(crate) trait PlaceNeedsDrop<'tcx> {
    fn needs_drop(&self, &Place<'tcx>) -> bool;
}

impl<'a, 'gcx, 'tcx> PlaceOneDropFlag<'tcx> for (TyCtxt<'a, 'gcx, 'tcx>, &'a Mir<'tcx>) {
    fn place_contents_drop_state_cannot_differ(&self, place: &Place<'tcx>) -> bool {
        place_contents_drop_state_cannot_differ(self.0, self.1, place)
    }
}

impl<'a, 'gcx, 'tcx> PlaceOneDropFlag<'tcx> for (TyCtxt<'a, 'gcx, 'tcx>,
                                                 &'a Mir<'tcx>,
                                                 ParamEnv<'gcx>)
{
    fn place_contents_drop_state_cannot_differ(&self, place: &Place<'tcx>) -> bool {
        place_contents_drop_state_cannot_differ(self.0, self.1, place)
    }
}

impl<'a, 'gcx, 'tcx> PlaceNeedsDrop<'tcx> for (TyCtxt<'a, 'gcx, 'tcx>,
                                               &'a Mir<'tcx>,
                                               ParamEnv<'gcx>)
{
    fn needs_drop(&self, place: &Place<'tcx>) -> bool {
        place_needs_drop(self.0, self.1, self.2, place)
    }
}

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
fn place_contents_drop_state_cannot_differ<'a, 'gcx, 'tcx>(
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

fn place_needs_drop<'a, 'gcx, 'tcx>(tcx: TyCtxt<'a, 'gcx, 'tcx>,
                                    mir: &Mir<'tcx>,
                                    param_env: ty::ParamEnv<'gcx>,
                                    place: &Place<'tcx>)
                                    -> bool
{
    let ty = place.ty(mir, tcx).to_ty(tcx);
    let gcx = tcx.global_tcx();
    let erased_ty = gcx.lift(&tcx.erase_regions(&ty)).unwrap();
    erased_ty.needs_drop(gcx, param_env)
}

pub(crate) fn on_lookup_result_bits<'tcx, F, PO>(tcx_mir: &PO,
                                                 move_data: &MoveData<'tcx>,
                                                 lookup_result: LookupResult,
                                                 each_child: F)
    where F: FnMut(MovePathIndex), PO: PlaceOneDropFlag<'tcx>,
{
    match lookup_result {
        LookupResult::Parent(..) => {
            // access to untracked value - do not touch children
        }
        LookupResult::Exact(e) => {
            on_all_children_bits(tcx_mir, move_data, e, each_child)
        }
    }
}

pub(crate) fn on_all_children_bits<'tcx, F, PO>(tcx_mir: &PO,
                                                move_data: &MoveData<'tcx>,
                                                move_path_index: MovePathIndex,
                                                mut each_child: F)
    where F: FnMut(MovePathIndex), PO: PlaceOneDropFlag<'tcx>
{
    fn is_terminal_path<'tcx, PO>(tcx_mir: &PO,
                                  move_data: &MoveData<'tcx>,
                                  path: MovePathIndex) -> bool
        where PO: PlaceOneDropFlag<'tcx>
    {
        let place = &move_data.move_paths[path].place;
        tcx_mir.place_contents_drop_state_cannot_differ(place)
    }

    fn on_all_children_bits<'tcx, F, PO>(tcx_mir: &PO,
                                         move_data: &MoveData<'tcx>,
                                         move_path_index: MovePathIndex,
                                         each_child: &mut F)
        where F: FnMut(MovePathIndex), PO: PlaceOneDropFlag<'tcx>
    {
        each_child(move_path_index);

        if is_terminal_path(tcx_mir, move_data, move_path_index) {
            return
        }

        let mut next_child_index = move_data.move_paths[move_path_index].first_child;
        while let Some(child_index) = next_child_index {
            on_all_children_bits(tcx_mir, move_data, child_index, each_child);
            next_child_index = move_data.move_paths[child_index].next_sibling;
        }
    }
    on_all_children_bits(tcx_mir, move_data, move_path_index, &mut each_child);
}

pub(crate) fn on_all_drop_children_bits<'tcx, F, PO>(tcx_mir_param_env: &PO,
                                                     move_data: &MoveData<'tcx>,
                                                     path: MovePathIndex,
                                                     mut each_child: F)
    where F: FnMut(MovePathIndex), PO: PlaceOneDropFlag<'tcx> + PlaceNeedsDrop<'tcx>
{
    on_all_children_bits(tcx_mir_param_env, move_data, path, |child| {
        let place = &move_data.move_paths[path].place;
        // let ty = place.ty(mir, tcx).to_ty(tcx);
        // debug!("on_all_drop_children_bits({:?}, {:?} : {:?})", path, place, ty);

        // let gcx = tcx.global_tcx();
        // let erased_ty = gcx.lift(&tcx.erase_regions(&ty)).unwrap();
        // if erased_ty.needs_drop(gcx, ctxt.param_env) {
        if tcx_mir_param_env.needs_drop(place) {
            each_child(child);
        } else {
            debug!("on_all_drop_children_bits - skipping")
        }
    })
}

pub(crate) fn drop_flag_effects_for_function_entry<'tcx, F, PO>(
          tcx_mir: &PO,
          mir: &Mir<'tcx>,
          move_data: &MoveData<'tcx>,
          mut callback: F)
    where F: FnMut(MovePathIndex, DropFlagState), PO: PlaceOneDropFlag<'tcx>
{
    for arg in mir.args_iter() {
        let place = Place::Local(arg);
        let lookup_result = move_data.rev_lookup.find(&place);
        on_lookup_result_bits(tcx_mir,
                              move_data,
                              lookup_result,
                              |mpi| callback(mpi, DropFlagState::Present));
    }
}

pub(crate) fn drop_flag_effects_for_location<'tcx, F, PO>(tcx_mir: &PO,
                                                          move_data: &MoveData<'tcx>,
                                                          loc: Location,
                                                          mut callback: F)
    where F: FnMut(MovePathIndex, DropFlagState), PO: PlaceOneDropFlag<'tcx>
{
    debug!("drop_flag_effects_for_location({:?})", loc);

    // first, move out of the RHS
    for mi in &move_data.loc_map[loc] {
        let path = mi.move_path_index(move_data);
        debug!("moving out of path {:?}", move_data.move_paths[path]);

        on_all_children_bits(tcx_mir,
                             move_data,
                             path,
                             |mpi| callback(mpi, DropFlagState::Absent))
    }

    debug!("drop_flag_effects: assignment for location({:?})", loc);

    for_location_inits(
        tcx_mir,
        move_data,
        loc,
        |mpi| callback(mpi, DropFlagState::Present)
    );
}

pub(crate) fn for_location_inits<'tcx, F, PO>(
    tcx_mir: &PO,
    move_data: &MoveData<'tcx>,
    loc: Location,
    mut callback: F)
    where F: FnMut(MovePathIndex), PO: PlaceOneDropFlag<'tcx>
{
    for ii in &move_data.init_loc_map[loc] {
        let init = move_data.inits[*ii];
        match init.kind {
            InitKind::Deep => {
                let path = init.path;

                on_all_children_bits(tcx_mir,
                                     move_data,
                                     path,
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
