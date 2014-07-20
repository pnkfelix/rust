// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ast;
use ast_map;

/// Flag indicating whether one is requesting a lookup in the Mod
/// namespace or in the Value namespace.
#[deriving(Show)]
pub enum ModOrValue {
    Mod,
    Val,
}

/// A slow way to lookup the `ast::NodeId` for `x::y::a`, given an
/// `ast_map::Map`, given the strings for the path-components ("x",
/// "y", "a").
///
/// Module items live in the type namespace while values (such as fn
/// items) live in the value namespace; therefore we need to specify
/// which namespace we are searching in order to distinguish when we
/// want the module `x::y::a` versus when we want the value `x::y::a`.
pub fn slow_lookup(ast_map: &ast_map::Map,
                   namespace: ModOrValue,
                   parts: &[&str]) -> Option<ast::NodeId> {
    assert!(parts.len() > 0);
    let parent = {
        let parts = parts.slice_to(parts.len() - 1);
        let mut parent = None;
        for &part in parts.iter() {
            let opt_id = slow_lookup_part(ast_map, parent, Mod, part);
            if opt_id.is_none() { return None; }
            parent = opt_id;
        }
        parent
    };
    slow_lookup_part(ast_map, parent, namespace, *parts.last().unwrap())
}


/// A slow way to lookup the `ast::NodeId` for `x::y::a`, given an
/// `ast_map::Map`, the node id for the parent item (e.g. the module
/// "x::y"), and a string for the final path-component ("a").
///
/// Module items live in the type namespace while values (such as fn
/// items) live in the value namespace; therefore we need to specify
/// which namespace we are searching in order to distinguish when we
/// want the module `x::y::a` versus when we want the value `x::y::a`.
fn slow_lookup_part(ast_map: &ast_map::Map,
                    mod_parent: Option<ast::NodeId>,
                    namespace: ModOrValue,
                    s: &str) -> Option<ast::NodeId> {

    let entries = ast_map.map.borrow();
    for (idx, map_entry) in entries.iter().enumerate() {
        let idx = idx.to_u32().unwrap();
        match *map_entry {
            super::EntryItem(idx_parent, item)
                if (item_name_matches_str(item, s) &&
                    item_matches_namespace(item, namespace) &&
                    first_mod_parent_of_matches(ast_map, idx_parent, mod_parent))
                => return Some(idx),

            _   => continue,
        }
    }
    return None;

    fn item_name_matches_str(item: &ast::Item, s: &str) -> bool {
        debug!("item_name_matches_str(item: {}, s: {})",
               item.ident.name.as_str(), s);
        item.ident.name.as_str() == s
    }

    /// Finds the first mod in the parent chain for id.
    /// If `id` itself is a mod, then returns `Some(id)`.
    /// If `id` has no mod in its parent chain, then returns `None`.
    fn find_first_mod_parent(ast_map: &ast_map::Map,
                             mut id: ast::NodeId) -> Option<ast::NodeId> {
        loop {
            match ast_map.find(id) {
                None => return None,
                Some(super::NodeItem(item)) if item_is_mod(item) =>
                    return Some(id),
                _ => {}
            }
            let parent = ast_map.get_parent(id);
            if parent == id { return None }
            id = parent;
        }
    }

    fn first_mod_parent_of_matches(ast_map: &ast_map::Map,
                                   idx: ast::NodeId,
                                   mod_parent: Option<ast::NodeId>) -> bool {
        let first = find_first_mod_parent(ast_map, idx);
        debug!("first_mod_parent_of_matches(idx: {}, mod_parent: {}) first: {}",
               idx, mod_parent, first);
        mod_parent == first
    }

    fn item_matches_namespace(item: &ast::Item, namespace: ModOrValue) -> bool {
        debug!("item_matches_namespace(item: {}, namespace: {})",
               item.ident.name.as_str(), namespace);
        match namespace {
            Val => !item_is_mod(item),
            Mod =>  item_is_mod(item),
        }
    }

    fn item_is_mod(item: &ast::Item) -> bool {
        match item.node {
            ast::ItemMod(_) | ast::ItemForeignMod(_) => true,
            _ => false,
        }
    }
}
