use rustc_index::bit_set::BitSet;
use rustc_middle::mir::{self, Local};

/// The set of locals in a MIR body that do not have `StorageLive`/`StorageDead` annotations.
///
/// These locals have fixed storage for the duration of the body.
pub fn always_storage_live_locals(body: &mir::Body<'_>) -> BitSet<Local> {
    let mut always_live_locals = BitSet::new_filled(body.local_decls.len());

    for block in &*body.basic_blocks {
        for statement in &block.statements {
            use mir::StatementKind::{StorageDead, StorageLive};
            if let StorageLive(l) | StorageDead(l) = statement.kind {
                // If we are reusing an uvar for l, then just treat it as always live,
                // since that will simplify things.
                let local_decl = &body.local_decls[l];
                if let Some(reuse_upvar) = local_decl.reuse_upvar {
                    debug!("treating local_decl: {local_decl:?} as always live \
                            due to reuse_upvar: {reuse_upvar:?}");
                    continue;
                }
                debug!("removing local_decl: {local_decl:?} from \
                        always_live_locals due to statement: {statement:?}");
                always_live_locals.remove(l);
            }
        }
    }

    always_live_locals
}
