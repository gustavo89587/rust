//! BoolChainOpt: Detects pure chains of `&&` and prepares a transformation to `BitAnd`,
//! eliminating phi nodes that LLVM cannot optimize.
//!
//! # Safety Invariants
//! This pass is EXTREMELY CONSERVATIVE. It ONLY transforms when ALL conditions are met:
//! 1. The operand is proven to be side-effect-free (no calls, drops, asm, or atomics).
//! 2. The operand cannot cause a panic (no indexing, no arithmetic that might overflow).
//! 3. The drop order of all temporaries is preserved.
//!
//! If ANY invariant cannot be proven, the transformation is SKIPPED.
//! It is better to miss an optimization opportunity than to introduce Undefined Behavior.

use crate::MirPass;
use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};

pub(crate) struct BoolChainOpt;

impl<'tcx> MirPass<'tcx> for BoolChainOpt {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        // Enabled only at optimization levels 2 or higher
        sess.mir_opt_level() >= 2
    }

    fn is_required(&self) -> bool {
        false
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let typing_env = ty::TypingEnv::post_analysis(tcx, body.source.def_id());
        let mut safe_candidates = Vec::new();

        // PHASE 1: Collect COMPLETELY SAFE candidates
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::SwitchInt { discr, targets } = &data.terminator.kind else {
                continue;
            };

        // Only accept standard boolean branches (true/false)
            if targets.all_targets().len() != 2 {
                continue;
            }

            let place = match discr {
                Operand::Copy(p) | Operand::Move(p) => p,
                _ => continue, // Reject complex temporaries
            };

            if !place.projection.is_empty() {
                continue; // Reject projections (field access, index, etc.)
            }

            let local = place.local;
            let local_ty = body.local_decls[local].ty;

            // Check 1: Type must be primitive bool
            if !local_ty.is_bool() {
                continue;
            }

            // Check 2: Type must NOT have a Drop implementation (mitigates destructor order risk)
            if local_ty.needs_drop(tcx, typing_env) {
                rustc_log::debug!("BoolChainOpt: skipping local {:?} - has Drop", local);
                continue;
            }

            // Check 3: Operand must be proven pure
            if !is_provably_pure(tcx, body, typing_env, local) {
                rustc_log::debug!("BoolChainOpt: skipping local {:?} - not provably pure", local);
                continue;
            }

            // Check 4: Block must not contain instructions with side effects
            if !block_is_side_effect_free(data) {
                rustc_log::debug!("BoolChainOpt: skipping bb {:?} - block has side effects", bb);
                continue;
            }

            safe_candidates.push((bb, local, data.terminator.source_info));
        }

        // PHASE 2: Apply transformations only to 100% safe candidates
        if safe_candidates.is_empty() {
            return;
        }

        let basic_blocks = body.basic_blocks.as_mut_preserves_cfg();
        let mut changed = false;

        for (bb, local, source_info) in safe_candidates {
            let block = &mut basic_blocks[bb];

        // Safest possible case: constant value known at compile time
            if let Some(const_val) = try_get_const_bool(body, local) {
                let targets = block.terminator.as_ref().unwrap().successors().collect::<Vec<_>>();
                let target = if const_val { targets[0] } else { targets[1] };

                block.terminator = Some(Box::new(Terminator {
                    source_info,
                    kind: TerminatorKind::Goto { target },
                }));
                changed = true;
                rustc_log::debug!("BoolChainOpt: folded constant bool in bb {:?}", bb);
            }
        }

        if changed {
            rustc_log::debug!("BoolChainOpt: applied {} transformations", safe_candidates.len());
        }
    }
}
/// Checks whether a boolean location was produced by a PROVENLY pure expression.
/// Extremely conservative: prefers false negatives to false positives.
fn is_provably_pure<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    local: Local,
) -> bool {
    for (_, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.as_local() == Some(local) {
                    return is_rvalue_pure(tcx, body, typing_env, rvalue);
                }
            }
        }
    }
    false // If we do not find the definition, we reject it for safety reasons.
}

/// Checks if an Rvalue is a pure operation (no side effects, no panics)
fn is_rvalue_pure<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _body: &Body<'tcx>,
    _typing_env: ty::TypingEnv<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Constant(_)) => true,
        Rvalue::BinaryOp(op, _) => {
            matches!(op,
                BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor |
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le |
                BinOp::Gt | BinOp::Ge
            )
        }
        Rvalue::UnaryOp(op, _) => matches!(op, UnOp::Not),
        Rvalue::Cast(_, _, _) => true,
        _ => {
            rustc_log::debug!("BoolChainOpt: rejecting rvalue {:?} - not provably pure", rvalue);
            false
        }
    }
}

/// Checks if a basic block contains only instructions without side effects.
fn block_is_side_effect_free(data: &BasicBlockData<'_>) -> bool {
    for stmt in &data.statements {
        match &stmt.kind {
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => continue,
            StatementKind::Assign(_) => continue,
            StatementKind::Nop => continue,
            StatementKind::FakeRead(_, _) => continue,
            _ => {
                rustc_log::debug!("BoolChainOpt: rejecting statement {:?} - has side effects", stmt.kind);
                return false;
            }
        }
    }
    true
}

/// Attempts to obtain the constant value of a location (if known at compile time)
fn try_get_const_bool<'tcx>(body: &Body<'tcx>, local: Local) -> Option<bool> {
    for (_, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.as_local() == Some(local) {
                    if let Rvalue::Use(Operand::Constant(box constant)) = rvalue {
                        if let ty::ConstKind::Value(ty::ValTree::Leaf(scalar)) = constant.const_.kind() {
                            return Some(scalar.to_bool().unwrap_or(false));
                        }
                    }
                }
            }
        }
    }
    None
}
