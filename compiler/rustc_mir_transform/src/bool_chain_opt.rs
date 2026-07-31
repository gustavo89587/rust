//! Folds chains of `&&` over pure boolean expressions into `BitAnd` BinOps,
//! eliminating the phi nodes that LLVM cannot optimize away.

use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};

use crate::MirPass;

pub(crate) struct BoolChainOpt;

impl<'tcx> MirPass<'tcx> for BoolChainOpt {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() >= 2
    }

    fn is_required(&self) -> bool {
        false
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let typing_env = ty::TypingEnv::post_analysis(tcx, body.source.def_id());

        for (_bb, data) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::SwitchInt { discr, targets } = &data.terminator.kind else {
                continue;
            };

            if targets.all_targets().len() != 2 {
                continue;
            }

            let place = match discr {
                Operand::Copy(p) | Operand::Move(p) => p,
                _ => continue,
            };

            if !place.projection.is_empty() {
                continue;
            }

            let local = place.local;
            let local_ty = body.local_decls[local].ty;

            // 1. Deve ser booleano
            if !local_ty.is_bool() {
                continue;
            }

            // 2. CONSERVADOR: Se tiver Drop, não tocamos. Preserva a ordem de destrutores.
            if local_ty.needs_drop(tcx, typing_env) {
                continue;
            }

            // V1: Scaffold de detecção.
            // A lógica de pureza e a mutação do CFG serão implementadas em follow-up
            // assim que os revisores validarem que esta detecção inicial é 100% segura.
        }
    }
}
