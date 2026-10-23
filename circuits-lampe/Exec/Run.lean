import Exec.Basic

namespace Exec.Basic
open Lampe

macro "run_step" : tactic => `(tactic|
  ((try dsimp only [mapToValHeapCondition]); first
    | (solve | decide +kernel)
    | exec_pure
    | (apply bind_ref; intro addr hfresh)
    | (apply bind_read; exact Finmap.lookup_insert _)
    | (apply bind_write; exact Finmap.lookup_insert _)
    | apply bind_cps
    | (apply Omni.loopNext; · exact of_decide_eq_true rfl)
    | (apply Omni.loopDone; · exact of_decide_eq_true rfl)
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok)
    | (apply Omni.callBuiltin; apply Builtin.genericPureOmni.ok (a := ()))
    | (apply Omni.callBuiltin; apply Builtin.castOmni.ok)
    | (apply Omni.callBuiltin; apply Builtin.readRefOmni.mk; · exact Finmap.lookup_insert _)
    | (apply Omni.callBuiltin; apply Builtin.writeRefOmni.mk; · exact Finmap.lookup_insert _)
    | (apply Omni.callBuiltin
       apply Builtin.modifyLensOmni.ok (hr := rfl)
       · exact Finmap.lookup_insert _
       · rfl
       · rfl
       · rfl)
    | apply Omni.skip
    | apply Omni.var
    | apply Omni.constU
    | apply Omni.litU
    | apply Omni.litField
    | apply Omni.fn
    | apply Omni.iteFalse
    | apply Omni.iteTrue
    | exact ()
    | trivial))

macro "run_steps" : tactic => `(tactic| repeat' run_step)
end Exec.Basic
