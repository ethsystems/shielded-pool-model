import AcirLean.Deposit.Controls
import AcirLean.Withdraw.Controls
import AcirLean.Transfer.Controls
import Lean

/-!
# Census of the AcirLean modules

Prints one JSON line per theorem declared in an `AcirLean.*` module: its name, module,
statement (pretty-printed type) and the axioms it depends on (`Lean.collectAxioms`, the
function behind `#print axioms`). Prints one JSON line per other constant kind that adds
trust (an `axiomInfo` or an `opaqueInfo` in an `AcirLean.*` module). `check.sh` compares
the output with `expected.json` and the allowlist of standard axioms.
-/

open Lean Elab Command Meta

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut rows : Array (String × String × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if (`AcirLean).isPrefixOf m then
        rows := rows.push (n.toString, m.toString, ci)
  rows := rows.qsort (fun a b => a.1 < b.1)
  for (n, m, ci) in rows do
    match ci with
    | .thmInfo _ =>
      let axs ← collectAxioms ci.name
      let ty ← liftTermElabM do return (← ppExpr ci.type).pretty 100000
      let axs := (axs.map toString).qsort (· < ·)
      IO.println (Json.compress (Json.mkObj [("kind", "theorem"), ("name", n), ("module", m),
        ("type", ty), ("axioms", toJson axs)]))
    | .axiomInfo _ =>
      IO.println (Json.compress (Json.mkObj [("kind", "axiomInfo"), ("name", n), ("module", m)]))
    | .opaqueInfo _ =>
      IO.println (Json.compress (Json.mkObj [("kind", "opaqueInfo"), ("name", n), ("module", m)]))
    | _ => pure ()
