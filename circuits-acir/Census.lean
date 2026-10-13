import AcirLean.Deposit.Controls
import AcirLean.Withdraw.Controls
import AcirLean.Transfer.Controls
import Lean

/-!
# Census of the AcirLean modules

Prints one JSON line per theorem declared in an `AcirLean.*` module: its name, module,
statement, a raw form of its type, and the axioms it depends on (`Lean.collectAxioms`, the
function behind `#print axioms`). The statement is printed with no elision
(`pp.deepTerms`, `pp.proofs`, a high `pp.maxSteps`). The raw form writes out every node of
the type expression, with full names and literals; `replay.py` pins its SHA-256. Prints one
JSON line per other constant kind that adds trust (an `axiomInfo` or an `opaqueInfo` in an
`AcirLean.*` module). `check.sh` compares the output with `expected.json` and the
allowlist of standard axioms.
-/

set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 100000000

open Lean Elab Command Meta

/-- Every node of `e`, with binder names and kinds, full constant names, universe levels
    and literal values. -/
partial def rawExpr : Expr → String
  | .bvar i => s!"(bvar {i})"
  | .fvar x => s!"(fvar {x.name})"
  | .mvar x => s!"(mvar {x.name})"
  | .sort l => s!"(sort {l})"
  | .const n ls => s!"(const {n} {ls})"
  | .app f a => s!"(app {rawExpr f} {rawExpr a})"
  | .lam n t b bi => s!"(lam {n} {repr bi} {rawExpr t} {rawExpr b})"
  | .forallE n t b bi => s!"(forall {n} {repr bi} {rawExpr t} {rawExpr b})"
  | .letE n t v b nd => s!"(let {n} {nd} {rawExpr t} {rawExpr v} {rawExpr b})"
  | .lit (.natVal v) => s!"(nat {v})"
  | .lit (.strVal v) => s!"(str {v.quote})"
  | .mdata d e => s!"(mdata {d} {rawExpr e})"
  | .proj s i e => s!"(proj {s} {i} {rawExpr e})"

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
        ("type", ty), ("raw", rawExpr ci.type), ("axioms", toJson axs)]))
    | .axiomInfo _ =>
      IO.println (Json.compress (Json.mkObj [("kind", "axiomInfo"), ("name", n), ("module", m)]))
    | .opaqueInfo _ =>
      IO.println (Json.compress (Json.mkObj [("kind", "opaqueInfo"), ("name", n), ("module", m)]))
    | _ => pure ()
