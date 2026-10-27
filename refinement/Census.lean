import Balance.PathLocalNonVacuity
import Gas.Envelope
import Journey.Withdraw
import Refinement.ProvenanceNonVacuity
import Lean

/-!
# Census of the modules

Prints one JSON line per theorem declared in a module of this package (the module groups in
`roots` below): its name, module, statement, a raw form of its type, and the axioms it
depends on (`Lean.collectAxioms`, the function behind `#print axioms`). The statement is
printed with no elision (`pp.deepTerms`, `pp.proofs`, a high `pp.maxSteps`) on one line. The
raw form writes out every node of the type expression with a tag per constructor, names
component by component and strings quoted; scripts/census.py pins its SHA-256. A syntax
value in metadata is written only as `(dsyntax)`, and census.py rejects a type that contains
one. Prints one JSON line per other constant kind that adds trust (an `axiomInfo` or an
`opaqueInfo` in a package module), and one line per package module that the census imports.
The imports above are the modules that no other module imports; with them the census sees every
module of the package, and census.py checks that. The model modules of the parent package are
imported too, but they are not in `roots` and are not listed.
-/

set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 100000000

open Lean Elab Command Meta

/-- A name, component by component (strings quoted), so that no two names share a form. -/
def rawName : Name → String
  | .anonymous => "(anon)"
  | .str p s => s!"(str {rawName p} {s.quote})"
  | .num p k => s!"(num {rawName p} {k})"

def rawLevel : Level → String
  | .zero => "(lzero)"
  | .succ l => s!"(lsucc {rawLevel l})"
  | .max a b => s!"(lmax {rawLevel a} {rawLevel b})"
  | .imax a b => s!"(limax {rawLevel a} {rawLevel b})"
  | .param n => s!"(lparam {rawName n})"
  | .mvar m => s!"(lmvar {rawName m.name})"

def rawData : DataValue → String
  | .ofString v => s!"(dstr {v.quote})"
  | .ofBool v => s!"(dbool {v})"
  | .ofName v => s!"(dname {rawName v})"
  | .ofNat v => s!"(dnat {v})"
  | .ofInt v => s!"(dint {v})"
  | .ofSyntax _ => "(dsyntax)"

/-- Every node of `e`, with a tag per constructor: binder names and kinds, constant names,
    universe levels, literal values and metadata (names component by component, strings
    quoted). -/
partial def rawExpr : Expr → String
  | .bvar i => s!"(bvar {i})"
  | .fvar x => s!"(fvar {rawName x.name})"
  | .mvar x => s!"(mvar {rawName x.name})"
  | .sort l => s!"(sort {rawLevel l})"
  | .const n ls => s!"(const {rawName n} {ls.map rawLevel})"
  | .app f a => s!"(app {rawExpr f} {rawExpr a})"
  | .lam n t b bi => s!"(lam {rawName n} {repr bi} {rawExpr t} {rawExpr b})"
  | .forallE n t b bi => s!"(forall {rawName n} {repr bi} {rawExpr t} {rawExpr b})"
  | .letE n t v b nd => s!"(let {rawName n} {nd} {rawExpr t} {rawExpr v} {rawExpr b})"
  | .lit (.natVal v) => s!"(nat {v})"
  | .lit (.strVal v) => s!"(str {v.quote})"
  | .mdata d e => s!"(mdata {d.entries.map fun (k, v) => (rawName k, rawData v)} {rawExpr e})"
  | .proj s i e => s!"(proj {rawName s} {i} {rawExpr e})"

/-- The module groups of the package (lakefile.toml). -/
def roots : List Name :=
  [`Refinement, `Tree, `Balance, `Journey, `Gas]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let ours (m : Name) := roots.any (·.isPrefixOf m)
  for m in mods do
    if ours m then
      IO.println (Json.compress (Json.mkObj [("kind", "module"), ("module", m.toString)]))
  let mut rows : Array (String × String × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if ours m then
        rows := rows.push (n.toString, m.toString, ci)
  rows := rows.qsort (fun a b => a.1 < b.1)
  for (n, m, ci) in rows do
    match ci with
    | .thmInfo _ =>
      let axs ← collectAxioms ci.name
      let ty ← liftTermElabM do return (← ppExpr ci.type).pretty 100000000
      let axs := (axs.map toString).qsort (· < ·)
      let internal := ci.name.isInternalDetail || isPrivateName ci.name
      IO.println (Json.compress (Json.mkObj [("kind", "theorem"), ("name", n), ("module", m),
        ("internal", toJson internal), ("type", ty), ("raw", rawExpr ci.type),
        ("axioms", toJson axs)]))
    | .axiomInfo _ =>
      IO.println (Json.compress (Json.mkObj [("kind", "axiomInfo"), ("name", n), ("module", m)]))
    | .opaqueInfo _ =>
      IO.println (Json.compress (Json.mkObj [("kind", "opaqueInfo"), ("name", n), ("module", m)]))
    | _ => pure ()
