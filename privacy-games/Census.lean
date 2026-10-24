import ChainGame.CommitOnly.CollisionControls
import ChainGame.CommitOnly.FundedChecks
import ChosenWorldGame.Controls
import OwnerGame.ROMCommit.Security
import OwnerGame.Toy
import RecipientGame.CommitOnly.CollisionControls
import RecipientGame.CommitOnly.Controls
import RecipientGame.CommitOnly.FundedPass
import RecipientGame.FundedWorlds
import RecipientGame.ROMCommit.Controls
import SenderGame.DropPRF
import SenderGame.ROMCommit.Security
import WithdrawGame.ROM.Control
import WithdrawGame.TransportControls
import Lean

/-!
# Census of the game modules

Prints one JSON line per constant declared in a module of this package (the module groups in
`roots` below) or in one of the three model modules it imports (`model` below). For a
theorem: its name, module, statement, a raw form of its type, and the axioms it depends on
(`Lean.collectAxioms`, the function behind `#print axioms`). The statement is printed with no
elision (`pp.deepTerms`, `pp.proofs`, a high `pp.maxSteps`) on one line. The raw form writes
out every node of the type expression with a tag per constructor, names component by
component and strings quoted; scripts/census.py pins its SHA-256. A syntax value in metadata
is written only as `(dsyntax)`, and census.py rejects a type that contains one. For every
other constant: its kind, and whether it is written in the source (`source`: a name that is
not internal and has a declaration range, and is not a constructor, a structure
projection, a recursor, or a `casesOn`, `noConfusion`, `ctorElim` or `elim` that Lean generates). Prints one line per package module that the census imports. The imports above
are the modules that no other module imports; with them the census sees every game module of
the package, and census.py checks that.
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
  [`PoolGame, `GameCorrespondence, `RecipientGame, `ChainGame, `ChosenWorldGame,
   `WithdrawGame, `OwnerGame, `SenderGame, `PrivacyTools, `CommitROM]

/-- The model modules the games import, from the gated model in the parent directory. -/
def model : List Name :=
  [`LeanShieldedPool.Pool.State, `LeanShieldedPool.Pool.Tx, `LeanShieldedPool.Pool.Events]

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiomInfo"
  | .opaqueInfo _ => "opaqueInfo"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let ours (m : Name) := roots.any (·.isPrefixOf m)
  for m in mods do
    if ours m then
      IO.println (Json.compress (Json.mkObj [("kind", "module"), ("module", m.toString)]))
  let mut rows : Array (String × String × String × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if ours m then
        rows := rows.push (n.toString, m.toString, "package", ci)
      else if model.contains m then
        rows := rows.push (n.toString, m.toString, "model", ci)
  rows := rows.qsort (fun a b => a.1 < b.1)
  for (n, m, group, ci) in rows do
    let internal := ci.name.isInternalDetail || isPrivateName ci.name
    let ranged := (← liftCoreM (findDeclarationRanges? ci.name)).isSome
    let elim := match ci.name with
      | .str p "ctorElim" => (env.find? p).any (·.isInductive)
      | .str p "elim" => (env.find? p).any (·.isCtor)
      | _ => false
    let derived := ci.isCtor || ci matches .recInfo _ || (env.getProjectionFnInfo? ci.name).isSome
      || isAuxRecursor env ci.name || isNoConfusion env ci.name || elim
    let source := !internal && ranged && !derived
    let base := [("kind", toJson (kindOf ci)), ("name", toJson n), ("module", toJson m),
      ("group", toJson group), ("internal", toJson internal), ("source", toJson source)]
    match ci with
    | .thmInfo _ =>
      let axs ← collectAxioms ci.name
      let ty ← liftTermElabM do return (← ppExpr ci.type).pretty 100000000
      let axs := (axs.map toString).qsort (· < ·)
      IO.println (Json.compress (Json.mkObj (base ++ [("type", toJson ty),
        ("raw", toJson (rawExpr ci.type)), ("axioms", toJson axs)])))
    | _ => IO.println (Json.compress (Json.mkObj base))
