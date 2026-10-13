# Declared trust

Allowed logical axioms (Lean/Mathlib standard):
- propext            : propositional extensionality
- Classical.choice   : classical choice
- Quot.sound         : quotient soundness

Domain axioms: none. The gate fails on an axiom declared in a control,
and on any other declared axiom not listed here. Separately, the axiom
census (`scripts/check_axioms.py`) allows exactly the three axioms above
for every result in `statements/INVENTORY.md` and rejects any other,
listed here or not. A domain assumption (hash collision resistance,
verifier soundness, ...) is therefore a named theorem hypothesis. An
inventoried result that uses a domain axiom needs a deliberate change to
the census.
