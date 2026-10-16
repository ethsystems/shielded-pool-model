# Declared trust

Allowed logical axioms (Lean/Mathlib standard):
- propext            : propositional extensionality
- Classical.choice   : classical choice
- Quot.sound         : quotient soundness

Domain axioms: none. A text check in the gate reads each line that
starts with `axiom`, after an optional `private` or `protected`. It
fails on such a line in a control, on one it cannot parse, and on any
other whose full name is not listed here. Separately, the axiom census
(`scripts/check_axioms.py`) allows exactly the three axioms above for
every result in `statements/INVENTORY.md` and rejects any other, listed
here or not. A domain assumption (hash collision resistance, verifier
soundness, ...) is therefore a named theorem hypothesis. An inventoried
result that uses a domain axiom needs a deliberate change to the census.
