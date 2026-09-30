# Declared trust

Allowed logical axioms (Lean/Mathlib standard):
- propext            : propositional extensionality
- Classical.choice   : classical choice
- Quot.sound         : quotient soundness

Domain axioms: NONE declared yet. Every future domain assumption
(hash collision resistance, verifier soundness, ...) is preferably a
named theorem hypothesis; if declared as an axiom it MUST be listed
here with one line of justification, or the gate fails.
