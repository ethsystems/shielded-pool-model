> Frozen copy. Measured once in the research phase, not rerun here. Source date 2026-10-11.
> Sanitised for publication: see [../README.md](../README.md).

# Retrospective: lessons learned

## 6. Lessons learned

1. **Every tool's all-clear needs its own witness.** Halmos's loop-bound warning was hidden by our log
   filter (chapter 33); its symbolic-storage flag left setUp slots concrete (chapter 31); Kontrol 1.0.255
   explored an impossible SafeERC20 branch until a rewrite rule told it the bytes could not match (section
   4). Rule: every pass has a planted fault beside it that must fail.
2. **The declaration, not the prose.** Twice a worker's prose said more than the theorem (chapters 22,
   39). The fix was usually the English; once it was the game definition itself (chapter 22). The counting judge failed the whole table once; each
   correction made a claim say less, and the record shows the judges biting.
3. **A second model family finds claims, not proofs.** In the record, Astra found no broken proof. It found
   claims that said more than the proofs: the first statement of no double spend (chapter 3), four rows on
   Sep 29 (chapter 39), and items in each night council. Cross-family review was not used for every
   historical landing (Sep 17 to 29 was one family, LEDGER). Pay for it before the status moves, not after.
4. **The scope line is the product.** "Withdraw pays the right amount" is not a result; "within a
   fixed-code environment, token above 0x11, fixed caller, canonical proof lengths below 2^64, mocks that
   record and do not move balances, gas off" is. The board exists so that scope lines cannot hide.
5. **Gates with planted faults make overnight work trustworthy.** 24 fixtures, frozen hashes, a kernel
   census of axioms, no `sorry`, no `native_decide`, no bare `simp`. A gate that passed a planted sorry
   today (because a variable leaked into the test, section 8) was caught by the same discipline.
6. **Archive or it did not happen.** Two rows were not re-checkable because files lived only on one
   laptop (chapter 39). The rule since 2026-09-28: archive every source a theorem needs, re-elaborate from
   `evidence/` alone before landing, and name every external input.
7. **Repins are deliberate and they invalidate.** The input-0 membership guard moved from the model repo
   review into the campaign as the A0V port; every privacy result was invalidated and re-landed (PRIVPORT).
   Prose that restated the old status went stale; the reuse memo's rule 3 (cite, do not restate) came
   from that failure.
8. **Cheap check before expensive proof.** Halmos found the banked-root bug in minutes (chapter 27); the
   proof effort then went to the fixed code. Source reading before modelling exposed missing guards.
9. **Negative results are theorems.** The privacy counterexamples (chapters 30, 38, 40), the Lampe loop
   rule, the evm-smith axioms: each is a proved statement that named exactly the premise the positive
   result needs.
10. **Councils work; the round cap needs a tail.** Writer plus reviewer from different families, six
    rounds, seal at zero rejects: it produced reviewable packets unattended. Two packets ended unsealed on
    wording and an exec bit; a corrections-only round might have resolved them, with closure still verified.
11. **Compute hygiene is correctness work.** Memory caps per scope, one heavy Lean job, core dumps off,
    `-M` below the cap, timeouts that survive a suspend, and a precheck that refuses to start when the
    numbers do not add up (the kontrol launcher's first precheck did exactly that).
12. **Keep the kernel honest everywhere.** The stage-2 Lampe worker found 102 `native_decide` uses in an
    upstream standard library and replaced them before accepting anything (chapter 35). `#print axioms`
    on every landing, including the ones we did not write.

