# Session 01 — what does a machine-checked proof actually certify?

The first meeting, and a tour of the whole tool, organised around this:

> Lean's kernel certifies that a **proof** establishes a **statement**.
> Nothing checks that the statement is the theorem you meant.

The session shows both: several things Lean does well, and several places
where a statement compiles and does not mean what it appears to.

## The arc

1. **An example of a tactic.** `plausible` hunts counterexamples rather than
   proofs, and finds one for `n < 2n` at `n = 0`. Then the same fact as a
   three-line proof — `intro`, `have`, `simp at` — with the state after each
   line written in the margin.
2. **One example, taken apart.** `#check` and types, including the one worth
   pausing on: `#check (2 + 2 = 4)` reports `Prop`, so a *statement* is a kind
   of thing, and being true is a separate question. Then a single `linarith`
   proof with its parts labelled — command, objects, assumption, goal, proof,
   tactic — and the Infoview read before and after it. Unicode input,
   `trace_state`, `exact?`.
3. **Every function is total, so some values are junk.** Framed by the type:
   `#check @Nat.sub` reports `ℕ → ℕ → ℕ`, which promises a natural back for
   *every* pair of inputs. So `1/0 = 0` and `3 - 5 = 0` in `ℕ`. Not a bug — the
   price of a logic with no "undefined". `(3 : ℤ) - 5 = -2` makes the point that
   the type is part of the question.
4. **Vacuously true statements**, which are worse than false ones. A false
   statement will not compile; a vacuous one compiles and is not your theorem.
   The Archimedean property as anyone would write it on a board is provable by
   taking `N = 0`.
5. **The name is not the definition.** `#print Continuous` shows a single
   field — preimages of open sets are open — so `Metric.continuous_iff` is a
   theorem *about* continuity rather than its definition. Then `ContinuousOn`:
   every function is `ContinuousOn` a singleton, and on any finite set, because
   the definition asks for continuity *within* the set. The rule to take away
   is `#print` the definition rather than read a lemma about it.
6. **What the kernel promises.** `#print axioms`: the ordinary three, then
   `sorryAx` from an unfinished proof, then `native_decide` — which makes Lean
   mint a brand-new axiom named after your own theorem. Mathlib's linter
   discourages it, and the source says why. Then: a `plausible` that *passes*
   also reports `sorryAx`, because on 100 successful tests it "acts like
   `admit`".
7. **And it proves real theorems.** √2 irrational in one line, because someone
   formalised it already; Gauss's sum by induction, proved rather than looked
   up. So nobody leaves thinking the tool is only a critic.

## Notes

- **§1–§4 each carry a `NOW TRY THIS` block.** These are for participants at
  their own keyboard, not for the demo: numbered, ten seconds each, and written
  so that following them literally produces what the text says. 
- **`No goals` *is* the success message.** VS Code adds a mark in the
  margin; the browser editor does not. Anyone on the web editor will otherwise
  go looking for a confirmation that never comes.
- **`trace_state` is the projector-safe way to show a goal.** It prints the
  state as a message wherever it is placed, so nothing depends on where the
  cursor is. The Infoview's **Pin** button does the same job in VS Code.
- **The `plausible` opener is live.** It is commented out in `Demo.lean` with
  its exact output; uncomment, watch it fail, comment it back.
- **§5 is the most demanding part of the session.** If you are struggling,
  the `#print Continuous` half makes the point on its own and the `ContinuousOn`
  half can be dropped.
- **Warning about `plausible`.** Try it on a true statement during the exercises, 
  see it apparently succeed, but use `#print axioms` for the check.
- The `native_decide` axiom name is worth reading aloud slowly:
  `big_sum._native.native_decide.ax_1_1`. Lean names the new axiom after the
  theorem it was invented for.
- Gauss is stated as `2 * ∑ = n(n+1)`, not `∑ = n(n+1)/2`, because `/` on `ℕ`
  is the junk-valued division from §3.
- **`Demo.lean` contains two deliberate holes**, both in §6: an explicit
  `sorry`, and a `plausible` that passes. Check it with `leancheck.sh
  --allow-sorry`; CI allows them because the file header declares
  `CI: allow-sorry (2)`, and a third hole would fail the build.

**Tactics introduced:** `#eval`, `#check`, `#print`, `#print axioms`,
`trace_state`, `linarith`, `exact?`, `simp`, `plausible`, `native_decide`,
`induction`, `ring`.

**Assumes:** nothing. This is the first session.

**Homework:** the [Natural Number Game](https://adam.math.hhu.de/).
