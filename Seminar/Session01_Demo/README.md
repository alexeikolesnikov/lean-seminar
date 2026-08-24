# Session 01 — what does a machine-checked proof actually certify?

The first meeting, and a tour of the whole instrument, organised around this:

> Lean's kernel certifies that a **proof** establishes a **statement**.
> Nothing checks that the statement is the theorem you meant.

The session shows both: several things Lean does well, and several places
where a statement compiles and does not mean what it appears to.

## The arc

1. **It tells you that you are wrong.** `plausible` hunts counterexamples
   rather than proofs, and finds one for `n < 2n` at `n = 0`. We open here
   deliberately: a tool that only ever agrees with you is not worth trusting.
   Then the same fact as a three-line proof — `intro`, `have`, `simp at` —
   with the Infoview read after each line.
2. **One example, taken apart.** `#check` and types — including the one that
   lands: `#check (2 + 2 = 4)` reports `Prop`, so a *statement* is a kind of
   thing, and being true is a separate question. Then a single `linarith`
   proof with its parts labelled — command, objects, assumption, goal, proof,
   tactic — and the Infoview read before and after it. Unicode input,
   `trace_state`, `exact?`.
3. **Every function is total, so some values are junk.** Framed by the type
   itself: `#check @Nat.sub` reports `ℕ → ℕ → ℕ`, which promises a natural
   back for *every* pair of inputs. So `1/0 = 0` and `3 - 5 = 0` in `ℕ`. Not a
   bug — the price of a logic with no "undefined". `(3 : ℤ) - 5 = -2` makes the
   point that the type is part of the question.
4. **Vacuously true statements**, which are worse than false ones. A false
   statement will not compile; a vacuous one compiles, goes green, and is not
   your theorem. The Archimedean property as anyone would write it on a board
   is provable by taking `N = 0`.
5. **Quantifier order.** `Metric.continuous_iff` and
   `Metric.uniformContinuous_iff` side by side. Nearly the same symbols,
   different mathematics, and only reading the quantifiers tells you which.
6. **What the kernel promises.** `#print axioms`: the ordinary three, then
   `sorryAx` from an unfinished proof, then `native_decide` — which makes Lean
   mint a brand-new axiom named after your own theorem. Mathlib's linter
   discourages it, and the source says why. Then: a `plausible` that *passes*
   also reports `sorryAx`, because on 100 successful tests it "acts like
   `admit`".
7. **And it proves real theorems.** √2 irrational in one line, because someone
   formalised it already; Gauss's sum by induction, proved rather than looked
   up. Nobody should leave thinking the tool is only a critic.

## Notes for whoever runs it

- **§1–§4 each carry a `NOW TRY THIS` block.** These are for participants at
  their own keyboard, not for the demo — numbered, ten seconds each, and
  written so that following them literally produces what the text says. That
  last part is the point: the earlier version told people to click at the end
  of the `linarith` line and read the hypotheses, where in fact the goals are
  already closed and the panel says `No goals`.
- **Say that `No goals` *is* the success message.** VS Code adds a mark in the
  margin; the browser editor does not. Anyone still on the web editor will
  otherwise go looking for a confirmation that never comes.
- **`trace_state` is the projector-safe way to show a goal.** It prints the
  state as a message wherever it is placed, so nothing depends on where the
  cursor happens to be. The Infoview's **Pin** button does the same job in
  VS Code, and is worth knowing for live use.
- **The `plausible` opener is live.** It is commented out in `Demo.lean` with
  its exact output; uncomment it in the room, watch it fail, comment it back.
- **`Demo.lean` contains two deliberate holes**, both in §6: an explicit
  `sorry`, and a `plausible` that passes. Both are the point. Check this file
  with `--allow-sorry`.
- **Warn the room about `plausible` explicitly.** Someone will try it on a true
  statement during the exercises, see it apparently succeed, and believe they
  proved something. `#print axioms` is the check.
- The `native_decide` axiom name is worth reading aloud slowly:
  `big_sum._native.native_decide.ax_1_1`. Lean names the new axiom after the
  theorem it was invented for.
- Gauss is stated as `2 * ∑ = n(n+1)`, not `∑ = n(n+1)/2`, because `/` on `ℕ`
  is the junk-valued division from §3. Say so — it closes the loop.

**Tactics introduced:** `#eval`, `#check`, `#print axioms`, `trace_state`,
`linarith`, `exact?`, `simp`, `plausible`, `native_decide`, `induction`, `ring`.

**Assumes:** nothing. This is the first session.

**Homework:** the [Natural Number Game](https://adam.math.hhu.de/).
