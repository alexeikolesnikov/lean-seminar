# Session 01 — what does a machine-checked proof actually certify?

This demo walks through some examples of Lean code. Lean's kernel certifies 
that a **proof** establishes a **statement**. But we will see that work
is needed to check that the statement is the theorem you meant.

We will see several things Lean does well, and several places
where a statement compiles and does not mean what it appears to.

Here's the session if you want to start it on the Lean server (a little
slow, but requires no installation work): here is [the link](https://h1.nu/1CvrS
).

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
