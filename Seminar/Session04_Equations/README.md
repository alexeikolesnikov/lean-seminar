# Session 04 — Equational reasoning, and what totality costs

The first session whose proofs are about familiar basic things: identities,
inequalities, and arithmetic. The second half is what it costs Lean to make
every function total, and the arithmetic step the √2 argument needs.

Here's the demo if you want to start it on the Lean server (a little slow, but
requires no installation work):
https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Falexeikolesnikov%2Flean-seminar%2Fmaster%2FSeminar%2FSession04_Equations%2FDemo.lean

## What is in `Demo.lean`

| | |
|---|---|
| §0 | Where the √2 argument stands after session 3 |
| §1 | `rw`: `rw [h]`, `rw [← h]`, `rw [h] at h'` |
| §2 | `ring` and `norm_num`; `calc` as a chain with a justification per line |
| §3 | `linarith`, and what it says when the goal is not linear |
| §4 | `simp`, and `simp?` printing the lemmas it used |
| §5 | The totality tax: `5 - 7 = 0`, `3 / 0 = 0`, `√(-1) = 0`, and two false statements `plausible` refutes |
| §6 | `omega`, the cancellation `4k² = 2q² → q² = 2k²`, and why not to divide |
| §7 | Summary |

## The exercises

`Exercises.lean` continues the thread from session 3 and takes it as far as it
goes without induction.

| Part | Content |
|---|---|
| A | The statements that need a hypothesis: `a - b + b = a`, `a / b * b = a`, `x / 0 = 0` |
| B | `ring` and `norm_num` |
| C | `calc` and `linarith`, with one step that is deliberately not linear |
| D | `rw` in the goal and in a hypothesis |
| E | `omega`: the cancellation, and last week's parity lemma |
| F | The descent step: if `p = 2a` and `q = 2b` solve `p² = 2q²`, so do `a` and `b` |
| G | No minimal counterexample exists |
| H | Nothing to do — what session 5 adds |

Part G assembles session 3's parity rung, this session's cancellation, and the
descent step, in that order. What it does not contain is the right to assume
the counterexample is minimal. That is the well-ordering of `ℕ`, which in Lean
is strong induction, and it is session 5.

## Notes

- **`omega` arrives a session earlier than the syllabus had it.** It decides
  linear arithmetic over `ℕ` and `ℤ`, and it is what settles the cancellation
  step without dividing. Since the step is in this session, so is the tactic.
- **`omega` treats `k ^ 2` as an opaque atom.** That is why a tactic for linear
  arithmetic proves a statement about squares: as a claim about two unknowns
  `X = k²` and `Y = q²`, `4X = 2Y → Y = 2X` is linear. Worth stating, since
  otherwise it looks as though `omega` knows something about squaring.
- **`ring` and `omega` divide the work.** `ring` knows algebraic identities and
  ignores hypotheses; `omega` uses hypotheses and knows no algebra. The pattern
  in Part F — `have ... := by ring`, then `omega` — is how most arithmetic
  proofs in Mathlib are shaped.
- **The division route fails, and is worth showing.** On paper, `4k² = 2q²`
  becomes `q² = 2k²` by dividing by 2. In Lean over `ℕ`, division is truncating
  and `ring` will not touch it: `2 * a / 2 = a` by `ring` fails with "the `ring`
  tactic failed to close the goal". The statement is true and `omega` proves
  it, but the argument never needs it. Avoiding the division is simpler than
  carrying it.
- **`plausible` applies here as well as in session 1.** The two false
  statements in §5 fail only at the edge — `a = 0, b = 1` and `b = 0` — which
  is what a reader checking by hand is least likely to try.
- **Keep `simp?` output.** A `simp` that closes a goal says nothing about why;
  the `simp only [...]` that `simp?` prints names the lemmas used. Session 6
  needs the same habit when `exact?` returns unfamiliar lemmas.
- **C1's middle step is a product, so `linarith` does not apply.** The lemma
  is `mul_le_mul`, and `#check @mul_le_mul` shows what it asks for.
- Work in `MyWork/`, not here — copy the exercise file over first, so that
  `git pull` does not conflict with your work.

**Tactics introduced:** `rw`, `calc`, `ring`, `norm_num`, `linarith`, `simp`,
`simp?`, `omega`.

**Assumes:** `plausible` and `#eval` from session 1; the colon and
propositions as types from session 2; `intro`, `exact`, `obtain`, `use`,
`rcases`, `exfalso`, `subst` from session 3.

**Homework:** *Mathematics in Lean* §2 and §4, and parts A–F of the exercises.
Part G is best attempted after the others; its hint is written as four moves
rather than a sketch.
