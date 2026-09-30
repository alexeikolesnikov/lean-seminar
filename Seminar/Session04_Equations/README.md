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
| §Q | Three questions from session 3: `-1` on `ℕ` (and what an instance is), `Fin 7`, `use` versus `exact` |
| §0 | Where we were: how far the √2 argument is from finished after session 3 |
| §1 | `rw`: `rw [h]`, `rw [← h]`, `rw [h] at h'` |
| §2 | `ring` and `norm_num`; `calc` as a chain with a justification per line |
| §3 | `linarith`, and what it says when the goal is not linear |
| §4 | `simp`, and `simp?` printing the lemmas it used |
| §5 | The totality tax: `5 - 7 = 0`, `3 / 0 = 0`, `√(-1) = 0`, and two false statements `plausible` refutes |
| §6 | `omega`, the cancellation `4k² = 2q² → q² = 2k²`, and why not to divide |
| §7 | Summary |

## Questions from session 3

Answered in §Q of the demo; the short forms are here.

**Why does `(-1 : ℕ)` fail?** Unary minus is the typeclass operation `Neg`,
and `ℕ` has no instance, so the error is `failed to synthesize Neg ℕ` before
any arithmetic is attempted. Binary subtraction is a different class, `Sub`,
which `ℕ` does have — with the truncation that §5 is about. Without a type
ascription, `#check -1` gives `-1 : ℤ`: numerals default to `ℕ`, but the minus
sign forces a type that has `Neg`.

*What an instance is.* A typeclass is a signature together with a theory
(`Neg`: one symbol, no axioms; `CommRing`: the ring signature and the ring
axioms), and an instance is a model of it attached to a type, with the proofs
of the axioms carried as fields. Lean looks the instance up by type whenever
the symbol appears. Unlike a set in model theory, a type is expected to have
one canonical instance per class, which is what the `Fin n` case below is
about.

**What does `Fin 7` do, and is it modular arithmetic?** `Fin n` is a structure
holding a natural number and a proof that it is below `n`. Mathlib's main use
for it is as the standard `n`-element type, for indexing vectors, matrices and
finite sums. Its arithmetic does wrap (`(5 : Fin 7) + 4 = 2` by `rfl`), but the
ring `ℤ/nℤ` in Mathlib is `ZMod n`, which for `n > 0` is defined to be `Fin n`
and is where the ring and field instances live. `Fin n` carries the order by
value, which is incompatible with the ring structure (`6 + 1 = 0` but
`6 ≤ 6 + 1` is false), so its ring instance is off by default at this version
(`open scoped Fin.CommRing` turns it on).

**Is `use` more general than `exact`?** No; they claim different things about
their argument. `exact e` says `e` proves the goal as it stands. `use e` looks
at the goal's structure first — on `∃`, `∧`, `↔` it applies the constructor and
says `e` fills the first slot, leaving the rest as a goal with a shallow
attempt (`rfl`, an assumption) at closing it. On `∃ n, n + 2 = 5` both work;
on `∃ x : ℝ, x ^ 2 = 2`, `use √2` leaves `√2 ^ 2 = 2` as a goal, while `exact`
has to give the whole term. The case that separates them: with a hypothesis
`h : ∃ n, n + 2 = 5` and the same goal, `exact h` closes it and `use h` fails,
because `use` tries to make `h` the witness. On goals with no such structure
(`→`, `∀`, `=`) `use` falls back to behaving like `exact`.

## The exercises

`Exercises.lean` continues the thread from session 3 and takes it as far as it
goes without induction.

| Part | Content |
|---|---|
| A | The statements that need a hypothesis: `a - b + b = a`, `a / b * b = a`, `x / 0 = 0` |
| B | `ring` and `norm_num` |
| C | `calc` and `linarith`, with one step that is deliberately not linear |
| D | `rw` in the goal and in a hypothesis |
| E | `omega`: the cancellation, and the parity fact `2a ≠ 2b + 1` from session 3 |
| F | The descent step: if `p = 2a` and `q = 2b` solve `p² = 2q²`, so do `a` and `b` |
| G | No minimal counterexample exists |
| H | Nothing to do — what session 5 adds |

The file opens by restating session 3's Part F — if `n²` is even then `n` is
even — as `even_of_even_sq`, proved, so that it can be used without importing
that file. Part G assembles that lemma, this session's cancellation, and the
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
