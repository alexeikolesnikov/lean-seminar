# Session 05 — Induction and finite sums

Opens with a question from session 4: how to see what a tactic did. Then
finite sums and induction — identities, inequalities, and one bound from
analysis — and strong induction, which completes the √2 argument begun in
session 3.

Here's the demo if you want to start it on the Lean server (a little slow, but
requires no installation work):
https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Falexeikolesnikov%2Flean-seminar%2Fmaster%2FSeminar%2FSession05_Induction%2FDemo.lean

## What is in `Demo.lean`

| | |
|---|---|
| §Q | A question from session 4: seeing what `linarith`, `omega` and `simp` did — traces, `linear_combination`, `show_term` |
| §0 | Where we were: no minimal counterexample, and what is still missing |
| §1 | `Finset.range`, `∑`, `decide`; the off-by-one, with `plausible` finding it |
| §2 | `induction … with`; Gauss stated without a division, and why; `sum_range_succ` |
| §3 | Induction on an inequality: `n < 2ⁿ`; `Nat.le_induction` for a statement that starts late |
| §4 | A bound from analysis: `∑_{k≤n} 1/(k+1)² ≤ 2 − 1/(n+1)`, by the same induction over `ℝ`; `positivity`, `nlinarith`, `push_cast` |
| §5 | `Nat.strong_induction_on`, read before it is used; `sqrt_two_irrational`; `#print axioms` |
| §6 | Summary |

## What is in `Extras.lean`

Reading material, answering two questions from the floor. How
Landau notation is written — `f =O[atTop] g`, `f =o[atTop] g`, and what
`∀ᶠ x in atTop` unfolds to — with `x = O(x²)` and `x = o(x²)` proved from the
definitions. How `(1 + 1/n)ⁿ → e` is stated and where the library proves it
(`Real.tendsto_one_add_div_pow_exp`). And a list of asymptotic theorems the
library has, to be read rather than reproved: `log x = o(x)`, `xᵏ = o(eᵇˣ)`,
`nᵏ/rⁿ → 0`, the harmonic series diverges, Stirling, `∑ 1/n² = π²/6`.

The statements use filters, which are session 9. The file ends with a
one-lemma proof that Mathlib's `Tendsto s atTop (nhds a)` is the ε-N statement
for a real sequence. It imports the whole of Mathlib and is slow to load.

## The exercises

`Exercises.lean` opens by restating session 4's Part G — `no_minimal_counterexample`,
proved — and session 3's parity lemma, so that it needs no other file.

| Part | Content |
|---|---|
| A | `range` and `∑` on concrete values, by `decide`; the off-by-one |
| B | Induction on a sum: Gauss (divisionless), the odd numbers, powers of two; Gauss with the division derived by `omega` |
| C | Induction on an inequality: `n < 2ⁿ`; `n² ≤ 2ⁿ` for `n ≥ 4` with `Nat.le_induction` |
| D | The Basel bound: the telescoping step, the induction, and `< 2` |
| E | `sqrt_two_irrational` by strong induction; optionally, the same with `Nat.find` |
| F | Nothing to do — what the next unit adds |

Parts A–D are the homework. E1 ends the three-session argument and is best
attempted after D; its hint is written as three moves. E2 is optional.

## Notes

- **§Q: a tactic showing its work.** `set_option trace.linarith true in`
  prints the certificate (coefficients on the hypotheses and negated goal);
  `linear_combination h1 + h2` is the same certificate written as a proof, the
  counterpart of `simp only [...]`. `trace.omega` shows the atoms (`↑(k ^ 2)`,
  `↑(q ^ 2)` for the cancellation step) and a justification per case.
  `trace.Meta.Tactic.simp.rewrite` lists each rewrite with its lemma.
  `show_term linarith` prints the hundred-line term the kernel checks.
  `linear_combination` over `ℕ` with a division in the coefficients fails
  (`ring failed`), so the ℝ example from session 4 §3 is the one used.
- **Session 5 completes the √2 argument.** Session 3 supplied parity, session
  4 the cancellation and the descent step, this session the induction. The
  statement proved is the one in Part H of session 3's exercises,
  `p ^ 2 ≠ 2 * q ^ 2` for `q ≠ 0`, and `#print axioms` on it lists the standard
  three and no `sorryAx`.
- **`generalizing p` is the step to watch.** Without it, the strong induction
  hypothesis fixes the numerator — "this `p` fails for every smaller `q`" —
  which is not what Part G needs, since the descent changes the numerator. The
  demo shows both hypotheses side by side. Ordinary `induction q` gives a
  hypothesis about `q − 1`, and the descent lands at `q / 2`.
- **Does `Nat.strong_induction_on` say "take the smallest counterexample"?**
  Not in those words: it says that if `p` cannot fail for the first time
  anywhere, it never fails. E2 is the literal version, with `Nat.find` as the
  least element and `Nat.find_min` as its minimality. The two are equivalent;
  E1 is shorter because the minimality hypothesis arrives already in the shape
  Part G wanted. `Nat.find` needs decidability (`classical` supplies it);
  strong induction needs nothing.
- **State ℕ identities without `−` or `/`.** Gauss is `2 * ∑ = n(n+1)`, and
  the `/ 2` form follows by `omega`; proving the `/ 2` form directly fails at
  `ring` with the goal `1 + k + (k + k ^ 2) / 2 = (2 + k * 3 + k ^ 2) / 2`.
  Powers of two are `∑ + 1 = 2ⁿ`, not `∑ = 2ⁿ − 1`. Same reason as session 4.
- **`omega` and `2 ^ (k + 1)`.** It rewrites `b ^ (k + 1)` as `b * b ^ k` for a
  numeral base in preprocessing and then treats `b ^ k` as an atom, which is
  why B3's step closes without a `have`. Verified for bases 2 and 3; a power
  not of that shape needs `ring` first.
- **The Basel bound is the asymptotic content.** `∑_{k≤n} 1/(k+1)² ≤ 2 − 1/(n+1)`
  says the partial sums are increasing and bounded, hence convergent, without a
  definition of limit. Over `ℝ`, `linarith` replaces `ring`/`omega`, `positivity`
  supplies signs, and `push_cast` is needed so that `((m + 1 : ℕ) : ℝ)` and
  `(m : ℝ) + 1` are the same atom to `linarith`. A numerical check with `#eval`
  works in `ℚ` (`1968329/1270080 ≈ 1.55` for ten terms) and not in `ℝ`.
- **The `#eval` in `ℝ` message depends on the imports.** Under the demo's
  narrow imports it is "failed to compile definition … 'Real.instDivInvMonoid',
  which is 'noncomputable'"; under `import Mathlib` it prints
  `Real.ofCauchy (sorry …)`. The demo quotes the first and mentions the second.
- **`decide` refuses free variables** — "Expected type must not contain free
  variables" — which is the natural way to say what induction is for.
- **Imports.** `Demo.lean` and `Solutions.lean` are narrow; `Exercises.lean`
  and `Extras.lean` import all of Mathlib (the exercises because `exact?`
  should see everything, the extras because asymptotics pulls in most of the
  analysis library anyway).
- Work in `MyWork/`, not here — copy the exercise file over first, so that
  `git pull` does not conflict with your work.

**Tactics introduced:** `induction … with`, `Nat.le_induction`,
`Nat.strong_induction_on`, `decide`, `positivity`, `nlinarith`, `push_cast`;
`linear_combination` and `set_option trace.… in` in §Q.

**Assumes:** `plausible` and `#eval` from session 1; `intro`, `exact`,
`obtain`, `rcases`, `exfalso`, `subst` from session 3; `rw`, `calc`, `ring`,
`norm_num`, `linarith`, `omega`, `simp` from session 4.

**Homework:** *Mathematics in Lean* §5.2 (induction and recursion), and parts
A–D of the exercises. E1 after that. The next unit is sequences and the ε-N
limit, with no new tactics.
