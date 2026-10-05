/-
  Session 05 — Induction and finite sums
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: induction ... with, Nat.le_induction,
                      Nat.strong_induction_on, decide, positivity, nlinarith
  Assumed from earlier: #eval, plausible                    (Session 01)
                        intro, exact, obtain, rcases, exfalso, subst
                                                            (Session 03)
                        rw, calc, ring, norm_num, linarith, omega, simp
                                                            (Session 04)

  Opens with a question from session 4 (§Q): how to see what a tactic did.
  Then finite sums and induction, including one bound from analysis; then
  strong induction, which completes the √2 argument begun in session 3.
  Extras.lean has reading material on asymptotic notation in Mathlib.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Plausible.Tactic

open Finset

/-! ## Q. A question from session 4: can a tactic show its work?

`simp?` prints the lemmas `simp` used. There is no `linarith?`, because
`linarith` does something different: it does not apply lemmas, it searches for
a *certificate* — non-negative coefficients that combine the hypotheses and the
negated goal into `0 < 0`. The certificate is what there is to see, and there
are three ways to see it. The examples are from the end of session 4. -/

/-! **The trace.** `set_option trace.X true in` before a declaration makes the
tactic `X` print its run. For `linarith`, the last lines are the certificate: -/

set_option trace.linarith true in
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b + 1 ≤ c) : a ≤ c := by
  linarith

/-  The output ends with

        [linarith] found a contradiction: [(0, 1), (1, 1), (2, 1), (3, 1)]
        [linarith]     -1 + (a - b) + (b + 1 - c) + (c - a)
                     should be both 0 and negative

    Coefficient 1 on `a ≤ b`, on `b + 1 ≤ c`, and on the negated goal `c < a`;
    the variables cancel and `1 ≤ 0` is left. The lines before that show the
    preprocessing — negating the goal, moving everything to the form `… ≤ 0` —
    which is what to read when `linarith` fails for a reason that is not the
    mathematics.                                                              -/

/-! **The certificate as a proof.** `linear_combination` is the tactic that
states the coefficients, and it is the counterpart of `simp only [...]`: -/

example (a b c : ℝ) (h1 : a ≤ b) (h2 : b + 1 ≤ c) : a ≤ c := by
  linear_combination h1 + h2

/-! The line says: add the two hypotheses. `ring` normalization then checks
that the result is the goal. `linarith` finds the coefficients;
`linear_combination` records them. -/

/-! **`omega`**, on the cancellation step from session 4. Its trace is long
(two case splits, about a hundred lines), and two parts of it are the ones
to read: -/

set_option trace.omega true in
example (k q : ℕ) (h : 4 * k ^ 2 = 2 * q ^ 2) : q ^ 2 = 2 * k ^ 2 := by
  omega

/-      [omega] Extracted linear arithmetic problem:
            Atoms: [↑(k ^ 2), ↑(q ^ 2)]

    — the squares are atoms, as session 4 said — and, in each case,

        [omega] Justification:
            • [2, -1] ∈ {0}:   from   [4, -2] ∈ {0}: assumption 0
            • [2, -1] ∈ [1, ∞): assumption 5

    i.e. the hypothesis `4X − 2Y = 0` halved, against the negated goal
    `2X − Y ≥ 1`. The same contradiction as `linarith`'s, found a different
    way.                                                                      -/

/-! **`simp`** has its own trace for when `simp?` is not enough — it shows each
rewrite, with the lemma and its priority: -/

set_option trace.Meta.Tactic.simp.rewrite true in
example (l : List ℕ) : (l ++ []).length = l.length := by
  simp

/-      [Meta.Tactic.simp.rewrite] List.append_nil:1000:  l ++ []  ==>  l
        [Meta.Tactic.simp.rewrite] eq_self:1000:  l.length = l.length  ==>  True   -/

/-! **The proof term.** `show_term tac` prints the term the tactic built. For
`linarith` it is about a hundred lines of `Mathlib.Tactic.Linarith.lt_irrefl
(Eq.mp …)`. It shows one thing: the certificate is small, the term the
kernel checks is not, and the kernel checks the term. A bug in `linarith`
produces a wrong term, which the kernel rejects. (Session 3, on what is
trusted.) -/

/-  NOW TRY THIS, if the question comes up:

        example (a b c : ℝ) (h1 : a ≤ b) (h2 : b + 1 ≤ c) : a ≤ c := by
          show_term linarith                                                  -/

/-! `ring` has no certificate to show; it normalizes both sides and compares.
`ring_nf` leaves the normal form in the goal, which is the way to see what it
compared. The same `set_option trace.…` pattern applies to `positivity`,
`norm_num`, `aesop` (session 11), and to instance search
(`trace.Meta.synthInstance`, the hint the `Neg ℕ` error printed). -/

/-! ## 0. Where we were

Session 4 ended with Part G of its exercises: no *minimal* counterexample to
`p² ≠ 2q²` exists. Given any counterexample, the descent produces a smaller
one. What is missing is the passage from "no minimal counterexample" to "no
counterexample": the fact that a non-empty set of natural numbers has a least
element. In Lean that is an induction principle, and it is §5 of this file.

Before that, let's discuss ordinary induction, on the usual objects:
finite sums. -/

/-! ## 1. `Finset.range` and `∑`

`Finset.range n` is the finite set `{0, 1, …, n − 1}`. It has `n` elements and
does not contain `n`. -/

#eval Finset.range 5                    -- {0, 1, 2, 3, 4}
#eval (Finset.range 5).card             -- 5
#eval ∑ i ∈ Finset.range 5, i           -- 10

/-! The sum notation is `∑ i ∈ s, f i` — the `∈` is the membership symbol, and
the variable ranges over the finite set `s`. (Type `\sum`.)

For a concrete `n`, a statement like this is a computation, and `decide`
settles it by running one and having the kernel check the run. -/

example : ∑ i ∈ range 5, i = 10 := by
  decide

example : 5 ∉ range 5 := by
  decide

/-  NOW TRY THIS. `decide` is for closed statements only:

        example (n : ℕ) : n < 2 ^ n := by decide

    gives

        Expected type must not contain free variables
          n < 2 ^ n

    For a statement with an `n`, we use induction.                  -/

/-! The off-by-one. On a board, "the sum of the first `n` numbers" runs
`1 + ⋯ + n`. In Lean, `∑ i ∈ range n, i` runs `0 + ⋯ + (n − 1)`. The formula
`n(n+1)/2` belongs to the first; the second is `n(n−1)/2`. -/

/-  NOW TRY THIS.

        example (n : ℕ) : ∑ i ∈ range n, i = n * (n + 1) / 2 := by plausible

        Found a counter-example!
        n := 1
        issue: 0 = 1 does not hold

    At `n = 1` the sum is `0` (the only term is `i = 0`) and the formula gives
    `1`. The fix is to state it for `range (n + 1)`, which is what §2 does.   -/

/-! ## 2. Induction on a sum

`induction n with` splits into two cases. In `zero`, the goal is the statement
at `n = 0`. In `succ k ih`, the goal is the statement at `k + 1`, and `ih` is
the statement at `k`. -/

/-- Gauss. Stated as `2 · ∑ = n(n+1)` rather than with a `/ 2`, for a reason
given below. -/
theorem gauss (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- The sum over `range (k + 2)` is the sum over `range (k + 1)` plus the
    -- last term. That is `Finset.sum_range_succ`.
    rw [sum_range_succ]
    -- Distribute the `2 *` so that `ih` can be used.
    rw [mul_add, ih]
    -- What is left is an identity in `k`.
    ring

#check @Finset.sum_range_succ
-- ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n

/-  NOW TRY THIS. Use `ih` before peeling off the last term:

        | succ k ih =>
          rw [ih]

        Tactic `rewrite` failed: Did not find an occurrence of the pattern
          2 * ∑ i ∈ range (k + 1), i
        in the target expression
          2 * ∑ i ∈ range (k + 1 + 1), i = (k + 1) * (k + 1 + 1)

    The goal has `range (k + 1 + 1)`, the hypothesis has `range (k + 1)`.
    Rewriting is syntactic; `sum_range_succ` is what makes them match.      -/

/-! Why not `∑ = n(n+1)/2` directly? Session 4: division on `ℕ` is not a ring
operation, so `ring` cannot finish the step. -/

/-  NOW TRY THIS.

        theorem gauss_div (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
          induction n with
          | zero => rfl
          | succ k ih =>
            rw [sum_range_succ, ih]
            ring

        The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a
        normal form.
        ⊢ 1 + k + (k + k ^ 2) / 2 = (2 + k * 3 + k ^ 2) / 2

    True, but not a ring identity. The divisionless statement is proved and
    the one with the division follows from it by `omega`:                   -/

theorem gauss_div (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  have h := gauss n
  omega

/-! The same three steps — `sum_range_succ`, `ih`, algebra — prove each of the
standard summation identities. One more: -/

theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

/-! ## 3. Induction on an inequality

The induction hypothesis is an inequality and the step is a chain. -/

theorem lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    calc k + 1 < 2 ^ k + 1 := by omega
      _ ≤ 2 ^ k + 2 ^ k := by
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          omega
      _ = 2 ^ (k + 1) := by ring

/-! A statement that is false for small `n` and true from some point on —
`n² ≤ 2ⁿ` fails at `n = 3` — needs an induction that starts later.
`Nat.le_induction` is `induction` with a floor; its base case is `n = 4`, and
the step carries `4 ≤ k` as a hypothesis. The exercises have it (C2). -/

#check @Nat.le_induction

/-! ## 4. A bound from analysis

Everything so far was in `ℕ`. The same induction works over `ℝ`. Here it
proves that the partial sums of `∑ 1/k²` stay below `2`.

The key is a telescoping inequality, `1/(m+2)² ≤ 1/(m+1) − 1/(m+2)`. Two
tactics appear here for the first time. `positivity` proves `0 < e` or `0 ≤ e`
when `e` is visibly built from positive pieces. `nlinarith` is `linarith`
allowed to multiply hypotheses together once; it handles the products that
clearing denominators produces. -/

theorem telescope (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 1 + 1) ^ 2 ≤ 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 1 + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < (m : ℝ) + 1 + 1 := by positivity
  -- Combine the right-hand side into one fraction, then clear denominators.
  rw [div_sub_div _ _ hm.ne' hm2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `∑_{k ≤ n} 1/(k+1)² ≤ 2 − 1/(n+1)`. The induction is §2's, with
`linarith` in the place of `ring`. -/
theorem basel_bound (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ]
    have key := telescope m
    -- `((m + 1 : ℕ) : ℝ)` and `(m : ℝ) + 1` are the same number written two
    -- ways; `push_cast` writes them the same way so `linarith` sees one atom.
    push_cast
    linarith

theorem basel_lt_two (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 < 2 := by
  have h := basel_bound n
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-! An increasing sequence bounded above converges, so the series converges;
no definition of limit was needed to say so. (The value is `π²/6`, which is
`hasSum_zeta_two` in Mathlib; see Extras.lean.)

A numerical check, in `ℚ` because `ℝ` does not compute: -/

#eval ∑ k ∈ range 10, (1 : ℚ) / ((k : ℚ) + 1) ^ 2   -- 1968329/1270080 ≈ 1.5498

/-  NOW TRY THIS. The same `#eval` over `ℝ`:

        #eval ∑ k ∈ range 10, (1 : ℝ) / ((k : ℝ) + 1) ^ 2

        failed to compile definition, consider marking it as 'noncomputable'
        because it depends on 'Real.instDivInvMonoid', which is 'noncomputable'

    (With the whole of Mathlib imported the message is different — it prints
    `Real.ofCauchy (sorry …)` — with the same meaning.) A real number is a
    Cauchy sequence modulo equivalence; division on them is defined but not
    computable. Proofs about `ℝ` are unaffected; evaluation is not available. -/

/-! ## 5. Strong induction, and the end of the √2 argument

Here is the principle, read before it is used: -/

#check @Nat.strong_induction_on
-- ∀ {p : ℕ → Prop} (n : ℕ), (∀ n, (∀ m < n, p m) → p n) → p n

/-! To prove `p n` for every `n`, prove it for each `n` assuming it for every
`m < n`. There is no separate base case: at `n = 0` the assumption is vacuous.

Does this say "take the smallest counterexample"? Not in those words. It says
that if the property cannot fail for the first time anywhere, it never fails.
That is the same thing, and the exercises (E2) have the version that says it
in the other words, with `Nat.find`.

Session 4's Part G, restated: -/

theorem even_of_even_sq (n : ℕ) (h : ∃ k, n ^ 2 = 2 * k) : ∃ k, n = 2 * k := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    exact ⟨k, by omega⟩
  · exfalso
    obtain ⟨k, hk⟩ := ho
    obtain ⟨m, hm⟩ := h
    subst hk
    have hsq : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    omega

theorem no_minimal_counterexample (p q : ℕ) (hq : q ≠ 0) (h : p ^ 2 = 2 * q ^ 2)
    (hmin : ∀ q' < q, q' ≠ 0 → ∀ p', p' ^ 2 ≠ 2 * q' ^ 2) : False := by
  obtain ⟨a, ha⟩ := even_of_even_sq p ⟨q ^ 2, h⟩
  have hsq : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
  have h4 : q ^ 2 = 2 * a ^ 2 := by subst ha; omega
  obtain ⟨b, hb⟩ := even_of_even_sq q ⟨a ^ 2, h4⟩
  have hsq2 : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
  have hab : a ^ 2 = 2 * b ^ 2 := by subst hb; omega
  exact hmin b (by omega) (by omega) a hab

/-! And the theorem. `induction q using Nat.strong_induction_on` runs the
induction on `q`; `generalizing p` lets the numerator vary, which it must,
since the smaller counterexample Part G produces has a different one. -/

theorem sqrt_two_irrational (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2 := by
  induction q using Nat.strong_induction_on generalizing p with
  | _ q ih =>
    -- ih : ∀ m < q, ∀ p, m ≠ 0 → p ^ 2 ≠ 2 * m ^ 2
    intro h
    -- Part G wants `hmin : ∀ q' < q, q' ≠ 0 → ∀ p', …`; that is `ih` with two
    -- arguments swapped.
    exact no_minimal_counterexample p q hq h (fun q' hq' hne p' => ih q' hq' p' hne)

/-  NOW TRY THIS. Leave out `generalizing p` and look at `ih`:

        ih : ∀ m < q, m ≠ 0 → p ^ 2 ≠ 2 * m ^ 2

    The same `p` throughout. That is a weaker hypothesis — "this numerator
    fails for every smaller denominator" — and it is not what Part G needs,
    because the smaller counterexample has numerator `a`, not `p`.

    And with ordinary `induction q with`, the step hypothesis is

        ih : k ≠ 0 → p ^ 2 ≠ 2 * k ^ 2

    about `k` alone, while the descent lands at `q / 2`, not at `q − 1`.     -/

#print axioms sqrt_two_irrational
-- 'sqrt_two_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]

/-! The statement from Part H of session 3's exercises is proved, across three
sessions: parity (3), cancellation and descent (4), induction (5). No
`sorryAx` in the list. -/

/-! ## 6. Summary

1. `Finset.range n` is `{0, …, n − 1}`; `∑ i ∈ range n, f i` sums over it.
   Formulas from a board that runs to `n` are stated for `range (n + 1)`.
2. `decide` settles closed statements by computation. It refuses a free
   variable; that is induction's job.
3. `induction n with | zero => … | succ k ih => …`. For a sum, the step is
   `rw [sum_range_succ, ih]` and then algebra.
4. State identities over `ℕ` without `-` or `/` where possible, and derive the
   divided form with `omega`.
5. `Nat.le_induction` starts an induction at `n₀`.
6. Over `ℝ`: `positivity` for signs, `nlinarith` for products, `push_cast` to
   make `((m + 1 : ℕ) : ℝ)` and `(m : ℝ) + 1` the same atom.
7. `Nat.strong_induction_on`: to prove `p n`, assume `p m` for all `m < n`.
   `generalizing` for the variables that must change along the way.
8. `set_option trace.linarith true in` shows the certificate; `linear_combination`
   states it; `show_term` shows the term. -/
