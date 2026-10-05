/-
  Session 05 — Exercises
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: induction ... with, Nat.le_induction,
                      Nat.strong_induction_on, decide, positivity, nlinarith
  Assumed from earlier: rw, calc, ring, norm_num, linarith, omega, simp
                        (Session 04); intro, exact, obtain, use, rcases,
                        exfalso, subst (Session 03)

  Copy this file into MyWork/ before editing it. Replace each `sorry`.
  Parts A–D are the homework; E1 completes the √2 argument and is best
  attempted after D; E2 is optional.
-/
import Mathlib

open Finset

/-! # Induction and finite sums

## From session 4

Part G of session 4, restated so that it can be used here without importing
that file. Both are proved, not exercises. -/

/-- If `n²` is twice something, so is `n`. (Session 3, Part F.) -/
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

/-- No minimal counterexample to `p² ≠ 2q²` exists. (Session 4, Part G.) -/
theorem no_minimal_counterexample (p q : ℕ) (hq : q ≠ 0) (h : p ^ 2 = 2 * q ^ 2)
    (hmin : ∀ q' < q, q' ≠ 0 → ∀ p', p' ^ 2 ≠ 2 * q' ^ 2) : False := by
  obtain ⟨a, ha⟩ := even_of_even_sq p ⟨q ^ 2, h⟩
  have hsq : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
  have h4 : q ^ 2 = 2 * a ^ 2 := by subst ha; omega
  obtain ⟨b, hb⟩ := even_of_even_sq q ⟨a ^ 2, h4⟩
  have hsq2 : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
  have hab : a ^ 2 = 2 * b ^ 2 := by subst hb; omega
  exact hmin b (by omega) (by omega) a hab

/-! ## Part A — Reading `Finset.range` and `∑`

`Finset.range n` is `{0, 1, …, n − 1}`. For a concrete `n`, statements about it
are computations, and `decide` settles them. Before proving anything, run

    #eval Finset.range 5
    #eval ∑ i ∈ Finset.range 5, i

and predict the output first. -/

/-- **A1.** `range 5` has five elements. -/
theorem card_range_five : (range 5).card = 5 := by
  sorry

/-- **A2.** `5` is not one of them. -/
theorem five_not_mem_range_five : 5 ∉ range 5 := by
  sorry

/-- **A3.** `0 + 1 + 2 + 3 + 4 = 10`. -/
theorem sum_range_five : ∑ i ∈ range 5, i = 10 := by
  sorry

/-- **A4.** Which is wrong, the statement or the formula? Decide first; then
`decide`. -/
theorem off_by_one : ¬ (∑ i ∈ range 3, i = 3 * (3 + 1) / 2) := by
  sorry

/-! ## Part B — Induction on a sum

The pattern, from the demo:

    induction n with
    | zero => ...
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ...

`sum_range_succ` peels the last term off `∑ i ∈ range (k + 1), f i`; `ih`
rewrites the rest; algebra finishes. -/

/-- **B1.** Gauss, stated without a division. -/
theorem gauss (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  -- hint: after `sum_range_succ` the sum is inside `2 * (… + …)`; `mul_add`
  -- distributes before `ih` can match. Then `ring`.
  sorry

/-- **B2.** The sum of the first `n` odd numbers is `n²`. -/
theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  sorry

/-- **B3.** Powers of two. Stated with `+ 1` on the left rather than `2ⁿ − 1`
on the right, because of session 4. -/
theorem sum_two_pow (n : ℕ) : ∑ i ∈ range n, 2 ^ i + 1 = 2 ^ n := by
  -- hint: `omega` can finish the step; it knows `2 ^ (k + 1) = 2 * 2 ^ k`.
  sorry

/-- **B4.** Gauss with the division. Do not do induction again: B1 and `omega`. -/
theorem gauss_div (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  sorry

/-! ## Part C — Induction on an inequality -/

/-- **C1.** `n < 2ⁿ`. -/
theorem lt_two_pow (n : ℕ) : n < 2 ^ n := by
  -- hint: in the step, `k + 1 < 2 ^ k + 1 ≤ 2 ^ k + 2 ^ k = 2 ^ (k + 1)`. The
  -- middle step needs `1 ≤ 2 ^ k`, which is `Nat.one_le_two_pow`.
  sorry

/-- **C2.** `n² ≤ 2ⁿ` for `n ≥ 4`. False at `n = 3`, so the induction starts
at `4`: `induction n, hn using Nat.le_induction with | base => … | succ k hk ih => …`. -/
theorem sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  -- hint: first `have h1 : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith` — it needs
  -- `hk : 4 ≤ k`, which is in context. Then a `calc` as in C1.
  sorry

/-! ## Part D — A bound from analysis

Over `ℝ`. The index `k : ℕ` appears cast, as `(k : ℝ)`. Two tactics not seen
before: `positivity` proves `0 < e` or `0 ≤ e` when `e` is built from positive
pieces; `nlinarith` is `linarith` allowed to multiply hypotheses once. -/

/-- **D1.** The telescoping step: `1/(m+2)² ≤ 1/(m+1) − 1/(m+2)`. -/
theorem telescope (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 1 + 1) ^ 2 ≤ 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 1 + 1) := by
  -- hint: get `0 < (m : ℝ) + 1` and `0 < (m : ℝ) + 1 + 1` by `positivity`; then
  -- `rw [div_sub_div _ _ hm.ne' hm2.ne', div_le_div_iff₀ (by positivity) (by positivity)]`
  -- clears the fractions, and `nlinarith` finishes.
  sorry

/-- **D2.** The partial sums are bounded by `2 − 1/(n+1)`. -/
theorem basel_bound (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
  -- hint: the step is `sum_range_succ`, then `have key := telescope m`, then
  -- `push_cast` so that `((m + 1 : ℕ) : ℝ)` becomes `(m : ℝ) + 1`, then `linarith`.
  sorry

/-- **D3.** So every partial sum is below `2`. -/
theorem basel_lt_two (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 < 2 := by
  -- hint: D2, and `0 < 1 / ((n : ℝ) + 1)` by `positivity`.
  sorry

/-! ## Part E — Strong induction, and the end of the √2 argument

    #check @Nat.strong_induction_on
    -- ∀ {p : ℕ → Prop} (n : ℕ), (∀ n, (∀ m < n, p m) → p n) → p n

To prove `p n` for every `n`, prove it for each `n` assuming it for all
`m < n`. Session 4's Part G, restated above as `no_minimal_counterexample`, is
exactly such a step. -/

/-- **E1.** No natural numbers `p`, `q` with `q ≠ 0` satisfy `p² = 2q²`. -/
theorem sqrt_two_irrational (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2 := by
  -- hint, in three moves:
  --   `induction q using Nat.strong_induction_on generalizing p with`
  --   `| _ q ih =>`  — then `intro h`, and read what `ih` says.
  --   `no_minimal_counterexample p q hq h ?_` wants `hmin`; `ih` is `hmin` with
  --   its arguments in the order `q' hq' p' hne`, so `fun q' hq' hne p' => ih q' hq' p' hne`.
  sorry

/-- **E2.** (Optional.) "Take the smallest counterexample", literally. `Nat.find`
returns the least `n` satisfying a predicate known to be satisfied somewhere;
`Nat.find_spec` says it satisfies it, `Nat.find_min` says nothing below it does.
The `classical` line is what lets `Nat.find` apply to a predicate that is not
obviously decidable. -/
theorem sqrt_two_irrational' (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2 := by
  intro h
  classical
  have hex : ∃ q : ℕ, q ≠ 0 ∧ ∃ p, p ^ 2 = 2 * q ^ 2 := ⟨q, hq, p, h⟩
  -- hint: `obtain ⟨hq0, p0, hp0⟩ := Nat.find_spec hex`, then apply Part G to
  -- `p0` and `Nat.find hex`; the minimality hypothesis is `Nat.find_min hex`.
  sorry

/-! Once E1 is done, `#print axioms sqrt_two_irrational` should list exactly
`propext`, `Classical.choice`, `Quot.sound` — and no `sorryAx`. -/

/-! ## Part F — Where this goes

Nothing to do here.

Part D proved that a sequence is bounded without saying what a limit is. The
next unit does say it, in the form every analysis course uses,

    ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n − a| < ε

and proves the basic facts — constants, `1/(n+1) → 0`, sums, uniqueness — with
the tactics already in hand. -/
