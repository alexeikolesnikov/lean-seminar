/-
  Session 05 — Extras: asymptotic notation in Mathlib
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Reading material, not a demo. Two questions from the floor — how is Landau
  notation written, and how would one prove (1 + 1/n)ⁿ → e — answered with
  what the library has. The statements use filters, which are session 9; they
  can be read before they can be written.

  Imports the whole of Mathlib: slow to load, and `exact?` sees everything.
-/
import Mathlib

open Finset Filter Asymptotics

/-! ## 1. Landau notation

Mathlib writes `f = O(g)` as `f =O[l] g` and `f = o(g)` as `f =o[l] g`, where
`l` says *where* the comparison is made: `atTop` for `x → ∞`, `nhds a` for
`x → a`, and so on. For sequences and for functions on `ℝ` going to infinity,
`l` is `atTop`. -/

#check @Asymptotics.IsBigO
#check @Asymptotics.IsLittleO

/-! What the notation unfolds to: -/

#check @Asymptotics.isBigO_iff
-- f =O[l] g ↔ ∃ c, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖

#check @Asymptotics.isLittleO_iff
-- f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖

/-! The one new symbol is `∀ᶠ x in l, P x` — "eventually, `P x`" — and for
`l = atTop` it means exactly what the textbook means: -/

#check @Filter.eventually_atTop
-- (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b ≥ a, p b

/-! So `f =O[atTop] g` is: there is a constant `c` and a threshold `a` such
that `‖f x‖ ≤ c · ‖g x‖` for all `x ≥ a`. That is the definition from the
board, with `‖·‖` for the absolute value. Here is `x = O(x²)` proved from it,
with `c = 1` and threshold `1`: -/

example : (fun x : ℝ => x) =O[atTop] (fun x : ℝ => x ^ 2) := by
  apply IsBigO.of_bound 1
  -- `filter_upwards` is `intro` for "eventually": pick the threshold, then
  -- argue for an `x` beyond it.
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by positivity)]
  nlinarith

/-! Little-o is a limit statement when `g` does not vanish: -/

#check @Asymptotics.isLittleO_iff_tendsto
-- (∀ x, g x = 0 → f x = 0) → (f =o[l] g ↔ Tendsto (fun x => f x / g x) l (nhds 0))

example : (fun x : ℝ => x) =o[atTop] (fun x : ℝ => x ^ 2) := by
  rw [isLittleO_iff_tendsto (fun x hx => by simpa using hx)]
  -- `x / x² = x⁻¹` for `x ≠ 0`, which is eventually true, and `x⁻¹ → 0`.
  have : (fun x : ℝ => x / x ^ 2) =ᶠ[atTop] (fun x => x⁻¹) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
  exact tendsto_inv_atTop_zero.congr' this.symm

/-! Asymptotic equivalence, `f ~ g`, is `f ~[l] g`: -/

#check @Asymptotics.IsEquivalent
#check @Stirling.tendsto_stirlingSeq_sqrt_pi
-- Tendsto Stirling.stirlingSeq atTop (nhds √π)   where stirlingSeq n = n! / (√(2n) (n/e)ⁿ)

/-! ## 2. `(1 + 1/n)ⁿ → e`

The library has it, for any `t`, as `(1 + t/n)ⁿ → exp t`: -/

#check @Real.tendsto_one_add_div_pow_exp
-- ∀ t : ℝ, Tendsto (fun n : ℕ => (1 + t / n) ^ n) atTop (nhds (Real.exp t))

example : Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) atTop (nhds (Real.exp 1)) := by
  simpa using Real.tendsto_one_add_div_pow_exp 1

/-! `Real.exp` is defined as a power series (`Complex.exp`, restricted), so
this is a theorem about the series, proved in Mathlib by way of
`(1 + t/n)ⁿ = exp (n · log (1 + t/n))` and a bound on the logarithm. The proof
is in `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean`; it is about
a page, and reading it is a reasonable exercise for after session 9.

What `Tendsto s atTop (nhds a)` means for a sequence of reals is the ε-N
statement, and the equivalence is one lemma: -/

#check @Metric.tendsto_atTop
-- Tendsto u atTop (nhds a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε

example (s : ℕ → ℝ) (a : ℝ) :
    ConvergesTo s a ↔ Tendsto s atTop (nhds a) := by
  rw [Metric.tendsto_atTop]
  simp only [ConvergesTo, Real.dist_eq]

/-! The next unit proves the basic facts about `ConvergesTo` directly from the
definition. Session 9 is about why Mathlib states the right-hand side instead. -/

/-! ## 3. Other asymptotic statements the library has

Each of these is a theorem to be read, not reproved. -/

#check @Real.isLittleO_log_id_atTop
-- Real.log =o[atTop] id

#check @isLittleO_pow_exp_pos_mul_atTop
-- ∀ (k : ℕ) {b : ℝ}, 0 < b → (fun x => x ^ k) =o[atTop] fun x => Real.exp (b * x)

#check @tendsto_pow_const_div_const_pow_of_one_lt
-- ∀ (k : ℕ) {r : ℝ}, 1 < r → Tendsto (fun n => ↑n ^ k / r ^ n) atTop (nhds 0)

#check @Real.tendsto_sum_range_one_div_nat_succ_atTop
-- Tendsto (fun n => ∑ i ∈ range n, 1 / (↑i + 1)) atTop atTop     (harmonic series)

#check @hasSum_zeta_two
-- HasSum (fun n => 1 / ↑n ^ 2) (Real.pi ^ 2 / 6)

#check @Real.exp_one_gt_d9
-- 2.7182818283 < Real.exp 1

#check @Real.pi_gt_three

/-! Two of these are "does this say what it claims" checks in their own right.
`Real.tendsto_sum_range_one_div_nat_succ_atTop` has `atTop` in the place where
`nhds a` would be: the limit is `+∞`, and the sum is over `range n` with
`1/(i+1)`, so it is `1 + 1/2 + ⋯ + 1/n`. And `hasSum_zeta_two` sums over all of
`ℕ` including `n = 0`, where `1 / 0 ^ 2 = 1 / 0 = 0` by session 4's convention;
the term contributes nothing and the statement is correct as written. -/
