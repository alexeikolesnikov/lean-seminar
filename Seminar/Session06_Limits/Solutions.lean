/-
  Session 06 — Sequences and limits
  Math Dept Lean seminar — solutions

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Run:  lake env lean Seminar/Session06_Limits/Solutions.lean
        (from the seminar project root), or leancheck.sh on this file.

  Tactics introduced: none. This session uses the tactics of sessions 3 to 5
  on a definition from analysis.
  Assumed from earlier: intro, exact, apply, obtain, use, rcases, by_contra
  (session 3); rw, calc, ring, linarith, norm_num (session 4); positivity,
  gcongr (session 5).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

/-! # Sequences and limits — solutions

A sequence of real numbers is a function `s : ℕ → ℝ`; its `n`-th term is
written `s n` rather than `sₙ`. The definition below is the one from a first
analysis course, written in Lean's notation. -/

/-- `ConvergesTo s a` says that the sequence `s` converges to `a`:
for every `ε > 0` there is an index `N` beyond which every term is within
`ε` of `a`. -/
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε

/-! ## Part A — Reading

No Lean to write. Four statements about a sequence `s` and a number `a`
follow. Exactly one of them says "`s` converges to `a`". The other three are
genuine statements, each of which says something else; the solutions say
what.

    (i)   ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε
    (ii)  ∃ N : ℕ, ∀ ε > 0, ∀ n ≥ N, |s n - a| < ε
    (iii) ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |s n - a| < ε
    (iv)  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, s n - a < ε

Answers.

(i) is the definition.

(ii) has `∃ N` before `∀ ε`, so the same `N` has to serve every `ε`. Beyond
`N` the terms are within every positive distance of `a`, hence equal to `a`:
the statement says `s` is eventually constant with value `a`. Exercise E
proves this.

(iii) says that for every `ε` the sequence comes within `ε` of `a` infinitely
often. That is the definition of `a` being a limit point (a subsequential
limit) of `s`; the sequence `(-1)^n` satisfies it with `a = 1`.

(iv) drops the absolute value. It says that `s n` is eventually below
`a + ε`, which holds for instance for any sequence bounded above by `a`.
Part D shows it follows from convergence; the converse fails. -/

/-! ## Part B — First proofs from the definition -/

/-- **B1.** Adding a constant to a convergent sequence shifts the limit by the
same constant. The index `N` is the one the hypothesis provides. -/
theorem convergesTo_add_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (hs : ConvergesTo s a) : ConvergesTo (fun n => s n + c) (a + c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  use N
  intro n hn
  have h : |s n + c - (a + c)| = |s n - a| := by ring_nf
  rw [h]
  exact hN n hn

/-- **B2.** Negating a convergent sequence negates the limit. -/
theorem convergesTo_neg {s : ℕ → ℝ} {a : ℝ}
    (hs : ConvergesTo s a) : ConvergesTo (fun n => -s n) (-a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  use N
  intro n hn
  have h : |-s n - -a| = |s n - a| := by
    rw [← abs_neg]
    ring_nf
  rw [h]
  exact hN n hn

/-- **B3.** The terms of a convergent sequence can be dropped one at a time:
if `s n → a` then `s (n + 1) → a`. The same `N` works. -/
theorem convergesTo_shift {s : ℕ → ℝ} {a : ℝ}
    (hs : ConvergesTo s a) : ConvergesTo (fun n => s (n + 1)) a := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  use N
  intro n hn
  apply hN (n + 1)
  omega

/-! ## Part C — Algebra of limits

The demo proved `convergesTo_add`. It is restated here so that this file is
self-contained. -/

/-- The limit of a sum is the sum of the limits. -/
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
    (hs : ConvergesTo s a) (ht : ConvergesTo t b) :
    ConvergesTo (fun n => s n + t n) (a + b) := by
  intro ε hε
  obtain ⟨Ns, hNs⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Nt, hNt⟩ := ht (ε / 2) (by linarith)
  use max Ns Nt
  intro n hn
  have h1 : |s n - a| < ε / 2 := hNs n (le_of_max_le_left hn)
  have h2 : |t n - b| < ε / 2 := hNt n (le_of_max_le_right hn)
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **C1.** The limit of a difference is the difference of the limits.
Assemble it from `convergesTo_add` and `convergesTo_neg`; no `ε` appears. -/
theorem convergesTo_sub {s t : ℕ → ℝ} {a b : ℝ}
    (hs : ConvergesTo s a) (ht : ConvergesTo t b) :
    ConvergesTo (fun n => s n - t n) (a - b) := by
  have h := convergesTo_add hs (convergesTo_neg ht)
  -- `h` is about `fun n => s n + -t n` and the limit `a + -b`; these are the
  -- same functions and the same number as in the goal, up to `sub_eq_add_neg`.
  simp only [sub_eq_add_neg]
  exact h

/-- **C2.** The squeeze theorem. If `u n ≤ s n ≤ v n` for all `n`, and `u` and
`v` both converge to `L`, so does `s`. -/
theorem convergesTo_of_le_of_le {u s v : ℕ → ℝ} {L : ℝ}
    (hu : ConvergesTo u L) (hv : ConvergesTo v L)
    (hus : ∀ n, u n ≤ s n) (hsv : ∀ n, s n ≤ v n) : ConvergesTo s L := by
  intro ε hε
  obtain ⟨Nu, hNu⟩ := hu ε hε
  obtain ⟨Nv, hNv⟩ := hv ε hε
  use max Nu Nv
  intro n hn
  have h1 : |u n - L| < ε := hNu n (le_of_max_le_left hn)
  have h2 : |v n - L| < ε := hNv n (le_of_max_le_right hn)
  -- `abs_lt : |x| < ε ↔ -ε < x ∧ x < ε` turns each absolute value into two
  -- inequalities, which `linarith` can then combine with `hus n` and `hsv n`.
  rw [abs_lt] at h1 h2 ⊢
  have h3 := hus n
  have h4 := hsv n
  constructor
  · linarith
  · linarith

/-! ## Part D — Variants of the definition -/

/-- **D1.** Convergence implies statement (iv) of Part A. -/
theorem eventually_lt_of_convergesTo {s : ℕ → ℝ} {a : ℝ}
    (hs : ConvergesTo s a) : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, s n - a < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  use N
  intro n hn
  have h : |s n - a| < ε := hN n hn
  -- `le_abs_self : x ≤ |x|`
  calc s n - a ≤ |s n - a| := le_abs_self _
    _ < ε := h

/-- **D2.** Replacing `< ε` by `≤ ε` in the definition changes nothing.
One direction is immediate; the other applies the hypothesis at `ε / 2`. -/
theorem convergesTo_iff_le (s : ℕ → ℝ) (a : ℝ) :
    ConvergesTo s a ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| ≤ ε := by
  constructor
  · intro hs ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    use N
    intro n hn
    exact le_of_lt (hN n hn)
  · intro hs ε hε
    obtain ⟨N, hN⟩ := hs (ε / 2) (by linarith)
    use N
    intro n hn
    have h : |s n - a| ≤ ε / 2 := hN n hn
    linarith

/-! ## Part E — A statement that compiles and says something else -/

/-- A real number within every positive distance of `0` is `0`.
Proof by contradiction: if `x ≠ 0` then `|x| > 0`, and taking `ε = |x|` gives
`|x| < |x|`. -/
theorem eq_zero_of_abs_lt_all {x : ℝ} (hx : ∀ ε > 0, |x| < ε) : x = 0 := by
  by_contra hne
  have hpos : 0 < |x| := abs_pos.mpr hne
  have h : |x| < |x| := hx |x| hpos
  exact lt_irrefl _ h

/-- **E1.** Statement (ii) of Part A says that `s` is eventually constant with
value `a`. -/
theorem eventually_eq_of_swapped {s : ℕ → ℝ} {a : ℝ}
    (h : ∃ N : ℕ, ∀ ε > 0, ∀ n ≥ N, |s n - a| < ε) :
    ∃ N : ℕ, ∀ n ≥ N, s n = a := by
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  have hzero : s n - a = 0 := by
    apply eq_zero_of_abs_lt_all
    intro ε hε
    exact hN ε hε n hn
  linarith

/-! ## Part F — Uniqueness of limits

The demo proved this. Restated for completeness. -/

/-- A sequence has at most one limit. If `a ≠ b`, take `ε = |a - b| / 2`: far
enough out, a term would have to be within `ε` of both, which is impossible. -/
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
    (ha : ConvergesTo s a) (hb : ConvergesTo s b) : a = b := by
  by_contra hne
  have hpos : 0 < |a - b| / 2 := by
    have : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
    linarith
  obtain ⟨Na, hNa⟩ := ha _ hpos
  obtain ⟨Nb, hNb⟩ := hb _ hpos
  have h1 : |s (max Na Nb) - a| < |a - b| / 2 := hNa (max Na Nb) (le_max_left _ _)
  have h2 : |s (max Na Nb) - b| < |a - b| / 2 := hNb (max Na Nb) (le_max_right _ _)
  have h : |a - b| < |a - b| := by
    calc |a - b| = |(a - s (max Na Nb)) + (s (max Na Nb) - b)| := by ring_nf
      _ ≤ |a - s (max Na Nb)| + |s (max Na Nb) - b| := abs_add_le _ _
      _ = |s (max Na Nb) - a| + |s (max Na Nb) - b| := by rw [abs_sub_comm a]
      _ < |a - b| / 2 + |a - b| / 2 := by linarith
      _ = |a - b| := by ring
  exact lt_irrefl _ h

/-! ## Part G — Optional -/

/-- **G1.** Scalar multiples. The case `c = 0` is a constant sequence; for
`c ≠ 0` apply the hypothesis at `ε / |c|`. -/
theorem convergesTo_const_mul {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (hs : ConvergesTo s a) : ConvergesTo (fun n => c * s n) (c * a) := by
  rcases eq_or_ne c 0 with hc | hc
  · -- `c = 0`: every term is `0`, and so is the limit.
    intro ε hε
    use 0
    intro n _
    rw [hc]
    simp [hε]
  · intro ε hε
    have hcpos : 0 < |c| := abs_pos.mpr hc
    obtain ⟨N, hN⟩ := hs (ε / |c|) (by positivity)
    use N
    intro n hn
    have h : |s n - a| < ε / |c| := hN n hn
    calc |c * s n - c * a| = |c * (s n - a)| := by ring_nf
      _ = |c| * |s n - a| := abs_mul _ _
      _ < |c| * (ε / |c|) := by gcongr
      _ = ε := by field_simp

/-- **G2.** The definition above agrees with Mathlib's.
`Filter.Tendsto s Filter.atTop (nhds a)` reads "`s n` tends to `a` as `n`
tends to infinity". `Metric.tendsto_atTop` unfolds it to an `ε`–`N` statement
with `dist (s n) a` in place of `|s n - a|`, and `Real.dist_eq` says those are
the same. -/
theorem convergesTo_iff_tendsto (s : ℕ → ℝ) (a : ℝ) :
    ConvergesTo s a ↔ Filter.Tendsto s Filter.atTop (nhds a) := by
  rw [Metric.tendsto_atTop]
  simp only [Real.dist_eq]
  rfl

/-! ## Part H — The three tasks in `Assistant.lean`

Reference proofs. Task 1 is `convergesTo_neg` above (Part B2). -/

/-- **H2.** A convergent sequence is bounded. Proved by moving to Mathlib's
`Tendsto` through `convergesTo_iff_tendsto` and using two library facts,
`Filter.Tendsto.bddAbove_range` and `Filter.Tendsto.bddBelow_range`. A direct
`ε`–`N` proof needs a maximum over the finitely many terms before `N`. -/
theorem bounded_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (hs : ConvergesTo s a) :
    ∃ M : ℝ, ∀ n, |s n| ≤ M := by
  rw [convergesTo_iff_tendsto] at hs
  obtain ⟨A, hA⟩ := hs.bddAbove_range
  obtain ⟨B, hB⟩ := hs.bddBelow_range
  use max |A| |B|
  intro n
  -- `hA : A ∈ upperBounds (Set.range s)`; applied to the element `s n` of the
  -- range, witnessed by `⟨n, rfl⟩`, it gives `s n ≤ A`.
  have h1 : s n ≤ A := hA ⟨n, rfl⟩
  have h2 : B ≤ s n := hB ⟨n, rfl⟩
  rw [abs_le]
  constructor
  · have := neg_abs_le B
    have := le_max_right |A| |B|
    linarith
  · have := le_abs_self A
    have := le_max_left |A| |B|
    linarith

/-- **H3a.** `(-1)^n` comes within every `ε` of `1` infinitely often: beyond
any `N`, the even index `2N` has `(-1)^(2N) = 1`. -/
theorem neg_one_pow_frequently_near_one :
    ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |((-1 : ℝ) ^ n) - 1| < ε := by
  intro ε hε N
  use 2 * N
  constructor
  · omega
  · have h : ((-1 : ℝ) ^ (2 * N)) = 1 := by
      rw [pow_mul]
      norm_num
    rw [h, sub_self, abs_zero]
    exact hε

/-- **H3b.** `(-1)^n` does not converge to `1`: take `ε = 1`; for any `N`,
the odd index `2N + 1` has `(-1)^(2N+1) = -1`, at distance `2` from `1`. -/
theorem not_convergesTo_neg_one_pow : ¬ ConvergesTo (fun n => (-1 : ℝ) ^ n) 1 := by
  intro h
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  have h1 := hN (2 * N + 1) (by omega)
  have hodd : ((-1 : ℝ) ^ (2 * N + 1)) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  simp only at h1
  rw [hodd] at h1
  norm_num at h1

/-- **H3c.** Hence the statement of Task 3 is false: if it held, applying it
to `(-1)^n` with `a = 1` would contradict H3b. -/
theorem task3_statement_false :
    ¬ ∀ (s : ℕ → ℝ) (a : ℝ),
        (∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |s n - a| < ε) → ConvergesTo s a := by
  intro h
  exact not_convergesTo_neg_one_pow (h _ 1 neg_one_pow_frequently_near_one)
