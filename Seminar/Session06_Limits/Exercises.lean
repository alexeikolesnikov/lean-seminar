/-
  Session 06 — Sequences and limits
  Math Dept Lean seminar — exercises

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Run:  lake env lean Seminar/Session06_Limits/Exercises.lean
        (from the seminar project root). Every `sorry` is yours to replace.
  CI: allow-sorry (11)

  Tactics introduced: none. Everything here uses the tactics of sessions 3
  to 5 on the definition of a limit.
  Assumed from earlier: intro, exact, apply, obtain, use, rcases, by_contra
  (session 3); rw, calc, ring, linarith, norm_num (session 4); positivity,
  gcongr (session 5).

  Copy this file into MyWork/ before editing it.
-/
import Mathlib

/-! # Sequences and limits — exercises

A sequence of real numbers is a function `s : ℕ → ℝ`; its `n`-th term is
`s n`. The definition is the one from the demo. -/

/-- `ConvergesTo s a` says that the sequence `s` converges to `a`:
for every `ε > 0` there is an index `N` beyond which every term is within
`ε` of `a`. -/
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε

/-! ## Part A — Reading

No Lean to write. Four statements about a sequence `s` and a number `a`
follow. Exactly one of them says "`s` converges to `a`". The other three are
genuine statements, each of which says something else. Say which is which,
and for each of the other three, say in one sentence what it does say and
name a sequence that satisfies it without converging to `a`.

    (i)   ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε
    (ii)  ∃ N : ℕ, ∀ ε > 0, ∀ n ≥ N, |s n - a| < ε
    (iii) ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |s n - a| < ε
    (iv)  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, s n - a < ε

Two of these are taken up in Lean below: (iv) in Part D, (ii) in Part E. -/

/-! ## Part B — First proofs from the definition

Each of these follows the pattern of the demo: `intro ε hε`, take the `N`
the hypothesis supplies, `use` it, `intro n hn`, and estimate. -/

/-- **B1.** Adding a constant to a convergent sequence shifts the limit by the
same constant. -/
theorem convergesTo_add_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (hs : ConvergesTo s a) : ConvergesTo (fun n => s n + c) (a + c) := by
  -- Hint: `|s n + c - (a + c)| = |s n - a|`. State that as a `have` and
  -- prove it by `ring_nf`; then `rw` it into the goal.
  sorry

/-- **B2.** Negating a convergent sequence negates the limit. -/
theorem convergesTo_neg {s : ℕ → ℝ} {a : ℝ}
    (hs : ConvergesTo s a) : ConvergesTo (fun n => -s n) (-a) := by
  -- Hint: `abs_neg : |-x| = |x|`. After `rw [← abs_neg]` the inside is
  -- `-(-s n - -a)`, and `ring_nf` makes it `s n - a`.
  sorry

/-- **B3.** If `s n → a` then `s (n + 1) → a`. -/
theorem convergesTo_shift {s : ℕ → ℝ} {a : ℝ}
    (hs : ConvergesTo s a) : ConvergesTo (fun n => s (n + 1)) a := by
  -- Hint: the same `N` works. The last step is `hN (n + 1)` applied to a
  -- proof that `n + 1 ≥ N`, which `omega` can give.
  sorry

/-! ## Part C — Algebra of limits

The demo proved `convergesTo_add`. It is restated here with its proof so that
this file is self-contained; nothing to do in it. -/

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
Assemble it from `convergesTo_add` and `convergesTo_neg`; no `ε` needs to
appear. -/
theorem convergesTo_sub {s t : ℕ → ℝ} {a b : ℝ}
    (hs : ConvergesTo s a) (ht : ConvergesTo t b) :
    ConvergesTo (fun n => s n - t n) (a - b) := by
  -- Hint: `have h := convergesTo_add hs (convergesTo_neg ht)` is a statement
  -- about `fun n => s n + -t n` and `a + -b`. `simp only [sub_eq_add_neg]`
  -- rewrites the goal into that form.
  sorry

/-- **C2.** The squeeze theorem. If `u n ≤ s n ≤ v n` for all `n`, and `u` and
`v` both converge to `L`, so does `s`. -/
theorem convergesTo_of_le_of_le {u s v : ℕ → ℝ} {L : ℝ}
    (hu : ConvergesTo u L) (hv : ConvergesTo v L)
    (hus : ∀ n, u n ≤ s n) (hsv : ∀ n, s n ≤ v n) : ConvergesTo s L := by
  -- Hint: take the maximum of the two indices, as in `convergesTo_add`.
  -- `abs_lt : |x| < ε ↔ -ε < x ∧ x < ε`; after `rw [abs_lt] at h1 h2 ⊢`
  -- the goal is a conjunction of two linear inequalities, and `hus n`,
  -- `hsv n` supply the missing links for `linarith`.
  sorry

/-! ## Part D — Variants of the definition -/

/-- **D1.** Convergence implies statement (iv) of Part A. -/
theorem eventually_lt_of_convergesTo {s : ℕ → ℝ} {a : ℝ}
    (hs : ConvergesTo s a) : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, s n - a < ε := by
  -- Hint: `le_abs_self : x ≤ |x|`, then one `calc` or one `linarith`.
  sorry

/-- **D2.** Replacing `< ε` by `≤ ε` in the definition changes nothing. -/
theorem convergesTo_iff_le (s : ℕ → ℝ) (a : ℝ) :
    ConvergesTo s a ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| ≤ ε := by
  -- Hint: `constructor` gives two directions. One is `le_of_lt`. For the
  -- other, apply the hypothesis at `ε / 2`.
  sorry

/-! ## Part E — A statement that compiles and says something else

Statement (ii) of Part A has `∃ N` before `∀ ε`. It typechecks, and it is
a statement about `s` and `a`; it is not the statement that `s` converges to
`a`. These two exercises establish what it does say. -/

/-- **E1.** A real number within every positive distance of `0` is `0`. -/
theorem eq_zero_of_abs_lt_all {x : ℝ} (hx : ∀ ε > 0, |x| < ε) : x = 0 := by
  -- Hint: `by_contra hne`. Then `abs_pos.mpr hne : 0 < |x|`, so `hx` can be
  -- applied with `ε = |x|`, giving `|x| < |x|`; `lt_irrefl` finishes.
  sorry

/-- **E2.** Statement (ii) says that `s` is eventually constant with value
`a`. -/
theorem eventually_eq_of_swapped {s : ℕ → ℝ} {a : ℝ}
    (h : ∃ N : ℕ, ∀ ε > 0, ∀ n ≥ N, |s n - a| < ε) :
    ∃ N : ℕ, ∀ n ≥ N, s n = a := by
  -- Hint: take the `N` from `h`. For `n ≥ N`, E1 applied to `x = s n - a`
  -- gives `s n - a = 0`, and `linarith` turns that into `s n = a`.
  sorry

/-! ## Part F — Uniqueness of limits

The demo proved this; it is restated here with its proof. Read it; nothing to
do. The exercises in Part G use it. -/

/-- A sequence has at most one limit. -/
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
  -- Hint: `rcases eq_or_ne c 0 with hc | hc` splits the cases. In the second,
  -- `abs_mul : |x * y| = |x| * |y|`, `gcongr` for the inequality, and
  -- `field_simp` for `|c| * (ε / |c|) = ε`.
  sorry

/-- **G2.** The definition above agrees with Mathlib's.
`Filter.Tendsto s Filter.atTop (nhds a)` reads "`s n` tends to `a` as `n`
tends to infinity". -/
theorem convergesTo_iff_tendsto (s : ℕ → ℝ) (a : ℝ) :
    ConvergesTo s a ↔ Filter.Tendsto s Filter.atTop (nhds a) := by
  -- Hint: `#check @Metric.tendsto_atTop` and `#check Real.dist_eq`. After
  -- rewriting with the first and simplifying with the second, the two sides
  -- are the same statement.
  sorry
