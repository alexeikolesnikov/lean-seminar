/-
  Session 06 — Sequences and limits
  Math Dept Lean seminar — demo file

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Open in the web editor from the link in README.md, or run
        lake env lean Seminar/Session06_Limits/Demo.lean
  from the seminar project root. leancheck.sh: use --allow-sorry.
  CI: allow-sorry (1)

  Tactics introduced: none. The session applies the tactics of sessions 3
  to 5 to the definition of a limit.
  Assumed from earlier: intro, exact, apply, obtain, use (session 3);
  rw, calc, ring, linarith, norm_num (session 4); gcongr, positivity
  (session 5).

  This file imports all of Mathlib so that it opens in the web editor
  whatever the state of Mathlib's module tree there. See NOTES.md.
-/
import Mathlib

/-! # Sequences and limits

A sequence of real numbers is a function `s : ℕ → ℝ`. Its `n`-th term is
written `s n`; the subscript of `sₙ` has become an argument.

Session 5 proved identities and inequalities about finite sums by induction.
Its §4, the bound `∑_{k<n} 1/(k+1)² ≤ 2 - 1/(n+1)`, was not reached in the
meeting and is left as reading; it ends with the remark that the series
converges, and the word "converges" is not defined there. This session
defines it, in the form every analysis course uses, and proves the first
facts about it with tactics already in hand.

## 0. Reading a proof as a list of tactics

Each sentence of a textbook proof of convergence corresponds to one tactic.

    Let ε > 0.                                   intro ε hε
    Since s converges, choose N such that ...     obtain ⟨N, hN⟩ := hs ε hε
    Take N := ... .                              use ...
    Let n ≥ N.                                   intro n hn
    Then |s n - a| = ... ≤ ... < ε.              calc ...

The proof state after each tactic is the "we now have" of the written proof:
the hypotheses in force above the line, the claim still to be shown below it.
-/

/-! ## 1. The definition -/

/-- `ConvergesTo s a` says that the sequence `s` converges to `a`. -/
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε

-- `∀ ε > 0, P ε` is notation. Lean reads it as `∀ ε, ε > 0 → P ε`, which is
-- why `intro ε hε` below produces two things: the number and the hypothesis.
#check ConvergesTo
#print ConvergesTo

/-- A constant sequence converges to its value. Any `N` works; `N = 0` is
chosen. -/
example (c : ℝ) : ConvergesTo (fun _ => c) c := by
  intro ε hε
  -- The goal is now `∃ N, ∀ n ≥ N, |(fun x => c) n - c| < ε`. The term
  -- `(fun x => c) n` is `c`, but Lean displays it unevaluated until asked.
  use 0
  intro n hn
  -- Goal: `|(fun x => c) n - c| < ε`, with `hn : n ≥ 0` unused.
  -- `simp only` (with no lemmas) evaluates the function application, giving
  -- `|c - c| < ε`; `sub_self` and `abs_zero` do the arithmetic. The `rw`
  -- would also have worked without the `simp only`, since the two goals are
  -- the same up to evaluating the function; the display is the difference.
  simp only
  rw [sub_self, abs_zero]
  exact hε

/-! ## 2. The sequence 1/(n+1)

The statement needs a coercion: `n` is a natural number and `1/(n+1)` is to
be a real number. The placement of the arrow decides what the statement says, as
in session 2. -/

-- Division of natural numbers is integer division. The second sequence
-- below is `1, 0, 0, 0, ...`; the first is the one intended.
#eval (1 / (3 + 1 : ℚ))      -- 1/4
#eval (1 / (3 + 1 : ℕ))      -- 0

#check fun n : ℕ => 1 / ((n : ℝ) + 1)          -- the intended sequence
#check fun n : ℕ => ((1 / (n + 1) : ℕ) : ℝ)    -- a sequence that is 0 on a tail

-- The proof needs one fact about ℝ: for every positive `ε` there is a
-- natural number `N` with `1/(N+1) < ε`. This is the Archimedean property,
-- and Mathlib states it as follows.
#check @exists_nat_one_div_lt

/-- `1/(n+1) → 0`. -/
theorem convergesTo_one_div : ConvergesTo (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  use N
  intro n hn
  -- Goal: `|(fun n => 1 / (↑n + 1)) n - 0| < ε`. First evaluate the function,
  -- then remove the `- 0` and the absolute value of a positive quantity.
  simp only
  rw [sub_zero, abs_of_pos (by positivity)]
  -- Goal: `1 / (↑n + 1) < ε`. Since `N ≤ n`, `1/(n+1) ≤ 1/(N+1) < ε`.
  calc 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        -- `gcongr` reduces an inequality between two expressions of the same
        -- shape to inequalities between the parts that differ: here `N ≤ n`.
        gcongr
    _ < ε := hN

-- Rehearsed failure. Without `abs_of_pos`, `linarith` does not know that
-- `|1/(↑n+1)|` is `1/(↑n+1)`; it treats the absolute value as an unknown.
-- Uncomment to see "linarith failed to find a contradiction".
-- example (n N : ℕ) (ε : ℝ) (hn : N ≤ n) (hN : 1 / ((N : ℝ) + 1) < ε) :
--     |1 / ((n : ℝ) + 1)| < ε := by
--   linarith

/-! ## 3. The limit of a sum

The textbook argument: given `ε`, get `Ns` for `s` at `ε/2` and `Nt` for `t`
at `ε/2`, and take `N = max Ns Nt`. -/

/-- The limit of a sum is the sum of the limits. -/
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
    (hs : ConvergesTo s a) (ht : ConvergesTo t b) :
    ConvergesTo (fun n => s n + t n) (a + b) := by
  intro ε hε
  obtain ⟨Ns, hNs⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Nt, hNt⟩ := ht (ε / 2) (by linarith)
  use max Ns Nt
  intro n hn
  -- `hn : n ≥ max Ns Nt`. The two facts below are `n ≥ Ns` and `n ≥ Nt`,
  -- fed to the two hypotheses.
  have h1 : |s n - a| < ε / 2 := hNs n (le_of_max_le_left hn)
  have h2 : |t n - b| < ε / 2 := hNt n (le_of_max_le_right hn)
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

-- Rehearsed failure. Taking `N = Ns` instead of the maximum leaves the second
-- hypothesis unusable: `hNt n` needs `Nt ≤ n`, and nothing supplies it.
-- Put the cursor on the `sorry` to see the state; the hole is `n ≥ Nt`,
-- which does not follow from `hn : n ≥ Ns`.
example {s t : ℕ → ℝ} {a b : ℝ}
    (hs : ConvergesTo s a) (ht : ConvergesTo t b) :
    ConvergesTo (fun n => s n + t n) (a + b) := by
  intro ε hε
  obtain ⟨Ns, hNs⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Nt, hNt⟩ := ht (ε / 2) (by linarith)
  use Ns
  intro n hn
  have h1 : |s n - a| < ε / 2 := hNs n hn
  have h2 : |t n - b| < ε / 2 := hNt n (by sorry)
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

#print axioms convergesTo_add

/-! ## 4. Uniqueness of the limit

If `s` converges to `a` and to `b` with `a ≠ b`, take `ε = |a - b| / 2`. Far
enough out, a single term `s n` would be within `ε` of both `a` and `b`, so
`|a - b| ≤ |a - s n| + |s n - b| < |a - b|`. -/

/-- A sequence has at most one limit. -/
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
    (ha : ConvergesTo s a) (hb : ConvergesTo s b) : a = b := by
  by_contra hne
  have hpos : 0 < |a - b| / 2 := by
    have : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
    linarith
  obtain ⟨Na, hNa⟩ := ha _ hpos
  obtain ⟨Nb, hNb⟩ := hb _ hpos
  -- One index beyond both thresholds.
  have h1 : |s (max Na Nb) - a| < |a - b| / 2 := hNa (max Na Nb) (le_max_left _ _)
  have h2 : |s (max Na Nb) - b| < |a - b| / 2 := hNb (max Na Nb) (le_max_right _ _)
  have h : |a - b| < |a - b| := by
    calc |a - b| = |(a - s (max Na Nb)) + (s (max Na Nb) - b)| := by ring_nf
      _ ≤ |a - s (max Na Nb)| + |s (max Na Nb) - b| := abs_add_le _ _
      _ = |s (max Na Nb) - a| + |s (max Na Nb) - b| := by rw [abs_sub_comm a]
      _ < |a - b| / 2 + |a - b| / 2 := by linarith
      _ = |a - b| := by ring
  exact lt_irrefl _ h

/-! ## 5. The same definition in Mathlib

Mathlib does not define convergence of sequences separately. It has one
notion, `Filter.Tendsto`, which covers `n → ∞`, `x → a`, `x → a⁺`, and the
rest; session 9 is about how. For a sequence of reals it reads as follows. -/

#check @Filter.Tendsto
-- `Filter.Tendsto s Filter.atTop (nhds a)`: `s n` tends to `a` as `n` tends
-- to infinity. `atTop` stands for "n → ∞", `nhds a` for "near a".

-- `Metric.tendsto_atTop` unfolds it to the ε–N form, with `dist (s n) a` in
-- place of `|s n - a|`.
#check @Metric.tendsto_atTop
#check @Real.dist_eq

/-- The definition above and Mathlib's agree. -/
theorem convergesTo_iff_tendsto (s : ℕ → ℝ) (a : ℝ) :
    ConvergesTo s a ↔ Filter.Tendsto s Filter.atTop (nhds a) := by
  rw [Metric.tendsto_atTop]
  simp only [Real.dist_eq]
  rfl

-- Consequence: anything Mathlib knows about `Tendsto` applies to
-- `ConvergesTo`. For instance, `1/(n+1) → 0` is in the library already.
example : ConvergesTo (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
  rw [convergesTo_iff_tendsto]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## 6. Summary

- A limit statement is `∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε`, and each
  quantifier is handled by one tactic: `intro` for `∀`, `use` for `∃`,
  `obtain` to take apart a hypothesis of that shape.
- `calc` carries the estimate, `linarith` the arithmetic between lines,
  `gcongr` the monotonicity, `abs_add_le` the triangle inequality.
- The order of the quantifiers is the content of the definition. The
  exercises (Part A and Part E) look at what the other orders say.
- Mathlib's `Filter.Tendsto s Filter.atTop (nhds a)` is the same statement;
  `Metric.tendsto_atTop` is the dictionary between the two. -/
