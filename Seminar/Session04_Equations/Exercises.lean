/-
  Session 04 — Exercises
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics needed: rw, calc, ring, norm_num, linarith, simp, omega
  Assumed from earlier: intro, exact, obtain, rcases, use, exfalso, subst
                        (Sessions 02–03)

  Copy this file into MyWork/ before editing it, so that `git pull` does not
  conflict with your work.

  Replace each `sorry` with a proof. Parts A–G are the session; G depends on F
  and is the last one to attempt. `Solutions.lean` carries the same statements
  with proofs and a note after each part headed "What this was for" — do the
  part first.
-/
import Mathlib

/-! # Equational reasoning, and what totality costs

## From session 3

Part F of session 3, restated so that it can be used here without importing
that file. It is proved, not an exercise. -/

/-- If `n²` is twice something, so is `n`. -/
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

/-! ## Part A — Statements that are true only sometimes

Before proving these, try each without its hypothesis and let `plausible`
look for a counterexample. The hypothesis is what the counterexample is
telling you about. -/

/-- **A1.** Subtraction on `ℕ` truncates, so this needs `b ≤ a`. -/
theorem sub_add_cancel' (a b : ℕ) (h : b ≤ a) : a - b + b = a := by
  -- hint: Mathlib has this. `exact?` will name it, or search for
  -- `Nat.sub_add_cancel`.
  sorry

/-- **A2.** Division on `ℕ` rounds down, so this needs `b` to divide `a`. -/
theorem div_mul_cancel' (a b : ℕ) (h : b ∣ a) : a / b * b = a := by
  sorry

/-- **A3.** Division by zero in `ℝ`. -/
theorem div_zero' (x : ℝ) : x / 0 = 0 := by
  -- hint: one tactic from §4 of the demo.
  sorry

/-! ## Part B — `ring` and `norm_num` -/

/-- **B1.** The square of a sum. -/
theorem sq_add (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry

/-- **B2.** A difference of squares. -/
theorem prod_sum_diff (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

/-- **B3.** Numerals only. -/
theorem numeral_fact : (2 : ℝ) ^ 10 = 1024 := by
  sorry

/-! ## Part C — `calc` and `linarith` -/

/-- **C1.** Squaring preserves `≤` on non-negative reals. Write it as a chain:
`x ^ 2 = x * x`, then `x * x ≤ y * y`, then `y * y = y ^ 2`. -/
theorem sq_le_sq_of_le (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  -- hint: the middle step is not linear, so `linarith` will not do it. The
  -- lemma is `mul_le_mul`; `#check @mul_le_mul` to see what it wants.
  sorry

/-- **C2.** A linear consequence of two linear hypotheses. -/
theorem linear_consequence (a b c : ℝ) (h1 : a ≤ b) (h2 : b + 1 ≤ c) :
    a ≤ c := by
  sorry

/-! ## Part D — `rw` -/

/-- **D1.** Rewriting the goal with a hypothesis. -/
theorem rw_goal (f : ℕ → ℕ) (a b : ℕ) (h : a = b) (hf : f b = 3) : f a = 3 := by
  sorry

/-- **D2.** Rewriting a hypothesis, in the other direction. -/
theorem rw_hyp (a b : ℕ) (h : a = b) (hb : b + 0 = 5) : a = 5 := by
  -- hint: `rw [← h] at hb`.
  sorry

/-! ## Part E — `omega` -/

/-- **E1.** Cancelling a factor of two. Do not divide: `omega` takes the
statement as it stands. -/
theorem cancel_two (k q : ℕ) (h : 4 * k ^ 2 = 2 * q ^ 2) : q ^ 2 = 2 * k ^ 2 := by
  sorry

/-- **E2.** A parity fact, supplied for you last week. -/
theorem two_mul_ne_two_mul_add_one (a b : ℕ) : 2 * a ≠ 2 * b + 1 := by
  sorry

/-! ## Part F — The descent step

From a solution, a smaller solution. Stated with witnesses — `p = 2a`,
`q = 2b` — so that no division appears anywhere. -/

/-- **F.** If `p² = 2q²` and both are even, the halves satisfy the same
equation. -/
theorem descent_step (p q a b : ℕ) (hp : p = 2 * a) (hq : q = 2 * b)
    (h : p ^ 2 = 2 * q ^ 2) : a ^ 2 = 2 * b ^ 2 := by
  -- hint: `subst` both equations, then give `omega` what it lacks —
  -- `have h1 : (2 * a) ^ 2 = 4 * a ^ 2 := by ring`, and the same for `b`.
  sorry

/-! ## Part G — The descent, set up

Part F applied twice rules out a *minimal* counterexample: a solution whose
`q` is as small as possible. That is the whole irrationality argument except
for the right to assume minimality, which session 5 supplies. -/

/-- **G.** No minimal counterexample exists. -/
theorem no_minimal_counterexample (p q : ℕ) (hq : q ≠ 0) (h : p ^ 2 = 2 * q ^ 2)
    (hmin : ∀ q' < q, q' ≠ 0 → ∀ p', p' ^ 2 ≠ 2 * q' ^ 2) : False := by
  -- hint, in four moves:
  --   `p` is even:  `obtain ⟨a, ha⟩ := even_of_even_sq p ⟨q ^ 2, h⟩`
  --   cancel:       `have h4 : q ^ 2 = 2 * a ^ 2` — you will need
  --                 `(2 * a) ^ 2 = 4 * a ^ 2` by `ring` first, then `omega`
  --   `q` is even:  the same lemma again, on `q`
  --   contradict:   apply `hmin` to the smaller witness. It wants four
  --                 arguments: the witness, a proof it is smaller, a proof it
  --                 is not zero, and the other half. The two side conditions
  --                 are `omega`'s work.
  sorry

/-! ## Part H — Where this goes

Nothing to do. Session 5 proves

    theorem sqrt_two_irrational (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2

by strong induction on `q`, with Part G as the step. No further arithmetic is
needed; what is added is the induction principle, and the question of whether
the principle says what one means by "take the smallest counterexample". -/
