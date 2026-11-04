/-
  Session 07 — Finding lemmas
  Math Dept Lean seminar — solutions

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Run:  lake env lean Seminar/Session07_Finding/Solutions.lean
        (from the seminar project root). No sorry.

  Tactics introduced: exact?, apply?, simp?, hint, rw?; the commands #check,
  #eval, #loogle, #leansearch; Mathlib's naming convention.
  Assumed from earlier: intro, exact, apply, obtain, rcases (session 3); rw,
  calc, ring, norm_num, linarith, simp (session 4); decide, ext, fin_cases
  (session 5).

  This file imports all of Mathlib: `exact?` searches only what is imported,
  and the exercises are about searching.
-/
import Mathlib

open Matrix

/-! # Finding lemmas — solutions

Where a proof uses a lemma that `exact?` returns, the comment says so. The
proofs are written out rather than left as `exact?`, so that the file states
which lemma did the work. -/

/-! ## Provided: Cayley–Hamilton for 2×2 matrices

Used in Problem 4. Mathlib has the theorem for every square matrix over a
commutative ring as `aeval_self_charpoly : aeval M M.charpoly = 0`, and the
characteristic polynomial of a 2×2 matrix as `charpoly_fin_two`. The three
lines below turn the general statement into the one a linear algebra course
states. -/

/-- `A² − (tr A) A + (det A) I = 0` for a 2×2 real matrix. -/
theorem cayley_hamilton_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ^ 2 - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  have h := aeval_self_charpoly A
  rw [charpoly_fin_two] at h
  simpa [Algebra.smul_def] using h

/-! ## Part I — Problems -/

/-- **Problem 1.** `det (AᵀA) ≥ 0`.
Decomposition: `det (AᵀA) = det Aᵀ · det A = (det A)²`. The two library facts
are `det_mul` and `det_transpose` (both found by `exact?` on the intermediate
statements, or by `simp? [det_mul]` on the goal); the last step is
`mul_self_nonneg`. -/
theorem P1 (A : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ (Aᵀ * A).det := by
  rw [det_mul, det_transpose]
  exact mul_self_nonneg A.det

/-- **Problem 2.** If `AB = I` then `det A ≠ 0`.
Decomposition: take determinants, `det A · det B = 1`, and a factor of a
nonzero product is nonzero. `exact?` on the whole statement also returns
`det_ne_zero_of_right_inverse h`; the proof below is the one by hand. -/
theorem P2 (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : A * B = 1) : A.det ≠ 0 := by
  intro hA
  have h1 : A.det * B.det = 1 := by
    rw [← det_mul, h, det_one]
  rw [hA, zero_mul] at h1
  exact zero_ne_one h1

/-- **Problem 2'.** The same, by the library lemma. -/
theorem P2' (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : A * B = 1) : A.det ≠ 0 :=
  det_ne_zero_of_right_inverse h  -- exact?

/-- **Problem 3 (a).** Similar matrices have the same trace.
Decomposition: `tr (P⁻¹ A P) = tr (P · P⁻¹ A)` by `trace_mul_comm`, and
`P · P⁻¹ = I`. The second fact is `mul_nonsing_inv`, whose hypothesis is
`IsUnit P.det`; `isUnit_iff_ne_zero` converts `P.det ≠ 0`. -/
theorem P3a (A P : Matrix (Fin 3) (Fin 3) ℝ) (hP : P.det ≠ 0) :
    (P⁻¹ * A * P).trace = A.trace := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP)
  calc (P⁻¹ * A * P).trace = (P * (P⁻¹ * A)).trace := by rw [trace_mul_comm]
    _ = (P * P⁻¹ * A).trace := by rw [Matrix.mul_assoc]
    _ = (1 * A).trace := by rw [hPP]
    _ = A.trace := by rw [Matrix.one_mul]

/-- **Problem 3 (b).** Similar matrices have the same determinant.
Decomposition: `det_mul` twice, `det (P⁻¹) = (det P)⁻¹`, cancel. The library
states `det_nonsing_inv : A⁻¹.det = Ring.inverse A.det`, and
`Ring.inverse_eq_inv'` says that in a field `Ring.inverse` is `⁻¹`. -/
theorem P3b (A P : Matrix (Fin 3) (Fin 3) ℝ) (hP : P.det ≠ 0) :
    (P⁻¹ * A * P).det = A.det := by
  calc (P⁻¹ * A * P).det = P⁻¹.det * A.det * P.det := by rw [det_mul, det_mul]
    _ = (P.det)⁻¹ * A.det * P.det := by rw [det_nonsing_inv, Ring.inverse_eq_inv']
    _ = A.det := by field_simp

/-- **Problem 3 (b').** Mathlib has (b) as `det_conj'`, with the hypothesis
`IsUnit P`. `exact?` finds it from that hypothesis and not from `P.det ≠ 0`;
`isUnit_iff_isUnit_det` and `isUnit_iff_ne_zero` bridge the gap. -/
theorem P3b' (A P : Matrix (Fin 3) (Fin 3) ℝ) (hP : P.det ≠ 0) :
    (P⁻¹ * A * P).det = A.det :=
  det_conj' ((isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hP)) A

/-- **Problem 4 (a).** A nilpotent 2×2 matrix has determinant 0.
Decomposition: `(det A)² = det (A²) = det 0 = 0`. The facts are `det_pow`
and `det_zero`; then `pow_eq_zero_iff`. -/
theorem P4a (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A ^ 2 = 0) : A.det = 0 := by
  have h1 : A.det ^ 2 = 0 := by
    rw [← det_pow, h, det_zero]
  exact (pow_eq_zero_iff two_ne_zero).mp h1

/-- **Problem 4 (b).** A nilpotent 2×2 matrix has trace 0.
Decomposition: Cayley–Hamilton with `A² = 0` and `det A = 0` leaves
`(tr A) • A = 0`, so either `tr A = 0` or `A = 0`, and in the second case
`tr A = tr 0 = 0`. The case split is `smul_eq_zero`. -/
theorem P4b (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A ^ 2 = 0) : A.trace = 0 := by
  have hd : A.det = 0 := P4a A h
  have hc := cayley_hamilton_two A
  rw [h, hd, zero_smul, add_zero, zero_sub, neg_eq_zero] at hc
  -- hc : A.trace • A = 0
  rcases smul_eq_zero.mp hc with ht | hA
  · exact ht
  · rw [hA, trace_zero]

/-- **Problem 5 (stretch).** If `A² = 0` then `I + A` is invertible, with
inverse `I − A`. The identity `(I + A)(I − A) = I − A²` holds in any ring,
commutative or not, and `noncomm_ring` proves it. -/
theorem P5 (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A ^ 2 = 0) : (1 + A) * (1 - A) = 1 := by
  have h1 : (1 + A) * (1 - A) = 1 - A ^ 2 := by noncomm_ring
  rw [h1, h, sub_zero]

/-! ## Part II — Conjectures

Each statement below is either proved or refuted. The refutations exhibit a
specific matrix: a concrete matrix identity is proved entrywise (`ext i j`,
`fin_cases`, `simp`), and an entry is extracted from a matrix equation `h`
with `congrFun (congrFun h i) j`. -/

/-- **Conjecture 1.** True. `det_mul_comm`, or `det_mul` twice and
`mul_comm`. -/
theorem conj1 : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, (A * B).det = (B * A).det := by
  intro A B
  rw [det_mul, det_mul, mul_comm]

/-- **Conjecture 2.** False: `A = I`, `B = −I` gives `det 0 = 0` on the left
and `det I + det (−I) = 2` on the right (`det_neg` has the sign
`(−1) ^ card n`, and `n = 2`). -/
theorem conj2 : ¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, (A + B).det = A.det + B.det := by
  intro h
  have h' := h 1 (-1)
  rw [add_neg_cancel, det_zero, det_neg, det_one, Fintype.card_fin] at h'
  norm_num at h'

/-- **Conjecture 3.** False: `A = B = I` gives `tr I = 2` and
`tr I · tr I = 4`. -/
theorem conj3 : ¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, (A * B).trace = A.trace * B.trace := by
  intro h
  have h' := h 1 1
  norm_num [trace_fin_two] at h'

/-- **Conjecture 4.** False; the correct statement is `transpose_mul`,
`(AB)ᵀ = BᵀAᵀ`. The counterexample compares the `(0, 0)` entries. -/
theorem conj4 : ¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, (A * B)ᵀ = Aᵀ * Bᵀ := by
  intro h
  have h' := h !![0, 1; 0, 0] !![0, 0; 1, 0]
  have h00 := congrFun (congrFun h' 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- **Conjecture 5.** False, and not for a mathematical reason: `A⁻¹` is
defined for every matrix, with `0⁻¹ = 0` (`Matrix.inv_zero`), so `A = 0`
gives `0 · 0 = 0 ≠ 1`. -/
theorem conj5 : ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A * A⁻¹ = 1 := by
  intro h
  have h' := h 0
  rw [Matrix.inv_zero, mul_zero] at h'
  have h00 := congrFun (congrFun h' 0) 0
  norm_num at h00

/-- **Conjecture 6.** True; this is Conjecture 5 with the hypothesis the
library lemma `mul_nonsing_inv` asks for, after `isUnit_iff_ne_zero`. -/
theorem conj6 : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.det ≠ 0 → A * A⁻¹ = 1 := by
  intro A hA
  exact mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)

/-- **Conjecture 7.** False, for the same reason as 5. A singular nonzero
matrix has `A⁻¹ = 0` (by `inv_def`, since `Ring.inverse 0 = 0`), and then
`A⁻¹⁻¹ = 0⁻¹ = 0 ≠ A`. The library's version carries the hypothesis:
`nonsing_inv_nonsing_inv : IsUnit A.det → A⁻¹⁻¹ = A`. -/
theorem conj7 : ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A⁻¹⁻¹ = A := by
  intro h
  have hinv : (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = 0 := by
    rw [inv_def]
    norm_num [det_fin_two_of]
  have h' := h !![1, 2; 2, 4]
  rw [hinv, Matrix.inv_zero] at h'
  have h00 := congrFun (congrFun h' 0) 0
  norm_num at h00

/-- **Conjecture 8.** False: `diag (1, −1)` squares to `I`. -/
theorem conj8 : ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A ^ 2 = 1 → A = 1 ∨ A = -1 := by
  intro h
  have hsq : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  rcases h _ hsq with h1 | h1
  · have h11 := congrFun (congrFun h1 1) 1
    norm_num at h11
  · have h00 := congrFun (congrFun h1 0) 0
    norm_num at h00

/-- **Conjecture 9.** False: matrices have zero divisors. -/
theorem conj9 : ¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B = 0 → A = 0 ∨ B = 0 := by
  intro h
  have hAB : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 0; 0, 1] = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rcases h _ _ hAB with h1 | h1
  · have h00 := congrFun (congrFun h1 0) 0
    norm_num at h00
  · have h11 := congrFun (congrFun h1 1) 1
    norm_num at h11

/-- **Conjecture 10.** True: `tr (AᵀA) = ∑ᵢ ∑ⱼ (A j i)²`. Unfolding `trace`
and `diag` and then `mul_apply` exposes the double sum; `Finset.sum_nonneg`
twice and `mul_self_nonneg` finish. No single library lemma states this. -/
theorem conj10 : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, 0 ≤ (Aᵀ * A).trace := by
  intro A
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg (A j i)

/-- **Conjecture 11.** True. Mathlib's `mul_eq_one_comm_of_card_eq` is stated
for rectangular matrices with the hypothesis that the index sets have the
same size; here that is `rfl`. -/
theorem conj11 : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B = 1 → B * A = 1 := by
  intro A B h
  exact (mul_eq_one_comm_of_card_eq (Fin 2) (Fin 2) ℝ rfl).mp h

/-- **Conjecture 12.** False: the matrix `!![0, 1; 0, 0]` squares to `0`.
(Problem 4 shows what *is* true of such a matrix.) -/
theorem conj12 : ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A ^ 2 = 0 → A = 0 := by
  intro h
  have hsq : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 := congrFun (congrFun (h _ hsq) 0) 1
  norm_num at h01
