/-
  Session 07 — Finding lemmas
  Math Dept Lean seminar — exercises

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Run:  lake env lean Seminar/Session07_Finding/Exercises.lean
        (from the seminar project root). Every `sorry` is yours to replace.
  CI: allow-sorry (19)

  Tactics introduced: exact?, apply?, simp?, hint, rw?; the commands #check,
  #eval, #loogle, #leansearch; Mathlib's naming convention.
  Assumed from earlier: intro, exact, apply, obtain, rcases (session 3); rw,
  calc, ring, norm_num, linarith, simp (session 4); decide, ext, fin_cases
  (session 5).

  This file imports all of Mathlib: `exact?` searches only what is imported,
  and these exercises are about searching.

  Copy this file into MyWork/ before editing it.
-/
import Mathlib

open Matrix

/-! # Finding lemmas — exercises

`Matrix (Fin 3) (Fin 3) ℝ` is the type of 3×3 real matrices; `Fin 3` is the
index set `{0, 1, 2}`. `A * B`, `Aᵀ`, `A⁻¹`, `A.det`, `A.trace`, `c • A` and
`1` mean what they usually mean. `!![a, b; c, d]` is a 2×2 matrix written out.

Two parts. Part I is five problems, stated as a linear algebra course would
state them and with no lemma names supplied: decide how the proof goes, then
find the facts it needs. Part II is twelve conjectures: decide whether each
is true, then prove it or refute it.

Three facts that nobody guesses, listed here so that no exercise depends on
guessing them:

- The library's hypothesis for "`A` is invertible" is `IsUnit A.det`.
  `isUnit_iff_ne_zero` converts it to and from `A.det ≠ 0`.
- A lemma may state the size of a matrix as `Fintype.card (Fin 3)` where
  you would write `3`. `Fintype.card_fin` rewrites one into the other.
- `Ring.inverse x` is the library's inverse in a ring that may not be a
  field; `Ring.inverse_eq_inv'` says that in a field it is `x⁻¹`.

In the meeting: Problems 1–3 and as many conjectures as time allows.
Homework: Problem 4 and the rest of Part II. Problem 5 is optional. -/

/-! ## Provided: Cayley–Hamilton for 2×2 matrices

Used in Problem 4. Mathlib has the theorem for every square matrix over a
commutative ring as `aeval_self_charpoly`, and the characteristic polynomial
of a 2×2 matrix as `charpoly_fin_two`; the three lines below turn the general
statement into the familiar one. Read it; it is not an exercise. -/

/-- `A² − (tr A) A + (det A) I = 0` for a 2×2 real matrix. -/
theorem cayley_hamilton_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ^ 2 - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  have h := aeval_self_charpoly A
  rw [charpoly_fin_two] at h
  simpa [Algebra.smul_def] using h

/-! ## Part I — Problems

For each: write the proof you would give on a blackboard as a sequence of
`have` statements, then find the library lemma for each step (`exact?` on
the `have`, `#check` on a guessed name, `simp?`, Loogle). Assemble with `rw`
or a `calc` block. -/

/-- **Problem 1.** The determinant of `AᵀA` is nonnegative. -/
theorem P1 (A : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ (Aᵀ * A).det := by
  sorry

/-- **Problem 2.** If `AB = I` then `det A ≠ 0`. Two proofs: one from
`det A · det B = 1` by hand, and the one-lemma proof `exact?` finds. -/
theorem P2 (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : A * B = 1) : A.det ≠ 0 := by
  sorry

/-- **Problem 3 (a).** Similar matrices have the same trace. -/
theorem P3a (A P : Matrix (Fin 3) (Fin 3) ℝ) (hP : P.det ≠ 0) :
    (P⁻¹ * A * P).trace = A.trace := by
  sorry

/-- **Problem 3 (b).** Similar matrices have the same determinant. After
proving it: state it again with the hypothesis `IsUnit P` instead of
`P.det ≠ 0`, run `exact?`, and read what the library calls it. -/
theorem P3b (A P : Matrix (Fin 3) (Fin 3) ℝ) (hP : P.det ≠ 0) :
    (P⁻¹ * A * P).det = A.det := by
  sorry

/-- **Problem 4 (a).** A 2×2 matrix with `A² = 0` has determinant 0. -/
theorem P4a (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A ^ 2 = 0) : A.det = 0 := by
  sorry

/-- **Problem 4 (b).** A 2×2 matrix with `A² = 0` has trace 0. Use (a) and
`cayley_hamilton_two`. A case split on a product being zero is a library
lemma; find it. -/
theorem P4b (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A ^ 2 = 0) : A.trace = 0 := by
  sorry

/-- **Problem 5 (optional).** If `A² = 0` then `I + A` is invertible, with
inverse `I − A`. The expansion `(I + A)(I − A) = I − A²` is an identity in a
noncommutative ring; `ring` will not prove it, and the tactic that does is
called `noncomm_ring`. -/
theorem P5 (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A ^ 2 = 0) : (1 + A) * (1 - A) = 1 := by
  sorry

/-! ## Part II — Conjectures

Each statement below is a claim about 2×2 real matrices. Some are true, some
are false, and some are false in Lean for a reason that has nothing to do
with linear algebra. For each:

1. Decide, before touching the keyboard.
2. If you think it is true, prove it (the `∀` is part of the statement, so
   the proof begins with `intro`).
3. If you think it is false, change the statement to its negation —
   `theorem conjN : ¬ ∀ A B : ..., ... := by` — and refute it with a
   specific matrix.

Two techniques for refutations. A concrete matrix identity such as
`!![0, 1; 0, 0] ^ 2 = 0` is proved entrywise:

    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]

and the `(i, j)` entry of a matrix equation `h : M = N` is the real-number
equation `congrFun (congrFun h i) j`, which `norm_num at` can then
contradict. `plausible` does not work on statements about matrices.

Running `exact?` on a false statement fails, as it should; running it on a
true one may succeed and tell you what the library calls the fact. -/

/-- **Conjecture 1.** -/
theorem conj1 : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, (A * B).det = (B * A).det := by
  sorry

/-- **Conjecture 2.** -/
theorem conj2 : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, (A + B).det = A.det + B.det := by
  sorry

/-- **Conjecture 3.** -/
theorem conj3 : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, (A * B).trace = A.trace * B.trace := by
  sorry

/-- **Conjecture 4.** -/
theorem conj4 : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, (A * B)ᵀ = Aᵀ * Bᵀ := by
  sorry

/-- **Conjecture 5.** -/
theorem conj5 : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A * A⁻¹ = 1 := by
  sorry

/-- **Conjecture 6.** -/
theorem conj6 : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.det ≠ 0 → A * A⁻¹ = 1 := by
  sorry

/-- **Conjecture 7.** -/
theorem conj7 : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A⁻¹⁻¹ = A := by
  sorry

/-- **Conjecture 8.** -/
theorem conj8 : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A ^ 2 = 1 → A = 1 ∨ A = -1 := by
  sorry

/-- **Conjecture 9.** -/
theorem conj9 : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B = 0 → A = 0 ∨ B = 0 := by
  sorry

/-- **Conjecture 10.** -/
theorem conj10 : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, 0 ≤ (Aᵀ * A).trace := by
  sorry

/-- **Conjecture 11.** -/
theorem conj11 : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B = 1 → B * A = 1 := by
  sorry

/-- **Conjecture 12.** -/
theorem conj12 : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A ^ 2 = 0 → A = 0 := by
  sorry
