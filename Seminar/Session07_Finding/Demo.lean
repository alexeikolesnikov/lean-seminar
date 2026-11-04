/-
  Session 07 — Finding lemmas
  Math Dept Lean seminar — demo file

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Open in the web editor from the link in README.md, or run
        lake env lean Seminar/Session07_Finding/Demo.lean
  from the seminar project root. leancheck.sh: use --allow-sorry.
  CI: allow-sorry (1)

  Tactics introduced: exact?, apply?, simp?, hint, rw?; the commands #check,
  #eval, #loogle, #leansearch; Mathlib's naming convention.
  Assumed from earlier: intro, exact, apply, obtain (session 3); rw, calc,
  ring, norm_num, simp (session 4); decide (session 5).

  This file imports all of Mathlib. `exact?` searches only what is imported,
  and this session is about searching. The `exact?` calls left in the file
  run each time it is opened; each takes a few seconds.
-/
import Mathlib

-- Everything about matrices lives in the `Matrix` namespace: the notation
-- `ᵀ`, and the lemma names, which become `det_mul` rather than
-- `Matrix.det_mul` once the namespace is open.
open Matrix

/-! # Finding lemmas

## 0. Where session 6 left off

Mathlib has about 250,000 named theorems. Almost everything a first course in
linear algebra proves is among them. The work of using the library is not
proving those facts again; it is finding the one you need and confirming that
it says what you think it says. The first half of this file is about finding;
the last section is about confirming.

The mathematics is matrices over `ℝ`, which is the linear algebra everyone
here has taught (or was taught). The tactics are from sessions 3 to 5. What
is new is the set of tools for asking the library a question. -/

/-! ## 1. Matrices

`Matrix (Fin 3) (Fin 3) ℝ` is the type of 3×3 real matrices: functions from
two indices to `ℝ`, where the index set `Fin 3` is `{0, 1, 2}`. `A i j` is an
entry. `!![a, b; c, d]` writes a 2×2 matrix out. -/

#check (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ)

-- Over `ℤ` or `ℚ`, products, transposes, determinants and traces compute.
#eval (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ) * !![0, 1; 1, 0]
#eval (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ)ᵀ
#eval (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ).det
#eval (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ).trace
#eval (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ) 0 1   -- row 0, column 1
#eval (1 : Matrix (Fin 2) (Fin 2) ℤ)

-- Rehearsed failure 1. The inverse does not compute:
--   failed to compile definition, consider marking it as 'noncomputable'
--   because it depends on 'inv', which is 'noncomputable'
-- `A⁻¹` is defined for every square matrix (§7 says how), but the definition
-- goes through `Ring.inverse`, which is not an algorithm. Facts about `A⁻¹`
-- are proved, not evaluated.
-- #eval (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹

-- Rehearsed failure 2. A determinant needs a commutative ring:
--   failed to synthesize instance of type class
--     CommRing ℕ
-- The determinant has signs in it, and `ℕ` has no negatives. The *statement*
-- does not elaborate; there is nothing to prove.
-- example (A : Matrix (Fin 2) (Fin 2) ℕ) : A.det = A.det := rfl

/-! ## 2. `exact?`

Put the goal in front of Lean and ask for a single library lemma that closes
it. The answer appears in the Infoview as `Try this: exact ...`; clicking it
replaces the `exact?`. -/

-- The determinant of a product.
example (A B : Matrix (Fin 3) (Fin 3) ℝ) : (A * B).det = A.det * B.det := by
  exact?
-- Try this: exact det_mul A B

-- Read what came back, with `#check`. The `@` shows every argument,
-- including the ones in braces and brackets that Lean normally fills in.
#check @Matrix.det_mul
-- ∀ {n : Type u_2} [DecidableEq n] [Fintype n] {R : Type u_1} [CommRing R]
--   (M N : Matrix n n R), (M * N).det = M.det * N.det
--
-- Three things to read off:
--   * `n` is any finite index type, not only `Fin 3`; `R` is any commutative
--     ring, not only `ℝ`. The lemma is more general than the goal.
--   * `[CommRing R]` is the hypothesis that made §1's `ℕ` example fail.
--   * The name. `det_mul` says "det of a mul" — a description of the
--     left-hand side, read from the outside in.

-- The transpose of a product. Before running `exact?`: what will the lemma
-- be called?
example (A B : Matrix (Fin 3) (Fin 3) ℝ) : (A * B)ᵀ = Bᵀ * Aᵀ := by
  exact?
-- Try this: exact transpose_mul A B

/-! ## 3. Names are descriptions

Mathlib's naming convention is regular enough to guess. A name reads the
statement right to left, in lower-case words joined by underscores:

    (A * B).det = ...        det_mul
    (A * B)ᵀ = ...           transpose_mul
    Aᵀ.det = ...             det_transpose
    (A + B).trace = ...      trace_add
    (c • A).det = ...        det_smul          (• is "smul", scalar multiple)
    det 1 = ...              det_one
    (A * B).trace = (B * A).trace     trace_mul_comm

Other pieces that recur: `_iff_` for `↔`, `X_of_Y` for "X follows from Y"
(read right to left across the `_of_`), `le`/`lt` for `≤`/`<`, `ne` for `≠`,
`inv` for `⁻¹`, `pow` for `^`, `sub`/`neg`, `zero`/`one`.

Guessing a name and typing it is often faster than searching. In VS Code,
typing `Matrix.det_` and pausing shows every lemma whose name starts that
way. The three below were written from the table, not found. -/

example (A : Matrix (Fin 3) (Fin 3) ℝ) : Aᵀ.det = A.det :=
  det_transpose A

example (A B : Matrix (Fin 3) (Fin 3) ℝ) : (A * B).trace = (B * A).trace :=
  trace_mul_comm A B

example : (1 : Matrix (Fin 3) (Fin 3) ℝ).det = 1 :=
  det_one

/-! ## 4. When `exact?` fails

`exact?` is a fairly narrow match against the library up. If the library states
a fact in a different form, it may find nothing. -/

-- Rehearsed failure 3. det (cA) = c³ det A for a 3×3 matrix:
--   `exact?` could not close the goal. Try `apply?` to see partial suggestions.
-- example (A : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) : (c • A).det = c ^ 3 * A.det := by
--   exact?

-- The name is guessable; check what the library actually says.
#check @Matrix.det_smul
-- (c • A).det = c ^ Fintype.card n * A.det
--
-- The exponent is `Fintype.card n`, the size of the index set, which for
-- `Fin 3` is `3` — but not *syntactically* `3`, so `exact?` does not match.
-- Rewrite with the lemma and then with `Fintype.card_fin : card (Fin n) = n`.
example (A : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) : (c • A).det = c ^ 3 * A.det := by
  rw [det_smul, Fintype.card_fin]

-- The general principle: state things the way the library states them, or be
-- ready to translate. `apply?` is `exact?`'s relaxed version — it looks for a
-- lemma whose conclusion matches and reports what would remain to prove. On
-- this goal it returns thirty suggestions, none useful; it works best when
-- the goal has a distinctive shape.

-- A related point about reading. Many people's first guess at this fact is
-- `(c • A).det = c * A.det`. `exact?` fails on it too, for a different
-- reason: it is false. Here is the instance with `A = 1`, `c = 2`, where
-- the right-hand side would be `2`.
example : ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 4 := by
  rw [det_smul, det_one, Fintype.card_fin]
  norm_num

/-! ## 5. `simp?`, `hint`, `rw?`

For a goal that needs several lemmas, three tactics report what they did or
what they would do. -/

-- `simp?` runs `simp` and prints the lemmas it used, so that the proof can
-- be replaced by a `simp only [...]` that names them.
example (A : Matrix (Fin 3) (Fin 3) ℝ) : (Aᵀ * A).det = A.det ^ 2 := by
  simp? [det_mul]
  -- Try this: simp only [det_mul, det_transpose]
  -- Remaining goal: A.det * A.det = A.det ^ 2
  ring

-- The same proof with the citation in place of the search:
example (A : Matrix (Fin 3) (Fin 3) ℝ) : (Aᵀ * A).det = A.det ^ 2 := by
  rw [det_mul, det_transpose]
  ring

-- `hint` tries a list of standard finishing tactics and reports which ones
-- make progress. Here it finds that `aesop`, `norm_num` and
-- `simp_all only [det_mul, det_transpose]` each reduce the goal to
-- `A.det * A.det = A.det ^ 2`, and that none closes it.
theorem hint_example (A : Matrix (Fin 3) (Fin 3) ℝ) : (Aᵀ * A).det = A.det ^ 2 := by
  hint
  -- Try these: aesop / norm_num / simp_all only [det_mul, det_transpose]
  -- each with remaining subgoal  A.det * A.det = A.det ^ 2

-- `hint` is a report, not a proof. When nothing it tries closes the goal, it
-- admits the goal so that the file goes on compiling, and the declaration
-- depends on `sorryAx` — the same axiom `#print axioms` caught in session 1.
#print axioms hint_example
-- 'hint_example' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

-- `rw?` lists every rewrite the library could perform on the goal. Its output
-- is long (on this goal, over twenty suggestions, most beside the point) and
-- the useful ones are near the top. It is for when you know a rewrite exists
-- and cannot name it; `exact?` and `simp?` are the everyday tools.
-- example (A : Matrix (Fin 3) (Fin 3) ℝ) : (Aᵀ * A).det = A.det ^ 2 := by
--   rw?
--   -- first suggestion: rw [det_mul]   -- Aᵀ.det * A.det = A.det ^ 2

/-! ## 6. Outside the file

Two search services can be queried from the editor; both need network access
and are therefore commented out here. The output quoted was produced when
this file was built.

**Loogle** searches by shape: list the constants that must appear.

    #loogle Matrix.det, Matrix.transpose
    -- Matrix.det_transpose, Matrix.det_eq_zero_of_not_linearIndependent_cols,
    -- Matrix.cramer_transpose_apply, ... (six results)

    #loogle Matrix.det (_ • _)
    -- Matrix.det_smul and its relatives

**LeanSearch** takes a sentence; it must end in `.` or `?`.

    #leansearch "the determinant of a product of matrices is the product of the determinants."
    -- Matrix.det_mul is the second result; the first is LinearMap.det_prodMap.

    #leansearch "rank nullity theorem."
    -- LinearMap.finrank_range_add_finrank_ker, first result.

Both have web pages, <https://loogle.lean-lang.org> and
<https://leansearch.net>, and the API documentation at
<https://leanprover-community.github.io/mathlib4_docs/> can be searched by
name. The file `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` is where
`det_mul` lives; the module docstring at the top of each file says what the
file covers, and reading the neighbourhood of a lemma is often the fastest
way to find the next one.

One more: the `#new members` and `#Is there code for X?` channels on
<https://leanprover.zulipchat.com>. Asking whether a lemma exists is what
the second channel is for. -/

/-! ## 7. Reading what comes back

A lemma that closes the goal has proved *the goal*. Whether the goal was the
theorem you meant is a separate question, and the hypotheses of the lemma are
the place to look. -/

-- (a) Hypotheses are mathematics.
#check @Matrix.det_zero
-- det 0 = 0, under `[Nonempty n]`. Why the hypothesis? Because:
#check @Matrix.det_fin_zero
-- the 0×0 matrix has determinant 1 (the empty product, summed over the one
-- permutation of the empty set). Statements about `Matrix (Fin n) (Fin n) ℝ`
-- include `n = 0`, and `exact?` will cheerfully prove things there that are
-- not theorems of linear algebra:
example (A B : Matrix (Fin 0) (Fin 0) ℝ) : A = B := by
  exact?
-- Try this: exact ext_of_single_vecMul (congrFun rfl)
-- Any two 0×0 matrices are equal. True; and if the `0` had been a variable
-- `n` left over from an earlier edit, the goal "all matrices are equal" would
-- have failed — the check is that the *statement* says what you meant.

-- (b) Totality. `A⁻¹` is defined for every square matrix. For a singular
-- matrix it is `0`, by the definition:
#check @Matrix.inv_def
-- A⁻¹ = Ring.inverse A.det • A.adjugate     and Ring.inverse 0 = 0.
-- So the lemmas that *are* theorems of linear algebra carry a hypothesis,
#check @Matrix.mul_nonsing_inv
-- IsUnit A.det → A * A⁻¹ = 1
-- and the ones that hold for the total function do not:
#check @Matrix.mul_inv_rev
-- (A * B)⁻¹ = B⁻¹ * A⁻¹       (no hypothesis)
-- A lemma about `⁻¹` with no invertibility hypothesis is a statement about
-- Mathlib's extension of the inverse, not about the inverse.

-- (c) A statement that is more general than expected. "AB = I implies BA = I
-- for square matrices" is in the library as:
#check @Matrix.mul_eq_one_comm_of_card_eq
-- Fintype.card m = Fintype.card n → (A * B = 1 ↔ B * A = 1)
-- for A : Matrix m n R and B : Matrix n m R. Rectangular matrices, with the
-- hypothesis that the two sizes agree — which is exactly the condition under
-- which the statement is true (for a 1×2 `A` and 2×1 `B` it fails).
-- The square case is the instance m = n, where the hypothesis is `rfl`.
example (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : A * B = 1) : B * A = 1 :=
  (mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) ℝ rfl).mp h

/-! ## 8. Exercises

`Exercises.lean` has two parts. Part I is five problems stated as a linear
algebra course would state them, with no lemma names supplied: decide how
the proof goes, then find what it needs. Part II is twelve conjectures about
2×2 matrices: decide whether each is true, then prove or refute it. In the
meeting, Problems 1–3 and as many conjectures as time allows. -/
