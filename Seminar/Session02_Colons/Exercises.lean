/-
  Session 02 — One colon, four tactics  ·  EXERCISES
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: exact, apply, intro, rfl, have, show
  Assumed from earlier: #check, #eval, plausible  (Session 01)

CI: allow-sorry (17)

  Every `sorry` below is a hole to fill. Work in `MyWork/` — copy this file
  there first, so that `git pull` does not conflict with your work.

  Do them in order. A, B and C take about ten minutes each. D is optional and
  is the only part that asks you to find a lemma yourself.
-/
import Mathlib

/-! ## A. Where the colon sits

Two statements can differ only in the position of a colon and mean different
mathematics. -/

/-- **A1.** For naturals `n` and `m` with `m ≤ n`, subtracting inside `ℕ` and
then moving to `ℤ` agrees with moving to `ℤ` and subtracting there.

Before proving it: why must the hypothesis `m ≤ n` be there? -/
theorem cast_sub_of_le (n m : ℕ) (h : m ≤ n) :
    ((n - m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) := by
  -- hint: one Mathlib lemma, applied to `h`. Its name begins `Nat.cast_`.
  sorry

/-  **A1, continued — no proof required.**

    The line below is the same statement with the hypothesis removed. Remove
    the two dashes, read what `plausible` reports, and answer for yourself:

      - which side is `0`, and why?
      - which side is negative, and why?
      - where did the colon move?

    Put the dashes back afterwards. -/

-- example (n m : ℕ) : ((n - m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) := by plausible

/-- **A2.** The same effect for division. Predict both answers before running
anything. -/
example : ((7 / 2 : ℕ) : ℚ) = 3 := by
  -- hint: `norm_num` closes both A2 goals.
  sorry

example : (7 : ℚ) / (2 : ℚ) = 3.5 := by
  sorry

/-! ## B. The four tactics as operations on colons

`exact e` — the goal is `⊢ T`; supply an `e : T`.
`apply f` — `f : A → B` and the goal is `⊢ B`; what remains is `⊢ A`.
`intro h` — move a binder out of the goal into the context as a new line.
`rfl`     — `rfl : a = a`, which typechecks at `a = b` when Lean already sees
            `a` and `b` as the same term.

A *binder* is a place where a name is introduced together with its type:
`(n : ℕ)` in a statement, `∀ n : ℕ`, `fun n : ℕ ↦ …`.

Watch the Infoview on every line. The goal window is the point of part B. -/

/-- **B1.** The goal is in the context. -/
theorem b1 (P : Prop) (hP : P) : P := by
  -- hint: one tactic, one word after it.
  sorry

/-- **B2.** An implication is a function. -/
theorem b2 (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  sorry

/-- **B2'.** The same statement again. Prove it a second way, using `apply`
first, and note what the goal becomes. -/
theorem b2' (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  sorry

/-- **B3.** The goal is itself an implication. -/
theorem b3 (P Q : Prop) : P → Q → P := by
  -- hint: `intro` takes as many names as there are arrows.
  sorry

/-- **B4.** Composition. -/
theorem b4 (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry

/-- **B5.** A `∀` is eliminated as an `→` is. -/
theorem b5 (f : ℕ → ℕ) (hf : ∀ n, f n = n) : f 3 = 3 := by
  -- hint: `hf` is a function; supply it an argument.
  sorry

/-- **B6.** The same, with the equality needed in the other direction. -/
theorem b6 (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : g 2 = f 2 := by
  -- hint: if `e : a = b` then `e.symm : b = a`.
  sorry

/-! ## C. `rfl`

`rfl` holds when both sides reduce to the same term with no theorem invoked.
Exactly two of C1–C5 are closed by `rfl`. Determine which by trying, and read
the error on those that are not. -/

/-- **C1.** -/
theorem c1 : 2 + 2 = 4 := by
  sorry

/-- **C2.** -/
theorem c2 (n : ℕ) : n + 0 = n := by
  sorry

/-- **C3.** If `rfl` fails here, that is the asymmetry from the Natural Number
Game rather than a mistake on your part. -/
theorem c3 (n : ℕ) : 0 + n = n := by
  -- hint: there is a `Nat.` lemma with nearly this name.
  sorry

/-- **C4.** -/
theorem c4 (n : ℕ) : n * 1 = n := by
  sorry

/-- **C5.** -/
theorem c5 (n : ℕ) : 1 * n = n := by
  sorry

/-! ## D. Stretch — optional

No new tactics. D1 uses one lemma you have not seen; finding it is the point. -/

/-- **D1.** Division truncates in `ℕ` as subtraction does, so a similar guard
is needed. Two hypotheses are supplied; work out why each is necessary before
proving anything.

`exact?` on the goal will find the lemma. -/
theorem cast_div_of_dvd (a b : ℕ) (hdvd : b ∣ a) (hb : (b : ℚ) ≠ 0) :
    ((a / b : ℕ) : ℚ) = (a : ℚ) / (b : ℚ) := by
  sorry

/-- **D2.** A `have` names an intermediate statement; what follows its colon is
again a type. Fill in the two `have`s and finish the `calc`. -/
theorem d2 (x y : ℕ) (hx : x = 2) (hy : y = 3) : x + y = 5 := by
  -- hint: `rw [hx]` rewrites `x` into `2` in the goal.
  sorry
