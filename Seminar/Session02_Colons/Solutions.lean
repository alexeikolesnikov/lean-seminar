/-
  Session 02 — One colon, four tactics  ·  SOLUTIONS
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: exact, apply, intro, rfl, have, show
  Assumed from earlier: #check, #eval, plausible  (Session 01)

  This file must compile with no `sorry`. If it does not, the exercise file is
  wrong too — they share their statements.
-/
import Mathlib

/-! ## A. Where the colon sits

Two statements can differ only in the position of a colon and mean different
mathematics. -/

/-- **A1.** For naturals `n` and `m` with `m ≤ n`, subtracting inside `ℕ` and
then moving to `ℤ` agrees with moving to `ℤ` and subtracting there.

The hypothesis `m ≤ n` is required; without it the statement is false. See the
counterexample below. -/
theorem cast_sub_of_le (n m : ℕ) (h : m ≤ n) :
    ((n - m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) :=
  Nat.cast_sub h

/-  A1, continued. The unguarded version is false. Uncommented, `plausible`
    reports:

        Found a counter-example!
        n := 0
        m := 4
        issue: 0 = -4 does not hold

    On the left, `0 - 4` is computed in `ℕ`, where it truncates to `0`, and
    then becomes the integer `0`. On the right, `0` and `4` become integers
    first and the subtraction happens in `ℤ`, giving `-4`. -/

-- example (n m : ℕ) : ((n - m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) := by plausible

/-- **A2.** The same effect for division. -/
example : ((7 / 2 : ℕ) : ℚ) = 3 := by norm_num

example : (7 : ℚ) / (2 : ℚ) = 3.5 := by norm_num

/-! ## B. The four tactics as operations on colons

`exact e` — the goal is `⊢ T`; supply an `e : T`.
`apply f` — `f : A → B` and the goal is `⊢ B`; what remains is `⊢ A`.
`intro h` — move a binder out of the goal into the context as a new line.
`rfl`     — `rfl : a = a`, which typechecks at `a = b` when Lean already sees
            `a` and `b` as the same term.

A *binder* is a place where a name is introduced together with its type:
`(n : ℕ)` in a statement, `∀ n : ℕ`, `fun n : ℕ ↦ …`. -/

/-- **B1.** The goal is in the context. -/
theorem b1 (P : Prop) (hP : P) : P := hP

/-- **B2.** An implication is a function, and is used by applying it. -/
theorem b2 (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := hPQ hP

/-- **B2'.** The same proof in tactic form, to see the goal change. -/
theorem b2' (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  -- goal is now `⊢ P`
  exact hP

/-- **B3.** A goal that is itself an implication. -/
theorem b3 (P Q : Prop) : P → Q → P := by
  intro hP _hQ
  exact hP

/-- **B4.** Composition. -/
theorem b4 (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR          -- goal `⊢ R` becomes `⊢ Q`
  apply hPQ          -- goal `⊢ Q` becomes `⊢ P`
  exact hP

/-- **B5.** A `∀` is eliminated as an `→` is. -/
theorem b5 (f : ℕ → ℕ) (hf : ∀ n, f n = n) : f 3 = 3 := hf 3

/-- **B6.** The same, with the equality used in the other direction. -/
theorem b6 (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : g 2 = f 2 := (h 2).symm

/-! ## C. `rfl`

`rfl` holds when both sides reduce to the same term with no theorem invoked.
That condition is narrower than "true" and is not symmetric. -/

/-- **C1.** Both sides compute. -/
theorem c1 : 2 + 2 = 4 := rfl

/-- **C2.** `rfl` applies: addition on `ℕ` recurses on its second argument, so
`n + 0` reduces to `n` directly. -/
theorem c2 (n : ℕ) : n + 0 = n := rfl

/-- **C3.** `rfl` does not apply here. `0 + n` cannot reduce until something is
known about `n`, so a theorem proved by induction is required. This is the
asymmetry from the Natural Number Game. -/
theorem c3 (n : ℕ) : 0 + n = n := Nat.zero_add n

/-  C3, continued. Uncommented, the error is:

        Type mismatch
          rfl
        has type
          ?m.9 = ?m.9
        but is expected to have type
          0 + n = n

    Lean needed `rfl`'s type to be the goal, and it is not. -/

-- example (n : ℕ) : 0 + n = n := rfl

/-- **C4.** Multiplication also recurses on the second argument. -/
theorem c4 (n : ℕ) : n * 1 = n := Nat.mul_one n

/-- **C5.** And so this side requires a theorem. -/
theorem c5 (n : ℕ) : 1 * n = n := Nat.one_mul n

/-! ## D. Stretch

No new tactics. D1 requires finding one Mathlib lemma. -/

/-- **D1.** Division truncates in `ℕ` as subtraction does, so a similar guard
is needed: when `b` divides `a` and `b ≠ 0`, casting the quotient agrees with
dividing the casts.

Found with `exact?`. The lemma is `Nat.cast_div`. -/
theorem cast_div_of_dvd (a b : ℕ) (hdvd : b ∣ a) (hb : (b : ℚ) ≠ 0) :
    ((a / b : ℕ) : ℚ) = (a : ℚ) / (b : ℚ) :=
  Nat.cast_div hdvd hb

/-- **D2.** A `have` names an intermediate statement; what follows its colon is
again a type. -/
theorem d2 (x y : ℕ) (hx : x = 2) (hy : y = 3) : x + y = 5 := by
  have hx' : x + y = 2 + y := by rw [hx]
  have hy' : 2 + y = 2 + 3 := by rw [hy]
  calc x + y = 2 + y := hx'
    _ = 2 + 3 := hy'
    _ = 5 := rfl
