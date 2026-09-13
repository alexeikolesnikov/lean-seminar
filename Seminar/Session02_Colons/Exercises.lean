/-
  Session 02 — One colon, four tactics  ·  EXERCISES
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics used: exact, apply, intro, rfl, have, show, rw, ring, norm_num
  Assumed from earlier: #check, #eval, plausible  (Session 01)

CI: allow-sorry (21)

  Work in `MyWork/` — copy this file there first, so that `git pull` does not
  conflict with your work.

  Parts A–E are the session. F needs no proof. G is optional.

  Each part in the solutions file ends with a note headed "What this was for".
  Do the part first. The note is worth more after you have been surprised by
  something than before.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Ring.RingNF
import Plausible.Tactic

/-! ## A. The type is part of the statement

A1 and A2 are the same sentence in English. Read both statements before proving
either. -/

/-- **A1.** Subtract, then add back. -/
theorem a1 (n m : ℤ) : (n - m) + m = n := by
  -- hint: `ring`.
  sorry

/-- **A2.** The same sentence over `ℕ`. Why is there a hypothesis here and not
in A1? -/
theorem a2 (n m : ℕ) (h : m ≤ n) : (n - m) + m = n := by
  -- hint: one `Nat.` lemma, applied to `h`.
  sorry

/-  **A3 — no proof required.** Remove the dashes below and read what
    `plausible` reports. Then say, in a comment, which of A1 and A2 it is the
    counterexample to, and why it is not a counterexample to the other. -/

-- example (n m : ℕ) : (n - m) + m = n := by plausible

/-! **A4.** Two definitions of "two", at different types.

Before proving anything: run both `#check` lines and read the output carefully.
It is not quite the statement written on the page. Then try the other order, and
predict whether `rfl` can possibly close this. -/

def rtwo : ℝ := 2
def ntwo : ℕ := 2

#check (rtwo = ntwo)          -- ?
#check (ntwo = rtwo)          -- ?

theorem a4 : rtwo = ntwo := by
  sorry

/-! ## B. What `rfl` can and cannot do

Try `rfl` on every item in this part before reaching for anything else. It will
surprise you in both directions. Exactly one of B3, B4, B5 is closed by `rfl`;
find out which by trying, and read the error on the others. -/

/-- **B1.** -/
theorem b1 : (fun x => x + 1) 3 = 4 := by
  sorry

/-- **B2.** -/
theorem b2 (p : Prop) : (¬p) = (p → False) := by
  sorry

/-- **B3.** -/
theorem b3 (n : ℕ) : n + 0 = n := by
  sorry

/-- **B4.** -/
theorem b4 (n : ℕ) : 0 + n = n := by
  -- hint: there is a `Nat.` lemma with nearly this name.
  sorry

/-- **B5.** Predict this one before you try it. -/
theorem b5 (n : ℕ) : n * 1 = n := by
  sorry

/-! ## C. A proof of `∀` is a function

Every item in this part can be written with `fun`, and that is the point. Write
term-mode proofs — `:= fun n => …` — rather than tactic blocks. -/

/-- **C1.** -/
theorem c1 : ∀ n : ℕ, 0 ≤ n := by
  -- hint: `fun n => Nat.zero_le n`.
  sorry

/-- **C2.** Try to write this one *without* mentioning the bound variable in
the body. -/
theorem addZero : ∀ n : ℕ, n + 0 = n := by
  sorry

/-- **C3.** Use `addZero`. You do not need to prove anything again. -/
theorem c3 : 5 + 0 = 5 := by
  -- hint: `addZero` is a function. Feed it something.
  sorry

/-- **C4.** -/
theorem comm2 : ∀ n m : ℕ, n + m = m + n := by
  sorry

/-- **C5.** Use `comm2`. Afterwards, run the `#check` below and read it. -/
theorem c5 : 2 + 3 = 3 + 2 := by
  sorry

#check comm2 2                -- ?

/-- **C6.** `P` holds of every natural. Show it holds of every `g n`. -/
theorem c6 (P : ℕ → Prop) (h : ∀ n, P n) (g : ℕ → ℕ) : ∀ n, P (g n) := by
  sorry

/-- **C7.** Note the underscore: the statement never uses what is bound. -/
theorem c7 : ∀ _ : ℕ, 2 + 2 = 4 := by
  sorry

/-! ## D. Applying a `∀` at a compound argument -/

/-- **D1.** Prove this in term mode, without `rw`. `hf` can be instantiated at
any term of type `ℕ`; you will need two instances, and one of them is not a
numeral. -/
theorem d1 (f : ℕ → ℕ) (hf : ∀ n, f n = n) : f (f 3) = 3 := by
  -- hint: if `e₁ : a = b` and `e₂ : b = c` then `e₁.trans e₂ : a = c`.
  sorry

/-- **D1'.** Now the same statement with `rw`, in one line. Compare the two. -/
theorem d1' (f : ℕ → ℕ) (hf : ∀ n, f n = n) : f (f 3) = 3 := by
  sorry

/-! ## E. Dot notation -/

/-- **E1.** -/
theorem e1 (a b : ℕ) (h : a = b) : b = a := by
  -- hint: `h.symm`.
  sorry

/-- **E2.** The same shape, on a different type. The suffix is not the same. -/
theorem e2 (p q : Prop) (h : p ↔ q) (hp : p) : q := by
  sorry

/-! ## F. Observation — no proof required -/

/-  **F1.** Uncomment these two lines and read what happens. You should get a
    warning, not an error.

        theorem anything : False := sorry
        #print axioms anything

    Then answer, in a comment: what does this tell you about every other
    exercise in this file at the moment you first opened it? -/

/-! ## G. Stretch — optional -/

/-- **G1.** Division truncates in `ℕ` as subtraction does, so a similar guard is
needed. Two hypotheses are supplied; work out why each is necessary before
proving anything. `exact?` will find the lemma. -/
theorem cast_div_of_dvd (a b : ℕ) (hdvd : b ∣ a) (hb : (b : ℚ) ≠ 0) :
    ((a / b : ℕ) : ℚ) = (a : ℚ) / (b : ℚ) := by
  sorry

/-- **G2.** Fill in the two `have`s and finish the `calc`. Then add a `show`
line stating the goal you believe you are working on, and check that Lean
accepts it. -/
theorem g2 (x y : ℕ) (hx : x = 2) (hy : y = 3) : x + y = 5 := by
  -- hint: `rw [hx]` rewrites `x` into `2` in the goal.
  sorry
