/-
  Session 03 — Exercises
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics needed: intro, exact, obtain, rcases, use, left, right, constructor,
                  exfalso, subst
  Assumed from earlier: #check, #eval, plausible  (Session 01); the colon and
                        propositions as types     (Session 02)

  Copy this file into MyWork/ before editing it, so that `git pull` does not
  conflict with your work.

  Replace each `sorry` with a proof. Parts A–F are the session; part G is
  optional. `Solutions.lean` carries the same statements with proofs and a note
  after each part headed "What this was for" — do the part first.
-/
import Mathlib

/-! # Parity, and the start of a longer proof

The thread running through sessions 3 to 5 ends at

    for all natural numbers p and q with q ≠ 0,  p² ≠ 2q²

which is the arithmetic content of "√2 is irrational". This week does the
parity rungs. The arithmetic is supplied; the logic is yours.

## Definitions

We define parity here rather than using Mathlib's `Even` and `Odd`, so that
every step is visible. Both definitions are existential statements. -/

/-- `n` is even when it is twice something. -/
def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k

/-- `n` is odd when it is one more than twice something. -/
def IsOdd (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

/-! ## Given: the arithmetic

Proved with `ring` and `omega` (session 4) and with a Mathlib lemma proved by
induction (session 5). Use them as results quoted from a previous lecture; you
are not expected to prove them this week. -/

/-- Twice `k` plus two is twice `k + 1`. -/
theorem two_mul_add_two (k : ℕ) : 2 * k + 2 = 2 * (k + 1) := by ring

/-- The square of an even number, in the form the definition wants. -/
theorem sq_two_mul (k : ℕ) : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring

/-- The square of an odd number, in the form the definition wants. -/
theorem sq_two_mul_add_one (k : ℕ) :
    (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring

/-- No number is both twice something and one more than twice something. -/
theorem two_mul_ne_two_mul_add_one (a b : ℕ) : 2 * a ≠ 2 * b + 1 := by omega

/-- Every natural number is even or odd. -/
theorem isEven_or_isOdd (n : ℕ) : IsEven n ∨ IsOdd n := by
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, hk⟩ := h
    exact Or.inl ⟨k, by omega⟩
  · obtain ⟨k, hk⟩ := h
    exact Or.inr ⟨k, by omega⟩

/-! ## Part A — Which statement is it?

No Lean to write here. For each English sentence, one of the three statements
says it. Decide which, and for each of the other two, say what it does say and
whether it is true.

**A1.** "Every even number has an even square."

    (i)   ∀ n, IsEven n → IsEven (n ^ 2)
    (ii)  ∀ n, IsEven (n ^ 2) → IsEven n
    (iii) ∀ n, IsEven n ∧ IsEven (n ^ 2)

**A2.** "Some even number is bigger than 100."

    (i)   ∀ n, IsEven n → 100 < n
    (ii)  ∃ n, IsEven n ∧ 100 < n
    (iii) ∃ n, IsEven n → 100 < n

**A3.** "If n² is even then n is even."

    (i)   ∀ n, IsEven (n ^ 2) → IsEven n
    (ii)  ∀ n, ¬IsEven (n ^ 2) → ¬IsEven n
    (iii) ∀ n, IsOdd (n ^ 2) → IsOdd n

All nine typecheck. Three of them are false. -/

/-! ## Part B — Existential statements

`use` supplies a witness; `obtain` takes one apart. -/

/-- **B1.** 10 is even. -/
theorem ten_isEven : IsEven 10 := by
  -- hint: `use` the witness. The equation that remains is a computation.
  sorry

/-- **B2.** 7 is odd. -/
theorem seven_isOdd : IsOdd 7 := by
  sorry

/-- **B3.** Two more than an even number is even. -/
theorem isEven_add_two (n : ℕ) (h : IsEven n) : IsEven (n + 2) := by
  -- hint: `obtain ⟨k, hk⟩ := h` names the witness, `subst hk` replaces `n` by
  -- `2 * k` everywhere, and `two_mul_add_two` finishes.
  sorry

/-! ## Part C — Conjunction and disjunction -/

/-- **C1.** An even number is even or odd. -/
theorem isEven_or (n : ℕ) (h : IsEven n) : IsEven n ∨ IsOdd n := by
  -- hint: you must say which side you are proving.
  sorry

/-- **C2.** If `n` is even and `m` is odd, then `m` is odd and `n` is even. -/
theorem swap_parity (n m : ℕ) (h : IsEven n ∧ IsOdd m) : IsOdd m ∧ IsEven n := by
  -- hint: take the hypothesis apart, then build the goal.
  sorry

/-- **C3.** If `n` is even or `n` is even, then `n` is even. -/
theorem isEven_of_or (n : ℕ) (h : IsEven n ∨ IsEven n) : IsEven n := by
  -- hint: `rcases h with h | h`. Both cases look the same; handle both anyway.
  sorry

/-! ## Part D — Negation -/

/-- **D1.** No number is both even and odd. -/
theorem not_isEven_and_isOdd (n : ℕ) : ¬(IsEven n ∧ IsOdd n) := by
  -- hint: `¬P` is `P → False`, so start with `intro`. After taking both
  -- witnesses apart you have `hk : n = 2 * k` and `hj : n = 2 * j + 1`;
  -- `hk.symm.trans hj` is the equation `2 * k = 2 * j + 1`, and
  -- `two_mul_ne_two_mul_add_one` refuses it.
  sorry

/-- **D2.** An odd number is not even. -/
theorem not_isEven_of_isOdd (n : ℕ) (h : IsOdd n) : ¬IsEven n := by
  -- hint: D1, with the two halves assembled as `⟨_, _⟩`.
  sorry

/-! ## Part E — Squares -/

/-- **E1.** The square of an even number is even. -/
theorem isEven_sq_of_isEven (n : ℕ) (h : IsEven n) : IsEven (n ^ 2) := by
  -- hint: the same four lines as B3. The mathematics is the witness you pick.
  sorry

/-- **E2.** The square of an odd number is odd. -/
theorem isOdd_sq_of_isOdd (n : ℕ) (h : IsOdd n) : IsOdd (n ^ 2) := by
  sorry

/-! ## Part F — The rung the argument uses

The statement the irrationality argument needs. Its proof is not a
computation: it goes through the other direction and a contradiction. -/

/-- **F.** If `n²` is even then `n` is even. -/
theorem isEven_of_isEven_sq (n : ℕ) (h : IsEven (n ^ 2)) : IsEven n := by
  -- hint: `rcases isEven_or_isOdd n with he | ho`. One case is immediate. In
  -- the other, `n ^ 2` is both even (by `h`) and odd (by E2), which D1 forbids;
  -- `exfalso` turns the goal into `False` so you can say so.
  sorry

/-! ## Part G — Optional

Neither is needed later; both reuse what is above. -/

/-- **G1.** A number that is not even is odd. -/
theorem isOdd_of_not_isEven (n : ℕ) (h : ¬IsEven n) : IsOdd n := by
  sorry

/-- **G2.** A number is even exactly when its square is. -/
theorem isEven_sq_iff (n : ℕ) : IsEven (n ^ 2) ↔ IsEven n := by
  -- hint: `constructor`, then one direction is F and the other is E1.
  sorry

/-! ## Part H — Where this goes

Nothing to do here. The target, for later in the semester:

    theorem sqrt_two_irrational (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2

Given Part F, the classical argument runs: suppose `p² = 2q²`. Then `p²` is
even, so `p` is even by F, say `p = 2k`. Then `4k² = 2q²`, so `q² = 2k²`, so
`q` is even by F again. Both are even, and the same applies to `p/2` and
`q/2`, and so on without end.

Two things are missing, and neither is logic:

* the cancellation `4k² = 2q² → q² = 2k²`, which is arithmetic (session 4);
* the "without end" step, which needs a minimal counterexample or strong
  induction (session 5). In Lean the descent is the part that has to be made
  precise — "and so on" is not a proof step. -/
