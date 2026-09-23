/-
  Session 03 — Solutions
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics used: intro, exact, apply, obtain, rcases, use, left, right,
                exfalso, subst
  Assumed from earlier: #check, #eval, plausible  (Session 01); the colon and
                        propositions as types     (Session 02)

  Each part ends with a note headed "What this was for". Do the part first.
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring.RingNF

/-! # Parity, and the start of a longer proof

The thread running through sessions 3 to 5 ends at

    for all natural numbers p and q with q ≠ 0,  p² ≠ 2q²

which is the arithmetic content of "√2 is irrational". This week does the
parity rungs of the ladder. The arithmetic is supplied; the logic is yours.

## Definitions

We define parity rather than using Mathlib's `Even` and `Odd`, so that every
step is visible. Both are existential statements, which is what makes them
exercises for this week. -/

/-- `n` is even when it is twice something. -/
def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k

/-- `n` is odd when it is one more than twice something. -/
def IsOdd (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

/-! ## Given: the arithmetic

These four are proved with `ring` and `omega`, which are session 4's material,
and with a Mathlib lemma whose own proof is by induction, which is session 5's.
Use them as you would a result quoted from a previous lecture. -/

/-- Twice `k` plus two is twice `k + 1`. -/
theorem two_mul_add_two (k : ℕ) : 2 * k + 2 = 2 * (k + 1) := by ring

/-- The square of an even number, in the form the definition wants. -/
theorem sq_two_mul (k : ℕ) : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring

/-- The square of an odd number, in the form the definition wants. -/
theorem sq_two_mul_add_one (k : ℕ) :
    (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring

/-- No number is both twice something and one more than twice something. -/
theorem two_mul_ne_two_mul_add_one (a b : ℕ) : 2 * a ≠ 2 * b + 1 := by omega

/-- Every natural number is even or odd. Session 5 proves this by induction;
this version is borrowed from Mathlib. -/
theorem isEven_or_isOdd (n : ℕ) : IsEven n ∨ IsOdd n := by
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, hk⟩ := h
    exact Or.inl ⟨k, by omega⟩
  · obtain ⟨k, hk⟩ := h
    exact Or.inr ⟨k, by omega⟩

/-! ## Part A — Which statement is it?

No proofs in this part. For each English sentence, one of the Lean statements
says it and the others say something else.

**A1.** "Every even number has an even square."

    (i)   ∀ n, IsEven n → IsEven (n ^ 2)
    (ii)  ∀ n, IsEven (n ^ 2) → IsEven n
    (iii) ∀ n, IsEven n ∧ IsEven (n ^ 2)

Answer: **(i)**.
(ii) is the converse — also true, and the harder half; it is Part F.
(iii) claims every number is even, and is false. It typechecks all the same.

**A2.** "Some even number is bigger than 100."

    (i)   ∀ n, IsEven n → 100 < n
    (ii)  ∃ n, IsEven n ∧ 100 < n
    (iii) ∃ n, IsEven n → 100 < n

Answer: **(ii)**.
(i) says every even number exceeds 100, which is false.
(iii) is true but vacuous: take `n = 1`, which is not even, so the implication
holds without saying anything about any even number. An existential with an
implication inside is almost never what is meant, and is worth recognising on
sight.

**A3.** "If n² is even then n is even."

    (i)   ∀ n, IsEven (n ^ 2) → IsEven n
    (ii)  ∀ n, ¬IsEven (n ^ 2) → ¬IsEven n
    (iii) ∀ n, IsOdd (n ^ 2) → IsOdd n

Answer: **(i)**.
(ii) is the inverse, not the contrapositive; it is equivalent to the converse
of (i), not to (i). The contrapositive would be `¬IsEven n → ¬IsEven (n ^ 2)`.
(iii) happens to be true as well, but by a different route, and it is not what
the sentence says.

### What this was for

Three of the nine statements are false and all nine compile. Deciding which
one a sentence means is the part of formalization no tactic performs, and
quantifier order and the placement of `→` inside `∃` are where it usually goes
wrong. -/

/-! ## Part B — Existential statements

`use` supplies a witness; `obtain` takes one apart. -/

/-- **B1.** 10 is even. -/
theorem ten_isEven : IsEven 10 := by
  use 5

/-- **B2.** 7 is odd. -/
theorem seven_isOdd : IsOdd 7 := by
  use 3

/-- **B3.** Two more than an even number is even. -/
theorem isEven_add_two (n : ℕ) (h : IsEven n) : IsEven (n + 2) := by
  obtain ⟨k, hk⟩ := h
  subst hk
  use k + 1
  exact two_mul_add_two k

/-! ### What this was for

In B1 the goal after `use 5` was `10 = 2 * 5`, and Lean closed it by
computation without being asked. In B3 the goal after `use (k + 1)` was
`2 * k + 2 = 2 * (k + 1)`, which is not a computation — both sides contain a
variable — so it needed the supplied lemma. The difference between the two is
the difference between `rfl` and a theorem, which is §3 of the demo.

`subst hk` used the equation `n = 2 * k` to replace `n` everywhere and then
discard it. Without it the goal would still mention `n`, and the supplied
lemma would not match. -/

/-! ## Part C — Conjunction and disjunction -/

/-- **C1.** An even number is even or odd. -/
theorem isEven_or (n : ℕ) (h : IsEven n) : IsEven n ∨ IsOdd n := by
  left
  exact h

/-- **C2.** If `n` is even and `m` is odd, then `m` is odd and `n` is even. -/
theorem swap_parity (n m : ℕ) (h : IsEven n ∧ IsOdd m) : IsOdd m ∧ IsEven n := by
  obtain ⟨hn, hm⟩ := h
  constructor
  · exact hm
  · exact hn

/-- **C3.** If `n` is even or `n` is even, then `n` is even. Both cases of the
`rcases` are the same, and that is the point: a disjunction is used by
handling every case, whether or not they differ. -/
theorem isEven_of_or (n : ℕ) (h : IsEven n ∨ IsEven n) : IsEven n := by
  rcases h with h | h
  · exact h
  · exact h

/-! ### What this was for

`constructor` splits a goal that is a conjunction; `obtain` splits a
hypothesis that is one. `left` and `right` choose a side of a goal that is a
disjunction; `rcases` handles both sides of a hypothesis that is one. The
pattern is the same throughout: proving and using are different operations,
and each connective has one of each. -/

/-! ## Part D — Negation -/

/-- **D1.** No number is both even and odd. -/
theorem not_isEven_and_isOdd (n : ℕ) : ¬(IsEven n ∧ IsOdd n) := by
  intro h
  obtain ⟨⟨k, hk⟩, ⟨j, hj⟩⟩ := h
  exact two_mul_ne_two_mul_add_one k j (hk.symm.trans hj)

/-- **D2.** An odd number is not even. -/
theorem not_isEven_of_isOdd (n : ℕ) (h : IsOdd n) : ¬IsEven n := by
  intro he
  exact not_isEven_and_isOdd n ⟨he, h⟩

/-! ### What this was for

`¬P` is notation for `P → False`, so D1 begins with `intro` like any other
implication, and what is then owed is `False`.

The term `hk.symm.trans hj` is two applications of dot notation. `hk` says
`n = 2 * k`; `hk.symm` says `2 * k = n`; `.trans hj` composes that with
`hj : n = 2 * j + 1` to give `2 * k = 2 * j + 1`, which is what the supplied
lemma refuses. Chaining equations this way is how the demo's `h.symm` works,
one step further along. -/

/-! ## Part E — Squares -/

/-- **E1.** The square of an even number is even. -/
theorem isEven_sq_of_isEven (n : ℕ) (h : IsEven n) : IsEven (n ^ 2) := by
  obtain ⟨k, hk⟩ := h
  subst hk
  use 2 * k ^ 2
  exact sq_two_mul k

/-- **E2.** The square of an odd number is odd. -/
theorem isOdd_sq_of_isOdd (n : ℕ) (h : IsOdd n) : IsOdd (n ^ 2) := by
  obtain ⟨k, hk⟩ := h
  subst hk
  use 2 * k ^ 2 + 2 * k
  exact sq_two_mul_add_one k

/-! ### What this was for

Both proofs have the same four lines: name the witness, substitute, supply the
new witness, quote the arithmetic. The mathematics is in choosing the witness
— `2k² ` in one case, `2k² + 2k` in the other — and that choice is exactly
what `use` asks for. -/

/-! ## Part F — The rung that matters

This is the statement the irrationality argument needs, and the one whose
proof is not a computation: it goes through the other direction and a
contradiction. -/

/-- **F.** If `n²` is even then `n` is even. -/
theorem isEven_of_isEven_sq (n : ℕ) (h : IsEven (n ^ 2)) : IsEven n := by
  rcases isEven_or_isOdd n with he | ho
  · exact he
  · exfalso
    exact not_isEven_and_isOdd (n ^ 2) ⟨h, isOdd_sq_of_isOdd n ho⟩

/-! ### What this was for

Every ingredient was already available: `isEven_or_isOdd` supplied the case
split, E2 turned the odd case into a statement about `n²`, and D1 said the two
descriptions of `n²` cannot both hold. What the proof adds is the shape —
case split, one case immediate, the other case impossible.

Note what is *not* here: no manipulation of `n²`, no arithmetic, no induction.
The parity argument carries it, which is why this rung can be done in the week
the connectives are introduced. -/

/-! ## Part G — Optional

Neither is needed later; both reuse what is above. -/

/-- **G1.** A number that is not even is odd. -/
theorem isOdd_of_not_isEven (n : ℕ) (h : ¬IsEven n) : IsOdd n := by
  rcases isEven_or_isOdd n with he | ho
  · exfalso
    exact h he
  · exact ho

/-- **G2.** A number is even exactly when its square is. -/
theorem isEven_sq_iff (n : ℕ) : IsEven (n ^ 2) ↔ IsEven n := by
  constructor
  · exact isEven_of_isEven_sq n
  · exact isEven_sq_of_isEven n

/-! ### What this was for

G1 is the case split again, with the two cases in the other order. G2 is the
observation that E1 and F are the two directions of one `↔`, and that
`constructor` assembles them without any further mathematics. Stating it this
way is how the fact appears in Mathlib. -/

/-! ## Part H — Where this goes

The target, for later in the semester:

    theorem sqrt_two_irrational (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2

Given Part F, the classical argument runs: suppose `p² = 2q²`. Then `p²` is
even, so `p` is even by F, say `p = 2k`. Then `4k² = 2q²`, so `q² = 2k²`, so
`q` is even by F again. So `p` and `q` are both even, and the same applies to
`p/2` and `q/2`, and so on without end.

Two things are missing, and neither is logic:

* the cancellation `4k² = 2q² → q² = 2k²`, which is arithmetic (session 4);
* the "without end" step, which needs either a minimal counterexample or
  strong induction (session 5). Stated in Lean, the descent is the part that
  has to be made precise — "and so on" is not a proof step.

The statement above is the one this thread ends at. `Irrational (Real.sqrt 2)`
is a separate matter of connecting it to the real numbers, and Mathlib has
that step under the name `Nat.Prime.irrational_sqrt`. -/
