/-
  Session 04 — Solutions
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics used: rw, calc, ring, norm_num, linarith, simp, omega
  Assumed from earlier: intro, exact, apply, obtain, rcases, use, left, right,
                        constructor, exfalso, subst  (Sessions 02–03)

  Each part ends with a note headed "What this was for". Do the part first.
-/
import Mathlib

/-! # Equational reasoning, and what totality costs

Session 3 proved that `n²` even implies `n` even. This session supplies the
arithmetic the √2 argument needs around it, and meets the price Lean pays for
making every function total.

## From session 3

Part F of session 3, restated so that it can be used here without importing
that file. The proof is the one from session 3, with `ring` and `omega` in
place of the lemmas that were supplied then. -/

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

Every function in Lean is total. `a - b` on `ℕ` has an answer when `b > a`, and
`a / b` has one when `b = 0`; the answers are `0`. Nothing is wrong with the
definitions, but statements written as though subtraction and division behaved
as they do on `ℝ` are usually false. -/

/-- **A1.** `a - b + b = a` needs `b ≤ a`. Without the hypothesis, `a = 0`,
`b = 1` is a counterexample, which `plausible` finds. -/
theorem sub_add_cancel' (a b : ℕ) (h : b ≤ a) : a - b + b = a :=
  Nat.sub_add_cancel h

/-- **A2.** `a / b * b = a` needs `b` to divide `a`. -/
theorem div_mul_cancel' (a b : ℕ) (h : b ∣ a) : a / b * b = a :=
  Nat.div_mul_cancel h

/-- **A3.** Division by zero is not an error and not undefined; it is zero,
in `ℝ` as well as in `ℕ`. -/
theorem div_zero' (x : ℝ) : x / 0 = 0 := by
  simp

/-! ### What this was for

A statement that fails only in the edge case is easy to miss, because it holds
for the examples one tries by hand. `plausible` tries the edge cases first,
which is why it is useful here and not only in session 1.

The two fixed statements are Mathlib lemmas, and their names say what the
hypotheses are: `Nat.sub_add_cancel` takes `m ≤ n`, `Nat.div_mul_cancel` takes
`n ∣ m`. Reading a lemma's hypotheses is how you find out what the
corresponding statement over `ℝ` quietly assumed. -/

/-! ## Part B — `ring` and `norm_num` -/

/-- **B1.** The square of a sum. -/
theorem sq_add (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- **B2.** A difference of squares. -/
theorem prod_sum_diff (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

/-- **B3.** A statement about numerals only. -/
theorem numeral_fact : (2 : ℝ) ^ 10 = 1024 := by
  norm_num

/-! ### What this was for

`ring` proves identities that hold in every commutative ring, by normalising
both sides; it does not use hypotheses. `norm_num` evaluates numerals. Neither
is doing anything you could not do by hand, and both fail loudly when the
statement is not of their kind — B1 with `norm_num` or B3 with `ring` both
fail, which is worth trying once. -/

/-! ## Part C — `calc` and `linarith` -/

/-- **C1.** A chain of steps, each with its own justification. -/
theorem sq_le_sq_of_le (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  calc x ^ 2 = x * x := by ring
    _ ≤ y * y := mul_le_mul h h hx (le_trans hx h)
    _ = y ^ 2 := by ring

/-- **C2.** A linear consequence of two linear hypotheses. -/
theorem linear_consequence (a b c : ℝ) (h1 : a ≤ b) (h2 : b + 1 ≤ c) :
    a ≤ c := by
  linarith

/-! ### What this was for

A `calc` block is the proof written as it would be on a board: each line states
the next form and how it was reached. The relation may change along the way —
C1 goes `=`, `≤`, `=` — and Lean composes them.

`linarith` closes goals that follow from the hypotheses by linear arithmetic.
It reports failure rather than guessing, and it does not know anything
non-linear: in C1 the middle step is `mul_le_mul`, named rather than left to a
tactic, because the step is a product and not a linear one. -/

/-! ## Part D — `rw` -/

/-- **D1.** Rewriting the goal with a hypothesis. -/
theorem rw_goal (f : ℕ → ℕ) (a b : ℕ) (h : a = b) (hf : f b = 3) : f a = 3 := by
  rw [h]
  exact hf

/-- **D2.** Rewriting a hypothesis, in the other direction. -/
theorem rw_hyp (a b : ℕ) (h : a = b) (hb : b + 0 = 5) : a = 5 := by
  rw [← h] at hb
  exact hb

/-! ### What this was for

`rw [h]` replaces occurrences of the left side of `h` by its right side, in the
goal; `rw [← h]` goes the other way; `rw [h] at h'` acts on a hypothesis rather
than the goal. It is one operation with three variations, and almost every
long Mathlib proof is made of it.

`rw` finishes by trying `rfl`, which is why D2's `b + 0 = 5` does not need a
separate step for the `+ 0`. -/

/-! ## Part E — `omega`, and the cancellation the argument needs -/

/-- **E1.** Cancelling a factor of two. Note what is *not* done: nothing is
divided. On `ℕ`, dividing both sides by 2 produces a term containing `/`, which
`ring` cannot touch and whose behaviour at `0` has to be argued separately. -/
theorem cancel_two (k q : ℕ) (h : 4 * k ^ 2 = 2 * q ^ 2) : q ^ 2 = 2 * k ^ 2 := by
  omega

/-- **E2.** A linear fact about parity, of the kind that would have been
supplied last week. -/
theorem two_mul_ne_two_mul_add_one (a b : ℕ) : 2 * a ≠ 2 * b + 1 := by
  omega

/-! ### What this was for

`omega` decides linear arithmetic over `ℤ` and `ℕ`, including the truncated
subtraction and the division and modulo by literals that make those statements
awkward by hand. It treats a non-linear term such as `k ^ 2` as an opaque
atom, which is exactly why E1 is within its reach: as a statement about the
two atoms `k ^ 2` and `q ^ 2`, it is linear.

That is the route past the step where one would divide by 2 on paper. The
division is avoidable, and avoiding it costs one tactic call. -/

/-! ## Part F — The descent step

From a solution, a smaller solution. Stated with
witnesses — `p = 2a`, `q = 2b` — rather than with `p / 2` and `q / 2`, so that
no division appears. -/

/-- **F.** If `p² = 2q²` and both are even, the halves satisfy the same
equation. -/
theorem descent_step (p q a b : ℕ) (hp : p = 2 * a) (hq : q = 2 * b)
    (h : p ^ 2 = 2 * q ^ 2) : a ^ 2 = 2 * b ^ 2 := by
  subst hp
  subst hq
  have h1 : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
  have h2 : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
  omega

/-! ### What this was for

`ring` puts the squares into a form `omega` can use, and `omega` finishes.
Neither tactic could do it alone: `ring` does not use hypotheses, and `omega`
does not know that `(2 * a) ^ 2` is `4 * a ^ 2`. Dividing the work between them
this way — `have` for the algebra, then the decision procedure — is the shape of
most arithmetic proofs in Mathlib. -/

/-! ## Part G — The descent, set up

The step above, applied twice, rules out a *minimal* counterexample. This is
the whole argument except for one thing: the right to assume the counterexample
is minimal. Session 5 supplies that. -/

/-- **G.** No minimal counterexample exists. -/
theorem no_minimal_counterexample (p q : ℕ) (hq : q ≠ 0) (h : p ^ 2 = 2 * q ^ 2)
    (hmin : ∀ q' < q, q' ≠ 0 → ∀ p', p' ^ 2 ≠ 2 * q' ^ 2) : False := by
  -- `p²` is twice `q²`, so `p` is even.
  obtain ⟨a, ha⟩ := even_of_even_sq p ⟨q ^ 2, h⟩
  have hsq : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
  -- Cancelling the factor of two leaves `q² = 2a²`, so `q` is even too.
  have h4 : q ^ 2 = 2 * a ^ 2 := by subst ha; omega
  obtain ⟨b, hb⟩ := even_of_even_sq q ⟨a ^ 2, h4⟩
  have hsq2 : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
  -- The halves satisfy the same equation, and `b` is a smaller witness.
  have hab : a ^ 2 = 2 * b ^ 2 := by subst hb; omega
  exact hmin b (by omega) (by omega) a hab

/-! ### What this was for

The proof is session 3's parity rung, this session's cancellation, and the
descent step, in that order. `hmin b (by omega) (by omega) a hab` supplies four
arguments to the minimality hypothesis: the smaller witness, a proof that it is
smaller, a proof that it is not zero, and the other half — the two `by omega`
calls are the side conditions `b < q` and `b ≠ 0`, both of which follow from
`q = 2 * b` and `q ≠ 0`.

What is missing is the passage from "no minimal counterexample" to "no
counterexample". It is not logic and not arithmetic: it is the fact that any
non-empty set of natural numbers has a least element, which in Lean is strong
induction. That is session 5. -/

/-! ## Part H — Where this goes

Session 5 proves

    theorem sqrt_two_irrational (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2

by strong induction on `q`, with Part G as the induction step. Nothing further
about parity or arithmetic is needed; what is added is the induction principle
itself, and the habit of reading `Nat.strong_induction_on` and deciding whether
it says what one means. -/
