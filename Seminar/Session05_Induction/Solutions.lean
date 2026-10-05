/-
  Session 05 — Solutions
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics used: induction ... with, Nat.le_induction, Nat.strong_induction_on,
                decide, positivity, nlinarith, gcongr
  Assumed from earlier: rw, calc, ring, norm_num, linarith, omega, simp
                        (Session 04); intro, exact, obtain, use, rcases,
                        exfalso, subst (Session 03)

  Each part ends with a note headed "What this was for". Do the part first.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity
import Plausible.Tactic

open Finset

/-! # Induction and finite sums

Two things in this session. Finite sums, with ordinary induction as the method
for identities and inequalities about them, including one bound from analysis.
And strong induction, by which "no minimal counterexample" becomes "no
counterexample" and the √2 argument begun in session 3 is complete.

## From session 4

Part G of session 4, restated so that it can be used here without importing
that file. It is proved, not an exercise. -/

/-- If `n²` is twice something, so is `n`. (Session 3, Part F.) -/
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

/-- No minimal counterexample to `p² ≠ 2q²` exists. (Session 4, Part G.) -/
theorem no_minimal_counterexample (p q : ℕ) (hq : q ≠ 0) (h : p ^ 2 = 2 * q ^ 2)
    (hmin : ∀ q' < q, q' ≠ 0 → ∀ p', p' ^ 2 ≠ 2 * q' ^ 2) : False := by
  obtain ⟨a, ha⟩ := even_of_even_sq p ⟨q ^ 2, h⟩
  have hsq : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
  have h4 : q ^ 2 = 2 * a ^ 2 := by subst ha; omega
  obtain ⟨b, hb⟩ := even_of_even_sq q ⟨a ^ 2, h4⟩
  have hsq2 : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
  have hab : a ^ 2 = 2 * b ^ 2 := by subst hb; omega
  exact hmin b (by omega) (by omega) a hab

/-! ## Part A — Reading `Finset.range` and `∑`

`Finset.range n` is the finite set `{0, 1, …, n − 1}`: it has `n` elements and
does not contain `n`. `∑ i ∈ range n, f i` is the sum of `f` over it. For a
concrete `n` these are computations, and `decide` settles them. -/

/-- **A1.** `range 5` has five elements. -/
theorem card_range_five : (range 5).card = 5 := by
  decide

/-- **A2.** `5` is not one of them. -/
theorem five_not_mem_range_five : 5 ∉ range 5 := by
  decide

/-- **A3.** `0 + 1 + 2 + 3 + 4 = 10`. -/
theorem sum_range_five : ∑ i ∈ range 5, i = 10 := by
  decide

/-- **A4.** The off-by-one: `∑_{i < n} i` is `n(n−1)/2`, not `n(n+1)/2`. The
wrong formula fails already at `n = 3`, where the sum is `3` and the formula
gives `6`. -/
theorem off_by_one : ¬ (∑ i ∈ range 3, i = 3 * (3 + 1) / 2) := by
  decide

/-! ### What this was for

`decide` evaluates a closed statement — no free variables — by running the
decision procedure its type carries, and the kernel checks the computation.
It is the right tool for "is this instance true", and it does nothing for a
statement with an `n` in it; that is what induction is for.

The off-by-one in A4 recurs: `range n` stops at `n − 1`, so
formulas copied from a board where the sum runs to `n` are usually stated for
`range (n + 1)` in Lean. -/

/-! ## Part B — Induction on a sum

`induction n with` splits into the case `n = 0` and the case `n = k + 1`, the
latter with the statement for `k` available as a hypothesis. For a sum, the
step is always the same: `Finset.sum_range_succ` peels off the last term,
the induction hypothesis rewrites the rest, and algebra finishes. -/

/-- **B1.** Gauss, without a division. -/
theorem gauss (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

/-- **B2.** The sum of the first `n` odd numbers is `n²`. -/
theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

/-- **B3.** Powers of two, stated without the subtraction `2ⁿ − 1`. -/
theorem sum_two_pow (n : ℕ) : ∑ i ∈ range n, 2 ^ i + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sum_range_succ]
    omega

/-- **B4.** Gauss with the division, derived from B1 rather than proved
directly. -/
theorem gauss_div (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  have h := gauss n
  omega

/-! ### What this was for

B1 is stated as `2 * ∑ = n(n+1)` rather than `∑ = n(n+1)/2`. The reason is
session 4's: division on `ℕ` is not a ring operation, so `ring` cannot close a
step containing it. Proving B1 directly and deriving B4 with `omega` is shorter
than proving B4 directly. B3 avoids `2ⁿ − 1` for the same reason — truncated
subtraction — by moving the `1` to the other side.

In B3, `omega` closes the step although it knows nothing about `2 ^ i`: after
`sum_range_succ`, the goal is `(S + 2^k) + 1 = 2^(k+1)` with `ih : S + 1 = 2^k`,
and it needs the fact `2^(k+1) = 2 * 2^k`. It has it because its preprocessing
rewrites `b ^ (k + 1)` as `b * b ^ k` for a numeral base `b`, and then treats
`b ^ k` as an opaque atom, exactly as it treated `k ^ 2` in session 4. For a
power that does not have this shape, a `have … := by ring` is needed first. -/

/-! ## Part C — Induction on an inequality

The induction hypothesis is an inequality, and the step is a chain. For a
statement that holds only from some `n₀` on, `Nat.le_induction` starts the
induction there. -/

/-- **C1.** `n < 2ⁿ`. -/
theorem lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    calc k + 1 < 2 ^ k + 1 := by omega
      _ ≤ 2 ^ k + 2 ^ k := by
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          omega
      _ = 2 ^ (k + 1) := by ring

/-- **C2.** `n² ≤ 2ⁿ` for `n ≥ 4`. The statement is false for `n = 3`, so the
induction starts at `4`. -/
theorem sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
    calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := h1
      _ ≤ 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

/-! ### What this was for

C2 is the first statement with an asymptotic content — `n²` is eventually
dominated by `2ⁿ` — and it is proved by an induction that starts at the first
`n` where it holds. `Nat.le_induction` is `induction` with a floor: the base
case is `n = 4` and the step carries the hypothesis `4 ≤ k`, which `nlinarith`
needs for `(k + 1)² ≤ 2k²`. In the `#check` of `Nat.le_induction`, the
`motive` is the statement, indexed by `n` and by the proof that `n₀ ≤ n`. -/

/-! ## Part D — A bound from analysis

The partial sums of `∑ 1/k²` are bounded by `2`, by induction and the
telescoping inequality `1/(m+2)² ≤ 1/(m+1) − 1/(m+2)`. Everything here is over
`ℝ`; the only casts are `(k : ℝ)` for the index. -/

/-- **D1.** The telescoping step. -/
theorem telescope (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 1 + 1) ^ 2 ≤ 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 1 + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < (m : ℝ) + 1 + 1 := by positivity
  rw [div_sub_div _ _ hm.ne' hm2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **D2.** `∑_{k ≤ n} 1/(k+1)² ≤ 2 − 1/(n+1)`. -/
theorem basel_bound (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ]
    have key := telescope m
    push_cast
    linarith

/-- **D3.** So every partial sum is below `2`. -/
theorem basel_lt_two (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 < 2 := by
  have h := basel_bound n
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-! ### What this was for

The shape is Part B's — `sum_range_succ`, the induction hypothesis, algebra —
with the algebra now an inequality over `ℝ`, so `linarith` replaces `ring` and
`omega`. The new tactics are `positivity`, which proves `0 < e` or `0 ≤ e` for
an expression built from positive pieces, and `nlinarith`, which is `linarith`
allowed to multiply hypotheses together once. The `push_cast` before `linarith`
turns `((m + 1 : ℕ) : ℝ)` into `(m : ℝ) + 1`, so that the terms in `key` and
in the goal are the same atoms.

D3 says the series converges, by monotone convergence, without the word
"converges" appearing: the sequence of partial sums is increasing and bounded.
The limit is `π²/6` (`hasSum_zeta_two` in Mathlib), which is a different kind
of fact. -/

/-! ## Part E — Strong induction, and the end of the √2 argument

Session 4 ended with Part G: no *minimal* counterexample to `p² ≠ 2q²` exists.
What turns that into "no counterexample" is that every non-empty set of natural
numbers has a least element — equivalently, strong induction:

    Nat.strong_induction_on : ∀ {p : ℕ → Prop} (n : ℕ),
      (∀ n, (∀ m < n, p m) → p n) → p n

To prove `p n` for all `n`, prove it for each `n` assuming it for every
`m < n`. -/

/-- **E1.** No natural numbers `p`, `q` with `q ≠ 0` satisfy `p² = 2q²`. -/
theorem sqrt_two_irrational (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2 := by
  induction q using Nat.strong_induction_on generalizing p with
  | _ q ih =>
    intro h
    exact no_minimal_counterexample p q hq h (fun q' hq' hne p' => ih q' hq' p' hne)

/-- **E2.** (Optional.) The same, phrased as "take the smallest counterexample"
with `Nat.find`, which returns the least `n` satisfying a decidable predicate
that is satisfied somewhere. -/
theorem sqrt_two_irrational' (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2 := by
  intro h
  classical
  -- The set of denominators of counterexamples is non-empty: `q` is in it.
  have hex : ∃ q : ℕ, q ≠ 0 ∧ ∃ p, p ^ 2 = 2 * q ^ 2 := ⟨q, hq, p, h⟩
  -- `Nat.find hex` is its least element; `Nat.find_spec` says it is in the set.
  obtain ⟨hq0, p0, hp0⟩ := Nat.find_spec hex
  -- Part G: a counterexample with minimal denominator is impossible.
  refine no_minimal_counterexample p0 (Nat.find hex) hq0 hp0 ?_
  -- Minimality is `Nat.find_min`: nothing below `Nat.find hex` is in the set.
  intro q' hq' hne p' hp'
  exact Nat.find_min hex hq' ⟨hne, p', hp'⟩

/-! ### What this was for

E1 is four lines, and three of them are bookkeeping. `induction q using
Nat.strong_induction_on generalizing p` sets up the strong induction on `q`,
with `p` allowed to vary (the smaller counterexample Part G produces has a
different numerator). `ih` then says: for every `q' < q`, every `p'`, and
`q' ≠ 0`, `p'² ≠ 2q'²`. That is Part G's hypothesis `hmin` with the arguments
in a different order, and the `fun` on the last line reorders them.

The judgment question for this session: does `Nat.strong_induction_on` say
"take the smallest counterexample"? Not literally — it says "to prove `p n`,
assume `p m` for all `m < n`" — and E2 is the literal version, with `Nat.find`
producing the least element and `Nat.find_min` saying it is least. The two are
equivalent, and E1 is shorter because the minimality hypothesis arrives already
in the shape Part G wanted. `Nat.find` needs the predicate to be decidable,
which is what the `classical` line supplies; strong induction needs nothing.

The three-session statement is now proved:

    theorem sqrt_two_irrational (p q : ℕ) (hq : q ≠ 0) : p ^ 2 ≠ 2 * q ^ 2

Session 3 supplied the parity, session 4 the cancellation and the descent
step, this session the induction. `#print axioms sqrt_two_irrational` lists
`propext`, `Classical.choice` and `Quot.sound` — the standard three from
session 3 — and no `sorryAx`. -/

#print axioms sqrt_two_irrational

/-! ## Part F — Where this goes

Nothing to do here.

Part D proved that a sequence is bounded without saying what a limit is. The
next unit does say it, in the form every analysis course uses,

    ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n − a| < ε

and proves the basic facts about it — constants, `1/(n+1) → 0`, sums, and
uniqueness — with the tactics already in hand. It needs nothing new. What it
leads to is Mathlib's own definition, which is stated for a general notion of
"approaching" called a filter and is the subject of session 9. -/
