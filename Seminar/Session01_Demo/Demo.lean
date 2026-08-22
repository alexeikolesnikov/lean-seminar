/-
  Session 01 — What does a machine-checked proof actually certify?
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: #eval, #check, #print axioms, intro, have, simp,
                      linarith, exact?, plausible, native_decide, induction,
                      ring
  Assumed from earlier: nothing — this is the first session.

CI: allow-sorry (2)

  Two declarations in §6 are deliberately unproved: `unfinished` (an explicit
  `sorry`) and `passes_plausible` (a `plausible` that finds no counterexample).
  Check this file with --allow-sorry.

-/
import Mathlib

open Real Finset

/-! ## 1. It will tell you if you are wrong

We start with counterexamples. The tactic
`plausible` looks for **counterexamples** rather than proofs. Live, type the
line below without the comment marks. The statement is false at `n = 0`, and
`plausible` reports:

    Found a counter-example!
    n := 0
    issue: 0 < 0 does not hold

    -- example (n : ℕ) : n < 2 * n := by plausible

Uncommenting it makes this file fail to compile — which is the demonstration.

Why `n = 0` breaks it: nothing subtle, and Lean will simply compute it. -/

#eval (0 : ℕ) < 2 * 0      -- false

/-- So the claim is not true of *every* natural number. Here is that written
as a proof, one step per line. Read the Infoview after each line.

`¬ P` is, by definition, `P → False`, so the first move is to assume `P`. -/
example : ¬ ∀ n : ℕ, n < 2 * n := by
  intro h            -- h : ∀ n, n < 2 * n     — suppose the claim did hold
  have h0 := h 0     -- h0 : 0 < 2 * 0         — then in particular at n = 0
  simp at h0         -- 2 * 0 = 0, so h0 says 0 < 0, which is false


/-- This can be accomplished with a one-liner: -/
example : ¬ ∀ n : ℕ, n < 2 * n := fun h => by simpa using h 0

/-! ## 2. The interface

Three commands, and one panel. `#eval` computes, `#check` reports a type, and
the **Infoview** on the right shows the goal wherever your cursor is. That
panel is the whole interface; there is nothing else to learn about the editor.

Unicode is typed with backslash abbreviations: `∀` is `\forall`, `ℝ` is `\R`,
`≤` is `\le`, `↦` is `\mapsto`, `∑` is `\sum`. Hover over any symbol to be
told how to type it. -/

#eval 2 ^ 10
#check fun x : ℝ ↦ x ^ 2
#check @Nat.add_comm

/-- Click at the end of this line and read the Infoview. It shows the
hypotheses above the bar and the goal below it — exactly the blackboard
convention. `linarith` closes goals that follow from linear arithmetic. -/
example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 2 := by linarith

/-- `exact?` searches Mathlib and reports the name of a lemma that closes the
goal. Use it to *learn the name*, then write the name — the search is slow and
the name is the transferable knowledge. Here it finds `Nat.add_comm`.

example (a b : ℕ) : a + b = b + a := by exact?
-/
example (a b : ℕ) : a + b = b + a := Nat.add_comm a b

/-! ## 3. Every function is total, so some values are junk

Lean's logic has no "undefined". A function of type `ℕ → ℕ` must return a
natural number on every input, so Mathlib picks one. -/

#eval (7 : ℕ) / 2        -- 3: division on ℕ rounds down
#eval (1 : ℕ) / 0        -- 0
#eval (3 : ℕ) - 5        -- 0: subtraction on ℕ is truncated

example : (1 : ℝ) / 0 = 0 := div_zero 1

/-- Cancellation for `ℕ` subtraction — **with** the hypothesis every
mathematician silently assumes. Without `b ≤ a` it is false at `a = 0, b = 1`,
and `plausible` finds that in seconds. -/
example (a b : ℕ) (hba : b ≤ a) : a - b + b = a := Nat.sub_add_cancel hba

/-! ## 4. The failure that matters: statements that are *vacuously* true

A false statement is harmless — it will not compile and you learn at once. The
dangerous one compiles but is not the theorem you meant. -/

/-- Vacuous truth in its purest form. There are no reals in the empty set, so
anything at all is true of all of them. -/
example : ∀ x ∈ (∅ : Set ℝ), x = 37 := by simp

/-- The Archimedean property, written the way one would write it on a board.
It is **provable**, and the proof is worthless: take `N = 0`, so that
`1/N = 0 < ε` by the junk value. Nothing about non-standard reals is involved. -/
example : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 / (N : ℝ) < ε := by
  intro ε hε
  refine ⟨0, ?_⟩
  simpa using hε          -- goal was `1 / (0 : ℝ) < ε`, i.e. `0 < ε`

/-- The statement one meant: `N` must be positive, and now the proof does
work. Note how Mathlib states its own version — `exists_nat_one_div_lt` gives
`1 / (n + 1) < ε` — with the `+ 1` there precisely to dodge this trap. -/
example (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact ⟨n + 1, Nat.succ_pos n, by exact_mod_cast hn⟩

/-! ## 5. The same failure, one step subtler: quantifier order

Compare these two. The symbols are nearly identical; the mathematics is not.
Read the Infoview output of both `#check`s side by side and find the
difference before saying it out loud. -/

#check @Metric.continuous_iff
--  Continuous f ↔ ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a, dist a b < δ → dist (f a) (f b) < ε

#check @Metric.uniformContinuous_iff
--  UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ a b, dist a b < δ → dist (f a) (f b) < ε

/-- One implication is a one-liner, and it is the true one. -/
example {f : ℝ → ℝ} (hf : UniformContinuous f) : Continuous f := hf.continuous

/-! The converse is false — `fun x ↦ x^2` is continuous on `ℝ` and not
uniformly so — but nothing in the *shape* of the two statements tells you
which way round it goes. Only reading the quantifiers does.

Write the wrong one on a worksheet and it will compile, be proved, and be a
different theorem. This is the single most common way a formalization drifts
from its intent, and it costs nothing to check. -/

/-! ## 6. What the kernel actually promises

`#print axioms` reports what a proof depends on. Three standard axioms —
`propext`, `Classical.choice`, `Quot.sound` — are the ordinary foundation of
Mathlib. Anything else is worth a look. -/

example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c := by grind

/-- A deliberately unfinished proof. `sorry` is Lean's "trust me for now": the
file still compiles, with a warning, and every theorem downstream inherits the
debt. -/
theorem unfinished (n : ℕ) : n + 0 = n := by sorry

#print axioms unfinished
--  'unfinished' depends on axioms: [sorryAx]

/-- `native_decide` proves goals by *running compiled code* rather than by
kernel reduction. It is fast and it enlarges what you are trusting from the
kernel to the entire compiler. -/
theorem big_sum : (List.range 1000).sum = 499500 := by native_decide

#print axioms big_sum
--  'big_sum' depends on axioms: [propext, big_sum._native.native_decide.ax_1_1]

/-- When `plausible` *fails* to find a counterexample it has not proved
anything. Its documentation says that after 100 successful tests it "acts like
`admit`", and `admit` is `sorry`. So a passing `plausible` looks green and
leaves a hole — check it the same way. -/
theorem passes_plausible : ∀ n : ℕ, n + 0 = n := by plausible

#print axioms passes_plausible
--  'passes_plausible' depends on axioms: [sorryAx]

/-! Read that second name again. Lean has **minted a new axiom, named after
this theorem**, whose content is "the compiler said so". That is the extra
promise, and it is worth pausing on in a room that has just been told the
kernel checks everything.

Mathlib's own linter discourages `native_decide` — deliberately "an incentive
... without being a ban" — and its source says why:

  "The `native_decide` tactic is not allowed in mathlib, as it trusts the
   entire Lean compiler (and not just the Lean kernel). Because the latter is
   large and complicated, at present it is probably possible to prove `False`
   using `native_decide`."

So `#print axioms` is not pedantry. It is how you find out which of the two
promises you are relying on, and it takes one line. -/

/-! ## 7. And it does prove real theorems

Nobody should leave thinking the tool is only a critic. -/

/-- √2 is irrational. One line, because somebody formalised it already — this
is what a library of two million lines buys you. -/
theorem sqrt_two_irrational : Irrational (√2) := irrational_sqrt_two

/-- Gauss's summation formula, proved here rather than looked up. Stated as
`2 * ∑ = n(n+1)` rather than `∑ = n(n+1)/2` deliberately: `/` on `ℕ` is the
junk-valued division from §3, and a statement with it in would need a proof
that the division is exact before it said what we mean. -/
theorem gauss_sum (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    -- Peel the last term off the sum, then use the induction hypothesis.
    rw [sum_range_succ, Nat.mul_add, ih]
    ring

#print axioms gauss_sum
--  'gauss_sum' depends on axioms: [propext, Classical.choice, Quot.sound]

/-! Mathlib's own version, for comparison, is stated with `ℕ` subtraction:

    Finset.sum_range_id_mul_two (n : ℕ) : (∑ i ∈ range n, i) * 2 = n * (n - 1)

and it is correct — because `range n` stops at `n - 1`, and because at `n = 0`
the truncated `0 - 1 = 0` gives `0 = 0`. The junk value does no harm *there*.
Whether it does harm is a question about the statement, every time, and it is
the question this seminar is about. -/
