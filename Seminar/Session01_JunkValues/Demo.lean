/-
  Session 01 — What a formal statement does and does not say
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: #eval, #check, simp, positivity, exact_mod_cast,
                      plausible, #print axioms
  Assumed from earlier: nothing — this is the first session.

  The point of the hour: a proof assistant checks that a proof establishes a
  statement. Nobody checks that the statement says what you meant. That second
  job does not go away, and it is the one you cannot delegate.
-/
import Mathlib

open Real

/-! ## 1. Every function in Lean is total

In ordinary mathematics `1/0` is undefined and `3 - 5` is not a natural
number. Lean's logic has no room for "undefined": a function of type `ℕ → ℕ`
must return a natural number on every input. So Mathlib picks a value. These
are called *junk values*, and they are not a bug — they are the price of
keeping the logic simple. -/

#eval (7 : ℕ) / 2        -- 3, as expected: division on ℕ rounds down
#eval (1 : ℕ) / 0        -- 0
#eval (3 : ℕ) - 5        -- 0, because ℕ subtraction is truncated

/-- Division by zero is zero in `ℝ` too. This is a theorem, not a convention
you have to remember: `div_zero` is in Mathlib. -/
example : (1 : ℝ) / 0 = 0 := div_zero 1

/-! ## 2. A statement that looks right and is false

Cancellation for natural subtraction. Every mathematician reads this as true,
because every mathematician silently assumes `b ≤ a`. -/

-- Uncommenting this line makes the file fail to compile. `plausible` searches
-- for counterexamples rather than proofs, and it finds one immediately:
--
--     Found a counter-example!
--     a := 0
--     b := 1
--     issue: 0 - 1 + 1 = 0 does not hold
--
-- example (a b : ℕ) : a - b + b = a := by plausible

/-- Natural subtraction cancels **when the hypothesis is stated**. -/
example (a b : ℕ) (hba : b ≤ a) : a - b + b = a := Nat.sub_add_cancel hba

/-! ## 3. The dangerous case: a statement that is trivially *true*

A false statement is harmless — it will not compile, and you find out at once.
The statement you have to fear is one that is true for reasons that have
nothing to do with your mathematics, because it *will* compile, and the green
checkmark will tell you that you have formalised something you have not.

Here is the Archimedean property, written the way one would write it on a
board. -/

/-- "For every ε > 0 there is a natural number N with 1/N < ε."
This is **provable**, and the proof is worthless: take `N = 0`, so that
`1/N = 0 < ε` by the junk value. Nothing about Archimedes is involved. -/
example : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 / (N : ℝ) < ε := by
  intro ε hε
  refine ⟨0, ?_⟩
  -- The goal is `1 / (0 : ℝ) < ε`, which `simp` rewrites to `0 < ε`.
  simpa using hε

/-- The statement one actually meant: `N` must be positive. Now the proof has
to do real work, and Mathlib's `exists_nat_one_div_lt` does it. -/
example (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  exact_mod_cast hn

/-! Note how Mathlib states its own version:

    exists_nat_one_div_lt (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1 : K) < ε

It quantifies over `n` and then uses `n + 1`. That `+ 1` is not stylistic; it
is Mathlib dodging exactly the trap above. Library design absorbs a great deal
of this, which is why reading how Mathlib states a thing is usually more
instructive than reading how it proves it. -/

/-! ## 4. The same phenomenon, at the top of the subject

`ζ` has a pole at `s = 1`, so mathematically `ζ(1)` is undefined. Lean's `ζ`
is a function `ℂ → ℂ`, so it returns *something* there. Mathlib's own
docstring is candid about it:

  "Note that mathematically `ζ 1` is undefined, but our construction ascribes
   this particular value to it."

The value it ascribes: -/

-- Lean prints:
--   riemannZeta 1 = (↑eulerMascheroniConstant - Complex.log (4 * ↑π)) / 2
-- that is, (γ - log 4π)/2, with the arrows marking coercions ℝ → ℂ.
#check @riemannZeta_one

/-- Numerically that is about `-0.9769` — the constant term of the Laurent
expansion at the pole, not an arbitrary choice. What matters is only that it
is **not zero**: -/
example : riemannZeta 1 ≠ 0 := riemannZeta_one_ne_zero

/-! Why anyone cares. The Riemann Hypothesis, as it is usually formalised, says
that every zero of `ζ` in the critical strip has real part `1/2`. If Mathlib's
junk value at the pole had happened to be `0`, then `s = 1` would be a zero of
the formal `ζ` lying off the critical line — and the formal statement of RH
would be trivially **false**, while looking exactly like RH.

That it is not zero is a small theorem someone had to prove. The comment
sitting in Mathlib's proof of it reads `-- This one's for you, Kevin.`

Nothing here is a defect in Lean. It is the general fact that a formal
statement carries commitments its informal counterpart leaves implicit, and
that checking those commitments is mathematical work. -/

/-! ## 5. What the kernel actually promises

`#print axioms` reports what a proof depends on. Three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) are the normal foundation; the
thing to look for is `sorryAx`, which means an unfinished proof is holding the
result up. -/

#print axioms riemannZeta_one_ne_zero

/-! It says nothing at all about whether `riemannZeta` is the Riemann zeta
function. That question is not decidable by machine, and it is the question
this seminar is about. -/
