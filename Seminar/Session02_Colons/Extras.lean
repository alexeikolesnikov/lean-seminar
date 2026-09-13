/-
  Session 02 — Additional material
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  This file is not part of any session, and nothing in the seminar depends on
  it. It continues the appendix of `Demo.lean` §7, which set out the
  correspondence between constructions on data and constructions on
  propositions. Here that correspondence is pushed until it breaks.

  Sections are added as they are written; this file is expected to grow.

  Several lines are left with `?` or `-- error:` for you to fill in. Run them
  and record what Lean says. Answers are in `NOTES.md`.

  Run it in VS Code, where you can hover over things.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Ring.RingNF
import Plausible.Tactic

/-! ## 1. What induction is

`Nat.rec` is the eliminator for `ℕ`: the thing the `induction` tactic applies.
Read its type slowly. -/

#check @Nat.rec

/-  {motive : ℕ → Sort u} → motive Nat.zero →
      ((n : ℕ) → motive n → motive n.succ) → (t : ℕ) → motive t

    The `motive` is what you are proving — or constructing — for each natural
    number. Supply a value at zero, supply a step taking the value at `n` to the
    value at `n + 1`, and you get a value at every `t`.

    The word is worth keeping, because it appears in error messages further
    down this file.

    Note where `motive` lands: in `Sort u`, which covers both `Prop` and
    `Type`. So one recursor does two jobs. With the motive in `Prop` this is
    proof by induction; with the motive in `Type` it is definition by
    recursion. They are not analogous constructions — they are the same
    constant, used twice. -/

/-! ## 2. Where the correspondence stops

`Demo.lean` §7 lined up `Sigma` against `Exists`, and `⊕` against `∨`. The
constructors match. The eliminators do not, and the asymmetry is deliberate: a
`Prop` may not be eliminated into a `Type`. If it could, proof irrelevance
would let you derive equalities between pieces of data that are not equal.

`Fin n` below is the type of natural numbers less than `n`; `Σ n : ℕ, Fin n`
pairs a natural with something smaller than it.

The witness of a `Sigma` is available as data — it is simply the first
component: -/

#check fun (s : Σ n : ℕ, Fin n) => s.1   -- ?  a function; note its codomain

/-! The witness of an `∃` is not. Uncomment the line below and record the
error:

    example (h : ∃ n : ℕ, n > 3) : ℕ := by obtain ⟨n, _⟩ := h; exact n
    -- error:

The same restriction applies to `∨` against `⊕`: a disjunction does not tell
you which side holds in a way you can compute with. This error is stated in
terms of the motive from section 1:

    example (p q : Prop) (h : p ∨ q) : Bool := by cases h with
      | inl _ => exact true
      | inr _ => exact false
    -- error:

There is a way across, and it is an axiom rather than a construction. -/

#check @Exists.choose         -- ?
#check @Classical.choice      -- ?

noncomputable def someWitness (h : ∃ n : ℕ, n > 3) : ℕ := h.choose

#print axioms someWitness     -- ?  expect Classical.choice

/-! The `noncomputable` marker is not decoration. Drop it and the definition is
rejected — uncomment and record the error:

    def someWitness' (h : ∃ n : ℕ, n > 3) : ℕ := h.choose
    -- error:

So "there exists an `n`" and "here is an `n`" are different statements in Lean,
and the distance between them is exactly the axiom of choice. A proof of the
first can be turned into the second, but only noncomputably, and
`#print axioms` records that you did it.

This is the machinery behind a distinction mathematicians make informally and
then forget they made. It returns in session 12, where the question is what a
formalisation actually asserts. -/
