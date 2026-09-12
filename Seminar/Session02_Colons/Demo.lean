/-
  Session 02 — One colon, four tactics
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: exact, apply, intro, rfl, have, show
  Assumed from earlier: #check, #eval, #print axioms, plausible  (Session 01)

  The claim this session is organised around:

      The colon has only one meaning; you can read it as "has type".
      Everything else that looks like a colon is a different token.

  Section 7 is an appendix for afterwards, on your own machine.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Ring.RingNF
import Plausible.Tactic

/-! ## 0. Where we were

Last time:

> Lean's kernel certifies that a **proof** establishes a **statement**.
> Nothing checks that the statement is the theorem you meant.

This session is about the notation in which the proofs and statements are written.
-/

/-! ## 1. The colon tour

Everything in Lean has a "type". Even if a type is not explicitly specified,
it is specified internally.

Every line below is `#check`. Read each output as a sentence: the thing on the
left has the type on the right. -/

#check 2                      -- 2 : ℕ
#check (2 : ℝ)                -- 2 : ℝ
#check (2 : ℤ)                -- 2 : ℤ

/-  In mathematics, we typically treat ℕ as subset of ℤ, which in turn is a subset of
    ℝ. The number 2 can be simultaneously a natural and a real number. In Lean, things are
    different. One can think of ℕ, ℤ, and ℝ as disjoint sets (what Lean calls "types").
    The overloaded symbols, for example `2`, have a default type, but can be specified to
    have a different type, depending on the context.

    *Elaboration* is the stage where Lean turns what you typed into its full
    internal form: filling in the arguments you left out, deciding which `+` or
    `2` you meant, and inserting conversions where they are needed. It works
    with an expected type supplied by the surrounding context, so the type is
    an input to the process rather than something applied to the result.

    `(2 : ℝ)` therefore says: build this numeral with `ℝ` as the expected type.
    Lean produces a real number from the start; no natural number is built and
    then "converted". -/

#check (1 : ℕ) = 1            -- 1 = 1 : Prop
#check ℕ                      -- ℕ : Type
#check Type                   -- Type : Type 1

/-! Types can be complicated; a statement has type `Prop`; type ℕ has type `Type`
    and `Type` of course has a type of its own. -/

theorem two_add_two : 2 + 2 = 4 := rfl

/-! The declaration above has only one colon. The other one is part of the punctuation
    token `:=` (which should be treated as a single monolithic thing).
    Here's what's going on:

    The command `theorem` declares the name `two_add_two` and states its type, `2 + 2 = 4`.

    Then the right-hand side of `:=` supplies a term (an object) of the type `2 + 2 = 4`.
    That term must have the type `2 + 2 = 4`. If it doesn't, the compiler will produce
    a "type mismatch" error.

    The next block briefly shows that for propositions (and only for propositions), any
    two terms of the same type are equal by definition. With the print commands, you
    can see that the proofs, one supplied by the term `rfl` and the other two
    produced by the `ring` and `rfl` tactic, look different, but they are declared
    the same by the kernel. When you are reading elsewhere about *proof irrelevance*, this
    is an example.
-/

theorem t1 : 2 + 2 = 4 := by ring
theorem t2 : 2 + 2 = 4 := by rfl
#print two_add_two
#print t1
#print t2
example : two_add_two = t1 := rfl

/-!
While we are talking about tokens that include colons, `::` is the other one, used
to add an element to the head of a list. -/

#check (1 :: [2, 3])          -- [1, 2, 3] : List ℕ

/-! To sum up this section: every expression has a type; a statement is itself a
type, whose terms are its proofs; and therefore *proving something is
constructing a term of the right type*. The tactics in section 4 are four ways
of building such a term, types allow the compiler to check that you have built
the right one. -/

/-! ## 2. Propositions are types

Two lines from section 1, side by side:

    2           : ℕ
    two_add_two : 2 + 2 = 4

These are the same relation. `ℕ` is a type and `2` is a term of it. `2 + 2 = 4`
is also a type whose terms are proofs of it. `two_add_two` is a name for a term
of that type.

The same shape turns up in the Infoview while you are proving. There,

    n : ℕ
    h : n + 0 = n

are entries of the same kind: a name, and the type it belongs to. You would read
the first as "let `n` be a natural number" and the second as "suppose
`n + 0 = n`", and Lean does not distinguish between them. What differs is the
type — the terms of `ℕ` are numbers, and the terms of `n + 0 = n` are proofs.

  ### Functions, on data and on proofs

`ℕ → ℕ` is a type, and its terms are functions. Nothing so far is new. In Lean,
the same construct is used for proofs. -/

#check Nat.succ               -- Nat.succ (n : ℕ) : ℕ

section
variable (P Q : Prop) (hPQ : P → Q) (hP : P)

#check hPQ                    -- hPQ : P → Q
#check hP                     -- hP : P

/- Read `hPQ` as a function: give it a proof of `P`, get a proof of `Q`.
   Applying it is ordinary function application, written the same way. -/

end

/-! Lean has one function type, and it binds a name:

    ∀ (x : A), B

`B` may mention `x`. When it does, the name is doing work and there is no
shorter way to write it: -/

#check ∀ n : ℕ, n + 0 = n

/-! When `B` does not mention `x`, the name is never referred to again, and
`A → B` is how that is written without inventing one. The two are the same
type, not merely equivalent ones — `rfl` suffices: -/

example : (∀ _ : ℕ, ℕ) = (ℕ → ℕ) := rfl

/-! So the arrow is not a second kind of function type; it is the notation
available when the bound variable is unused. `hPQ : P → Q` above is
`hPQ : ∀ _ : P, Q`: the proof of `P` goes in, and `Q` is the same proposition
whichever proof it was.

Two consequences for §3. `intro` strips a binder, so an implication goal and a
`∀` goal are one problem. `apply` is function application run backwards, so
modus ponens and instantiating a universal statement are one operation.

("Binder" is the general word for a place where a name is introduced along with
its type: `(n : ℕ)` in a statement, `∀ n : ℕ`, `fun n : ℕ ↦ …`. All three
introduce `n` and say what it is.) -/

#check Nat.add_comm           -- Nat.add_comm (n m : ℕ) : n + m = m + n
#check @Nat.add_comm          -- ∀ (n m : ℕ), n + m = m + n

/-  Those are the same theorem displayed two ways. The `@` turns off the
    convention that pulls leading binders to the left of the colon. Worth
    seeing once so that neither shape is unfamiliar later. -/

/-! ## 3. Parentheses, commas, and how things get applied

Lean writes `f 2 3` where most of mathematics writes `f(2, 3)`. This is not a
stylistic quirk, and it is worth a few minutes because it affects how Lean
thinks about proofs as well.

**Application is juxtaposition.** Writing two things next to each other *is*
applying the first to the second. There is no call syntax and no argument
list. -/

def scale (n : ℕ) : ℕ := n * 10
def addPair (a b : ℕ) : ℕ := a + b

/-! The above defines two functions, one for scaling a natural number by 10
and the other for adding two natural numbers. Let's see the types of objects
they produce.
-/

#check scale 2                -- scale 2 : ℕ
#check addPair 2              -- addPair 2 : ℕ → ℕ
#check addPair 2 3            -- addPair 2 3 : ℕ

/-! The first line is not surprising: the result of applying `scale` to 2
is a natural number. But the middle line is a bit surprising. A function of
"two arguments" is really a function of one argument that returns a function,
so supplying one argument, say 2, is legal and hands you back the function that
inputs a natural number `b` and returns the natural number `2 + b`.
`addPair 2 3` means `(addPair 2) 3`. There is no notion of arity to get wrong.

Theorems are applied the same way, because they are functions too: -/
#check Nat.add_comm 2 3       -- Nat.add_comm 2 3 : 2 + 3 = 3 + 2
#check Nat.add_comm 2         -- Nat.add_comm 2 : ∀ (m : ℕ), 2 + m = m + 2

/-! **Parentheses group; they never apply.** Mind the order of operations: -/

#eval scale 2 + 3             -- 23 — parsed as (scale 2) + 3
#eval scale (2 + 3)           -- 50

/-! Application binds more tightly than every operator, so `f x + g y` is
`(f x) + (g y)`. Parentheses appear only where you would need them on paper to
force a different grouping. -/

def double (n : ℤ) : ℤ := n * 2

/-  NOW TRY THIS. Add the line

        #check double -1

    and read the output carefully. There is no error:

        double - 1 : ℤ → ℤ

    Lean parsed it as `double - 1`: the function `double`, minus the constant
    function `1`, subtracted pointwise. That is a perfectly good function of
    type `ℤ → ℤ`. It is simply not what you meant. What you meant was

        #eval double (-1)     -- -2

    The mistakes worth fearing are the ones that compile. -/

/-! **Commas are never argument separators.** They appear in three unrelated
roles, and none of them is "next argument": -/

#check (⟨1, 2⟩ : ℕ × ℕ)       -- assembling a pair
#check ∀ n : ℕ, n + 0 = n     -- separating a binder from its body
#check [1, 2, 3]              -- list elements

/-! **Dot notation.** For `x : T`, writing `x.foo` means `T.foo x`. It is
shorthand and nothing more, and it is why proofs sometimes carry a suffix: -/

example (a b : ℕ) (h : a = b) : b = a := h.symm
example (a b : ℕ) (h : a = b) : b = a := Eq.symm h    -- the same term

/-! The point is: there are fewer moving parts than the syntax initially
suggests. One relation, "has type"; two ways to build terms, application and
binding. Everything else: `+`, `∑`, `⟨_, _⟩`, is notation that unfolds into
those.
 -/

/-! ## 4. The four tactics as operations on colons

Each of today's tactics is a statement about types. -/

/-- `exact e` — the goal is `⊢ T`; supply an `e : T`. -/
example (P : Prop) (hP : P) : P := by
  exact hP

/-- `apply f` — `f : A → B` and the goal is `⊢ B`; what remains is `⊢ A`. -/
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  -- In the Infoview: the goal was `⊢ Q` and is now `⊢ P`.
  exact hP

/-- `intro h` — take a binder off the front of the goal and put it in the
context as a new colon line. -/
example (P Q : Prop) : P → Q → P := by
  intro hP hQ
  -- Two new lines above the turnstile; the goal has shrunk to `⊢ P`.
  exact hP

/-- The three together. -/
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR
  apply hPQ
  exact hP

/-- A `∀` behaves as an `→` does: it is eliminated by applying it. -/
example (f : ℕ → ℕ) (hf : ∀ n, f n = n) : f 3 = 3 := by
  exact hf 3

/-! ### `rfl`

`rfl : a = a`, so `rfl` closes a goal `a = b` when Lean can already see `a` and
`b` as the same term, with no theorem invoked. That condition is narrower than
"true", and it is not symmetric. -/

example (n : ℕ) : n + 0 = n := rfl      -- works

/-  NOW TRY THIS. Remove the two dashes below and read the error:

        Type mismatch
          rfl
        has type
          ?m.9 = ?m.9
        but is expected to have type
          0 + n = n

    Lean needed the type of `rfl` to be the goal, and it is not.

    The asymmetry has a cause: addition on `ℕ` recurses on its second
    argument, so `n + 0` reduces to `n` immediately, while `0 + n` cannot
    reduce until something is known about `n`. This is behind the corresponding
    exercise in the Natural Number Game.

    Put the dashes back. -/

-- example (n : ℕ) : 0 + n = n := rfl

example (n : ℕ) : 0 + n = n := Nat.zero_add n   -- a theorem, proved by induction

/-! ## 5. Does this say what it claims?

A statement with no hypotheses that looks reasonable. -/

section
variable (n m : ℕ)

#check ((n - m : ℕ) : ℤ)      -- ↑(n - m) : ℤ
#check ((n : ℤ) - (m : ℤ))    -- ↑n - ↑m  : ℤ

end

/-  Those are different terms, and the difference is where the colon sits.

    On the left: subtract inside `ℕ`, where subtraction truncates at zero, and
    move the result to `ℤ` afterwards.
    On the right: move each number to `ℤ` first and subtract there.

    The `↑` marks a *coercion* — Lean moving a value from one type to another
    where the surrounding expression requires it. Note where the arrow sits in
    each case: outside the subtraction on the left, on each argument separately
    on the right.

    Both, computed: -/

#eval ((0 - 1 : ℕ) : ℤ)       -- 0
#eval ((0 : ℤ) - (1 : ℤ))     -- -1

/-  NOW TRY THIS. Uncomment the line below and let `plausible` search:

        Found a counter-example!
        n := 0
        m := 4
        issue: 0 = -4 does not hold

    As in session 1, the tool reports the failure without anyone having to
    notice it first. Here the subject is a piece of notation rather than a
    theorem. -/

-- example (n m : ℕ) : ((n - m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) := by plausible

/-- The statement with its hypothesis. `m ≤ n` is what separates this from the
false version above. -/
theorem cast_sub_of_le (n m : ℕ) (h : m ≤ n) :
    ((n - m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) :=
  Nat.cast_sub h

/-! ## 6. Summary

1. The colon has one meaning: "has type".
2. A proposition is a type; a proof is a term of it, so proving something is
   constructing a term of the right type.
3. Application is juxtaposition; parentheses group but never apply.
4. `exact`, `apply`, `intro` and `rfl` are four operations on the typing
   relation.
5. Where the colon sits is mathematical content, not punctuation.

Exercises: `Exercises.lean`. Parts A–C are the session; D is optional.

## 7. Appendix: the same construct twice

Lean has one mechanism for building types. Data and propositions are both
built with it, which is why `2 : ℕ` and `two_add_two : 2 + 2 = 4` read the
same way (the thing on the left of `:` has the type on the right).
Laid out as a correspondence:

    data                          proposition
    ----------------------------  ----------------------------
    α → β                         p → q
    α × β        (Prod)           p ∧ q        (And)
    α ⊕ β        (Sum)            p ∨ q        (Or)
    (x : α) → β x                 ∀ x : α, p x
    Σ x : α, β x (Sigma)          ∃ x : α, p x (Exists)
    Unit,  ()                     True,  True.intro
    Empty                         False

The left column is `Type`; the right is `Prop`. The shapes match because they
are the same constructions. They are not interchangeable, and §7.4 is where
that shows. -/

/-! ### 7.1 The pairs, side by side
Hover over the expression to see its type. If you want, you can record it in
the place of the `?` below.
-/

#check @Prod                  -- Prod : Type u_1 → Type u_2 → Type (max u_1 u_2)
#check @And                   -- ?
#check @Sum                   -- ?
#check @Or                    -- ?
#check @Sigma                 -- ?
#check @Exists                -- ?
#check @Unit                  -- ?
#check @True                  -- ?
#check @Empty                 -- ?
#check @False                 -- ?

/-- A dependent function type: the codomain depends on the argument. -/
example : Type := (n : ℕ) → Fin n

/-- Negation is not a separate primitive. -/
example (p : Prop) : (¬p) = (p → False) := rfl

/-! ### 7.2 Prop is a type, and so is Type

`Sort 0` prints as `Prop` and `Sort 1` as `Type`; the hierarchy continues
upward without end. -/

#check Prop                   -- Type
#check Type                   -- Type 1
#check Type 1                 -- Type 2
#check Sort 0                 -- ?
#check Sort 1                 -- ?

/-! One asymmetry, visible here. Quantifying over all propositions stays a
proposition; quantifying over all types does not stay in `Type`. -/

#check ∀ p : Prop, p → p      -- ?  expect Prop
#check (α : Type) → α → α     -- ?  expect Type 1

/-! ### 7.3 Proof irrelevance

Any two proofs of the same proposition are definitionally equal, so `rfl`
suffices. The data analogue is false: two terms of `ℕ` are not equal by
virtue of both being naturals. -/

example (h₁ h₂ : 2 + 2 = 4) : h₁ = h₂ := rfl

/-! ### 7.4 Where the correspondence stops

`Sigma` and `Exists` have matching constructors. Their eliminators differ,
and this is deliberate: a `Prop` may not be eliminated into a `Type`. If it
could, proof irrelevance would let you derive equalities between pieces of
data that are not equal.

The witness of a `Sigma` is available as data: -/

#check fun (s : Σ n : ℕ, Fin n) => s.1          -- ?  expect ℕ

/-! The witness of an `∃` is not. Uncomment each line and record what Lean
says:

    example (h : ∃ n : ℕ, n > 3) : ℕ := h.choose'
    -- error:

    example (h : ∃ n : ℕ, n > 3) : ℕ := by obtain ⟨n, _⟩ := h; exact n
    -- error:

The same restriction applies to `∨` against `⊕`: a disjunction does not tell
you which side holds in a way you can compute with.

    example (p q : Prop) (h : p ∨ q) : Bool := by cases h with
      | inl _ => exact true
      | inr _ => exact false
    -- error:

There is a way across, and it is an axiom rather than a construction. -/

#check @Exists.choose         -- ?
#check @Classical.choice      -- ?

noncomputable def someWitness (h : ∃ n : ℕ, n > 3) : ℕ := h.choose

#print axioms someWitness     -- ?  expect Classical.choice

/-! Dropping `noncomputable` above is the demonstration:

    def someWitness' (h : ∃ n : ℕ, n > 3) : ℕ := h.choose
    -- error:

So "there exists an n" and "here is an n" are different statements in Lean,
and the distance between them is exactly the axiom of choice. -/

/-! ### 7.5 What induction is

`Nat.rec` is the eliminator for `ℕ`. The `induction` tactic applies it. Its
motive may land in `Prop` or in `Type` — the same recursor does proof by
induction and definition by recursion. -/

#check @Nat.rec
