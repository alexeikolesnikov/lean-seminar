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
import Mathlib

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
stylistic quirk, and it is worth a few minutes because it affects how Lean thinks about
proofs as well.

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
  intro hP _hQ
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

──────────────────────────────────────────────────────────────────────────────
Everything below is an appendix. It is not part of the session and nothing
later depends on it. It is here because "what is a type, then?" is a reasonable
next question.

Run it in VS Code on your own machine, where you can hover over things.
────────────────────────────────────────────────────────────────────────────-/

/-! ## 7. Appendix — what the colon rests on

### 7.1 If propositions are types, what is `Prop`?

Types have types, and the tower does not stop. -/

#check (2 = 2)                -- 2 = 2 : Prop
#check Prop                   -- Prop : Type
#check Type                   -- Type : Type 1
#check Type 1                 -- Type 1 : Type 2

/-  `Prop` is a type whose terms are propositions, whose terms are proofs. The
    hierarchy `Type 0, Type 1, Type 2, …` exists to avoid `Type : Type`, which
    would make the system inconsistent (Girard's paradox).

    `Prop` and `Type u` are both `Sort`s; Lean displays the bottom two
    specially: -/

#check Sort 0                 -- Prop : Type
#check Sort 1                 -- Type : Type 1

/-  `Prop` is `Sort 0`. What distinguishes it from `Type` is not its position
    in the tower but proof irrelevance: any two proofs of the same proposition
    are definitionally equal. -/

example (h₁ h₂ : 2 + 2 = 4) : h₁ = h₂ := rfl

/-  Hence a proof cannot be `#eval`'d, and it never matters which proof you
    have, only that you have one. -/

/-! ### 7.2 `∀` and `→`

`A → B` is notation for a `∀` whose bound variable does not occur on the
right. -/

example : (∀ _ : ℕ, ℕ) = (ℕ → ℕ) := rfl

/-  When the bound variable does occur on the right, the result is a dependent
    function type: a function whose return type varies with its argument. That
    cannot be written with `→`, which is why `∀` is the primitive and `→` the
    abbreviation. -/

#check @id                    -- {α : Sort u_1} → α → α

/-  Read: for any sort `α`, a function from `α` to `α`. The type of the result
    depends on the value of the first argument. This is what "dependent type
    theory" refers to.

    The induction principle for `ℕ` has the same shape: -/

#check @Nat.rec

/-  {motive : ℕ → Sort u} → motive 0 →
      ((n : ℕ) → motive n → motive (n+1)) → (t : ℕ) → motive t

    Base case, inductive step, conclusion for all `t`. Because `motive` may
    land in `Prop` or in `Type`, the same principle gives both proof by
    induction and definition by recursion. -/

/-! ### 7.3 Definitional and propositional equality

Section 4's asymmetry, stated properly. Two terms are definitionally equal if
Lean can reduce both to the same thing on its own, by unfolding definitions and
computing — no theorem, no induction, no appeal to anything proved earlier.
`rfl` proves exactly the definitional equalities; everything else requires a
theorem.

`Nat.add` is defined by recursion on its second argument. These are its two
defining equations, and both hold by `rfl`: -/

example (n : ℕ)   : n + 0 = n                 := rfl
example (n m : ℕ) : n + (m + 1) = (n + m) + 1 := rfl

/-  The mirror images are theorems rather than reductions, each proved by
    induction on `n`: -/

#check @Nat.zero_add          -- ∀ (n : ℕ), 0 + n = n
#check @Nat.succ_add          -- ∀ (n m : ℕ), n.succ + m = (n + m).succ

/-  So `n + 0` reduces to `n` by one step of the definition, while `0 + n` is
    stuck on an unknown `n`. The two statements are equally true and are not
    equally definitional, and only the second distinction concerns `rfl`.

    A closing check in the style of session 1: what do today's theorems rest
    on? -/

#print axioms two_add_two     -- 'two_add_two' does not depend on any axioms
#print axioms Nat.zero_add
