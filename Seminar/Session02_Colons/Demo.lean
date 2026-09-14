/-
  Session 02 — Reading Lean
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: exact, apply, intro, rfl, have, show, trace_state
  Assumed from earlier: #check, #eval, #print axioms, sorry, plausible  (Session 01)

  The claim this session is organised around:

      The colon has only one meaning; you can read it as "has type".
      Everything else that looks like a colon is a different token.

  Section 7 is an appendix for afterwards, on your own machine. It continues in
  `Extras.lean`, which is additional material belonging to no session.

CI: allow-sorry (1)

  §4 ends with one deliberate `sorry`, in `unfinished`, whose whole point is
  that it compiles. Check this file with --allow-sorry.
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

    The one thing that *is* published is the statement. Which proof you supplied
    stops mattering the moment Lean has accepted it — §7.3 shows that directly.
-/

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

/-! ### One construct, and two things you already write

You write

    ∀ n ∈ ℕ, B(n)

and Lean writes

    ∀ (n : ℕ), B n

Two changes, neither cosmetic. The `∈` became a colon because `ℕ` is a type,
not a set you are a member of — §1's point. (Lean does have `∀ n ∈ S, …` for an
actual set `S`, and it means something else: `∀ n, n ∈ S → …`, a binder with a
side condition. Session 1 made the same remark about `∀ ε > 0`.) And `B(n)` lost
its parentheses, for the reason in §3.

What is left is one construct, which you already read in two ways depending on
what `B(n)` is:

    B(n) is a statement      ∀ n : ℕ, B n     the universally quantified sentence
    B(n) is an object        ∀ n : ℕ, B n     the family (Bₙ) indexed by ℕ

Lean does not distinguish them. The bound name exists so that `B` may mention
it — which is exactly why you write `B(n)` and not `B`. -/

#check ∀ n : ℕ, n + 0 = n     -- ∀ (n : ℕ), n + 0 = n : Prop
#check ∀ n : ℕ, Fin n         -- (n : ℕ) → Fin n : Type

/-! Both were typed with `∀`, and Lean printed the second with an arrow. That is
a display convention — `∀` when the members are proofs, `→` when they are
objects — not a difference of construct, and either form may be typed in either
case. (`Fin n` is the type of naturals below `n`, so the second line is the
family whose `n`th member is something smaller than `n`.) -/

example : ((n : ℕ) → Fin n) = (∀ n : ℕ, Fin n) := rfl

/-! When `B` does not mention `n`, every member has the same type, the name is
never referred to again, and `A → B` is the notation for that case: -/

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

/-  Those are the same theorem displayed two ways. The first is the shape a
    declaration is written in: name, binders, colon, type. The `@` turns that
    convention off and shows the type on its own.

    `@` does one more thing, and it will matter when you read a Mathlib
    lemma. Binders come in two kinds:

      `(n : ℕ)`   explicit — you supply it
      `{n : ℕ}`   implicit — Lean works it out from the other arguments

    Most Mathlib lemmas take their variables implicitly, because they can be
    read off the hypotheses. Session 1 used one: `Nat.sub_add_cancel`, whose
    signature is `{n m : ℕ} (h : m ≤ n) : n - m + m = n`. You write
    `Nat.sub_add_cancel h` and `n` and `m` arrive from the type of `h`.

    `@` makes the implicit ones explicit again, which is how you supply one by
    hand when Lean cannot guess it. -/

#check @Nat.sub_add_cancel    -- ∀ {n m : ℕ}, m ≤ n → n - m + m = n

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

### The proof state, and where to look at it

A proof in progress is two things: a **context** — the named things you have,
each with its type — and a **goal**, the type you still owe a term of. The
Infoview shows both, separated by `⊢`:

    P Q : Prop        ← context: names and their types
    hP : P
    ⊢ Q               ← goal: what you owe

Everything above the turnstile is a colon line. The goal is a type with no name
yet; producing that name is what finishing the proof means.

Every tactic is a transformation of that pair. That is the whole of this
section: `intro` moves a binder from the goal into the context, `exact`
discharges the goal, `apply` replaces the goal with whatever is left over, and
`rfl` discharges it when the two sides are already the same term.

**Where to look.** The Infoview shows the state at the cursor, so move the
cursor down a tactic block line by line and watch the context grow and the goal
shrink. On a projector, or in the browser editor, clicking is fiddly;
`trace_state` prints the state as a message wherever you put it, and needs no
cursor. -/

example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  trace_state          -- P Q : Prop ⏎ hPQ : P → Q ⏎ hP : P ⏎ ⊢ Q
  apply hPQ
  trace_state          -- the same context, but now ⊢ P
  exact hP

/-! Each of today's tactics is a statement about types. -/

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

/-! ### Two more, and they are the same two operations

`have h : T := e` adds a line to the context. It is the tactic form of naming an
intermediate result, and what follows its colon is — again — a type.

`show T` replaces the goal with `T`, provided `T` is *definitionally* equal to
the goal. It changes nothing that Lean checks; it states the goal you believe
you are working on, so that a mismatch is caught where you wrote it rather than
several lines later. -/

example (a b : ℕ) (h : a = b) : b = a := by
  have h' : a = b := h        -- a new context line, named
  show b = a                  -- the goal, restated; Lean accepts it
  exact h'.symm

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

    That error is worth reading structurally, because almost every type error
    you will meet has these three parts:

        the term            `rfl`
        the type it has     `?m.9 = ?m.9`
        the type expected   `0 + n = n`

    Find those three and you have found the problem. A type error is a colon
    mismatch, and it tells you which colon.

    (The `?m.9` is a placeholder Lean has not yet resolved — it was waiting to
    learn what `a` in `rfl : a = a` should be, and never found out.)

    The asymmetry has a cause: addition on `ℕ` recurses on its second
    argument, so `n + 0` reduces to `n` immediately, while `0 + n` cannot
    reduce until something is known about `n`. This is behind the corresponding
    exercise in the Natural Number Game.

    Put the dashes back. -/

-- example (n : ℕ) : 0 + n = n := rfl

example (n : ℕ) : 0 + n = n := Nat.zero_add n   -- a theorem, proved by induction

/-! ### `sorry`, and why "it compiled" is not "it is proved"

One more term belongs here, because the exercise file is built out of it.
`sorry` has whatever type is expected of it — any type at all. So it satisfies
the colon everywhere, and a file full of `sorry` compiles.

What it leaves behind is visible in one place only, which is why session 1 spent
time on `#print axioms`: -/

theorem unfinished : 2 + 2 = 5 := sorry

#print axioms unfinished      -- 'unfinished' depends on axioms: [sorryAx]

/-! Note the statement. `sorry` proved something false without complaint, and
nothing but `#print axioms` will tell you. -/

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
4. A proof in progress is a context and a goal; every tactic transforms that
   pair. `exact`, `apply`, `intro` and `rfl` are four such transformations.
5. Where the colon sits is mathematical content, not punctuation.
6. A type error names three things: the term, the type it has, and the type
   expected.

Exercises: `Exercises.lean`. Parts A–E are the session, F needs no proof, and G
is optional. Each part of `Solutions.lean` ends with a note headed "What this
was for" — do the part first.

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
are the same constructions. They are not interchangeable, and `Extras.lean` is
where that shows. -/

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

/-- A dependent function type: the codomain depends on the argument. `Fin n` is
the type of natural numbers less than `n`, so this is the type of functions
sending each `n` to something smaller than `n`. -/
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

/-! This is what §1 was pointing at. Three proofs of `2 + 2 = 4`, written three
ways, and `#print` shows three different terms: -/

theorem t1 : 2 + 2 = 4 := rfl
theorem t2 : 2 + 2 = 4 := by ring
theorem t3 : 2 + 2 = 4 := by decide

#print t1
#print t2
#print t3

/-! `t2`’s term is a page of `Mathlib.Tactic.Ring` machinery and `t3`’s invokes a
decision procedure, yet all three are interchangeable: -/

example : t1 = t2 := rfl
example : t2 = t3 := rfl

/-! So the proof you supply is not part of what a theorem exports. Only the
statement is. That is why `have` can forget its body, and why a proof can be
erased from compiled code entirely. -/
