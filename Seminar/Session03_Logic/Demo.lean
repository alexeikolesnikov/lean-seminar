/-
  Session 03 — The rest of the syntax, and logic
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: constructor, obtain, rcases, use, left, right, exfalso
  Assumed from earlier: #check, #eval, #print axioms, plausible  (Session 01)
                        the colon, propositions as types            (Session 02, §1–§2)

  Sections 1 to 4 are the part of session 2 we did not get to, in shorter form.
  Section 5 onwards is new. The session 2 file remains the longer treatment.

CI: allow-sorry (1)

  §3 ends with one deliberate `sorry`, in `unfinished`, whose whole point is
  that it compiles. Check this file with --allow-sorry.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Use
import Plausible.Tactic

/-! ## 0. Where we were

Session 2 got as far as functions on data and on proofs. The two claims it
established:

> The colon has only one meaning; you can read it as "has type".

> A proposition is a type, a proof is a term of that type, and therefore
> proving something is constructing a term of the right type.

A question from the floor, which belongs here: if Lean checks the proof, what
is it that we are trusting?

Not the tactics, and not Mathlib. Those produce a *term*; a separate and much
smaller program, the kernel, checks that the term has the type claimed. What is
assumed on top of that is visible: -/

theorem two_add_two : 2 + 2 = 4 := rfl

#print axioms two_add_two     -- 'two_add_two' does not depend on any axioms

theorem add_zero_real (x : ℝ) : x + 0 = x := by ring

#print axioms add_zero_real
-- 'add_zero_real' depends on axioms: [propext, Classical.choice, Quot.sound]

/-! Those three are the ones in ordinary use: `propext` (equivalent
propositions are equal), `Classical.choice` (excluded middle follows from it),
and `Quot.sound` (quotients). They are what makes Lean's mathematics classical,
and they are consistent relative to ZFC with some inaccessible cardinals.

Anything else appearing in that list — an unfinished proof, or a proof that
trusts the compiler — is a finding. §3 shows the first of those; session 12 is
about the rest. -/

/-! ## 1. `∀` and `→` are essentially the same construct

You write

    ∀ n ∈ ℕ, B(n)

and Lean writes

    ∀ (n : ℕ), B n

The `∈` became a colon because `ℕ` is a type rather than a set, and `B(n)` lost
its parentheses for the reason in §2. What is left is a single construct, read
two ways depending on what `B n` is: -/

#check ∀ n : ℕ, n + 0 = n     -- ∀ (n : ℕ), n + 0 = n : Prop
#check ∀ n : ℕ, Fin n         -- (n : ℕ) → Fin n : Type

/-! The first is a universally quantified statement; its terms are proofs. The
second is a family indexed by `ℕ`; its terms are functions choosing a member of
`Fin n` for each `n`. (`Fin n` is the type of naturals below `n`.) Lean does not
distinguish the two constructs — both were typed with `∀`, and the display
convention is `∀` when the members are proofs and `→` when they are objects. -/

example : ((n : ℕ) → Fin n) = (∀ n : ℕ, Fin n) := rfl

/-! When `B` does not mention the bound variable, every member has the same
type and the name is never used again. `A → B` is the notation for that case: -/

example : (∀ _ : ℕ, ℕ) = (ℕ → ℕ) := rfl

/-! So the arrow is not a second kind of function type. `hPQ : P → Q` is
`hPQ : ∀ _ : P, Q`: a proof of `P` goes in, a proof of `Q` comes out.

Two consequences for §3, and they are the reason this section comes first:

* `intro` strips a binder, so an implication goal and a `∀` goal are one
  problem.
* `apply` is function application run backwards, so modus ponens and
  instantiating a universal statement are one operation.

### Binders, explicit and implicit -/

#check Nat.add_comm           -- Nat.add_comm (n m : ℕ) : n + m = m + n
#check @Nat.add_comm          -- ∀ (n m : ℕ), n + m = m + n

/-! The same theorem displayed two ways. The first is the shape a declaration is
written in: name, binders, colon, type. `@` turns that convention off.

`@` does one more thing, and it matters when reading Mathlib. Binders come in
two kinds:

    (n : ℕ)   explicit — you supply it
    {n : ℕ}   implicit — Lean works it out from the other arguments

Most Mathlib lemmas take their variables implicitly, because they can be read
off the hypotheses. Session 1 used one: -/

#check @Nat.sub_add_cancel    -- ∀ {n m : ℕ}, m ≤ n → n - m + m = n

/-! You write `Nat.sub_add_cancel h` and `n` and `m` arrive from the type of
`h`. `@` makes them explicit again, which is how you supply one by hand when
Lean cannot work it out. -/

/-! ## 2. Application is juxtaposition

Lean writes `f 2 3` where most of us write `f(2, 3)`. Writing two things next to
each other *is* applying the first to the second: no call syntax, no argument
list. -/

def addPair (a b : ℕ) : ℕ := a + b

#check addPair 2              -- addPair 2 : ℕ → ℕ
#check addPair 2 3            -- addPair 2 3 : ℕ

/-! The middle line is the surprising one. A function of "two arguments" is a
function of one argument returning a function, so supplying one argument is
legal and hands back the function `b ↦ 2 + b`. `addPair 2 3` means
`(addPair 2) 3`, and there is no arity to get wrong.

Theorems are applied the same way, because they are functions too: -/

#check Nat.add_comm 2 3       -- Nat.add_comm 2 3 : 2 + 3 = 3 + 2
#check Nat.add_comm 2         -- Nat.add_comm 2 : ∀ (m : ℕ), 2 + m = m + 2

/-! Application binds more tightly than every operator, so `f x + g y` is
`(f x) + (g y)`. Parentheses group; they never apply. -/

def scale (n : ℕ) : ℕ := n * 10

#eval scale 2 + 3             -- 23 — parsed as (scale 2) + 3
#eval scale (2 + 3)           -- 50

def double (n : ℤ) : ℤ := n * 2

/-  NOW TRY THIS. Add the line

        #check double -1

    below and read the output. There is no error:

        double - 1 : ℤ → ℤ

    Lean parsed it as the function `double` minus the constant function `1`,
    subtracted pointwise — a perfectly good function, and not what you meant.
    What you meant was `#eval double (-1)`, which is `-2`.

    The mistakes worth fearing are the ones that compile. -/

/-! Commas are never argument separators. They appear in unrelated roles —
assembling a pair, separating a binder from its body, listing elements — and
none of them is "next argument": -/

#check (⟨1, 2⟩ : ℕ × ℕ)
#check [1, 2, 3]

/-! Dot notation: for `x : T`, writing `x.foo` means `T.foo x`. Shorthand, and
nothing more, which is why proofs sometimes carry a suffix: -/

example (a b : ℕ) (h : a = b) : b = a := h.symm
example (a b : ℕ) (h : a = b) : b = a := Eq.symm h    -- the same term

/-! ## 3. The proof state, and four tactics

A proof in progress is two things: a **context** — the named things you have,
each with its type — and a **goal**, the type you still owe a term of. The
Infoview shows both, separated by `⊢`:

    P Q : Prop        ← context: names and their types
    hP : P
    hPQ : P → Q
    ⊢ Q               ← goal: what you owe

Everything above the turnstile is a colon line. The goal is a type with no name
yet, and producing that name is what finishing the proof means.

Every tactic transforms that pair. The Infoview shows the state at the cursor;
`trace_state` prints it wherever you put it, which is what to use on a projector
or in the browser editor. -/

example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  trace_state          -- P Q : Prop ⏎ hPQ : P → Q ⏎ hP : P ⏎ ⊢ Q
  apply hPQ
  trace_state          -- the same context, but now ⊢ P
  exact hP

/-- `exact e` — the goal is `⊢ T`; supply an `e : T`. -/
example (P : Prop) (hP : P) : P := by
  exact hP

/-- `apply f` — `f : A → B` and the goal is `⊢ B`; what remains is `⊢ A`. -/
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP

/-- `intro h` — take a binder off the front of the goal and put it in the
context as a new colon line. -/
example (P Q : Prop) : P → Q → P := by
  intro hP hQ
  exact hP

/-- The same tactic handles a `∀` goal, because it is the same construct. -/
example (f : ℕ → ℕ) (hf : ∀ n, f n = n) : ∀ n, f n = n := by
  intro n
  exact hf n

/-- The three together. -/
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR
  apply hPQ
  exact hP

/-! `rfl` closes a goal `a = b` when Lean already sees `a` and `b` as the same
term, with no theorem invoked. That condition is narrower than "true", and it is
not symmetric. -/

example (n : ℕ) : n + 0 = n := rfl      -- works

/-  NOW TRY THIS. Remove the two dashes below and read the error:

        Type mismatch
          rfl
        has type
          ?m.9 = ?m.9
        but is expected to have type
          0 + n = n

    Almost every type error names the same three things:

        the term            `rfl`
        the type it has     `?m.9 = ?m.9`
        the type expected   `0 + n = n`

    Find those three and you have found the problem.

    The asymmetry has a cause: addition on `ℕ` recurses on its second argument,
    so `n + 0` reduces to `n` immediately, while `0 + n` cannot reduce until
    something is known about `n`. Put the dashes back. -/

-- example (n : ℕ) : 0 + n = n := rfl

example (n : ℕ) : 0 + n = n := Nat.zero_add n   -- a theorem, proved by induction

/-! `have h : T := e` adds a line to the context; `show T` restates the goal,
provided the new form is definitionally equal to the old one. Neither changes
what Lean checks. -/

example (a b : ℕ) (h : a = b) : b = a := by
  have h' : a = b := h
  show b = a
  exact h'.symm

/-! One more term, because the exercise files are built out of it. `sorry` has
whatever type is expected of it, so it satisfies the colon everywhere and a file
full of it compiles: -/

theorem unfinished : 2 + 2 = 5 := sorry

#print axioms unfinished      -- 'unfinished' depends on axioms: [sorryAx]

/-! Note the statement. `sorry` proved something false without complaint, and
nothing but `#print axioms` reports it. This is the first of the findings
mentioned in §0. -/

/-! ## 4. Does this say what it claims?

A statement with no hypotheses that looks reasonable. -/

section
variable (n m : ℕ)

#check ((n - m : ℕ) : ℤ)      -- ↑(n - m) : ℤ
#check ((n : ℤ) - (m : ℤ))    -- ↑n - ↑m  : ℤ

end

/-  Different terms, and the difference is where the colon sits. On the left,
    subtract inside `ℕ`, where subtraction truncates at zero, then move the
    result to `ℤ`. On the right, move each number to `ℤ` first and subtract
    there. Both, computed: -/

#eval ((0 - 1 : ℕ) : ℤ)       -- 0
#eval ((0 : ℤ) - (1 : ℤ))     -- -1

/-  NOW TRY THIS. Uncomment the line below and let `plausible` search:

        Found a counter-example!
        n := 0
        m := 1
        issue: 0 = -1 does not hold

    The search is random, so the values you get may differ from these. The tool
    reports the failure without anyone having to notice it first. -/

-- example (n m : ℕ) : ((n - m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) := by plausible

/-- The statement with its hypothesis. `m ≤ n` is what separates this from the
false version above. -/
theorem cast_sub_of_le (n m : ℕ) (h : m ≤ n) :
    ((n - m : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) :=
  Nat.cast_sub h



/-! ## 5. The connectives

Each connective comes with two questions: how do you prove one, and what do you
do with one you have. The tactics come in those pairs.

### Conjunction

To prove `P ∧ Q`, `constructor` splits the goal in two. -/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

/-! The bullets `·` are not decoration: after `constructor` there are two goals,
and a bullet focuses on one of them. Without them the proof still works, and
nobody reading it can tell which tactic addresses which goal.

`⟨_, _⟩` is the term form of the same thing, and is often shorter: -/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

/-! To use a conjunction, take it apart. `obtain` names the pieces: -/

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

/-! `h.left` and `h.right` reach the components without naming them, by the dot
notation of §2 — `h.left` is `And.left h`. -/

example (P Q : Prop) (h : P ∧ Q) : P := h.left

/-! ### Implication and logical equivalence

`↔` behaves like a conjunction of two implications, and `constructor` splits it
the same way. -/

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  constructor
  · exact hPQ
  · exact hQP

/-! The two directions of an `↔` you already have are `.mp` and `.mpr`
(*modus ponens* and its reverse). They are functions, applied as in §2: -/

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q := h.mp hP

/-! ### Disjunction

To prove a disjunction you must say which side you are proving. -/

example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP

/-! To use one, you do not know which side holds, so you handle both. `rcases`
splits on the `|`, and the two cases are the two bullets: -/

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hP | hQ
  · right
    exact hP
  · left
    exact hQ

/-! ### Negation

`¬ P` is notation for `P → False`. It is not a new construct: -/

example (P : Prop) : ¬P ↔ (P → False) := Iff.rfl

/-! So a negation is proved by `intro`, like any implication, and used by
applying it: -/

example (P : Prop) (hnP : ¬P) (hP : P) : False := hnP hP

/-! `exfalso` replaces any goal with `False`. It is the tactic form of *ex falso
quodlibet*: if the hypotheses are contradictory, the goal does not matter. -/

example (P Q : Prop) (hP : P) (hnP : ¬P) : Q := by
  exfalso
  exact hnP hP

/-! ### Existence

`use` supplies the witness; what remains is the statement about it. -/

example : ∃ n : ℕ, n + 3 = 7 := by
  use 4

/-! `use 4` left the goal `4 + 3 = 7`, which Lean closed by computation without
being asked. When the remaining goal is not automatic, it stays as a goal.

To use an existence statement, `obtain` names the witness and the property: -/

example (P : ℕ → Prop) (h : ∃ n, P n) : ∃ n, P n ∨ P (n + 1) := by
  obtain ⟨n, hn⟩ := h
  use n
  left
  exact hn

/-! ## 6. Does this say what it claims? — quantifier order

Two statements, differing only in the order of the quantifiers. The first: for
every `n` there is a larger `m`. -/

example : ∀ n : ℕ, ∃ m : ℕ, n < m := by
  intro n
  use n + 1
  exact Nat.lt_succ_self n

/-! The second says there is a single `m` larger than every `n`, and it is
false. The proof of its negation is this session's four tactics together: -/

example : ¬ ∃ m : ℕ, ∀ n : ℕ, n < m := by
  intro h
  obtain ⟨m, hm⟩ := h
  exact lt_irrefl m (hm m)

/-! Both statements read as "for all n, there is an m with n < m" and "there is
an m with n < m for all n" — English that a reader skims past. In Lean the order
is written down and cannot be skimmed. This is the continuity / uniform
continuity distinction in miniature; sessions 9 and 10 return to it with the
real definitions.

### Vacuous hypotheses

A hypothesis that can never hold makes any conclusion provable. -/

example (n : ℕ) (h : n < 0) : n = 42 := by
  exfalso
  exact Nat.not_lt_zero n h

/-! Nothing is wrong with that proof, and nothing is wrong with Lean accepting
it. It is a true statement about an empty set of cases. The failure mode is a
theorem whose hypotheses are contradictory for a reason nobody noticed, which
then proves whatever its author wanted. Only reading the statement catches it. -/

/-! ## 7. Summary

1. `∀` and `→` are one construct, so `intro` and `apply` each do one job rather
   than two.
2. Application is juxtaposition; parentheses group but never apply.
3. A proof in progress is a context and a goal, and every tactic transforms that
   pair.
4. Each connective has a tactic for proving one and a tactic for using one:
   `constructor` / `obtain` for `∧` and `↔`, `left`-`right` / `rcases` for `∨`,
   `intro` / application for `¬`, `use` / `obtain` for `∃`.
5. `exfalso` is available whenever the hypotheses are contradictory.
6. Quantifier order and vacuous hypotheses are mathematical content, and both
   are visible in the statement if you read it. -/
