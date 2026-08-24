/-
  Session 01 — What does a machine-checked proof actually certify?
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: #eval, #check, #print axioms, trace_state, intro, have,
                      simp, linarith, exact?, plausible, native_decide,
                      induction, ring
  Assumed from earlier: nothing — this is the first session.

CI: allow-sorry (2)

  Two declarations in §6 are deliberately unproved: `unfinished` (an explicit
  `sorry`) and `passes_plausible` (a `plausible` that finds no counterexample).
  Check this file with --allow-sorry.

-/
import Mathlib

open Real Finset

/-! ## 1. It will tell you if you are wrong

Most tools of this kind are introduced by proving something. We start with a
counterexample.

`plausible` does not look for a proof. It tries the statement on random inputs
and reports the first one that breaks it. -/

/-  NOW TRY THIS. The line below is commented out. Remove the two dashes,
    watch the file stop compiling, and read what Lean says:

        Found a counter-example!
        n := 0
        issue: 0 < 0 does not hold

    Then put the dashes back. Breaking a file on purpose and reading the
    complaint is worth doing often. -/

-- example (n : ℕ) : n < 2 * n := by plausible

/-! `n = 0` is the whole story. `#eval` runs an expression and prints the
answer, so you can check it directly. -/

#eval (0 : ℕ) < 2 * 0      -- false

/-! So "every natural number is less than twice itself" is not a theorem. Here
is that written out as a proof. Do not worry yet about the shape of these
lines — §2 takes one apart piece by piece. For now, put the cursor at the start
of each line in turn and watch the panel on the right change.

`¬ P` means `P → False`: to refute something, assume it and derive nonsense. -/

example : ¬ ∀ n : ℕ, n < 2 * n := by
  intro h            -- suppose the claim did hold; call it `h`
                     --   h : ∀ (n : ℕ), n < 2 * n
                     --   ⊢ False
  have h0 := h 0     -- then it holds in particular at n = 0
                     --   h0 : 0 < 2 * 0
  simp at h0         -- and `simp` computes 2 * 0 = 0, so h0 says 0 < 0

/-- The same proof, compressed. Both are equally valid; the long one is for
reading and the short one is what you write once you know what it says. -/
example : ¬ ∀ n : ℕ, n < 2 * n := fun h => by simpa using h 0

/-! ## 2. The interface, and one example taken apart

Three commands: `#eval` computes, `#check` reports a type, and the **Infoview**
on the right shows the goal wherever your cursor is. That panel is the whole
interface; there is nothing else to learn about the editor.

Everything written in Lean has a **type** — "what kind of thing this is".
`#check` reports it without evaluating anything. -/

#check (2 : ℕ)              -- 2 : ℕ
#check (2 ^ 10)             -- 2 ^ 10 : ℕ   — inferred; you never said so
#check fun x : ℝ ↦ x ^ 2    -- a function, of type ℝ → ℝ
#check @Nat.add_comm        -- a theorem is a thing with a type too
#check (2 + 2 = 4)          -- 2 + 2 = 4 : Prop

/-! The last line is worth a pause. A *statement* has a type too, and it is
called `Prop`. Both `2 + 2 = 4` and `2 + 2 = 5` are things of type `Prop`.
Being a statement and being true are separate questions; the second is what a
proof is for.

`#eval`, by contrast, computes: -/

#eval 2 ^ 10

/-! Unicode is typed with backslash abbreviations — `∀` is `\forall`, `ℝ` is
`\R`, `≤` is `\le`, `↦` is `\mapsto`, `∑` is `\sum`. Hover over any symbol to
be told how to type it. -/

/-  Now the anatomy of a proof. Here is the whole thing, with its parts named:

    example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 2 := by linarith
    └─────┘ └───────┘ └─────────┘   └───────────┘ └───┘ └──────┘
    command  objects  assumption      the goal    proof  tactic

    · `example`       — "here is a claim". A theorem you do not bother to name.
    · `(a b : ℝ)`     — the objects the claim is about, and what they are.
    · `(h : a ≤ b)`   — an assumption, given the name `h` so the proof can
                        refer to it. On a blackboard: "suppose a ≤ b".
    · `a + 1 ≤ b + 2` — the statement to be proved. Lean calls it the *goal*.
    · `:= by`         — "and here is the proof, as a list of instructions".
    · `linarith`      — one such instruction: "this follows by linear
                        arithmetic from what we have". -/

example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 2 := by linarith

/-  NOW TRY THIS — four things, in order. Each takes ten seconds.

    1. Put the cursor immediately BEFORE `linarith` (click just left of the
       `l`). The Infoview shows the state at that moment:

           a b : ℝ
           h : a ≤ b
           ⊢ a + 1 ≤ b + 2

       Everything above `⊢` is what you have. Below it is what you owe.

    2. Now put the cursor at the END of the line, after `linarith`. The state
       is gone and the Infoview says `No goals`. That is what "finished"
       means: nothing is owed. Do not go looking for a success message —
       `No goals` is the success message.

       (In VS Code you also get a small mark in the margin. In the browser
       editor you do not. Same proof either way.)

    3. Break it. Change `b + 2` to `b - 2` and read the error:

           linarith failed to find a contradiction
           a b : ℝ
           h : a ≤ b
           a✝ : b - 2 < a + 1
           ⊢ False

       Two things worth noticing. Lean does not say the claim is false — it
       says this tactic could not settle it. And the state shows how the
       tactic works: it assumed the opposite of the goal (the line with the
       dagger) and went looking for a contradiction. Change it back.

    4. Some proofs are longer than one instruction. Move the cursor down the
       tactic lines below and watch the state change with it. -/

example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 2 := by
  have step : a + 1 ≤ b + 1 := by linarith
  linarith

/-! If clicking around is fiddly — on a projector, or in the browser editor —
`trace_state` prints the state as a message instead, wherever you put it. No
cursor required, and it shows the same thing in both editors. -/

example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 2 := by
  trace_state          -- a b : ℝ ⏎ h : a ≤ b ⏎ ⊢ a + 1 ≤ b + 2
  have step : a + 1 ≤ b + 1 := by linarith
  trace_state          -- the same, now with `step` added above the ⊢
  linarith
  -- A `trace_state` here would print nothing at all: no goals are left.

/-- One more command. `exact?` searches Mathlib and reports the name of a lemma
that closes the goal. Use it to find the name, then write the name: the search
is slow, and the name is what you keep. Here it finds `Nat.add_comm`.

    example (a b : ℕ) : a + b = b + a := by exact?
-/
example (a b : ℕ) : a + b = b + a := Nat.add_comm a b

/-! ## 3. Every function is total, so some values are junk

Now a consequence of types that will bite us all semester. Ask Lean what
subtraction on `ℕ` is: -/

#check @Nat.sub            -- Nat.sub : ℕ → ℕ → ℕ

/-! That type says: given any two naturals, return a natural. Not "when the
answer makes sense" — there is no "undefined" anywhere in `ℕ → ℕ → ℕ`, and
Lean's logic has no such value. So something must come back, and Mathlib
picks it. -/

#eval (7 : ℕ) / 2        -- 3: division on ℕ rounds down
#eval (1 : ℕ) / 0        -- 0
#eval (3 : ℕ) - 5        -- 0: subtraction on ℕ is truncated

example : (1 : ℝ) / 0 = 0 := div_zero 1

/-  NOW TRY THIS. Add the type annotation `(3 : ℤ) - 5` and evaluate it:

        #eval (3 : ℤ) - 5        -- -2

    Same symbols, different answer, because the type changed. Nothing was
    overloaded and nothing went wrong — you asked a different question. When
    you read a formal statement, the types are part of the statement. -/

#eval (3 : ℤ) - 5          -- -2

/-- Cancellation for `ℕ` subtraction — **with** the hypothesis every
mathematician silently assumes. Without `b ≤ a` it is false at `a = 0, b = 1`,
and `plausible` finds that in seconds. -/
example (a b : ℕ) (hba : b ≤ a) : a - b + b = a := Nat.sub_add_cancel hba

/-! ## 4. The failure that matters: statements that are *vacuously* true

A false statement is harmless — it will not compile, and you find out at once.
The dangerous one compiles, but is not the theorem you meant. -/

/-- Vacuous truth in its purest form. There are no reals in the empty set, so
anything at all is true of all of them. -/
example : ∀ x ∈ (∅ : Set ℝ), x = 37 := by simp

/-  NOW TRY THIS, before reading on. Predict, out loud, whether the next
    statement is provable. It is the Archimedean property, written the way one
    would write it on a board.

    Then put the cursor before `refine` and read the goal, and after
    `simpa` and read what is left. -/

example : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 / (N : ℝ) < ε := by
  intro ε hε
  refine ⟨0, ?_⟩          -- offer N = 0 as the witness
  simpa using hε          -- goal was `1 / (0 : ℝ) < ε` — which is `0 < ε`

/-! It is provable, and the proof is worthless. Take `N = 0`; then `1/N` is the
junk value `0` from §3, and `0 < ε` was given. Nothing about non-standard
analysis is involved. The kernel checked the proof. The kernel has nothing to
say about whether the statement was the one you meant. -/

/-- The statement one meant: `N` must be positive, and now the proof does real
work. Mathlib's own version, `exists_nat_one_div_lt`, gives `1 / (n + 1) < ε`,
with the `+ 1` there to avoid exactly this. -/
example (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact ⟨n + 1, Nat.succ_pos n, by exact_mod_cast hn⟩

/-! ## 5. The name is not the definition

`Continuous f` is not the ε–δ definition. In Mathlib it is the topological one,
and `Metric.continuous_iff` is a **theorem** relating the two. Ask Lean what the
definition actually is: -/

#print Continuous
--  fields:
--    Continuous.isOpen_preimage : ∀ (s : Set Y), IsOpen s → IsOpen (f ⁻¹' s)
--  (the rest of the output is universe and instance bookkeeping)

/-! One field: preimages of open sets are open. The ε–δ form is proved from it,
and is what these report: -/

#check @Metric.continuous_iff
#check @Metric.uniformContinuous_iff

/-! (`∀ ε > 0, P ε` is notation for `∀ ε, ε > 0 → P ε`: a binder with a side
condition, not a new quantifier.)

To find out what a Mathlib name says, `#print` the definition rather than
reading a lemma about it. The next example is why. -/

/-! ### A name that misleads

`ContinuousOn f s` reads like "f is continuous on s". Its definition asks for
continuity *within* `s`: at each point of `s`, only the nearby points of `s`
count. On a one-point set there are no other points of `s`, so there is nothing
for the condition to test.

Read this signature and predict the hypotheses on `f` before running it. -/

#check @continuousOn_singleton

/-- There are none. *Every* function `ℝ → ℝ` is `ContinuousOn` a singleton. -/
example (f : ℝ → ℝ) : ContinuousOn f {(0 : ℝ)} :=
  continuousOn_singleton f 0

/-- The same for any finite set. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : s.Finite) : ContinuousOn f s :=
  hs.continuousOn f

/-! This is not a defect. `ContinuousOn` is the definition that behaves well on
an interval, which is what it is for. It is simply not "continuous at each point
of `s`". Going from one to the other needs `s` to be a neighbourhood of the
point, not merely to contain it: -/

#check @ContinuousOn.continuousAt

/-- The other direction needs no extra hypothesis. -/
example (f : ℝ → ℝ) (s : Set ℝ) (h : ∀ x ∈ s, ContinuousAt f x) : ContinuousOn f s :=
  continuousOn_of_forall_continuousAt h

/-! The quantifiers here are the ones you expect, in the order you expect. What
differs is the definition underneath, and `#print` is how you check it. -/

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
