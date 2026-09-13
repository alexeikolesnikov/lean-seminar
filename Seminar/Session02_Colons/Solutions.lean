/-
  Session 02 — One colon, four tactics  ·  SOLUTIONS
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics used: exact, apply, intro, rfl, have, show, rw, ring, norm_num
  Assumed from earlier: #check, #eval, plausible  (Session 01)

  Each part closes with a note headed "What this was for". That note is the
  point of the exercise; the proof is only how you get there.

  This file must compile with no `sorry`. If it does not, the exercise file is
  wrong too — they share their statements.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Ring.RingNF
import Plausible.Tactic

/-! ## A. The type is part of the statement -/

/-- **A1.** Subtract, then add back. -/
theorem a1 (n m : ℤ) : (n - m) + m = n := by ring

/-- **A2.** The same sentence, over `ℕ`, needs a hypothesis. -/
theorem a2 (n m : ℕ) (h : m ≤ n) : (n - m) + m = n :=
  Nat.sub_add_cancel h

/-  **A3.** The `ℕ` version without the hypothesis. `plausible` reports

        Found a counter-example!
        n := 0
        m := 2
        issue: 2 = 0 does not hold
-/

-- example (n m : ℕ) : (n - m) + m = n := by plausible

/-! **A4.** Two definitions of "two", at different types. -/

def rtwo : ℝ := 2
def ntwo : ℕ := 2

#check (rtwo = ntwo)          -- rtwo = ↑ntwo : Prop
#check (ntwo = rtwo)          -- ↑ntwo = rtwo : Prop

theorem a4 : rtwo = ntwo := rfl

/-! ### What this was for

A1 and A2 are the same English sentence. Over `ℤ` it is a theorem; over `ℕ` it
is false, because subtraction truncates at zero and `plausible` finds `n = 0`,
`m = 2` in seconds. Nothing in the words distinguishes them. The type does.

A4 is stranger. Note first that the statement you wrote is not the statement
Lean checked: `#check` reports `rtwo = ↑ntwo`. A coercion was inserted, and
writing the equation the other way round moves nothing — the arrow lands on
`ntwo` either way, because the direction is decided by which coercion exists,
not by which side you typed first.

Then `rfl` closes it. After unfolding, `ℝ`'s `2` and the cast of `ℕ`'s `2` are
the same term.

That looks like it contradicts section 5 of the demo, and it does not. There the
two sides were `↑(n - m)` and `↑n - ↑m`: the coercion sat outside an *operation*
in one and inside it in the other, and truncation happened between them. Here
there is no operation, only an atom. So the rule is neither "casts are safe" nor
"casts are dangerous":

> Look at where the arrow sits relative to the operations.

On atoms, coercions agree. Around operations, they are exactly what you have to
check. -/

/-! ## B. What `rfl` can and cannot do -/

/-- **B1.** A function applied to an argument. -/
theorem b1 : (fun x => x + 1) 3 = 4 := rfl

/-- **B2.** Negation, unfolded. -/
theorem b2 (p : Prop) : (¬p) = (p → False) := rfl

/-- **B3.** -/
theorem b3 (n : ℕ) : n + 0 = n := rfl

/-- **B4.** `rfl` fails here; a theorem is needed. -/
theorem b4 (n : ℕ) : 0 + n = n := Nat.zero_add n

/-- **B5.** `rfl` fails here too, which is the surprise. -/
theorem b5 (n : ℕ) : n * 1 = n := Nat.mul_one n

/-! ### What this was for

`rfl` does not mean "obviously true". It means "both sides reduce to the same
term with no theorem invoked", and that condition is not aligned with
mathematical obviousness in either direction.

It is *stronger* than expected in B1 and B2. Applying a function to an argument
is a reduction, so `(fun x => x + 1) 3` and `4` are literally the same term. And
`¬p` is not a primitive at all — it is notation for `p → False`, so B2 holds by
unfolding a definition.

It is *weaker* than expected in B4 and B5. Addition on `ℕ` recurses on its
second argument, so `n + 0` reduces immediately and `0 + n` cannot move until
something is known about `n`. If you guessed that multiplication would be the
mirror image — `n * 1` definitional, `1 * n` not — B5 says otherwise: neither
is. `n * 1` reduces to `0 + n`, and there the computation stops.

The lesson is not a list of which goals `rfl` closes. It is that "true" and
"true by computation" are different properties, and only the second is `rfl`'s
business. -/

/-! ## C. A proof of `∀` is a function -/

/-- **C1.** Write the proof as a function of `n`. -/
theorem c1 : ∀ n : ℕ, 0 ≤ n := fun n => Nat.zero_le n

/-- **C2.** The body never mentions `n`. -/
theorem addZero : ∀ n : ℕ, n + 0 = n := fun _ => rfl

/-- **C3.** A theorem is applied, not cited. -/
theorem c3 : 5 + 0 = 5 := addZero 5

/-- **C4.** Two bound variables. -/
theorem comm2 : ∀ n m : ℕ, n + m = m + n := fun n m => Nat.add_comm n m

/-- **C5.** Supply one argument and see what is left. -/
theorem c5 : 2 + 3 = 3 + 2 := comm2 2 3

#check comm2 2                -- comm2 2 : ∀ (m : ℕ), 2 + m = m + 2

/-- **C6.** Transporting a proof along a function. -/
theorem c6 (P : ℕ → Prop) (h : ∀ n, P n) (g : ℕ → ℕ) : ∀ n, P (g n) :=
  fun n => h (g n)

/-- **C7.** A bound variable the statement never uses. -/
theorem c7 : ∀ _ : ℕ, 2 + 2 = 4 := fun _ => rfl

/-! ### What this was for

`∀ n : ℕ, P n` is a function type, so a proof of it is a function: give it an
`n`, get a proof of `P n`. Every item here is that one fact.

C2 is the first surprise. The statement mentions `n`, but the proof does not
have to look at it — `fun _ => rfl` works because `rfl` closes the goal
whichever `n` arrives. A proof of a universal statement can be a constant
function.

C3 and C5 are the second. `addZero 5` is not a citation of a theorem; it is
function application, and its type is `5 + 0 = 5`. Feeding `comm2` one argument
leaves `∀ (m : ℕ), 2 + m = m + 2` — a proof, partially applied, exactly as
`addPair 2` was a function partially applied in section 3 of the demo. Theorems
curry because they are functions, and there was never a second mechanism.

C6 is what that buys. Composing `h` with `g` transports a proof along a
function, and the proof term is the composition.

C7 then stops being a curiosity. If the bound variable is unused, `∀ _ : ℕ, Q`
is the same type as `ℕ → Q`, and its proof is a constant function returning a
proof of `Q`. That is also why a statement quantified over an empty type is
provable: there is nothing to supply, so the function is vacuous. Session 1's
vacuous truth and this are one phenomenon. -/

/-! ## D. Applying a `∀` at a compound argument -/

/-- **D1.** `hf` may be instantiated at any term of type `ℕ`, including `f 3`. -/
theorem d1 (f : ℕ → ℕ) (hf : ∀ n, f n = n) : f (f 3) = 3 :=
  (hf (f 3)).trans (hf 3)

/-- **D1'.** The same, in tactic form. -/
theorem d1' (f : ℕ → ℕ) (hf : ∀ n, f n = n) : f (f 3) = 3 := by
  rw [hf, hf]

/-! ### What this was for

`hf 3` is the instance everyone reaches for. `hf (f 3)` is the one that matters:
the argument does not have to be a numeral, only a term of the right type. Its
type is `f (f 3) = f 3`, and chaining that with `hf 3` finishes the proof.

Written as a tactic, `rw [hf, hf]` does the same thing twice without naming
either instance. That is more convenient and less informative; the term version
shows which instances were used. -/

/-! ## E. Dot notation -/

/-- **E1.** `.symm` on an equation, `.mp` on an iff. -/
theorem e1 (a b : ℕ) (h : a = b) : b = a := h.symm

theorem e2 (p q : Prop) (h : p ↔ q) (hp : p) : q := h.mp hp

/-! ### What this was for

`h.symm` means `Eq.symm h` and `h.mp` means `Iff.mp h`. The suffix is not a
fixed vocabulary: `x.foo` means `T.foo x` where `T` is the *type* of `x`, so the
same suffix names different theorems depending on what you apply it to, and a
suffix that works on one hypothesis will be unknown on another.

This is worth ten seconds now and will be unavoidable next week: `∧` and `↔` are
read almost entirely through `.1`, `.2`, `.mp` and `.mpr`. -/

/-! ## F. Observations — no proof required

Run these; there is nothing to fill in. -/

/-  **F1.** Uncomment, and read the warning rather than an error:

        theorem anything : False := sorry
        #print axioms anything

    The file still compiles. `sorry` produces a term of *any* type, including
    `False`, so it typechecks wherever a proof is expected. What it leaves behind
    is visible only to `#print axioms`:

        'anything' depends on axioms: [sorryAx]
-/

/-! ### What this was for

Every exercise in this file has been held together by `sorry` until you replaced
it, and `sorry` proves `False`. So "the file compiles" was never evidence that
anything had been proved — it was evidence that nothing had a type error.

That is session 1's point arriving from underneath: the kernel checks that a
proof establishes a statement, and `#print axioms` is how you find out what the
proof actually rested on. -/

/-! ## G. Stretch — find the lemma yourself -/

/-- **G1.** Division truncates in `ℕ` as subtraction does, so a similar guard is
needed. Found with `exact?`; the lemma is `Nat.cast_div`. -/
theorem cast_div_of_dvd (a b : ℕ) (hdvd : b ∣ a) (hb : (b : ℚ) ≠ 0) :
    ((a / b : ℕ) : ℚ) = (a : ℚ) / (b : ℚ) :=
  Nat.cast_div hdvd hb

/-- **G2.** A `have` names an intermediate statement; `show` restates the goal
as a definitionally equal one. -/
theorem g2 (x y : ℕ) (hx : x = 2) (hy : y = 3) : x + y = 5 := by
  have hx' : x + y = 2 + y := by rw [hx]
  have hy' : 2 + y = 2 + 3 := by rw [hy]
  show x + y = 5
  calc x + y = 2 + y := hx'
    _ = 2 + 3 := hy'
    _ = 5 := rfl

/-! ### What this was for

G1 is the first time you have been asked to find a Mathlib lemma without being
told its name, and the two hypotheses are the interesting part: work out why
each is needed before proving anything. It is a trailer for session 6.

In G2, note what `show` did: nothing. The goal was already `x + y = 5`, and
`show` restated it. That is its use — it names the goal you believe you are
working on, so that a mismatch is caught where you wrote it rather than three
lines later. `show` accepts any *definitionally equal* restatement, which makes
it the practical use of part B. -/
