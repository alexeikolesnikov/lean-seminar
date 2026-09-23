/-
  Session 04 — Equational reasoning, and what totality costs
  Math Dept Lean seminar · https://github.com/alexeikolesnikov/lean-seminar

  Checked against: Lean 4.33.0 / Mathlib v4.33.0
  Build:  lake build Seminar        (from the repository root)
  Drafted with AI assistance, then compiled against the pinned toolchain
  before release. See "How these files were made" in the README.

  Tactics introduced: rw, calc, ring, norm_num, linarith, simp, simp?, omega
  Assumed from earlier: #check, #eval, plausible          (Session 01)
                        the colon, propositions as types  (Session 02)
                        intro, exact, obtain, use, rcases, exfalso, subst
                                                          (Session 03)

  The first half is the familiar ground: identities and inequalities over ℝ,
  written the way they would be written on a board. The second half is the
  price of every function being total, and the arithmetic step the √2 argument
  needs.
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.NormNum.Basic
import Plausible.Tactic

/-! ## 0. Where we were

Session 3 ended with: if `n²` is even then `n` is even. That is the rung the
irrationality argument turns on, and it was provable with the connectives
alone.

What is still missing from the argument is arithmetic — cancelling a factor of
two — and that is this session. The tactics involved are the ones that make
ordinary algebra usable in Lean, so the session begins with them on familiar
ground. -/

/-! ## 1. `rw`

`rw [h]` takes an equation `h : a = b` and replaces `a` by `b`. Everything
else about rewriting is a variation on that. -/

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) (hf : f b = 3) : f a = 3 := by
  rw [h]                    -- goal becomes `f b = 3`
  exact hf

/-- Several rewrites in order, left to right. -/
example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

/-! Two variations:

* `rw [← h]` rewrites right to left, replacing `b` by `a`.
* `rw [h] at h'` rewrites inside the hypothesis `h'` instead of the goal. -/

example (a b : ℕ) (h : a = b) (hb : b + 0 = 5) : a = 5 := by
  rw [← h] at hb            -- hb becomes `a + 0 = 5`
  exact hb

/-! The last proof did not need a step for `+ 0`: after rewriting, `rw` tries
`rfl`, and `a + 0` reduces to `a`. That is the reduction from session 3's §3,
turning up as a convenience. -/

/-  NOW TRY THIS. Replace `rw [h1, h2]` above with `rw [h2, h1]` and read the
    error:

        Tactic `rewrite` failed: Did not find an occurrence of the pattern
          b
        in the target expression
          a = c

    The rewrites are attempted in the order given, and after `rw [h2]` there is
    no `b` in the goal yet. A rewrite that does not apply is an error, not a
    no-op. -/

/-! ## 2. `ring` and `calc`

`ring` proves identities that hold in every commutative ring. It normalises
both sides and compares; it does not look at the hypotheses. -/

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

/-! `norm_num` is the corresponding tactic for numerals. -/

example : (2 : ℝ) ^ 10 = 1024 := by
  norm_num

/-! A `calc` block is a proof written as a chain, each line carrying its own
justification. The relation may change along the way, and Lean composes the
steps. -/

example (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  calc x ^ 2 = x * x := by ring
    _ ≤ y * y := mul_le_mul h h hx (le_trans hx h)
    _ = y ^ 2 := by ring

/-! The middle step is a named lemma rather than a tactic. `mul_le_mul` is the
statement that products respect `≤` given the right non-negativity, and naming
it keeps the step readable. -/

/-! ## 3. `linarith`

`linarith` closes a goal that follows from the hypotheses by linear
arithmetic over an ordered field. -/

example (a b c : ℝ) (h1 : a ≤ b) (h2 : b + 1 ≤ c) : a ≤ c := by
  linarith

/-  NOW TRY THIS. Ask it for something non-linear:

        example (x : ℝ) (h : 0 ≤ x) : 0 ≤ x ^ 2 := by linarith

    It fails, with

        linarith failed to find a contradiction

    `nlinarith` and `positivity` handle cases like this one. The point is not
    the workaround: it is that the tactic says it failed rather than proving
    something adjacent. -/

/-! ## 4. `simp`, and making it say what it did

`simp` rewrites with a large library of lemmas marked for the purpose, until
nothing applies. It is used constantly, and it is easy to use without
understanding what it did. -/

example (l : List ℕ) : (l ++ []).length = l.length := by
  simp

/-! `simp?` does the same and prints the lemmas it used, as a `simp only` call
that can replace it:

    Try this: simp only [List.append_nil]

So the proof above is really `List.append_nil`, and now the file can say so. -/

example (l : List ℕ) : (l ++ []).length = l.length := by
  simp only [List.append_nil]

/-! Using `simp?` and keeping its output is a habit worth forming now. A `simp`
that closes a goal does not say why; a `simp only [...]` names the lemmas. -/

/-! ## 5. The totality tax

Every function in Lean is total: it returns a value for every input of its
type. There is no error, no exception, and no undefined. The values chosen for
the cases mathematics leaves out are conventional, and they are the source of
statements that compile and are false. -/

#eval (5 - 7 : ℕ)             -- 0     subtraction on ℕ truncates
#eval (7 / 2 : ℕ)             -- 3     division on ℕ rounds down
#eval (3 / 0 : ℕ)             -- 0     and division by zero is zero

example (x : ℝ) : x / 0 = 0 := by simp

example : Real.sqrt (-1) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)

/-! The last two are about `ℝ`, so this is not a quirk of `ℕ`. Division by zero
and the square root of a negative number are defined, and the definition is
zero.

Two statements that a reader would accept without a second look: -/

/-  NOW TRY THIS. Uncomment each and let `plausible` work:

        example (a b : ℕ) : a - b + b = a := by plausible

        Found a counter-example!
        a := 0
        b := 1
        issue: 1 = 0 does not hold

        example (a b : ℕ) : a / b * b = a := by plausible

        Found a counter-example!
        a := 1
        b := 0
        issue: 0 = 1 does not hold

    The values may differ between runs; the search is random. -/

-- example (a b : ℕ) : a - b + b = a := by plausible
-- example (a b : ℕ) : a / b * b = a := by plausible

/-! Both become true with a hypothesis, and Mathlib's names for them say which
hypothesis: -/

#check @Nat.sub_add_cancel    -- ∀ {n m : ℕ}, m ≤ n → n - m + m = n
#check @Nat.div_mul_cancel    -- ∀ {n m : ℕ}, n ∣ m → m / n * n = m

example (a b : ℕ) (h : b ≤ a) : a - b + b = a := Nat.sub_add_cancel h
example (a b : ℕ) (h : b ∣ a) : a / b * b = a := Nat.div_mul_cancel h

/-! The practical form of this: when a statement about `ℕ` involves `-` or `/`,
ask what it says at the edge before asking whether it is provable. `plausible`
usually answers that faster than reading does. -/

/-! ## 6. `omega`, and the step the argument needs

`omega` decides linear arithmetic over `ℕ` and `ℤ`. It knows how truncated
subtraction behaves and how division and modulo by a literal behave, which is
exactly the ground §5 made dangerous. -/

example (a b : ℕ) (h : a - b = 3) (h2 : b ≤ a) : a = b + 3 := by omega

example (a b : ℕ) : 2 * a ≠ 2 * b + 1 := by omega

/-! Now the arithmetic step the √2 argument needs. On paper: from `4k² = 2q²`,
divide both sides by 2 to get `q² = 2k²`.

Dividing is the natural move, and in `ℕ` it is the more expensive one. -/

/-  NOW TRY THIS. The division route, as far as it gets:

        example (a : ℕ) : 2 * a / 2 = a := by ring

        The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a
        normal form.
        ⊢ a * 2 / 2 = a

    `ring` works in commutative rings, and division on `ℕ` is not a ring
    operation — `2 * a / 2` is a term about rounding, not about the field of
    fractions. Any proof written through it has to carry the rounding along.

    The statement is true and `omega` proves it. But the argument does not need
    it: nothing forces us to divide. -/

-- example (a : ℕ) : 2 * a / 2 = a := by ring

example (k q : ℕ) (h : 4 * k ^ 2 = 2 * q ^ 2) : q ^ 2 = 2 * k ^ 2 := by
  omega

/-! `omega` treats `k ^ 2` and `q ^ 2` as opaque atoms — it knows nothing about
squaring. As a statement about two unknowns `X = k²` and `Y = q²`, the
hypothesis is `4X = 2Y` and the goal is `Y = 2X`, which is linear. That is why
a decision procedure for linear arithmetic settles a step about squares.

Where `ring` and `omega` divide the work: `ring` knows algebraic identities and
no hypotheses; `omega` uses hypotheses and knows no algebra. Put together with
`have`, they cover most arithmetic in Mathlib: -/

example (a b : ℕ) (h : (2 * a) ^ 2 = 2 * (2 * b) ^ 2) : a ^ 2 = 2 * b ^ 2 := by
  have h1 : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
  have h2 : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
  omega

/-! That is the descent step: if `p = 2a` and `q = 2b` solve `p² = 2q²`, then
`a` and `b` solve it too. The exercises assemble it into the statement that no
*minimal* counterexample exists, which is the whole argument except for the
right to assume minimality. Session 5 supplies that, by induction. -/

/-! ## 7. Summary

1. `rw` replaces equals by equals: `rw [h]`, `rw [← h]`, `rw [h] at h'`.
2. `ring` proves ring identities and ignores hypotheses; `norm_num` evaluates
   numerals; `linarith` uses linear hypotheses; `omega` decides linear
   arithmetic on `ℕ` and `ℤ`.
3. `calc` writes a chain of steps with a justification each, and the relation
   may change along the chain.
4. `simp?` prints the lemmas `simp` used. Keep the output; it is a citation.
5. Every function is total, so `5 - 7 = 0` and `3 / 0 = 0` and `√(-1) = 0`.
   Statements about `ℕ` involving `-` or `/` are the ones to check at the edge.
6. Avoiding a division is often simpler than carrying one. -/
