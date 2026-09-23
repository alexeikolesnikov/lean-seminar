# Session 03 — The rest of the syntax, and logic

Two halves. The first finishes session 2: `∀` and `→` as essentially the same
construct, application, the proof state and the four tactics, and the coercion
example. The second introduces the connectives and the tactics that prove and
use them.

Here's the demo if you want to start it on the Lean server (a little slow, but
requires no installation work):
https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Falexeikolesnikov%2Flean-seminar%2Fmaster%2FSeminar%2FSession03_Logic%2FDemo.lean

## What is in `Demo.lean`

| | |
|---|---|
| §0 | Where we were, and what `#print axioms` answers about trusting Lean |
| §1 | `∀` and `→` as essentially the same construct; explicit and implicit binders; `@` |
| §2 | Application is juxtaposition; parentheses; commas; dot notation |
| §3 | The proof state; `exact`, `apply`, `intro`, `rfl`, `have`, `show`; `sorry` |
| §4 | Does this say what it claims? — coercion placement and `ℕ` subtraction |
| §5 | The connectives: `∧`, `↔`, `∨`, `¬`, `∃` |
| §6 | Does this say what it claims? — quantifier order, vacuous hypotheses |
| §7 | Summary |

§1 to §4 are the part of session 2 we did not reach, in shorter form. Session
2's `Demo.lean` remains the longer treatment of the same material, and
`Extras.lean` there is still worth reading afterwards.

## What a machine-checked proof relies on

A question from session 2, which §0 of the demo answers in part: if Lean says a
proof is correct, what is being trusted?

Not the tactics, and not Mathlib. A tactic produces a *term*, and a separate
program — the kernel, much smaller than the rest of the system — checks that
the term has the type claimed. A bug in `simp` can make a proof fail; it cannot
make a false proof pass. Trust reduces to the kernel and to the axioms.

The axioms are visible. `#print axioms` on a theorem lists them, and in
ordinary use there are three: `propext` (equivalent propositions are equal),
`Quot.sound` (quotients; function extensionality is derived from it), and
`Classical.choice` (excluded middle follows). They are what makes Lean's
mathematics classical. The logic with them is consistent relative to ZFC with
some inaccessible cardinals — an assumption of about the same size as the one
under ordinary set-theoretic practice. Anything else in that list is a finding:
`sorryAx` means the proof is unfinished, and `Lean.trustCompiler` means the
compiler has been trusted as well.

The kernel is a program and can have bugs. In August 2026 a systematic hunt
found four soundness bugs in it, each exploited to produce a proof of `False`.
They required deliberately constructed terms, no Mathlib proof was affected,
and an independently written checker rejected all of them. The fixes are in
Lean v4.33.1. That episode is also the answer to "why more than one checker":
`lean4checker` re-runs the compiled proofs through the kernel, and `nanoda` and
Lean4Lean are kernels written separately from the official one, so that
accepting a false theorem would take the same bug in several implementations.

Mathlib's reviewers are not part of this. They do not certify proofs — the
kernel does that — and no amount of review would add to it. What their
judgement bears on is whether a *definition* is the intended one and whether a
theorem's statement says what its name suggests, which no checker settles. That
is the same line §6 of the demo draws, and the reason the exercises begin with
Part A.

## The exercises

`Exercises.lean` starts a proof that runs to session 5: that no natural
numbers `p` and `q` with `q ≠ 0` satisfy `p² = 2q²`, which is the arithmetic
content of the irrationality of √2.

This week is the parity part of it. Even and odd are defined in the file as
existential statements,

```lean
def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k
def IsOdd  (n : ℕ) : Prop := ∃ k, n = 2 * k + 1
```

so every exercise is an exercise about `∃`, `∧`, `∨` and `¬` — this session's
material and nothing else. The arithmetic the argument needs is supplied at the
top of the file, already proved; the algebra tactics that prove it arrive in
session 4, and the induction behind "every number is even or odd" in session 5.

| Part | Content |
|---|---|
| A | Which of three Lean statements says the English sentence. No Lean to write. |
| B | `use` and `obtain`: 10 is even, 7 is odd, `n` even implies `n + 2` even |
| C | `constructor`, `left`/`right`, `rcases` on conjunctions and disjunctions |
| D | Negation: no number is both even and odd |
| E | The square of an even number is even; of an odd number, odd |
| F | If `n²` is even then `n` is even |
| G | Optional: not even implies odd; `IsEven (n ^ 2) ↔ IsEven n` |
| H | Nothing to do — what remains for sessions 4 and 5, and why |

Part F is the rung the irrationality argument uses, and it is provable this
week because the parity argument carries it: a case split, one case immediate,
the other impossible. No arithmetic and no induction appear in it.

## Notes

- **`subst` is the one tactic here that the demo does not cover.** Given
  `hk : n = 2 * k`, `subst hk` replaces `n` by `2 * k` everywhere and discards
  the equation. Without it the goal still mentions `n` and the supplied
  arithmetic lemmas do not match.
- **`hk.symm.trans hj` chains two equations.** `hk : n = 2 * k` reversed is
  `2 * k = n`, and composing with `hj : n = 2 * j + 1` gives
  `2 * k = 2 * j + 1`. This is the `h.symm` of the demo's §2, one step further.
  Part D is where it is needed.
- **`use` sometimes closes the goal and sometimes does not.** `use 5` on
  `IsEven 10` leaves `10 = 2 * 5`, which Lean settles by computation. `use
  (k + 1)` leaves `2 * k + 2 = 2 * (k + 1)`, which contains a variable and
  needs a theorem. The difference is the one §3 of the demo makes about `rfl`.
- **Part A is reading rather than warm-up.** Three of its nine statements are
  false and all nine compile. `∃ n, IsEven n → 100 < n` in A2 is worth
  recognising: true, and true for a reason that has nothing to do with even
  numbers.
- **We define parity instead of using Mathlib's `Even` and `Odd`.** Mathlib's
  `Odd` is the same statement as ours and its `Even n` is `∃ r, n = r + r`
  rather than `∃ k, n = 2 * k`. Session 6 is where finding and reading the
  library version becomes the subject. Here the definition is in front of you,
  which is what makes `obtain` and `use` the natural moves.
- **The demo's §0 answers a question from last time** — what a machine-checked
  proof rests on — with `#print axioms` on two theorems. Session 12 returns to
  it.
- Work in `MyWork/`, not here — copy the exercise file over first, so that
  `git pull` does not conflict with your work.

**Tactics introduced:** `constructor`, `obtain`, `rcases`, `use`, `left`,
`right`, `exfalso`, and `subst` in the exercises.

**Assumes:** `#check`, `#eval`, `#print axioms`, `plausible` from session 1;
the colon and propositions as types from session 2.

**Homework:** *Mathematics in Lean* §3, and parts A–F of the exercises. Part G
is optional.
