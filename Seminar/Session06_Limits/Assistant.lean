/-
  Session 06 — Sequences and limits
  Math Dept Lean seminar — three tasks for an AI assistant

  Checked against: Lean 4.33.0 / Mathlib v4.33.0 (the statements and the
  reference proofs in Solutions.lean, Part H; not any assistant's output).
  CI: allow-sorry (3)

  Tactics introduced: none.
-/
import Mathlib

/-! # Three tasks for an assistant

The seminar's rule for AI assistance (`GROUND-RULES.md`): compile it,
understand it, disclose it. These three tasks are a rehearsal of that rule.
In each, the assistant — Copilot, Claude, or another — is given the task in
the prompt quoted in the comment, its answer is pasted into this file, and
the file is checked. What Lean checks and what it does not check are the
subject of session 12; the short version is in the last section of this
file.

The definition is the one from the demo. -/

/-- `ConvergesTo s a` says that the sequence `s` converges to `a`. -/
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε

/-! ## Task 1 — Ask for a proof, then check it

Prompt, with the definition pasted above it:

    Prove this in Lean 4 with Mathlib. Give only the code.

    theorem convergesTo_neg {s : ℕ → ℝ} {a : ℝ}
        (hs : ConvergesTo s a) : ConvergesTo (fun n => -s n) (-a)

Paste the answer in place of the `sorry`. Three outcomes are possible, and
each is a lesson: the file compiles and `#print axioms` lists the usual
three; the file compiles but `#print axioms` lists `sorryAx`, because the
assistant left a hole; or the file does not compile, usually because a lemma
name is stale or invented. A proof that compiles is still to be read: the
test is whether each line corresponds to a step one could explain. -/

theorem convergesTo_neg {s : ℕ → ℝ} {a : ℝ}
    (hs : ConvergesTo s a) : ConvergesTo (fun n => -s n) (-a) := by
  sorry

#print axioms convergesTo_neg

/-! ## Task 2 — Ask for a statement, then read it

Prompt:

    Using the definition of ConvergesTo above, state in Lean 4 that every
    convergent sequence of real numbers is bounded. Do not prove it.

The statement is the part to read. Questions to ask of whatever comes back:

- Is the bound on `|s n|`, or only on `s n` (bounded above, not bounded)?
- Does the bound come before or after the `∀ n`? With `∀ n, ∃ M, |s n| ≤ M`
  every sequence is bounded, since `M` may depend on `n`.
- Is `M` required to be positive, or nonnegative? It need not be, but an
  assistant may add it.

Then ask for a proof. A direct `ε`–`N` proof needs a maximum over the finitely
many terms before `N`, which is longer than anything in this session; the
reference proof in `Solutions.lean` instead moves to Mathlib's `Tendsto`
through the equivalence proved in the demo and uses two library facts. -/

/-- A convergent sequence is bounded. -/
theorem bounded_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (hs : ConvergesTo s a) :
    ∃ M : ℝ, ∀ n, |s n| ≤ M := by
  sorry

#print axioms bounded_of_convergesTo

/-! ## Task 3 — Ask for a proof of something false

Statement (iii) of the exercises' Part A says that `s` comes within `ε` of
`a` infinitely often. It does not imply convergence. Prompt:

    Prove this in Lean 4 with Mathlib. Give only the code.

    theorem convergesTo_of_frequently {s : ℕ → ℝ} {a : ℝ}
        (h : ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |s n - a| < ε) : ConvergesTo s a

Possible outcomes: the assistant says the statement is false (and may or may
not name the counterexample `(-1)^n` with `a = 1`); it produces a proof that
does not compile; or it produces something that compiles. In the last case,
`#print axioms` is the first thing to run. `Solutions.lean` proves that
`(-1)^n` satisfies the hypothesis with `a = 1` and does not converge to `1`,
so no proof of the statement can exist without an added axiom. -/

theorem convergesTo_of_frequently {s : ℕ → ℝ} {a : ℝ}
    (h : ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |s n - a| < ε) : ConvergesTo s a := by
  sorry

#print axioms convergesTo_of_frequently

/-! ## What the check checks

`#print axioms` on a theorem lists what the proof rests on. The expected list
is `propext`, `Classical.choice`, `Quot.sound`. Anything else is a flag:
`sorryAx` means a hole; `Lean.trustCompiler` means `native_decide` or
`decide +native` was used and the compiler is being trusted (session 1).

What the check does not cover is the statement. Lean certifies that the
proof establishes the theorem as written; whether the theorem as written is
the one that was meant is Task 2, and nothing in the toolchain answers it. -/
