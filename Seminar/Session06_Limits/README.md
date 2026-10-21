# Session 06 — Sequences and limits

A sequence of real numbers is a function `s : ℕ → ℝ`, and `s n` is its
`n`-th term. This session defines convergence in the ε–N form,

    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - a| < ε

proves the first facts about it, and ends by checking that this is the same
statement as Mathlib's `Filter.Tendsto s Filter.atTop (nhds a)`.

No new tactics. Each quantifier in the definition is handled by a tactic from
session 3 (`intro` for `∀`, `use` for `∃`, `obtain` to take apart a hypothesis
of that shape), and the estimates are `calc` blocks from session 4 with
`linarith`, `gcongr` and the triangle inequality `abs_add_le`.

## Files

| File | Contents |
|---|---|
| `Demo.lean` | The definition; a constant sequence; `1/(n+1) → 0`; the limit of a sum; uniqueness of limits; the comparison with Mathlib. Two rehearsed failures. |
| `Exercises.lean` | Parts A–G: a reading exercise on quantifier order, then the algebra of limits, the squeeze theorem, two variants of the definition, and the statement with the quantifiers swapped. |
| `Solutions.lean` | Every exercise proved, and the three tasks below. The Part A answers are in the comments. |
| `Assistant.lean` | Three tasks for an AI assistant — ask for a proof, ask for a statement, ask for a proof of something false — each with a `#print axioms` line under it. |
| `GitHub_Copilot_Notes.md` | For whoever leads the meeting. |

## In the browser

Open the demo in the Lean web editor, no account or install needed:

<https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Falexeikolesnikov%2Flean-seminar%2Fmaster%2FSeminar%2FSession06_Limits%2FDemo.lean>

The web editor runs the current Mathlib rather than the seminar's pinned
version, so the output of a `#check` may differ in detail from what the
comments say. The proofs were checked against the pinned version.

Copy `Exercises.lean` into `MyWork/` before editing, or paste it into the
web editor.

**Assumes:** `intro`, `exact`, `apply`, `obtain`, `use`, `rcases`,
`by_contra` from session 3; `rw`, `calc`, `ring`, `linarith`, `norm_num` from
session 4; `gcongr`, `positivity` from session 5.

**From session 5:** §4 (the bound on `∑ 1/(k+1)²`) and §5 (strong induction
and the end of the √2 argument) of its demo were not reached in the meeting.
Read them; the √2 finish is also exercises E1–E2 of session 5, with
solutions.

**Homework:** *Mathematics in Lean* §3.6 (sequences and convergence), which
proves the same results with the same definition. Exercises B1–B3, C1–C2, D1
and E1–E2; the rest optional. If `Assistant.lean` Task 2 was not reached in
the meeting, its statement question is homework as well. The next session is
on finding lemmas in
Mathlib: `exact?`, `apply?`, Loogle and the naming conventions. G2 is a
preview, and so is the `exact?` call in `NOTES.md`.
