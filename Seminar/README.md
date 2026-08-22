# Sessions

One folder per meeting. Each contains up to four files:

| File | What it is |
|---|---|
| `Demo.lean` | what gets typed live, in the order it gets typed, with narration in comments |
| `Exercises.lean` | statements to prove yourself; `sorry` marks each gap |
| `Solutions.lean` | the same statements, fully proved |
| `Notes.md` | the arc of the session and what the tactics do, in words |

Every `.lean` file states in its header which Lean and Mathlib versions it was
checked against, and which tactics it introduces.

Work through the exercises in `MyWork/`, not here — copy the file over. That is
what keeps `git pull` from ever conflicting with what you have written.

## Index

| | Session | What it is about |
|---|---|---|
| 00 | [Install check](Session00_Install/) | One file that proves your installation works. Not a session. |
| 01 | [What does a machine-checked proof certify?](Session01_Demo/) | A tour: counterexamples, the interface, junk values, vacuous truth, quantifier order, `#print axioms`, and two real theorems. |

*Sessions are added as they are written; this index is the place to look for
what exists.*
