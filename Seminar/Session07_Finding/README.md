# Session 07 — Finding lemmas

Mathlib has about 250,000 named theorems, and almost everything a first
course in linear algebra proves is among them. This session is about finding
the one you need and reading what comes back: `exact?`, `apply?`, `simp?`,
`hint`, `rw?`, the `#check` command, Mathlib's naming convention, and the two
search services Loogle and LeanSearch.

The mathematics is matrices over `ℝ`: determinants, traces, transposes,
inverses, similarity, nilpotent matrices. The exercises are problems and
conjectures rather than a list of lemmas to look up: the search tools are
what one reaches for in the course of a proof. No new proof tactics; the
tactics of sessions 3–5 are enough once the lemmas are found.

## Files

| File | Contents |
|---|---|
| `Demo.lean` | Matrices in Lean; `exact?` and how to read its answer; the naming convention; what an `exact?` failure means; `simp?`, `hint`, `rw?`; Loogle and LeanSearch; reading hypotheses (the 0×0 matrix, the total inverse, `AB = I ⇒ BA = I`). Three rehearsed failures. |
| `Exercises.lean` | Part I: five problems stated without lemma names (`det (AᵀA) ≥ 0`; `AB = I ⇒ det A ≠ 0`; similarity invariance of trace and determinant; a nilpotent 2×2 matrix has trace and determinant 0; `A² = 0 ⇒ I + A` invertible). Part II: twelve conjectures about 2×2 matrices to decide, then prove or refute. Cayley–Hamilton for 2×2 is provided. |
| `Solutions.lean` | Every problem proved and every conjecture settled, with the lemma `exact?` returns named in a comment and the decomposition stated in words. |
| `NOTES.md` | For whoever leads the meeting. |

## In the browser

Open the demo in the Lean web editor, no account or install needed:

<https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Falexeikolesnikov%2Flean-seminar%2Fmaster%2FSeminar%2FSession07_Finding%2FDemo.lean>

And here is the link to the Exercises:
<https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Falexeikolesnikov%2Flean-seminar%2Fmaster%2FSeminar%2FSession07_Finding%2FExercises.lean>


The web editor runs the current Mathlib rather than the seminar's pinned
version. For this session that matters more than usual: the names `exact?`
returns there may differ from the ones in the comments, since names are what
changes between versions. The proofs were checked against the pinned version.

Copy `Exercises.lean` into `MyWork/` before editing, or paste it into the
web editor.

**Assumes:** `intro`, `exact`, `apply`, `obtain` from session 3; `rw`,
`calc`, `ring`, `norm_num`, `linarith`, `simp` from session 4; `decide` from
session 5.

**Imports.** The files import all of Mathlib. `exact?` searches only what is
imported, so a file with narrow imports finds less; for this session the full
import is the point, and the 30–90 second load is the price.

**Network.** `#loogle` and `#leansearch` send the query to a web service. They
work in a Codespace and in a local install with a network connection; the
demo file has them in comments with the recorded output, and the web pages
<https://loogle.lean-lang.org> and <https://leansearch.net> do the same job
from a browser.

**Homework:** Problem 4 and whatever remains of Part II; Problem 5 is
optional. *Mathematics
in Lean* §2.1 has the same naming conventions described for real numbers, and
the community guide
<https://leanprover-community.github.io/blog/posts/searching-for-theorems-in-mathlib/>
covers every tool in this session in more detail. The next session is on
definitions and structures — how Mathlib says what a group, a ring, or a
vector space is.
