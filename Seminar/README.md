# Sessions

One folder per meeting. 

Every `.lean` file states in its header which Lean and Mathlib versions it was
checked against, and which tactics it introduces.

Work through experiments in `MyWork/`, not here — copy the file over. That is
what keeps `git pull` from ever conflicting with what you have written.

## Index

| | Session | What it is about |
|---|---|---|
| 00 | [Install check](Session00_Install/) | One file that proves your installation works. Not a session. |
| 01 | [A brief demo](Session01_Demo/) | A tour: counterexamples, the interface, junk values, vacuous truth, quantifier order, `#print axioms`, and some real theorems. |
| 02 | [One colon](Session02_Colons/) | The colon as the typing relation; propositions as types; one function type, with `→` as the unused-binder case; application and parentheses; the proof state, and the tactics that transform it. Appendix, plus `Extras.lean` on where the correspondence between data and propositions breaks down. |

*Sessions are added as they are written; this index is the place to look for
what exists.*
