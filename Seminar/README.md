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
| 03 | [Logic](Session03_Logic/) | The rest of session 2 in shorter form — `∀` and `→` as one construct, application, the proof state, the four tactics — then the connectives `∧ ∨ ¬ ↔ ∃` and the tactics that prove and use them. Exercises start the parity ladder that ends at the irrationality of √2 in session 5. |
| 04 | [Equations](Session04_Equations/) | `rw`, `calc`, `ring`, `norm_num`, `linarith`, `simp` and `omega`; what totality costs — truncated subtraction, division by zero, `√(-1) = 0`; and the cancellation step the √2 argument needs. |

*Sessions are added as they are written; this index is the place to look for
what exists.*
