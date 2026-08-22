# Session 00 — install check

Not a session. One file, `Smoke.lean`, whose only job is to tell you whether
Lean, Mathlib, and the VS Code Infoview are all working.

Open it, wait for the orange progress bar at the top of the editor to finish —
30 to 90 seconds the first time, while Mathlib loads into memory — and click at
the end of the `linarith` line on the first example. The **Lean Infoview**
panel should appear on the right showing

```
a b : ℝ
h : a ≤ b
⊢ a + 1 ≤ b + 2
```

If you see that, your installation is complete and that panel is the entire
interface.

The file also demonstrates four things worth meeting on day one: unicode input,
`exact?` (which finds a Mathlib lemma and tells you its name), `grind`
(automation on equational goals), and `plausible` (which looks for
counterexamples rather than proofs). The `plausible` example is commented out
deliberately — uncommenting it makes the file fail, which is the demonstration.

Setup instructions: [`../../handouts/setup-guide.md`](../../handouts/setup-guide.md).
