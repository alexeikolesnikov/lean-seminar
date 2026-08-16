/-
Session 00 — Smoke test
Lean 4.33.0 · Mathlib v4.33.0 · checked 2026-08-16

Purpose: confirm that Lean, Mathlib, and the VS Code Infoview are all working.
If every line below is free of red squiggles and the Infoview shows a goal
state, the installation is complete.

Tactics introduced: `linarith`, `exact?`, `grind`, `plausible`.
-/
import Mathlib

/-! ## 1. Unicode input and a first proof

Type `∀` as `\forall`, `ℝ` as `\R`, `→` as `\to`, `≤` as `\le`, `↦` as `\mapsto`.
Hover over any symbol to see how to type it.

Click at the end of the next line. The Infoview on the right should show

    a b : ℝ
    h : a ≤ b
    ⊢ a + 1 ≤ b + 2

`linarith` closes goals that follow from linear arithmetic over an ordered
field, given the hypotheses in context. -/
example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 2 := by linarith

/-! ## 2. Asking Lean to find the lemma

`exact?` searches Mathlib for a lemma closing the goal and reports its name.
Here it finds `Nat.add_comm`. Using the name it gives you, rather than leaving
`exact?` in place, is the habit worth forming: the search is slow, the lemma is
instant, and the name is what you actually learn. -/
example (a b : ℕ) : a + b = b + a := by exact Nat.add_comm a b

/-! ## 3. Automation on equational goals

`grind` is SMT-style automation in recent Lean core. Here it chains the two
hypotheses by transitivity without being told to. -/
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c := by grind

/-! ## 4. Looking for counterexamples instead of proofs

`plausible` tests a statement on random inputs and reports a counterexample if
it finds one. The statement below is **false** at `n = 0`, so this line is left
commented out — uncommenting it makes the file fail to compile, which is the
point of the demo.

    example (n : ℕ) : n < 2 * n := by plausible

reports:

    Found a counter-example!
    n := 0
    issue: 0 < 0 does not hold

The true statement needs `0 < n`, and then `plausible` finds no counterexample
and leaves the goal open — it is a refutation tool, not a proof tool, so the
proof below is done by `omega`. -/
example (n : ℕ) (hn : 0 < n) : n < 2 * n := by omega
