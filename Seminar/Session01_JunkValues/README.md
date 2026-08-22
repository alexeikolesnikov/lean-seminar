# Session 01 — what a formal statement does and does not say

**The claim of the hour:** a proof assistant checks that a proof establishes a
statement. Nothing checks that the statement says what you meant. That second
job is mathematical work, it does not go away, and it is the part you cannot
delegate to a machine.

The demonstration runs on arithmetic everyone in the room already knows.

1. **Every function in Lean is total.** `1/0` and `3 - 5` must return
   *something* in `ℕ`, and Mathlib picks `0` for both. These are called junk
   values. They are not a bug; they are the price of a simple logic.
2. **A statement that is false.** `a - b + b = a` over `ℕ` fails at
   `a = 0, b = 1`, and `plausible` finds the counterexample in seconds.
3. **A statement that is trivially true, which is worse.** The Archimedean
   property, written the way anyone would write it on a board — *for every
   ε > 0 there is N with 1/N < ε* — is provable in Lean by taking `N = 0`,
   because `1/0 = 0 < ε`. It compiles. It goes green. It has nothing to do with
   Archimedes. Note how Mathlib states its own version, with `n + 1`, to dodge
   exactly this.
4. **The same thing at the top of the subject.** `ζ` has a pole at `s = 1`, so
   Lean's `ζ` returns a junk value there. Had that value been `0`, `s = 1`
   would be a zero of the formal `ζ` off the critical line and the formal
   Riemann Hypothesis would be trivially *false* while looking exactly like RH.
   That it is not zero is a small theorem somebody had to prove.
5. **`#print axioms`**, which tells you what a proof depends on — and says
   nothing whatever about whether `riemannZeta` is the Riemann zeta function.

**Tactics introduced:** `#eval`, `#check`, `simp`, `positivity`,
`exact_mod_cast`, `plausible`, `#print axioms`.

**Assumes:** nothing. This is the first session.
