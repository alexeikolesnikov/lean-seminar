# Session 02 — one colon, four tactics

Several people asked, in different words, what the colons in a Lean file mean.
This session is the answer.

The claim it is organised around:

> The colon has only one meaning; you can read it as "has type".
> Everything else that looks like a colon is a different token.

A proposition is a type, a proof is a term of that type, and therefore proving
something is constructing a term of the right type. The four tactics of the day
— `exact`, `apply`, `intro`, `rfl` — are four operations on that relation.

Here's the session if you want to start it on the Lean server (a little slow,
but requires no installation work): https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Falexeikolesnikov%2Flean-seminar%2Fmaster%2FSeminar%2FSession02_Colons%2FDemo.lean

## What is in the file

| | |
|---|---|
| §1 | The colon tour: everything has a type, `ℕ`/`ℤ`/`ℝ` as separate types, what elaboration is, and `:=` |
| §2 | Propositions are types; one function type, with `→` as the unused-binder case; implicit versus explicit binders |
| §3 | Parentheses, commas, application, dot notation |
| §4 | The proof state; `exact`, `apply`, `intro`, `rfl`, `have`, `show`; how to read a type error; `sorry` |
| §5 | Does this say what it claims? — coercion placement and `ℕ` subtraction |
| §6 | Summary |
| §7 | Appendix; not part of the session |

`Extras.lean` in this folder carries the appendix further — where the
data/proposition correspondence breaks down — and belongs to no session.

## Notes

- **§3–§5 carry `NOW TRY THIS` blocks**, as in session 1: at your own keyboard,
  ten seconds each, written so that following them literally produces what the
  text says.
- **In mathematics `ℕ ⊆ ℤ ⊆ ℝ`; in Lean they are separate types.** `2` has a
  default type and can be asked for at another one. §1 works through what that
  request actually does.
- **`(2 : ℝ)` is not a cast.** It says to build the numeral with `ℝ` as the
  expected type, so Lean produces a real number from the start rather than
  converting a natural one. §1 defines elaboration; the distinction is what §5
  turns on.
- **`:=` is a single token**, not a colon followed by an equals sign. §1 takes
  apart `theorem two_add_two : 2 + 2 = 4 := rfl` on that basis.
- **§2 covers `{}` versus `()`.** Most Mathlib lemmas take their variables
  implicitly, and `@` is what makes them explicit again. You have already met
  one: `Nat.sub_add_cancel` in session 1.
- **§4 is where the Infoview gets used.** A proof in progress is a context and
  a goal, and every tactic transforms that pair. Move the cursor down a tactic
  block and watch it. `trace_state` prints the state without needing a cursor,
  which is what to use in the browser editor.
- **§4 ends with `sorry`.** It has whatever type is expected of it, so it
  satisfies the colon everywhere and a file full of it compiles — including a
  proof of `2 + 2 = 5`. Only `#print axioms` tells you.
- **§7.3 shows proof irrelevance concretely.** `#print` on three proofs of
  `2 + 2 = 4` — by `rfl`, by `ring`, by `decide` — displays three unrecognisably
  different terms, and then proves them equal.
- **The §3 `NOW TRY THIS` produces no error, and that is the point.**
  `#check double -1` prints `double - 1 : ℤ → ℤ`. Lean read it as the function
  `double` minus the constant function `1`, subtracted pointwise — legal, and
  not what anyone meant. A negative argument needs `double (-1)`.
- **The `rfl` failure in §4** prints `rfl`'s type next to the goal's type.
  Uncomment it, read it, put the dashes back. It is worth reading structurally:
  almost every type error names the term, the type it has, and the type
  expected. The asymmetry it exposes — `n + 0 = n` closes by `rfl` and
  `0 + n = n` does not — is the one from the Natural Number Game.
- **§5 is the judgement beat.** `↑(n - m)` and `↑n - ↑m` differ only in where
  the colon sits, and the first truncates at zero. `plausible` finds the
  counterexample; nobody has to spot it.
- **`No goals` is the success message**, in the browser and in VS Code alike.
  The margin checkmark is a VS Code decoration and the web editor does not draw
  one, so there is no confirmation to look for beyond `No goals`.
- **§7 is an appendix and is not part of the session.** It covers `Prop`,
  `Type`, `Sort` and the universe hierarchy, proof irrelevance, `∀` as the
  primitive with `→` as an abbreviation, `@Nat.rec`, and definitional versus
  propositional equality. Run it in VS Code, where you can hover over things.
  Nothing later in the semester depends on it.
- **`Solutions.lean` and `Extras.lean` contain no holes.** `Demo.lean`
  declares `CI: allow-sorry (1)` — the deliberate one in §4 — and
  `Exercises.lean` declares `CI: allow-sorry (21)`; one more hole in either
  would fail the build.
- **The exercises are in seven parts.** A–E are the session, F needs no proof,
  G is optional. Each part of `Solutions.lean` closes with a note headed "What
  this was for". Do the part first; the note is worth more after you have been
  surprised by something than before.
- Work in `MyWork/`, not here — copy the exercise file over first, so that
  `git pull` does not conflict with your work.

**Tactics introduced:** `exact`, `apply`, `intro`, `rfl`, `have`, `show`, `trace_state`.

**Assumes:** `#check`, `#eval`, `plausible` from session 1, and enough of the
Natural Number Game that `0 + n = n` is familiar.

**Homework:** *Mathematics in Lean* §2, and parts A–E of the exercises. Session
3 is logic and assumes today's editor loop is fluent, so part C matters more
than its length suggests.
