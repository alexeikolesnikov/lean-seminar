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
| §1 | The colon tour: everything has a type, `ℕ`/`ℤ`/`ℝ` as separate types, what elaboration is, `:=`, and a first look at proof irrelevance |
| §2 | Propositions are types, and the two ways Lean displays a theorem |
| §3 | Parentheses, commas, application, dot notation |
| §4 | `exact`, `apply`, `intro`, `rfl` |
| §5 | Does this say what it claims? — coercion placement and `ℕ` subtraction |
| §6 | Summary |
| §7 | Appendix; not part of the session |

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
  apart `theorem two_add_two : 2 + 2 = 4 := rfl` on that basis. `::`, the other
  token containing a colon, is list cons and is unrelated.
- **§1 shows proof irrelevance concretely.** `#print` on three proofs of
  `2 + 2 = 4` — one supplied as the term `rfl`, two produced by the `ring` and
  `rfl` tactics — displays three different terms that the kernel treats as the
  same. §7.1 says why that is so.
- **The §3 `NOW TRY THIS` produces no error, and that is the point.**
  `#check double -1` prints `double - 1 : ℤ → ℤ`. Lean read it as the function
  `double` minus the constant function `1`, subtracted pointwise — legal, and
  not what anyone meant. A negative argument needs `double (-1)`.
- **The `rfl` failure in §4** prints `rfl`'s type next to the goal's type.
  Uncomment it, read it, put the dashes back. The asymmetry it exposes —
  `n + 0 = n` closes by `rfl` and `0 + n = n` does not — is the one from the
  Natural Number Game.
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
- **`Demo.lean` and `Solutions.lean` contain no holes** and are checked with
  plain `leancheck.sh`. `Exercises.lean` declares `CI: allow-sorry (17)` in its
  header; an eighteenth hole would fail the build.
- Work in `MyWork/`, not here — copy the exercise file over first, so that
  `git pull` does not conflict with your work.

**Tactics introduced:** `exact`, `apply`, `intro`, `rfl`, `have`, `show`.

**Assumes:** `#check`, `#eval`, `plausible` from session 1, and enough of the
Natural Number Game that `0 + n = n` is familiar.

**Homework:** *Mathematics in Lean* §2. Session 3 is logic and assumes today's
editor loop is fluent, so exercises B1–B6 are worth completing.
