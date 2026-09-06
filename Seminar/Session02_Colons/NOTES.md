# Session 02 — One colon, four tactics

Instructor notes. Not for participants.

Checked against Lean 4.33.0 / Mathlib v4.33.0. Every output quoted below was
produced by the pinned toolchain.

**Goal.** By the end, participants can read a colon in a Lean file and say what
it asserts, and can close a goal with `exact`, `apply`, `intro` or `rfl`
knowing why that tactic was the one to use.

**Why this shape.** The topic came from the room, and it coincides with the
syllabus's own line for this week ("propositions as types, stated once,
lightly"). The four tactics scheduled for today are each an operation on the
typing relation, so the notation material supports the tactics material rather
than competing with it for time.

---

## The organising claim

> There is one colon. It means **has type**.
> Everything else that looks like a colon is a different token.

Section 1 of the demo is evidence for it; section 2 states the consequence.

---

## Arc (75 min)

| Time | | |
|---|---|---|
| 0:00 | Recap; Natural Number Game check-in | 5 |
| 0:05 | §1–3 the colon tour, propositions as types, the two imposters | 15 |
| 0:20 | §4 the four tactics, including the `rfl` failure | 20 |
| 0:40 | Exercises A–C, in pairs | 30 |
| 1:10 | §5 the judgement beat | 5 |

§5 is placed at the end rather than the middle. It requires no tactic knowledge
and so survives the exercises running long. If the room is moving quickly, take
it before the exercises instead.

**Recap wording.** Last week's sentence: *Lean's kernel certifies that a proof
establishes a statement; nothing checks that the statement is the theorem you
meant.* Then: today is about the notation both are written in, which turns out
to be one notation rather than two.

---

## The three points that carry the session

### 1. Propositions as types (§2)

Put these two lines on screen together:

```
2           : ℕ
two_add_two : 2 + 2 = 4
```

They are the same relation. `ℕ` is a type and `2` is a term of it;
`2 + 2 = 4` is a type and `two_add_two` is a term of it. A proposition is a
type, a proof is a term, and proving is constructing.

Everything before this is setup and everything after is consequence, so it is
worth giving time to.

### 2. The rehearsed failure (§4)

Uncomment `example (n : ℕ) : 0 + n = n := rfl`:

```
Type mismatch
  rfl
has type
  ?m.9 = ?m.9
but is expected to have type
  0 + n = n
```

The compiler states the day's point in the day's vocabulary: it needed `rfl`'s
type to be the goal. Ask why `n + 0 = n` worked and this did not before
explaining — participants who did the Natural Number Game have met this, and
the answer is better coming from them.

Answer: `Nat.add` recurses on its second argument, so `n + 0` reduces
immediately while `0 + n` is stuck on an unknown `n`.

### 3. The judgement beat (§5)

```
#check ((n - m : ℕ) : ℤ)      -- ↑(n - m) : ℤ
#check ((n : ℤ) - (m : ℤ))    -- ↑n - ↑m  : ℤ
```

Ask which one is "subtract the naturals" before revealing anything. Then
`#eval` both at `n = 0, m = 1` (`0` and `-1`), then uncomment the `plausible`
line:

```
Found a counter-example!
n := 0
m := 4
issue: 0 = -4 does not hold
```

The point: the tool reports the failure without anyone having to notice it
first, as in session 1, and the subject here is notation rather than a theorem.
The fix is not a better proof but the hypothesis `m ≤ n`, which is mathematical
content that the colon placement was implicitly asserting.

---

## Predicted friction

- **"Is `(2 : ℝ)` a cast?"** No. It says to build the numeral with `ℝ` as the
  expected type, so Lean produces a real from the start; nothing is converted
  afterwards. Calling it a cast makes §5 harder to explain, because the point
  there is that the colon is chosen *before* the subtraction happens and
  determines which subtraction happens. §1 of the demo defines elaboration and
  §5 defines coercion, so both words are available by the time they are needed.
- **`↑` on the projector.** The arrows carry §5 and are small; increase font
  size beforehand. `set_option pp.numericTypes true` annotates numerals with
  their types (`(2 : ℝ) : ℝ`) and can help, at the cost of more noise
  elsewhere. `set_option pp.coercions false` is counterproductive here: it
  renders `↑(n - m)` as `(n - m).cast`. Leave coercions displayed.
- **`#check Nat.add_comm` vs `#check @Nat.add_comm`.** Two displays of one
  type. Show it once so that neither shape is unfamiliar later; there is no
  need to explain the elaborator.
- **Someone will ask what `Type` is.** That is §7.1, below the divider. Say it
  is there and that it is optional — see below.
- **The `::` imposter does not demonstrate well.** `#check (1 :: [2, 3])`
  prints `[1, 2, 3] : List ℕ`, so the cons does not appear in the output. Make
  the point in words.

## Containing the type theory

The main risk today. The audience is mathematicians, the foundations are
interesting, and the hour can be spent on universes without anyone learning
`apply`. The appendix (§7) exists to hold that material: `Prop`/`Type`/`Sort`
and the universe hierarchy, proof irrelevance, `∀` as primitive with `→` as
abbreviation, `@Nat.rec` as the induction principle, and definitional versus
propositional equality. It sits below a divider and is marked as not part of
the session.

Suggested response in the room: the question has an answer, it is in §7 of the
file with runnable code, and it is not on today's path. Anyone who wants to
pursue it can do so on their own machine.

---

## Two routes, one room

Lab is the browser (`live.lean-lang.org`); personal experimentation is VS Code.

1. **Teach `No goals` as the done-signal, not the checkmark.** "Goals
   accomplished" is a VS Code gutter decoration and lean4web does not draw it;
   `No goals` is what the Infoview prints on both routes. This is the session
   that introduces the Infoview as the whole interface, so it is where a split
   would otherwise be created (see `13-weblink-and-the-web-editor.md`).
   Consider setting `lean4.goalsAccomplishedDecorationKind` to `Off` on the
   demo machine so the projector matches the lab.
2. **The appendix is VS Code material.** §7.2–7.3 involve `Sort u_1` and
   universe metavariables, which are easier to read with hover available.

**Web editor caveat.** live.lean-lang.org serves the latest Mathlib rather than
the pinned v4.33.0, and this session reads exact `#check` output aloud more
than previous ones. The coercion display in §5 is the exposed part. Click the
link before the session:

```
bash scripts/weblink.sh Seminar/Session02_Colons/Demo.lean
```

If `↑(n - m)` renders differently upstream the beat still works — the two terms
remain visibly different — but the narration will need adjusting.

---

## Exercises

Parts A–C are the session; D is optional and is the first time anyone is asked
to find a Mathlib lemma unaided (`exact?`), which anticipates session 6 rather
than being required today.

Seventeen holes, of which B1–B6 are one line each and exist to make the goal
window move. Two worth walking through at the end if time allows:

- **C3** (`0 + n = n`), where the failure of `rfl` is the content.
- **A1's commented `plausible` line**, if §5 was cut for time.

Solutions are published; reading them is not cheating.

---

## Before next time

*Mathematics in Lean* §2. Session 3 is logic — `∀ ∃ → ¬ ∧ ∨ ↔` and the tactics
that manipulate them — and assumes today's editor loop is fluent, so the B
exercises matter more than their length suggests.
