# Session 03 — The rest of the syntax, and logic

Instructor notes. Not for participants.

Checked against Lean 4.33.0 / Mathlib v4.33.0. Every output quoted below was
produced by the pinned toolchain.

**Goal.** By the end, participants can prove and use a statement built from
`∧`, `∨`, `¬`, `↔` and `∃`, and can say which tactic belongs to which side of
that distinction. The session 2 material that was not reached is closed out
rather than re-taught.

---

## The demo does not fit in 75 minutes, again

Measured from the file: §0 is 35 lines, §1 63, §2 59, §3 103, §4 40, §5 102,
§6 38, §7 12. Presented at the pace the room followed in session 2:

| | | min |
|---|---|---|
| 0:00 | Recap and questions from the reading | 10 |
| 0:10 | §0 what a proof rests on, §1 `∀`/`→`, binders | 15 |
| 0:25 | §2 application, parentheses, dot notation | 8 |
| 0:33 | §3 proof state and the four tactics | 20 |
| 0:53 | §4 coercion beat | 5 |
| 0:58 | §5 the connectives | 20 |
| 1:18 | — | |

That is the demo alone, over time, with §6 unplaced and no exercise time.

**The recommendation: do not present §1–§4.** The homework asked participants to
read the rest of session 2's demo and bring questions, and §1–§4 is that same
material in shorter form. Run those four sections as questions from the floor,
with the file on screen to answer from. Budget 15 minutes for the lot, and if
no questions come, move on rather than filling the time.

| | | min |
|---|---|---|
| 0:00 | Recap; §0, including the trust question if it is raised again | 10 |
| 0:10 | §1–§4 as questions from the reading, file on screen | 15 |
| 0:25 | §5 the connectives, live | 25 |
| 0:50 | Exercises A and C in pairs | 15 |
| 1:05 | §6 quantifier order and vacuous hypotheses | 7 |
| 1:12 | Close; set the homework | 3 |

§6 sits after the exercises deliberately: it is the judgement beat, it is
self-contained, and if the pairs run long it can be cut to the two statements
without losing the session.

If the questions in the second block turn into a re-teach of §3 — which is the
likeliest way this session goes wrong, since §4 of session 2 was never
demonstrated — let it happen and cut §5 to `∧`, `∃` and `¬`, leaving `∨` and
`↔` to the exercises. The connectives are parallel enough that three of them
teach the pattern.

## What each part of the exercises is for

- **A** is reading, not proving. It is the only part that works before anyone
  can prove anything, and it is a discussion exercise: expect ten minutes for
  three items in a room that argues.
- **B** is `use` and `obtain` on their own.
- **C** is the four remaining connective tactics, with no mathematics in the
  way.
- **D** is negation, and the one part with a step nobody will produce unaided —
  see below.
- **E** is the same shape as B, twice, and the content is the choice of witness.
- **F** is the rung the √2 argument uses. It should be walked through at the
  end if time allows.
- **G** is optional and reuses what is above.
- **H** is prose. Nothing to do.

**Part A answers.** A1 is **(i)**; (ii) is the converse, which is Part F, and
(iii) claims every number is even. A2 is **(ii)**; (i) says every even number
exceeds 100, and (iii) is true but vacuous — `n = 1` is not even, so the
implication holds while saying nothing. A3 is **(i)**; (ii) is the inverse,
not the contrapositive, and (iii) is true by a different route.

## Predicted friction

- **`subst` is introduced in the homework, not the demo.** It is needed from B3
  onwards, because without `rw` there is no other way to use `hk : n = 2 * k`
  inside a goal. Put one line of it on screen when setting the exercises rather
  than leaving it to the hint.
- **`hk.symm.trans hj` in Part D.** This is the step to walk through at the
  end. `hk` says `n = 2 * k`; `hk.symm` says `2 * k = n`; `.trans hj` composes
  with `hj : n = 2 * j + 1`. It follows from the demo's `h.symm`, but the
  composition is a jump.
- **`use` closing goals silently.** `use 5` on `IsEven 10` finishes, because
  `10 = 2 * 5` is a computation; `use (k + 1)` in B3 leaves a goal. Expect
  "why did that one finish?" and have §3's `rfl` discussion ready.
- **The bullet `·`.** Typed as `\.` in VS Code. People will use `.` or omit it;
  the proof still compiles without bullets, which is worth saying once, along
  with why the file uses them.
- **The trust question may return.** The README section answers it in prose.
  If it comes up mid-session, `#print axioms` in §0 is the five-minute version;
  the rest belongs to session 12.

## Web editor

The link in the README points at the demo through live.lean-lang.org. That
service serves the current Mathlib, not v4.33.0. The demo's narrow import set
and everything it uses are old and stable, so this has not bitten yet, but a
file that fails there and compiles locally is a version difference, not a
mistake.

## Before next time

Session 4 is written: `Seminar/Session04_Equations/`. It introduces `rw`,
`calc`, `ring`, `norm_num`, `linarith`, `simp` and `omega`, and its exercises
carry the √2 thread to the statement that no minimal counterexample exists.
`omega` was moved forward from session 5 to do the cancellation there.
