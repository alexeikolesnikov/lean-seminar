# Session 06 — notes for whoever leads the meeting

Written for a meeting Alexei cannot attend in person. Two arrangements are
covered: Alexei joins by video call and runs the demo from his screen
(**arrangement R**), or a participant leads from this file (**arrangement S**).
The material is the same; the difference is who types.

Everything in `Demo.lean` has been compiled against Lean 4.33.0 / Mathlib
v4.33.0, and every error message quoted below was produced by that toolchain.
Nothing in the file needs to be invented or improvised during the meeting.

## Before the meeting

- **Click the web-editor link in `README.md`** the day before and again an
  hour before. The editor runs the current Mathlib, which may differ from the
  pinned version. If the file fails to open, the one fix that does not need
  Lean knowledge is to replace the first line of the file with `import
  Mathlib` (it already is; the failure would then be upstream and the
  fallback is a local VS Code on one laptop).
- The first load takes 30–90 seconds while Mathlib is read. Open the link
  before people arrive.
- Zoom the browser to 150% or more. The proof state panel on the right is
  the thing the room needs to read; the code on the left is secondary.
- Have `Solutions.lean` open in a second tab. Opening it during the meeting
  is allowed; the solutions are public and reading them is not cheating.

### Arrangement R — Alexei remote

- A 15-minute test call before the start: audio both ways, Alexei's screen
  on the projector, and one laptop in the room with the same web-editor link
  open. If the call drops, the room continues from that laptop and the
  in-room host takes over the script below.
- Alexei shares the browser tab, not the whole screen.
- The in-room host runs the pairs section (0:37–1:05): walks around,
  listens for the places people are stuck, and collects two or three of
  them for the walk-through at 1:05. On a call, Alexei cannot hear the
  pairs; the host is the connection.
- Questions from the floor are repeated by the host before Alexei answers
  them; a room microphone rarely picks them up.

### Arrangement S — a participant leads

- The script below says what to type and what to say. Typing the proofs
  line by line is better than scrolling through the finished file: the
  proof state after each line is the content of the session.
- If a line produces an error that is not one of the rehearsed ones, the
  likely cause is a typo (a missing `:`, a `(` for a `⟨`). Compare with the
  file. If that does not resolve it in a minute, scroll to the finished
  version in the file and continue from there. Nobody expects a live
  recovery.
- Questions you cannot answer: write them down for Alexei. The list at the
  end of this file covers the ones that came up when the material was built.

## Timing (75 minutes)

| | Section | Minutes |
|---|---|---|
| 0:00 | Where session 5 left off; the sentence-to-tactic table (§0) | 5 |
| 0:05 | The definition and the constant sequence (§1) | 10 |
| 0:15 | `1/(n+1) → 0`, with the ℕ-division point and the first rehearsed failure (§2) | 12 |
| 0:27 | The limit of a sum, with the second rehearsed failure (§3) | 10 |
| 0:37 | Exercises in pairs: B1, B2, B3 | 20 |
| 0:57 | Walk through B3 (or whichever one stopped the most pairs) | 5 |
| 1:02 | The same definition in Mathlib (§5) | 3 |
| 1:05 | With an assistant: `Assistant.lean`, Tasks 1 and 3 (Task 2 if time) | 10 |

This is the plan with the assistant segment, which is Alexei's to run over
the call; it exists because the room is in the browser and he is not. If the
call is not working at 1:05, the in-room host runs §5 and then C2 from the
exercises instead, and the segment moves to the next meeting. Without the
segment the earlier plan holds: pairs to 1:05 including C2, walk-through 7
minutes, §5 at 1:12.

§4 (uniqueness) is not in the plan. It is in the file with full narration
and in `Exercises.lean` Part F; say that it is there to read. If §3 finishes
early, do §4 rather than starting the pairs early.

The budget is the lesson of session 2, where the demo filled the hour and
the pairs did not happen. If §2 runs past 0:30, cut the ℕ-division point
(the two `#eval` lines and the two `#check` lines) and do it at 1:12 instead.

## Script

### §0 — Where we are (0:00)

Say: session 5 was about finite sums and induction. The meeting stopped
before its §4, a bound on the partial sums `∑_{k<n} 1/(k+1)²`, and §5, the
strong-induction finish of the √2 argument; both are in that folder as
reading, with solutions. The §4 bound ends with "so the series converges",
and the word "converges" was never defined. Today it is, and the tactics
already in hand are enough to prove the first theorems about it.

Show the table in §0 of the demo. Each sentence of a textbook proof of
convergence is one tactic:

| In the written proof | In Lean |
|---|---|
| Let ε > 0. | `intro ε hε` |
| Since `s` converges, choose `N` with … | `obtain ⟨N, hN⟩ := hs ε hε` |
| Take `N := …` | `use …` |
| Let `n ≥ N`. | `intro n hn` |
| Then `|s n − a| = … ≤ … < ε`. | `calc …` |

Say: the proof state after each tactic is the "so far we have" of the written
proof. Hypotheses above the line; what remains to be shown below it.

### §1 — The definition (0:05)

Show the `def`. Two things to say about it:

- `s n`, not `sₙ`: a sequence is a function, and its `n`-th term is the
  function applied to `n`.
- `∀ ε > 0, …` is notation for `∀ ε, ε > 0 → …`. This is why `intro ε hε`
  produces two things.

Then the constant sequence. Type it line by line:

```
example (c : ℝ) : ConvergesTo (fun _ => c) c := by
  intro ε hε
```

Point at the proof state: `c ε : ℝ`, `hε : ε > 0`, and the goal has become
`∃ N, ∀ n ≥ N, |(fun x => c) n - c| < ε`. Say: "Let ε > 0" has been written.

```
  use 0
  intro n hn
```

Goal: `|(fun x => c) n - c| < ε`, with `hn : n ≥ 0` in the context. Say: any
`N` would do; `0` was chosen. The expression `(fun x => c) n` is `c`, but Lean
leaves it as written until asked.

```
  simp only
  rw [sub_self, abs_zero]
  exact hε
```

`simp only` with no lemmas evaluates the function application; the goal is
`|c - c| < ε`, then `|0| < ε`, then `0 < ε`, which is `hε`.

If asked: the `rw` would also have worked without `simp only`; the two goals
differ only in display. `simp only` is there so the room can read the goal.

### §2 — `1/(n+1) → 0` (0:15)

**The ℕ-division point** (3 minutes). Run the two `#eval` lines:

```
#eval (1 / (3 + 1 : ℚ))      -- 1/4
#eval (1 / (3 + 1 : ℕ))      -- 0
```

Division of natural numbers is integer division. Then the two `#check`
lines, which display as

```
fun n => 1 / (↑n + 1) : ℕ → ℝ
fun n => ↑(1 / (n + 1)) : ℕ → ℝ
```

Say: the up-arrow is the coercion from ℕ to ℝ, and its placement relative to
the division decides which sequence this is. The first is `1/(n+1)`. The
second divides in ℕ first and converts afterwards, so it is `1, 0, 0, 0, …`.
Both converge to `0`; only one is the sequence anyone meant. This is the
session 2 rule about the placement of the arrow, in a new setting.

**The Archimedean property.** Run `#check @exists_nat_one_div_lt`. It
displays with a long list of typeclass assumptions and ends

```
… {ε : K}, 0 < ε → ∃ n, 1 / (↑n + 1) < ε
```

Say: the assumptions say `K` is an ordered field with the Archimedean
property; ℝ is one. The conclusion is the fact the proof needs.

**The proof.** Type it:

```
theorem convergesTo_one_div : ConvergesTo (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  use N
  intro n hn
```

Proof state now: `hN : 1 / (↑N + 1) < ε`, `hn : n ≥ N`, goal
`|(fun n => 1 / (↑n + 1)) n - 0| < ε`.

```
  simp only
  rw [sub_zero, abs_of_pos (by positivity)]
```

Goal: `1 / (↑n + 1) < ε`. Say: the absolute value is gone because the
quantity inside is positive, and `positivity` proved that.

```
  calc 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
    _ < ε := hN
```

Say: `gcongr` handles the monotonicity. It compares the two sides, sees that
they differ only in `n` versus `N`, and reduces the goal to `N ≤ n`, which it
finds in the context as `hn`. If `hn` were missing, `gcongr` would leave the
goal `⊢ N ≤ n` open instead of failing — a thing to show if there is time.

**Rehearsed failure 1.** Uncomment the `example` after the theorem and run
it. It attempts `linarith` on `|1 / (↑n + 1)| < ε` without first removing the
absolute value. The message is

```
linarith failed to find a contradiction
```

and the state it prints includes `a✝ : ε ≤ |1 / (↑n + 1)|` — `linarith` has
negated the goal and is trying to derive `False`, and it treats
`|1 / (↑n + 1)|` as an unknown with no relation to anything else. Say:
`linarith` does linear arithmetic over the atoms it sees; an absolute value
is an atom until a lemma opens it. Comment the example out again.

### §3 — The limit of a sum (0:27)

Say the argument first, in words: given `ε`, get `Ns` for `s` at `ε/2` and
`Nt` for `t` at `ε/2`; take `N = max Ns Nt`; then for `n ≥ N` both estimates
hold, and the triangle inequality adds them. Then type it:

```
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
    (hs : ConvergesTo s a) (ht : ConvergesTo t b) :
    ConvergesTo (fun n => s n + t n) (a + b) := by
  intro ε hε
  obtain ⟨Ns, hNs⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Nt, hNt⟩ := ht (ε / 2) (by linarith)
```

Say: `hs` is a `∀ ε > 0, ∃ N, …`; applied to `ε / 2` and a proof that
`ε / 2 > 0`, it becomes an `∃ N, …`, which `obtain` takes apart. The
`by linarith` proves `ε / 2 > 0` from `hε`.

```
  use max Ns Nt
  intro n hn
  have h1 : |s n - a| < ε / 2 := hNs n (le_of_max_le_left hn)
  have h2 : |t n - b| < ε / 2 := hNt n (le_of_max_le_right hn)
```

Proof state: `hn : n ≥ max Ns Nt`, and `h1`, `h2` as stated. Say:
`le_of_max_le_left hn` is `n ≥ Ns`, extracted from `hn`.

```
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring
```

Say: `abs_add_le` is the triangle inequality; the `_ _` are its two
arguments, which Lean fills in from the line. Then `#print axioms
convergesTo_add`, which lists the standard three and no `sorryAx`.

**Rehearsed failure 2.** The `example` that follows is already uncommented
and has a `sorry` in it. It takes `use Ns` instead of the maximum. Put the
cursor on the `sorry`: the goal there is `n ≥ Nt`, and the context has
`hn : n ≥ Ns` and nothing about `Nt`. Say: this is the step the maximum
exists for. The `sorry` is why the file's header says `CI: allow-sorry (1)`.

### Pairs (0:37)

B1, B2, B3 in that order; C2 for pairs that finish, and homework otherwise. All four have the shape of §2 and §3; the
hints in the file name the one lemma each needs. Things to look out for:

- `obtain ⟨N, hN⟩ := hs` without the `ε hε`. Error: ``Tactic `rcases`
  failed: `hs : ∀ ε > 0, …` is not an inductive datatype``. The hypothesis is
  a `∀`, not an `∃`, until it is applied to an `ε`.
- B1: after `use N` and `intro n hn` the goal is
  `|(fun n => s n + c) n - (a + c)| < ε`. The `have h : |s n + c - (a + c)| =
  |s n - a| := by ring_nf` then `rw [h]` works directly, because the goal and
  the left side of `h` agree once the function is evaluated.
- B3: `apply hN (n + 1)` leaves the goal `n + 1 ≥ N`, which `omega` closes.
  `linarith` also closes it.
- C2: `rw [abs_lt] at h1 h2 ⊢` — the `⊢` means "and in the goal". After it,
  the goal is `-ε < s n - L ∧ s n - L < ε`, and `constructor` splits it.

### Walk-through (0:57)

B3 unless something else stopped more pairs. The solution is in
`Solutions.lean`; type it or display it.

### §5 — The same definition in Mathlib (1:02)

Run the three `#check` lines and the `theorem convergesTo_iff_tendsto`. Say:
Mathlib has one notion of limit, `Filter.Tendsto`, which covers `n → ∞`,
`x → a`, and one-sided limits in one definition; session 9 is about how.
`Metric.tendsto_atTop` unfolds it to the ε–N statement with `dist (s n) a`
where we wrote `|s n - a|`, and `Real.dist_eq` says those are equal. The
proof of the equivalence is three lines, and the `rfl` at the end is the
claim that nothing else differs.

Then the last `example`: `1/(n+1) → 0` is already in Mathlib under the name
`tendsto_one_div_add_atTop_nhds_zero_nat`, and the equivalence transfers it.
Say: this is the preview of the next session, which is about finding such
names. On the statement, `exact?` finds it:

```
Try this: exact tendsto_one_div_add_atTop_nhds_zero_nat
```

and `exact?` also finds `exists_nat_one_div_lt` from its statement.

### With an assistant (1:05) — Alexei, over the call

`Assistant.lean` has three tasks, each a prompt in a comment and a statement
with a `sorry`. The mechanics are the same for every task: paste the prompt
(with the definition) into the assistant, paste its answer over the `sorry`
in the web editor, wait for the file to re-elaborate, and run the
`#print axioms` line under it. Two tabs on the shared screen: the web editor
and the assistant. Say the seminar's rule once before starting: compile it,
understand it, disclose it.

What was and was not verified: the three statements compile with `sorry`,
and the reference proofs in `Solutions.lean` Part H compile; no assistant's
output has been checked in advance, because the segment is about checking it
in the room. Whatever comes back is the material. If the assistant cannot be
reached, Part H is what to show instead, in the same order.

**Task 1 (4 min) — ask for a proof.** `convergesTo_neg`, exercise B2, which
some pairs have just proved. Three possible outcomes, each a lesson:

- Compiles, `#print axioms` lists the usual three. Then read it: does each
  line correspond to a step one could explain? A proof made of `simp` and
  `nlinarith` calls that happens to close the goal passes the first check and
  not the second.
- Compiles, `#print axioms` lists `sorryAx`. The assistant left a hole,
  possibly without saying so. This is why the line is there.
- Does not compile. Usually a lemma name that was renamed or never existed.
  Say: Mathlib changes names every few weeks, and an assistant's names are
  from whenever it was trained. The fix is `exact?` on the failing line.

**Task 3 (6 min) — ask for a proof of something false.** Statement (iii) of
Part A implies convergence; it does not. Either the assistant says so, which
is the good outcome, or it produces text. If the text compiles, run
`#print axioms` before anything else; a compiling proof of a false statement
can only exist with `sorryAx` or another extra axiom in the list. If it does
not compile, the error is usually at the step where the argument actually
fails, and that step is worth reading aloud: it is the place where "within
`ε` infinitely often" is being used as if it said "within `ε` eventually".
Then show `Solutions.lean` H3a–H3c: `(-1)^n` satisfies the hypothesis with
`a = 1` and does not converge to `1`, in twenty lines of session 3–4 tactics.

**Task 2 (if time) — ask for a statement.** "Every convergent sequence is
bounded." The questions to ask of the result are in the file: is it `|s n|`
or `s n`; does `∃ M` come before or after `∀ n`. Then, if wanted, ask for the
proof. A direct `ε`–`N` proof needs a maximum over the terms before `N`; the
reference proof instead crosses to Mathlib's `Tendsto` by the equivalence
from §5 and uses `Filter.Tendsto.bddAbove_range` and `bddBelow_range`. An
assistant that knows Mathlib will likely take that route; one that does not
will produce something long. Either is fine to show.

If Task 2 is not reached, it is homework: the file is in the folder, and the
statement question (not the proof) is the part to do.

## Questions that came up while building this, with answers

**Why `n ≥ N` and not `N ≤ n`?** They are the same proposition; `≥` is
notation for `≤` with the arguments swapped. Lean displays whichever was
typed. `le_of_max_le_left` is stated with `≤` and accepts `hn : n ≥ max Ns Nt`
without complaint.

**Why does the goal show `(fun x => c) n` instead of `c`?** Lean does not
evaluate function applications in a goal on its own. `simp only` does; so does
`show |c - c| < ε`, and most tactics see through it anyway.

**What does `↑n` mean?** The coercion from ℕ to ℝ, written `(n : ℝ)` in the
source. Session 2, §5.

**Why `abs_of_pos (by positivity)` rather than `abs_of_nonneg`?** Either
works. `positivity` proves `0 < 1 / (↑n + 1)`; `abs_of_pos` wants exactly that.

**Is `|·|` the absolute value?** Yes: `|x|` is notation for `abs x`, and the
lemmas are named `abs_…` (`abs_add_le`, `abs_sub_comm`, `abs_pos`, `abs_lt`,
`abs_of_pos`, `abs_mul`, `abs_neg`).

**Could the proof of `convergesTo_add` use `Ns + Nt` instead of
`max Ns Nt`?** Yes; `max` matches the textbook and `le_of_max_le_left` is the
lemma that extracts the two inequalities. With `Ns + Nt` the extraction is
`by omega`.

**Why `by linarith` for `ε / 2 > 0`?** It is a linear consequence of `hε`.
`positivity` would also work; `norm_num` reduces the goal to `0 < ε` and
stops there.

**What is `ring_nf` doing in the first `calc` line?** Normalizing both
sides of `|s n + t n - (a + b)| = |(s n - a) + (t n - b)|`. The expressions
inside the absolute values are equal as polynomials, and `ring_nf` rewrites
each side into the same normal form, after which the two sides are
syntactically identical. `ring` fails on this line, because the goal is an
equation of absolute values rather than of ring expressions, and its error
message suggests `ring_nf`. `congr 1` followed by `ring` is another way: it
reduces the equation of absolute values to the equation of their contents.

**Is `ConvergesTo` Mathlib's definition?** No; Mathlib's is `Filter.Tendsto`.
§5 proves they agree. The hand-written one is here so that every quantifier
is visible.

**Does the sequence in the second `#check` of §2 converge?** Yes, to `0`; it
is `1, 0, 0, …`. It does converge; it is a different sequence from the one
written on the board.

## Import note

`Demo.lean` and `Exercises.lean` import all of Mathlib. `Solutions.lean`
imports two modules. The seminar's usual rule (narrow imports on demo files,
for load time on local installs) is set aside for this session: the demo is
run from the web editor, where load time is the server's, and a file that
fails to open because a module moved upstream is a failure nobody in the room
can repair. Restore narrow imports after the meeting if desired; the set is
in `Solutions.lean`.
