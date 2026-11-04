# Session 07 — notes for the leader

Everything in `Demo.lean` has been compiled against Lean 4.33.0 / Mathlib
v4.33.0, and every error message and `Try this` quoted in the file or below
was produced by that toolchain. Nothing needs to be improvised.

## Before the meeting

- Open `Demo.lean` ten minutes early. The full `import Mathlib` takes 30–90
  seconds, and the `exact?` calls in the file each take a few seconds the
  first time the file elaborates. Open the file and let it settle before
  people arrive.
- Decide whether to run `#loogle` and `#leansearch` live (§6). They need
  network access and a response from an external service. In a Codespace or
  a local install they worked when the file was built; in the web editor,
  untested. The fallback is the recorded output in the comments and the two
  web pages in a browser tab.
- If using the web editor, click the link in `README.md` the day before. The
  editor runs the current Mathlib, and this session is the one where that
  matters: `exact?` may return a differently named lemma from the one in
  the comments. If it does, that is §3's point made for you — say so and go
  on.
- Zoom to 150% or more. The Infoview's `Try this` suggestion is the thing the
  room needs to read.

## Timing (75 minutes)

| | Section | Minutes |
|---|---|---|
| 0:00 | Where session 6 ended; what this session is (§0) | 5 |
| 0:05 | Matrices: notation, `#eval`, rehearsed failures 1 and 2 (§1) | 8 |
| 0:13 | `exact?` on `det_mul` and `transpose_mul`; reading `#check @`; the naming table (§2–3) | 9 |
| 0:22 | `det_smul`: rehearsed failure 3; `simp?`, `hint`, `rw?` (§4–5) | 8 |
| 0:30 | One live Loogle query, or the recorded one (§6) | 3 |
| 0:33 | Problems 1–3 in pairs, then conjectures | 27 |
| 1:00 | Reading what comes back (§7) | 8 |
| 1:08 | Walk through Problem 3 (a) and one conjecture | 7 |

If §1–5 run long, cut `rw?` (it is commented out anyway) and the second
`simp?` example. Do not cut §7; it is the session's judgement content, and Conjectures 5
and 7 depend on it.

## Script

### §0 — Where session 6 left off (5 min)

Session 6 ran to plan: the definition, `1/(n+1) → 0`, the limit of a sum,
Parts B1–B3 in pairs, and the assistant segment. Its G2 compared the
hand-written `ConvergesTo` with `Filter.Tendsto`, and its hint was
`#check @Metric.tendsto_atTop` — a name nobody could have guessed. That is
the problem for today.

Say what the session is: not proving things, finding them. The mathematics
is matrices because everyone has taught it; the content is the tools.

### §1 — Matrices (8 min)

Type the `#check` and the `#eval`s. Points to make:

- `Fin 3 = {0, 1, 2}`. Indices start at 0. `A 0 1` is the top-right entry
  of a 2×2 matrix.
- `!![1, 2; 3, 4]` — semicolons between rows.
- Over `ℤ` everything computes. **Rehearsed failure 1**: uncomment the
  `#eval` of the inverse over `ℚ`. Error: *failed to compile definition,
  consider marking it as 'noncomputable' because it depends on 'inv'*. The
  inverse is defined (§7 says how) but not as an algorithm.
- **Rehearsed failure 2**: uncomment the `ℕ` example. Error: *failed to
  synthesize instance of type class CommRing ℕ*. The determinant has signs.
  The statement does not even elaborate — compare session 4, where the
  totality of `ℕ`-subtraction let a wrong statement through; here the type
  system refuses it.

### §2 — `exact?` (5 min)

Type the `det_mul` example with `exact?` and wait for `Try this`. Click it
(or say that clicking replaces the line). Then `#check @Matrix.det_mul` and
read the three things listed in the file: the generality (`n`, `R`), the
`[CommRing R]` hypothesis that failure 2 hit, and the name as a description.

Then `transpose_mul`: ask the room for the name *before* running `exact?`.
Someone will say `transpose_mul`; that is the point of §3.

### §3 — Names (4 min)

Walk down the table in the comment. Then type `Matrix.det_` and pause, so the
room sees autocomplete filtering. The three examples after the table are
typed from the table, not found; type at least `det_transpose A` live.

### §4 — When `exact?` fails (5 min)

**Rehearsed failure 3**: uncomment the `det_smul` example with `exact?`.
Error: *`exact?` could not close the goal. Try `apply?` to see partial
suggestions.* Then `#check @Matrix.det_smul` and read the exponent,
`Fintype.card n`. Explain: `exact?` matches up to syntax, `Fintype.card
(Fin 3)` is not the symbol `3`, so two rewrites are needed. Type the `rw`.

If someone asks for `apply?` on this goal: it returns about thirty
suggestions, none useful (`Real.ext_cauchy`, `Real.sqrt_inj`, …). Say that
`apply?` works best when the goal has a distinctive shape; do not run it on
the projector unless asked, it is a minute of scrolling.

The `(c • A).det = c * A.det` remark: many people's first guess at the fact
is this, and it is false. The example with `A = 1`, `c = 2` is in the file.
(`plausible` does not help here: it cannot generate random matrices. The
exercise file says so in the Part II preamble.)

### §5 — `simp?`, `hint`, `rw?` (3 min)

`simp? [det_mul]` on `(Aᵀ * A).det = A.det ^ 2`: output `simp only [det_mul,
det_transpose]`, remaining goal `A.det * A.det = A.det ^ 2`, closed by
`ring`. Say: `simp?` turns a tactic that did something into a citation of
what it did — this is the session 4 question "can a tactic show its work"
again.

`hint`: output lists `aesop`, `norm_num`, `simp_all only [det_mul,
det_transpose]`, each with the same remaining subgoal. Then `#print axioms
hint_example` shows `sorryAx`. Say: `hint` reports and then admits the goal
so the file keeps compiling; it is not a proof, and `#print axioms` is how
you would catch it (session 1).

`rw?`: mention only. If asked, uncomment; the first suggestion is
`rw [det_mul]`, and the list runs to twenty-odd entries including
`Real.ext_cauchy_iff` and `det_fin_three`.

### §6 — Outside the file (3 min)

One live query if the network allows: `#loogle Matrix.det, Matrix.transpose`
returns six results with `det_transpose` first. Otherwise read the recorded
output. Name the four places: Loogle (by shape), LeanSearch (by sentence),
the API docs (by name, and for the module docstrings), and Zulip's
`#Is there code for X?`.

### Pairs (27 min)

Problems 1–3, then Part II conjectures as time allows. The problems carry
no lemma names; the preamble of the exercise file lists the three facts
nobody guesses (`isUnit_iff_ne_zero`, `Fintype.card_fin`,
`Ring.inverse_eq_inv'`). Expected progress: Problem 1 in five minutes,
Problem 2 in five, Problem 3 in ten, then conjectures. What to listen for:

- **Problem 1.** The decomposition `det (AᵀA) = det Aᵀ · det A = (det A)²`
  is immediate on paper; the Lean work is two `exact?` calls (or one
  `simp? [det_mul]`) and `mul_self_nonneg`. A pair that tries `positivity`
  on `0 ≤ A.det * A.det` finds it fails; `nlinarith [sq_nonneg A.det]` or
  `mul_self_nonneg` close it.
- **Problem 2.** Two proofs. By hand: `rw [← det_mul, h, det_one]` for
  `det A · det B = 1` — pairs who write `rw [det_mul]` get *Did not find an
  occurrence of the pattern (?M * ?N).det* because the goal has no product
  of matrices in it — then `zero_mul`, `zero_ne_one`. By search: `exact?`
  returns `det_ne_zero_of_right_inverse h`; read that name with the room.
- **Problem 3 (a).** `trace_mul_comm` moves `P` to the front; then
  `Matrix.mul_assoc` and `P * P⁻¹ = 1`. The last is `mul_nonsing_inv`, with
  `IsUnit P.det` — the first of the three listed facts. This is the step
  most pairs stall on; it is the walk-through.
- **Problem 3 (b).** `det_mul` twice, then `det (P⁻¹)`. `exact?` on a `have`
  stating `P⁻¹.det = P.det⁻¹` returns `Ring.inverse_eq_inv A.det` after
  `rw [det_nonsing_inv]`; or Loogle `Matrix.det, Inv.inv`. Then
  `field_simp`. The follow-up — restate with `IsUnit P`, `exact?` returns
  `det_conj'` — is the point of the problem: it was in the library all
  along, under a hypothesis stated differently.
- **Conjectures.** The intended rhythm is a minute of discussion per
  conjecture before anyone types. 1, 6, 10, 11 are true; the rest false. 5
  and 7 are false for the §7 reason (`A⁻¹` is total), and a pair that calls
  them true has understood the mathematics and not yet the library — that
  is the conversation to have. 10 has no single library lemma; the solution
  unfolds `trace` and `diag` and uses `Finset.sum_nonneg` twice, which is
  more than the meeting has time for; it is fine to leave it for homework.
- The refutation technique (`ext i j; fin_cases i <;> fin_cases j <;> simp
  [...]`, then `congrFun (congrFun h i) j`) is in the Part II preamble.
  `norm_num at h` on the extracted entry closes every refutation in the
  solutions.

### §7 — Reading what comes back (8 min)

The judgement content. Three items, in the file's order.

(a) `det_zero` has `[Nonempty n]`; `det_fin_zero` says why (det of the 0×0
matrix is 1). Then the `Fin 0` example: `exact?` proves `A = B` for any two
0×0 matrices, with the proof term `ext_of_single_vecMul (congrFun rfl)`.
The point is not the curiosity; it is that a statement about `Matrix (Fin n)
(Fin n) ℝ` includes `n = 0`, and a proof found by search is a proof of the
statement as written.

(b) `A⁻¹` is total. `inv_def` shows the definition; `mul_nonsing_inv` has
the hypothesis `IsUnit A.det`; `mul_inv_rev` (B6) has none. Say: a lemma
about `⁻¹` with no invertibility hypothesis is a statement about the
extended function. B6 and B7 are true and are not theorems of linear
algebra in the usual sense. Connect to session 4's `x / 0 = 0`.

(c) `mul_eq_one_comm_of_card_eq`. Read the statement: rectangular, with
`Fintype.card m = Fintype.card n`. The square case is `rfl`, and is
Conjecture 11.

### Walk-through (7 min)

Problem 3 (a), typed from the solutions: the `calc` block, with the `have
hPP : P * P⁻¹ = 1` line and its `isUnit_iff_ne_zero` bridge said aloud.
Then one conjecture the room disagreed about — 7 if it came up, since its
refutation uses `inv_def` and the singular matrix `!![1, 2; 2, 4]` from
§7(b).

## Predicted friction

- `open Matrix` is at the top of every file. Without it, the notation `ᵀ`
  does not parse (*unexpected token 'ᵀ'; expected command*) and the names
  need the `Matrix.` prefix. A participant who pastes a single exercise into
  a fresh file will hit this.
- `exact?` in the web editor may return a name that differs from the
  solutions. Say that this is the version difference the README warns about.
- `exact?` takes 3–10 seconds on a laptop with the full import. People will
  think it has hung. Say so once at the start of the pairs.
- `#eval` of a determinant over `ℝ` prints `Real.ofCauchy (sorry …)` under
  the full import (session 5 saw this). Use `ℤ` or `ℚ` for numerics.
- The `Try this` suggestion drops the `Matrix.` prefix because of `open
  Matrix`. `#check det_mul` without the prefix also works once the namespace
  is open; `#check @Matrix.det_mul` always works.
- Problems 3 and 4 and Conjecture 6 need `isUnit_iff_ne_zero`, which
  nobody will guess. The exercise file's preamble names it.
- Problem 4 (b) needs a case split on `A.trace • A = 0`. The lemma is
  `smul_eq_zero`; with `hc : A.trace • A = 0` in context, `exact?` on the
  goal `A.trace = 0 ∨ A = 0` returns `smul_eq_zero.mp hc`. The step a pair
  may miss is stating that disjunction as a `have` so that there is a goal
  to search on.

## Questions that came up while building the material

- *Why `IsUnit A.det` rather than `A.det ≠ 0`?* Because the lemmas are
  stated over a commutative ring, where "invertible" and "nonzero" differ
  (over `ℤ`, `det = 2` is nonzero and the matrix has no integer inverse).
  `isUnit_iff_ne_zero` is the field case.
- *Why does `det_smul` have `Fintype.card n` and not `n`?* Because `n` is
  the index *type*, not a number; `Fintype.card n` is its number of
  elements. `Fin 3` has three.
- *Is `hint` safe to leave in a file?* No; it admits the goal. CI would flag
  it as a `sorry` outside an exercise file. `Demo.lean` declares the one it
  contains in its header.
- *Does `exact?` use the network?* No. It searches the imported library on
  the machine. That is why the import is `Mathlib` and not something
  narrower.
- *What is `IsStablyFiniteRing R` in `mul_eq_one_comm_of_card_eq`?* The
  ring-theoretic condition under which left inverses are right inverses for
  square matrices. Every commutative ring satisfies it; so does every field.
  Not for the room unless asked.
