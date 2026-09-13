# Session 02 — One colon, four tactics

Instructor notes. Not for participants.

Checked against Lean 4.33.0 / Mathlib v4.33.0. Every output quoted below was
produced by the pinned toolchain.

**Goal.** By the end, participants can read any colon in a Lean file and say
what it asserts, can read a type error, and can close a goal with `exact`,
`apply`, `intro` or `rfl` knowing why that tactic was the one to use.

---

## The material no longer fits in 75 minutes

This needs a decision before the session runs. Taking the demo at a pace the
room can follow:

| | | min |
|---|---|---|
| 0:00 | Recap; Natural Number Game check-in | 5 |
| 0:05 | §1 colon tour — types, ℕ/ℤ/ℝ, elaboration, `:=` | 15 |
| 0:20 | §2 propositions are types; functions on data and on proofs | 15 |
| 0:35 | §3 parentheses, commas, application, dot notation | 10 |
| 0:45 | §4 proof state, the four tactics, `have`/`show`, `rfl`, `sorry` | 20 |
| 1:05 | §5 the judgement beat | 5 |
| 1:10 | Close | 5 |

That is 75 minutes with **no exercise time at all**, against a session pattern
that allocates 30 minutes to work in pairs. Three ways out:

1. **Exercises become homework.** Run §1–§5 in the room, assign A–E. Cheapest,
   but it gives up the pairs, which are the attrition control — people debug
   each other's unicode faster than an instructor can, and it converts silent
   frustration into conversation.
2. **Cut §3 to five minutes.** Keep application-is-juxtaposition and the
   parentheses contrast; drop commas and dot notation, which are the least
   load-bearing. Buys 5 minutes; not enough on its own.
3. **Split across two meetings.** §1–§2 and the A–C exercises in the first,
   §3–§5 and D–G in the second. Costs a session against a 12-session syllabus,
   which pushes everything after it.

My recommendation is 1 plus 2, giving roughly 20 minutes of pairs on parts A
and B in the room and the rest as homework. But this is a call about the
semester arc, so it is yours.

---

## The organising claim

> The colon has only one meaning; you can read it as "has type".
> Everything else that looks like a colon is a different token.

---

## The five beats that carry the session

### 1. Propositions are types (§2)

Put these on screen together and say nothing for a moment:

```
2           : ℕ
two_add_two : 2 + 2 = 4
```

Then the Infoview pair — `n : ℕ` and `h : n + 0 = n` are entries of the same
kind. You read the first as "let `n` be a natural" and the second as "suppose";
Lean does not distinguish them.

### 2. There is one function type (§2)

`∀ (x : A), B`, with `A → B` as the notation available when `x` is unused. The
`rfl` proof of `(∀ _ : ℕ, ℕ) = (ℕ → ℕ)` is the evidence. The payoff is stated
in the file and is worth saying aloud: `intro` strips a binder, so an
implication goal and a `∀` goal are one problem; `apply` is application run
backwards, so modus ponens and instantiating a universal are one operation.

### 3. The proof state (§4)

New this revision, and the piece the session was missing. A proof in progress is
a context and a goal; every tactic transforms that pair. Move the cursor down
the tactic block and let the room watch it happen. `trace_state` is the
projector-safe version and prints the state wherever you put it — it needs no
cursor and behaves identically in the browser editor.

### 4. The rehearsed failure, and how to read an error (§4)

Uncomment `example (n : ℕ) : 0 + n = n := rfl`:

```
Type mismatch
  rfl
has type
  ?m.9 = ?m.9
but is expected to have type
  0 + n = n
```

Read it structurally — term, type it has, type expected — and say that almost
every type error has those three parts. Then ask why `n + 0 = n` worked before
explaining; participants who did the Natural Number Game have met this.

### 5. The judgement beat (§5)

```
#check ((n - m : ℕ) : ℤ)      -- ↑(n - m) : ℤ
#check ((n : ℤ) - (m : ℤ))    -- ↑n - ↑m  : ℤ
```

Ask which is "subtract the naturals" before revealing anything, `#eval` both at
`n = 0, m = 1`, then uncomment the `plausible` line:

```
Found a counter-example!
n := 0
m := 4
issue: 0 = -4 does not hold
```

The fix is not a better proof but the hypothesis `m ≤ n` — mathematical content
that the colon placement was implicitly asserting.

---

## The exercises, and what each part is for

Parts A–E are the session, F needs no proof, G is optional. Each part of
`Solutions.lean` ends with a note headed **"What this was for"**, which is where
the point lands. Tell participants to do the part before reading the note.

| Part | The surprise |
|---|---|
| **A** | The same English sentence is a theorem over `ℤ` and false over `ℕ`. Then `rtwo = ntwo`: the statement Lean checked is not the one you typed, and `rfl` closes it anyway. |
| **B** | `rfl` is *stronger* than expected on `(fun x => x + 1) 3 = 4` and `¬p = (p → False)`, and *weaker* than expected on `0 + n = n` and `n * 1 = n`. |
| **C** | A proof of `∀` is a function: it can ignore its argument, it can be applied, and it curries exactly as `addPair` did. |
| **D** | A `∀` can be instantiated at `f 3`, not only at numerals. |
| **E** | `x.foo` means `T.foo x`, so the same suffix names different theorems. |
| **F** | `sorry` proves `False`. So "the file compiles" was never evidence of anything. |
| **G** | First unaided lemma search (`exact?`), and what `show` is actually for. |

**A4 is the one to walk through at the end if time allows.** It looks like a
counterexample to §5 and is not: §5's trouble came from a coercion sitting
outside an *operation*, and A4 has no operation in it. The rule the two together
establish is *look at where the arrow sits relative to the operations* — neither
"casts are safe" nor "casts are dangerous".

**F is deliberately not a proof.** It cannot be: the solutions file must compile
with no `sorry`, and F's whole content is that `sorry` typechecks. Both files
carry it as a commented observation.

Twenty-one holes. B1–B5 and C1–C7 are one line each.

---

## Predicted friction

- **"Is `(2 : ℝ)` a cast?"** No. It says to build the numeral with `ℝ` as the
  expected type, so Lean produces a real from the start. Calling it a cast makes
  §5 harder to explain, because the point there is that the colon is chosen
  *before* the subtraction and determines which subtraction happens.
- **`↑` on the projector.** The arrows carry §5 and are small; increase font
  size beforehand. `set_option pp.numericTypes true` annotates numerals with
  their types and can help. `set_option pp.coercions false` is a trap here: it
  renders `↑(n - m)` as `(n - m).cast`, which is worse.
- **`{}` versus `()`.** §2 now covers this, because it is unavoidable —
  `Nat.sub_add_cancel {n m : ℕ} (h : m ≤ n)` was already used in session 1.
- **The §3 `NOW TRY THIS` produces no error.** `#check double -1` prints
  `double - 1 : ℤ → ℤ`; Lean read it as pointwise subtraction of the function
  and the constant function `1`. Someone expecting an error will think their
  install is broken.
- **Someone will ask what `Type` is.** §7.1–7.2, below the divider. Say it is
  there and optional.

## Containing the type theory

The appendix (§7.1–7.3) covers the data/proposition correspondence, the
`Prop`/`Type` hierarchy, and proof irrelevance. `Extras.lean` continues past
that into where the correspondence breaks: `Sigma` against `Exists`, large
elimination, and choice. Neither belongs to any session and nothing depends on
either.

The line to use: *"That's a real question, it has a real answer, and it's in the
appendix or in `Extras.lean` with the code to run. It isn't on today's path."*

`Extras.lean` is where session-12 material accumulates. Its §2 closes by saying
so.

---

## Two routes, one room

Lab is the browser (`live.lean-lang.org`); personal experimentation is VS Code.

1. **Teach `No goals` as the done-signal, not the checkmark.** "Goals
   accomplished" is a VS Code gutter decoration and lean4web never draws it.
   This is the session that introduces the Infoview as the whole interface, so
   it is exactly where a split would be created. Consider setting
   `lean4.goalsAccomplishedDecorationKind` to `Off` on the demo machine.
2. **`trace_state` is the browser-safe way to show a proof state**, and §4 now
   uses it for that reason.
3. **The appendix and `Extras.lean` are VS Code material** — they reward
   hovering, and involve universe metavariables that are easier to read with an
   editor that will tell you what you are pointing at.

**Web editor caveat.** live.lean-lang.org serves the latest Mathlib, not the
pinned v4.33.0, and this session reads exact `#check` output aloud more than any
so far. The coercion display in §5 is the exposed part. Click the link before
the session.

**Imports.** All four `.lean` files now use a seven-line targeted import set
rather than `import Mathlib` — about 4.7× fewer modules and 11× fewer olean
bytes, which is what participants were complaining about. `Exercises.lean` is
the exception in principle (G1 asks for `exact?`, which only sees imported
modules) but the narrow set covers `Nat.cast_div`, so it stands; if a
participant's `exact?` comes up empty on G1, adding `import Mathlib` at the top
of their `MyWork/` copy is the fix. See project doc 15.

---

## Instructor key for the `?` placeholders

**Demo §7.1**

```
And    : Prop → Prop → Prop
Sum    : Type u_1 → Type u_2 → Type (max u_1 u_2)
Or     : Prop → Prop → Prop
@Sigma : {α : Type u_1} → (α → Type u_2) → Type (max u_1 u_2)
@Exists : {α : Sort u_1} → (α → Prop) → Prop
Unit   : Type        True  : Prop
Empty  : Type        False : Prop
```

Note that `@` vanishes from the display on the ones with no implicit arguments.

**Demo §7.2**

```
Sort 0                    Prop : Type
Sort 1                    Type : Type 1
∀ p : Prop, p → p         ∀ (p : Prop), p → p : Prop
(α : Type) → α → α        (α : Type) → α → α : Type 1
```

**Exercises A4 and C5**

```
#check (rtwo = ntwo)      rtwo = ↑ntwo : Prop
#check (ntwo = rtwo)      ↑ntwo = rtwo : Prop
#check comm2 2            comm2 2 : ∀ (m : ℕ), 2 + m = m + 2
```

**Extras §2**

```
fun (s : Σ n : ℕ, Fin n) => s.1
    fun s => s.fst : (n : ℕ) × Fin n → ℕ        (a function; ℕ is the codomain)
@Exists.choose
    {α : Sort u_1} → {p : α → Prop} → (∃ a, p a) → α
@Classical.choice
    {α : Sort u_1} → Nonempty α → α
#print axioms someWitness
    'someWitness' depends on axioms: [Classical.choice]
```

The three errors, verbatim:

```
obtain ⟨n, _⟩ := h; exact n
    Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate
    into `Prop`

cases h with | inl _ => … | inr _ => …          (p ∨ q into Bool)
    Type mismatch when assigning motive
      fun t => h = t → Bool
    has type
      p ∨ q → Type
    of sort `Type 1` but is expected to have type
      p ∨ q → Prop

def someWitness' (h : ∃ n : ℕ, n > 3) : ℕ := h.choose
    failed to compile definition, consider marking it as 'noncomputable'
    because it depends on 'Exists.choose', which is 'noncomputable'
```

---

## Before next time

*Mathematics in Lean* §2. Session 3 is logic — `∀ ∃ → ¬ ∧ ∨ ↔` and the tactics
that manipulate them — and assumes today's editor loop is fluent, so part C
matters more than its length suggests. Dot notation (part E) becomes unavoidable
there: `∧` and `↔` are read almost entirely through `.1`, `.2`, `.mp`, `.mpr`.
