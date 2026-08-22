# Lean seminar — Mathematics Department

A semester-long working seminar on the [Lean 4](https://lean-lang.org) theorem
prover and its mathematical library, [Mathlib](https://leanprover-community.github.io).

Everything the seminar uses is in this repository, and all of it is public. You
do not need a GitHub account to read any of it.

## Who this is for

People with mathematical interests: faculty, graduate students, and interested undergraduates. No
prior experience of proof assistants is expected. We assume you can prove some math things, and have
never installed a compiler. Nothing here explains what induction is; a fair
amount would explain things like: why Lean's `Finset.range n` is `{0, …, n−1}`.

This is a *working* seminar. The measure of success is that you prove and formalize things
yourself, not that you follow a talk.

## Three ways in

| | What it costs | What you get |
|---|---|---|
| **Just read** | nothing | Browse the files here. Every session folder has a README explaining what it does. |
| **Codespaces** *(default)* | a free GitHub account | Real VS Code in a browser tab, Lean and Mathlib preinstalled, work persists between sessions. Runs on the locked-down lab machines. |
| **Install locally** | 30–45 min, ~11 GB | Faster, offline, no quota. Encouraged if you intend to formalize seriously. |
| **Web editor** | nothing | [live.lean-lang.org](https://live.lean-lang.org) runs Lean with Mathlib in a browser tab. No account, nothing saved — one file at a time. |

Codespaces is the documented route because it is identical for everyone and
works everywhere. The web editor exists so that nobody is stuck at the door in
week 1. Full instructions for all three: [`handouts/setup-guide.md`](handouts/setup-guide.md).

## What is in here

```
Seminar/       one folder per meeting: demo, exercises, solutions, notes
handouts/      the setup guide and other things printed or emailed
MyWork/        yours; ignored by git, so it never conflicts when you pull
scripts/       small utilities (generating no-install links, checking files)
```

Start at [`Seminar/README.md`](Seminar/README.md) for the session index.

## Versions

Everything here is pinned to **Lean 4.33.0** and **Mathlib v4.33.0**, and every
file states the version it was checked against in its header.

This matters more than it looks. Mathlib renames lemmas and changes tactic
behaviour every few weeks; I was promised that a file that worked in August 
might fail in November against a different library. The two files that 
enforce the versions are `lean-toolchain` and `lake-manifest.json`, both 
committed here. Cloning this repository reproduces the exact environment 
the material was written in.

The practical consequence: **do not create your own Lean project for this
seminar.** VS Code's "Create Project Using Mathlib" fetches whatever Mathlib
version is newest on the day you run it, which is how a room ends up with five
incompatible environments. Clone this repository instead.

## How these files were made

The Lean in this repository was drafted with substantial AI assistance and then
**compiled** — every file, against the pinned toolchain, before it was committed. 
Solutions files contain no `sorry`; exercise files contain `sorry` and
nothing else unproved. The per-file headers record what each file was checked
against.

I state this for two reasons. First, the Lean community requires disclosure of AI
assistance and we are guests in that community. Neither Lean community nor this seminar
would shy away from the AI assistance, but we will document it. Second reason is, in a short
phrase, human accountability. A machine can propose ideas and materials for this seminar, but
humans need to decide if they are worthwhile. This is not unlike the issue that 
a machine can check that a proof establishes a statement, but cannot check that
the statement says what was really meant. 


See [`GROUND-RULES.md`](GROUND-RULES.md) for what this implies for your own
work.

## Ground rules

Read [`GROUND-RULES.md`](GROUND-RULES.md) before posting anything to the Lean
Zulip, if you choose to post something there. One of the rules is worth noting: 
asking the community to do seminar exercises (if we were to have some) is grounds 
for suspension there.

## Licence

Apache 2.0, the same licence as Mathlib and *Mathematics in Lean*. See [`LICENSE`](LICENSE).
