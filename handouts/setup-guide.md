# Getting Lean running

Three options, not mutually exclusive. You can change your
mind at any point.

**You do not need any of this for the first 2-3 sessions.** We start by 
reading a formal statement and judging whether it says what it claims;
Option B, a browser tab, is enough. **When we start proving
things ourselves**, need to have Option A working by then.

Option A is worth the half hour because of what Lean does every time it starts:
it reads about 2 GB of compiled library into memory. Locally, this is quick; otherwise, you spend spend time watching a progress bar instead of doing mathematics.

Repository: <https://github.com/alexeikolesnikov/lean-seminar>

---

## Option A — Local install (the plan)

Faster than anything in a browser, offline, no quota, and your files are on your
own disk. Install it on whichever machine you will actually use. Set aside half an hour (ish) for this. 

### Before you start: check disk space

**You may regret skipping this step.** A Lean install with Mathlib needs
about **10.5 GB**, measured:

| | |
|---|---|
| `~/.elan` — the toolchain manager and one Lean | 2.9 GB |
| the project's `.lake` — 7.1 GB of it is Mathlib | 7.5 GB |
| transient download staging | 0.4 GB |

Check what you have:

```powershell
(Get-PSDrive C).Free / 1GB      # Windows
```

```bash
df -h ~                          # macOS / Linux
```

**Under 15 GB free, stop and free some up first.** The failure mode when you
run out mid-download is not a clean error: the Mathlib cache arrives
incomplete, Lake decides to build Mathlib from source instead, and your computer
uses its CPU for several hours producing nothing useful.

### 1. Git

macOS and Linux have it. On Windows, install [Git for
Windows](https://git-scm.com/download/win) and accept every default — in
particular the PATH option in the middle, "Git from the command line and also
from 3rd-party software". Then **close VS Code completely** if it was open; it
reads PATH at startup.

Tell Git who you are, once:

```
git config --global user.name "Your Name"
git config --global user.email "you@example.com"
```

### 2. VS Code and the Lean extension

Install [VS Code](https://code.visualstudio.com), open the Extensions panel
(Ctrl+Shift+X, or ⌘⇧X), search `lean4`, and install the one published by
**leanprover**. Ignore anything mentioning Lean 3.

That is the only extension you need — it brings its own language server,
Infoview panel, and unicode input.

### 3. Let the extension install Lean

A **∀** appears in the top right of the editor. Click it; the extension detects
that no Lean is installed and offers to set it up. Accept.

What it is doing: installing **elan**, a version manager, into `~/.elan`. Elan
then installs whichever Lean version a project asks for — you never choose a
version by hand, the project's `lean-toolchain` file decides. That mechanism is
what keeps the whole room on identical Lean.

If the `∀` menu does not offer it: Ctrl+Shift+P → `Lean 4: Setup`.

### 4. Clone this repository — do not create a project

**Do not use "Create Project Using Mathlib."** It fetches whichever Mathlib
version is newest on the day you run it, which will not be ours. Clone instead:

- **GitHub Desktop**: File → Clone repository → paste the URL above.
- **VS Code**: Ctrl+Shift+P → `Git: Clone` → paste the URL.
- **Command line**: `git clone https://github.com/alexeikolesnikov/lean-seminar.git`

Public repositories need no account to clone. Choose a destination with a
**short path and no spaces** — on Windows, `C:\Users\<you>\lean\` is safer than
Documents or Desktop, because Mathlib generates deeply nested paths and because
OneDrive will otherwise try to sync the tens of thousands of files Lean
produces and fight you continuously.

### 5. Download the compiled Mathlib

Open the cloned folder in VS Code, open a terminal in it (Ctrl+`), and run:

```
lake exe cache get
lake build
```

The first downloads 8,690 prebuilt library files — 5 to 15 minutes depending on
your connection. If you ever see it *compiling* Mathlib rather than downloading,
stop it and ask: the cache did not arrive and it will take hours.

**Never run `lake update`.** It re-resolves everything against the newest
versions and undoes the pin.

### 6. Windows only: exclude the Lean folders from Defender

Optional but potentially a big improvement in speed. Defender's real-time scanner inspects each of the
thousands of `.olean` files Lean reads on every build. In an administrator
PowerShell:

```powershell
Add-MpPreference -ExclusionPath "$HOME\.elan"
Add-MpPreference -ExclusionPath "<your clone>\.lake"
```

If your machine's policy blocks this, skip it — Lean still works, just slower.
It is not worth an OTS ticket.

### 7. Check it worked

Open `Seminar/Session00_Install/Smoke.lean`. Wait for the orange bar — the
first file after starting VS Code takes 30 to 90 seconds while Mathlib loads
into memory — then click at the end of the `linarith` line. A panel called
**Lean Infoview** should appear on the right showing

```
a b : ℝ
h : a ≤ b
⊢ a + 1 ≤ b + 2
```

**If you see that, you are done.** That panel is the entire interface.

---

## Option B — the web editor (weeks 1–3)

<https://live.lean-lang.org> runs Lean with Mathlib in a browser tab. No
account, no install, nothing to go wrong. Paste a file in and it works, or open
the link emailed for that week, which loads the session's file directly.

This is how sessions 1 to 3 run. Nothing is saved and it handles one file at a
time, which is fine while the exercises are about reading statements rather than
building up work you want to keep. It stays useful afterwards for looking at a
single example someone sends you.

One caveat, and it is the reason to say when something looks wrong: the web
editor runs the *latest* Mathlib, not the version 4.33.0 this seminar pins. That
is almost always the same thing, but if a file behaves differently here than in
the room, that is the likely reason — and worth mentioning rather than
assuming you did something wrong.

---

## Option C — Codespaces (backup)

A full VS Code running on GitHub's machines, in your browser, with Lean and
Mathlib already installed. Nothing to install locally, works on the locked-down
lab machines, and it is the *real* VS Code interface — so anything you learn
transfers if you later install locally.

**This is the fallback, not the recommended way.** Use it if you are on a lab
machine with no admin rights, or if Option A has fought you and you need
something working now. Everything is slower here than on your own disk, and the
slowness returns every time you resume a stopped codespace.

You need a free GitHub account. That is the only requirement.

1. Go to the repository page.
2. Click the green **Code** button → **Codespaces** tab → **Create codespace on
   master**.
3. **Choose the 4-core machine** if offered a choice. Lean with a full
   `import Mathlib` wants the memory, and the 2-core option is slow enough to
   give a bad first impression. The default configuration will request 4 cores.
4. Wait — **about twenty minutes** for the first launch, while the container is
   built, Lean is installed, and Mathlib is fetched. Do this the evening before
   you need it, not ten minutes before a meeting.
5. Open any Lean file under `Seminar/` and wait for the orange progress bar at
   the top of the editor (or the side of it) to finish. Expect several more
   minutes: Lean is reading about 2 GB of compiled library off a network disk.
   Walk away and come back.
6. Every time you resume a stopped codespace, step 5 happens again. That is the
   cost of this option, and it is why it is not the recommended one.

**Two habits that keep this free.** GitHub gives each personal account 120
core-hours and 15 GB of storage per month; on a 4-core machine that is 30 hours
of actual use per month, which is comfortable for a seminar plus homework.

- **Stop your codespace when you finish** — the Codespaces menu, *Stop current
  codespace*. It also idles out after 30 minutes, so a forgotten one is bounded
  rather than catastrophic.
- **Keep one codespace, not three.** Storage is the tighter limit and a Mathlib
  codespace is several GB. Delete old ones.

---

## Each week

*(Once you have a clone — Option A or C. On the web editor there is nothing to
pull: each week's link always serves the current file.)*

One click: **Source Control** panel → **⋯** → **Pull**. That is the only git
operation the seminar asks of you all semester.

It cannot conflict with your own work, because your work lives in `MyWork/`,
which git ignores, while material arrives in `Seminar/`. The cost of that
arrangement is that `MyWork/` is not backed up — copy anything you care about
somewhere else.

---

## When something goes wrong

Click **∀** → **Troubleshooting: Show Setup Information** (or Ctrl+Shift+P →
`Lean 4: Troubleshooting`). It prints versions, paths, and what it believes is
broken. Send that output to Alexei; it is usually diagnosable in one exchange.

| Symptom | Cause |
|---|---|
| `git` not recognised after installing it | VS Code or the terminal was not restarted |
| Elan download fails with a permission or TLS error | Managed-laptop policy or a corporate proxy — an IT conversation |
| A build that takes hours with the CPU pinned | Mathlib is compiling from source; the cache did not download |
| Everything works but is slow | Defender scanning `.lake` — see step 6 |
| Files reverting or duplicating themselves | The project is inside a OneDrive-synced folder; move it |
| `expected a Name` from `lake` | Something edited `lake-manifest.json` by hand |

Please do not take seminar exercises to the Lean Zulip — see
[`../GROUND-RULES.md`](../GROUND-RULES.md). Ask here first.
