# Getting Lean running

Three routes, in the order we recommend trying them. Pick one; you can change
your mind later, and nothing you do in one blocks another.

Repository: <https://github.com/alexeikolesnikov/lean-seminar>

---

## Route A — Codespaces (the default)

A full VS Code running on GitHub's machines, in your browser, with Lean and
Mathlib already installed. Nothing to install locally, works on the lab
machines, and it is the *real* VS Code interface — so anything you learn
transfers if you later install locally.

You need a free GitHub account. That is the only requirement.

1. Go to the repository page.
2. Click the green **Code** button → **Codespaces** tab → **Create codespace on
   master**.
3. **Choose the 4-core machine** if offered a choice. Lean with a full
   `import Mathlib` wants the memory, and the 2-core option is slow enough to
   give a bad first impression.
4. Wait. The first launch takes about five minutes while Mathlib is fetched.
   Later launches take seconds.
5. Open any file under `Seminar/` and wait for the orange progress bar at the
   top of the editor to finish.

**Two habits that keep this free.** GitHub gives each personal account 120
core-hours and 15 GB of storage per month; on a 4-core machine that is 30 hours
of actual use, which is comfortable for a seminar plus homework.

- **Stop your codespace when you finish** — the Codespaces menu, *Stop current
  codespace*. It also idles out after 30 minutes, so a forgotten one is bounded
  rather than catastrophic.
- **Keep one codespace, not three.** Storage is the tighter limit and a Mathlib
  codespace is several GB. Delete old ones.

---

## Route B — Local install

Better once it works: faster, offline, no quota, and your files are on your own
disk. It is not the default only because supporting five operating
systems is not something I can promise.

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

## Route C — the web editor

<https://live.lean-lang.org> runs Lean with Mathlib in a browser tab. No
account, no install, nothing to go wrong. Paste a file in and it works.

Nothing is saved, and it handles one file at a time, so it is a poor home for a
semester. It is the right tool for week 1 if your laptop is fighting you, and
for looking at a single example someone sends you.

---

## Each week

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
