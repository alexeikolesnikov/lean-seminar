# GitHub Copilot through GitHub Education

How to get Copilot at no cost with a university affiliation, turn it on in
VS Code, and choose which model answers. Written for this seminar; the
details below were checked against GitHub's documentation on 2026-10-21 and
change often, so the official pages linked at the end take precedence when
they disagree with this one.

Copilot is one assistant among several. The seminar's rule for all of them
is in `GROUND-RULES.md`: compile it, understand it, disclose it. Nothing
here replaces that.

## What the affiliation gets you

GitHub Education verifies two kinds of academic status, and they lead to
different Copilot plans.

| Status | Plan | Model choice | Monthly allowance |
|---|---|---|---|
| Verified teacher (faculty, instructors) | Copilot Pro, at no cost | A model picker: GPT, Claude, Gemini and other families | 1,500 GitHub AI Credits, plus unlimited code completions |
| Verified student | Copilot Student, at no cost | Automatic only; no picker | An allowance of AI credits (amount not published), plus unlimited code completions |
| No verification | Copilot Free | Automatic only | 2,000 completions per month and an allowance of AI credits |

Graduate students who also teach can apply as teachers; the application asks
for the role, not the degree status. Everyone else applies with what they
are.

"Automatic" means Copilot chooses the model for each request from the pool
the plan allows. On the Pro plan the same option exists under the name
**Auto**, and it is the default there too; the difference is that Pro lets
you override it.

GitHub re-checks eligibility monthly. A plan granted this way cannot be
canceled from the account settings, which is a feature of the free grant
rather than a problem.

## Step 1 — Get verified (10 minutes, then wait)

1. Sign in to GitHub and go to <https://github.com/settings/education/benefits>.
2. Click **Start an application**. Choose student or teacher.
3. Supply proof of current affiliation. A university email address is the
   quickest route when it is accepted; otherwise a faculty or student ID,
   a transcript, an enrollment letter, or a class schedule. The document
   must show your name, the full name of the university, and a date that
   establishes the affiliation is current. A photograph of the ID taken
   with the laptop camera is the usual method.
4. Submit and wait. GitHub says applications are "generally processed
   within a few days" and take longer at the start of a semester. After
   approval, the benefits themselves take up to about three days more to
   appear. If nothing has appeared five days after approval, GitHub's
   advice is to post in the GitHub Education community discussions rather
   than wait further.

Do not buy a plan in the meantime. If the Copilot settings page offers only
paid options after approval, wait a few days and look again; GitHub's own
page says the same.

## Step 2 — Activate Copilot

**Teachers.** Click your profile picture at the top right of any GitHub
page, then **Copilot settings**. A page titled "GitHub Copilot Pro" states
that you are eligible; click **Get access to GitHub Copilot**, set the use
policies, and click **Save and complete**.

**Students.** On the benefits page from Step 1, under "Free GitHub
developer resources for students and teachers", click **Learn more** and
follow the prompts to activate Copilot Student. Set the use policies when
asked.

The use policies worth a moment: "Allow suggestions matching public code"
decides whether Copilot may show you code that matches public repositories
verbatim, and the data-use settings decide whether your prompts are used
for training. Neither affects what the seminar does; set them as you
prefer.

## Step 3 — Turn it on in VS Code

This applies equally to VS Code on your own machine (Route B of the setup
guide) and to the browser VS Code in a Codespace (Route A); Copilot follows
the GitHub account, not the machine.

1. Open the Extensions panel (four squares in the left sidebar), search for
   **GitHub Copilot Chat**, and install the one published by GitHub. It
   installs the completions extension alongside it.
2. A Copilot icon appears in the title bar, or a prompt to sign in. Sign in
   with the GitHub account that holds the plan. The browser opens once to
   authorize VS Code.
3. Click the Copilot icon, or the chat icon in the title bar, to open the
   chat view.

You now have two things. **Completions** are the gray text that appears as
you type in a `.lean` file; Tab accepts, Esc dismisses. **Chat** is the
panel, where you type a question and can attach the open file. Chat has
modes, chosen from a dropdown at the bottom of the panel: *Ask* answers
without changing files, *Edit* proposes changes to the open file, and
*Agent* can run commands and edit several files. For the seminar, *Ask* is
the one to use; the other two are for later.

## Step 4 — Choose the model (Pro only)

At the bottom of the chat view, next to the mode dropdown, is a second
dropdown showing the current model. Click it to see the list. Students and
Copilot Free users see this dropdown but it offers only Auto.

Three things to know before choosing.

- **Auto is the default**, and GitHub's documentation describes it as
  choosing by availability, partly to reduce rate limiting. Once a chat
  session has started under Auto, switching to a named model requires
  starting a new chat.
- **Models cost different amounts.** Since June 2026 chat usage is billed in
  GitHub AI Credits, one credit being one US cent, charged per token at a
  rate that depends on the model. The rates differ by more than an order of
  magnitude: at the time of writing, GPT-5 mini is billed at $0.25 per
  million input tokens, Claude Sonnet 4.6 at $3, Claude Opus 5 at $5, and
  Claude Fable 5 at $10, with output tokens at several times those figures.
  The Pro plan's 1,500 credits ($15) go a long way with a small model and
  not far with a large one. Code completions are not billed against the
  allowance on any paid plan.
- **Which model is good at Lean is an empirical question**, and the answer
  changes with each release. The one thing the seminar can say from
  experience is that every model's knowledge of Mathlib lemma names is from
  whenever it was trained, and Mathlib renames things every few weeks, so
  stale names are the most common failure whichever model you pick.
  `Assistant.lean` in session 6 is built around checking for exactly this.

The usage page at <https://github.com/settings/billing> shows how many
credits the month has consumed.

## Using it with Lean

Copilot sees the files you have open and attach; it does not see the Lean
Infoview, and it does not run Lean. So:

- When asking about a goal, paste the goal state from the Infoview into the
  question. The assistant cannot read it otherwise.
- Whatever comes back is text until Lean has checked it. Paste it in, wait
  for the orange bar, and read the messages. A proof that elaborates can
  still contain `sorry`; `#print axioms` on the theorem is the check for
  that.
- Lemma names in the answer are the first thing to distrust. If a name does
  not exist, `exact?` on the same goal usually finds the current one.
- Disclose it. A comment at the top of the file, or beside the proof, saying
  what was assisted and with what, is the seminar's standard and also
  Mathlib's.

The seminar's own test of all this is `Seminar/Session06_Limits/Assistant.lean`:
three tasks with a prompt each, to be pasted into whichever assistant you
have and checked in Lean.

## If it does not work

- *The chat view says the plan has no access to a feature.* The benefit has
  not finished applying. Check <https://github.com/settings/copilot> for
  the plan name, and wait if it still shows Free.
- *The model dropdown offers only Auto on a teacher account.* Either the
  Pro grant has not landed (see above) or VS Code is signed in to a
  different GitHub account. The account menu at the bottom left of VS Code
  shows which.
- *Completions appear but chat does not.* Only one of the two extensions is
  installed. Install **GitHub Copilot Chat**.
- *Rate-limit messages under Auto.* These are transient; wait a minute.
- *Verification was denied.* The usual reasons are proof that does not show
  a current date, or a name on the document that does not match the GitHub
  account's name. Re-apply with a document that shows both.

## Official pages

- Student access: <https://docs.github.com/en/copilot/how-tos/copilot-on-github/set-up-copilot/enable-copilot/set-up-for-students>
- Teacher access: <https://docs.github.com/en/copilot/how-tos/manage-your-account/get-free-access-to-copilot-pro>
- Applying to GitHub Education as a teacher: <https://docs.github.com/en/education/about-github-education/github-education-for-teachers/apply-to-github-education-as-a-teacher>
- Plans and allowances: <https://docs.github.com/en/copilot/get-started/plans>
- Changing the model in chat: <https://docs.github.com/en/copilot/using-github-copilot/ai-models/changing-the-ai-model-for-copilot-chat?tool=vscode>
- Supported models by plan: <https://docs.github.com/en/copilot/reference/ai-models/supported-models>
- Model pricing in AI credits: <https://docs.github.com/en/copilot/reference/copilot-billing/models-and-pricing>
- GitHub Education community (for applications that stall): <https://github.com/orgs/community/discussions/111352>
