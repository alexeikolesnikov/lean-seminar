# Ground rules

Two sets of rules apply here: the Lean community's, and ours. The community's
came first. When you post to the Lean Zulip you are a guest in a room other
people have maintained for years.

Everything in the first section is quoted from the community's own documents,
linked at the bottom.

---

## 1. The Lean community's rules

The community has adopted the **Contributor Covenant Code of Conduct**:

> We are devoted to developing an open and accepting community that welcomes
> participation from everyone. Behavior that is offensive, discriminatory, or
> aggressive will not be tolerated in any form.

Four of the listed grounds for suspension or banning are worth spelling out,
because three of them are not what a newcomer expects.

**Do not use the community to complete coursework or work tasks.**
This is the one that catches seminar participants. Posting a seminar exercise
to Zulip and asking how to finish it is a breach — not rudeness, a breach. Ask
in the seminar, ask a colleague, ask the instructor, or ask about the *concept*
in general terms without the exercise attached.

**Do not use an LLM to write your Zulip or GitHub comments.**
Stated flatly in the guidelines: *"Please do not use an LLM when writing
comments on github or Zulip."* Write in your own words. Non-native English is
explicitly welcome — *"as long as you can be understood, you will be fine."*

**Significant use of AI without attribution is a bannable offence**, as is
*"unrequested posting of 'slop' AI-generated code."* If AI helped produce
something you post, say so.

**No harassment, discrimination, sustained off-topic posting, or repeated
low-effort posts.** If you see someone breaching the code of conduct, the
guidance is not to answer in kind but to report it to the moderators.

If you contribute to Mathlib itself, its contributing page adds:

> If you use artificial intelligence (such as, by using GitHub's copilot mode,
> asking an LLM like ChatGPT or using an agent like Codex, Claude, Gemini, or
> even Lean-dedicated agents like Aristotle), you must explain this in the PR
> description.

and, decisively:

> It is essential that you understand all the content written by an AI.

---

## 2. Using AI in this seminar

AI is not banned here. It is a genuinely useful tool for finding Mathlib lemma
names and for getting unstuck, and pretending otherwise would be silly in a
seminar partly *about* what these tools can and cannot do. Three conditions:

**Compile it.** Never present Lean you have not run. Language models produce
Lean that looks right and names lemmas that were renamed two releases ago. This
applies to the instructor's material too — see "How these files were made" in
the README.

**Understand it.** If you cannot explain why a proof works, you have not
finished. A tactic block you cannot read is a black box you will not be able to
modify next week.

**Disclose it.** In the seminar this is informal — "I got this from Claude and
then fixed the third line" is a perfectly good thing to say, and usually an
interesting one. Outside the seminar, on Zulip or in a PR, disclosure is
mandatory and enforced.

---

## 3. Inside the seminar

**Solutions are published, and reading them is not cheating.** Nobody is
assessed and nothing is graded. The exercises exist to give you something to
struggle with; the solutions exist so the struggle ends. Try first, look after.

**Work in `MyWork/`.** It is gitignored, so pulling the next week's material
can never conflict with anything you have written. The cost is that it is not
backed up — if your files matter to you, copy them somewhere.

**Debug in pairs.** People find each other's unicode typos far faster than an
instructor at the front can. Most of what goes wrong in the first month is
mechanical, and mechanical problems are contagious in a good way: everyone who
watches you fix one has learned it too.

**Say when you are stuck and how long you have been stuck.** Twenty minutes of
silent frustration is the mechanism by which voluntary seminars lose people. It
is not a sign of anything except that Lean is unfamiliar.

---

## 4. Attribution

Mathlib is licensed **Apache 2.0**, and so is this repository, so material can
move freely in both directions. That is a legal permission, not a substitute
for saying where something came from.

**Name the lemma.** When an automated tactic closes a goal, find out what it
used — `exact?` reports the name — and write it down. The lemma name is the
part you can reuse later; `simp` closing a goal is not.

**Say when you adapted a Mathlib proof.** A comment naming the file is enough.

**Cite Mathlib properly in published work.** The community's requested citation
is on their [citing page](https://leanprover-community.github.io/cite.html).

---

## Sources

- [Lean community guidelines](https://leanprover-community.github.io/community_guidelines.html) — the code of conduct and the list of bannable behaviour
- [Contributing to Mathlib](https://leanprover-community.github.io/contribute/index.html) — the AI disclosure requirement
- [Citing Mathlib and licence](https://leanprover-community.github.io/cite.html)
- [The Lean Zulip](https://leanprover.zulipchat.com/) — where the community actually is

*Quotations retrieved 2026-08-16. If they have drifted, the linked documents
win, not this file.*
