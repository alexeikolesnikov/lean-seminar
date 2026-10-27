# AI and professional mathematics: a two-page briefing

*For the Math Department conversation on AI in research, Wednesday 28 October 2026.*
*Snapshot as of October 26, 2026, condensed from a longer inventory of 65 documents. I included a timeline because a June document could not respond to what happened in October, and positions have shifted with events.*

---

## Section 1: timeline, reactions, and consensus topics

### 1. Brief 2026 timeline

| Date | Event |
|---|---|
| Jan–Feb | AI systems resolve several open Erdős problems, with Lean formalization; Tao starts a public wiki tracking AI contributions. Some claimed solutions turn out to be rediscoveries. |
| 2 Jun | Leiden Declaration on AI and Mathematics published; endorsed by the IMU the same day. |
| Jul–Aug | Security researchers using AI models find several soundness bugs in the Lean 4 kernel, each a way to prove False. All are fixed and Mathlib is re-checked (see §7). |
| 1 Aug | OpenAI publishes ten results on long-open problems, each with a machine-checked proof. |
| 5 Aug | The European Mathematical Society declines to formally endorse Leiden, citing the range of views among its members. |
| Aug | Hexagon Mathematics Foundation registered; its repository accepts AI-generated results, including ones no human claims to understand. |
| 8 Sep | OpenAI says its model has resolved more than 100 open problems and announces a Navier–Stokes claim. |
| 10 Sep | An open letter from 771 mathematicians leads OpenAI to withdraw sponsorship of a Caltech AI-math contest. |
| 11 Sep | 25 Fields Medalists publish *A Severe Misalignment of AI in Mathematics*; more than 7,400 endorsements within days. |
| Sep | OpenAI convenes an advisory group (AGMAI), hosted at the Institute for Advanced Study. On 29 Sep AGMAI publishes recommendations for releasing AI-generated mathematics. |
| 1 Oct | arXiv caps every submitter at two submissions a month and three active at a time. September volume was 40,363, against 20,569 two years earlier. |
| 6–7 Oct | OpenAI releases 722 manuscripts in 372 result families from an unreleased model, and withdraws three the next day after an error. The Association for Human Mathematics calls the release "a demonstration of power". |

### 2. What nearly everyone agrees on

1. **No AI authors.** An AI system cannot take responsibility, so it cannot be a listed author. COPE, Nature, Science, SIAM, LMS, Elsevier, arXiv and the *Annals* all say this.
2. **Humans answer for correctness.** Responsibility for a paper's content, citations included, rests with the people who sign it.
3. **Disclose use; keep refereed work out of the tools.** For authors, the mainstream position is permissive with disclosure. For referees it is close to a prohibition: manuscripts and proposals under review stay out of generative AI.

### 3. Where the journals and funders took a position

Most policies have converged on disclosure. The differences are in what counts as substantive use and how much the author has to say about it.

*Journals.* The *Annals* asks that authors be human and that any idea contributed by an AI tool be described and located in the paper. SIAM (policy v2.0, May 2026) asks for disclosure and for authors to be able to defend every part of the work, citations included. LMS journals attach an AI declaration to every submission, including a statement that none was used. A *Notices of the AMS* article (Sep 2025) surveys publisher policies and reports the same split: copy-editing with AI tools is ordinary, substantive use is disclosed, and no AI is a coauthor. arXiv asks that significant generative-AI use be reported.

*Refereeing.* SIAM, Elsevier, Springer Nature and the NSF all treat a manuscript or proposal under review as confidential and not to be entered into AI tools. Separately: the volunteer refereeing system was built for a fraction of current volume, and nobody has said how it is meant to absorb the difference.

*Advising.* No society has said anything, as far as I can see. The closest thing to a reference point is a first-draft report from a September 2026 Harvard summit on PhD education: responsibility for correctness and understanding sits with the person whose name is on the work; AI use is disclosed; other people's material goes into an AI system only with their agreement.

---

## Section 2: where people disagree, and what is open

### 4. Four positions

Several people hold more than one of these at once. Tao formalizes, endorses Leiden, signed the Fields letter, and uses the tools daily. The positions differ less on whether to use AI than on two separate questions: what norms govern your own use, and how to deal with the companies.

The last column imagines what each position would look like in our department.

| Position | Representative documents | What it says | What it would mean here |
|---|---|---|---|
| **Refuse** | Weinreich, *The crisis of AI-generated mathematics* (Aug 2026); Lazić, *Where I Stand on AI*; AHM pledges | Total opposition. AI-free work should count for more in hiring and tenure; no collaboration with AI companies. | Keep the manual tradition on purpose; accept slower output and a widening gap with the AI-assisted literature. *Mathematical monastery.* |
| **Contain** | Leiden Declaration; Fields Medalists' letter; AGMAI recommendations | Use is permitted, but needs norms: disclosure, attribution, responsible release. The objection is to the companies racing to solve famous problems as a benchmark, not to mathematicians using the tools. | Adopt disclosure norms; push societies and journals; treat lab releases as material to check rather than results to cite. *Mathematical situationship.* |
| **Adapt** | EMS position; Gowers, *Why I didn't sign*; Loh; Harlev | Powerful models will arrive regardless. Update hiring and journal criteria for this cycle instead of waiting for consensus. | Learn the workflow; decide what the department rewards (exposition, verification, collaboration) before a tenure case forces the question. *Mathematical evolution.* |
| **Embrace and formalize** | Buzzard and the Xena Project; Hexagon; Tao's 2023–25 formalization projects | A Lean-checked proof is correct whoever wrote it. Understanding can come later, from someone else. | Build on the Lean seminar; formal verification becomes something the department is known for. *Mathematical revolution.* |


### 5. A working rule example

Tao's rule for his own practice: an AI output belongs in your workflow only if you could present and defend it yourself, without further AI help. For students he argues for leaving some of the friction in.

### 6. Three open questions

No institution has ruled on any of these.

1. **What counts as a contribution?** Is a correct, checked result the contribution (Buzzard, Hexagon), or is a proof unfinished until a person understands and explains it (Kra, Sanderson, Tao's ICM essay)? Kra's version: deep theorems used to be scarce, so producing one was a reliable sign of deep thought. That signal is broken.
2. **Who absorbs the volume?** Submissions have doubled in two years and arXiv calls its cap a stopgap. Proposals range from journals that refuse AI-generated papers outright (Craven) to formal-verification certificates as a condition of review (Rogers).
3. **Hiring, promotion and tenure.** No funder, society or university has issued guidance. Individual proposals run from reserving hire lines for mathematicians who don't use AI (Weinreich) to demanding precise disclosure together with evaluation that does not penalize it (Harlev). A department can act on this one before anyone tells it what to do.

### 7. For the Lean seminar

Every position except outright refusal treats a formalized proof as the baseline for trust and argues only about what comes after. Rogers's September draft for mid-sized departments points out that Lean and mathlib infrastructure work doesn't fit evaluation systems built around papers, talks and grants, and asks departments to decide how to credit it. That question is open.

Tom Hales, who led the formal proof of the Kepler conjecture, describes the limits of that baseline (Tao's blog, 9 Oct). A Lean proof is as reliable as Lean's kernel, a few thousand lines of C++. This summer's soundness bugs in it were found by AI models in the hands of security researchers and have been fixed; independent checkers exist, but there is still no complete published proof that Lean's type theory is consistent relative to set theory. His rule for accepting a Lean proof has two parts: the kernel checks the proof, and a person checks that the statement and the definitions mean what they are claimed to mean. The second part is not delegated to the software. He also argues that the type-theoretic foundations get less attention from mathematicians than their use now calls for.

### 8. Questions for the session on Wednesday

- What has changed in your work or in your research field in the past year? Have you tried to use any of the new tools in your work, and what happened?
- Imagine your research career in 10 years. What kinds of things do you envision yourself working on?
- In that long-term career plan, what particular aspects of your research work bring you joy, meaning, and satisfaction?
- What opportunities does AI contribute to that vision? What barriers/challenges does it introduce?


---

### Primary sources

- Leiden Declaration: <https://leidendeclaration.ai/> · EMS position: <https://euromathsoc.org/news/leiden-declaration-on-artificial-intelligence-and-mathematics-224>
- *A Severe Misalignment of AI in Mathematics*: <https://mathandai.org/>
- AGMAI: <https://agmai.org/>
- arXiv rate-limit policy: <https://blog.arxiv.org/2026/10/01/updated-rate-limit-policy/>
- OpenAI release: <https://github.com/openai/math>
- Hexagon: <https://hexagonmath.org/>
- Tao, views on AI (living summary): <https://teorth.github.io/tao-web/ai-views.html> · AI contributions to Erdős problems: <https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems>
- SIAM AI policy: <https://epubs.siam.org/artificial-intelligence> · *Annals* submission guidelines: <https://annals.math.princeton.edu/submission-guidelines> · LMS submission page: <https://www.lms.ac.uk/publications/plms/submission>
- Harvard summit report (first draft): <https://cmsa.fas.harvard.edu/media/2026/09/Summit-on-PhD-Math-Education-in-the-Age-of-AI.pdf>
- Rogers, *Preparing Mathematics Departments for AI-Assisted Research and Formalization*: <http://hoalg.net/chrisrogers/AI-Formal_Dept_Proposal.pdf>

### Documents named in the text

- Weinreich, *The crisis of AI-generated mathematics* (Aug 2026): <https://arxiv.org/abs/2608.02859>
- Lazić, *Where I stand on AI*: <https://www.uni-saarland.de/en/lehrstuhl/lazic/prof-dr-vladimir-lazic/vladimir-lazic-where-i-stand-on-ai.html>
- Association for Human Mathematics: <https://www.ahmath.org/> · statement on the 6 October release: <https://proofsandprompts.com/2026/10/08/ahm-statement-on-openais-october-6-release-of-mathematical-documents/>
- Open letter about the Caltech Mathathon (10 Sep): <https://proofsandprompts.com/2026/09/10/open-letter-about-the-mathathon/>
- Gowers, *Why I didn't sign the Fields medallists' letter* (17 Sep): <https://gowers.wordpress.com/2026/09/17/why-i-didnt-sign-the-fields-medallists-letter/>
- Loh, *Why do we need human mathematicians anymore?* (19 Sep): <https://terrytao.wordpress.com/2026/09/19/why-do-we-need-human-mathematicians-anymore/>
- Harlev, *Dear conferences, journals, and hiring committees: don't wait for everyone else* (25 Sep): <https://proofsandprompts.com/2026/09/25/dear-conferences-journals-and-hiring-committees-dont-wait-for-everyone-else/>
- Kra, *Deep theorems were scarce and difficult…* (13 Sep): <https://terrytao.wordpress.com/2026/09/13/deep-theorems-were-scarce-and-difficult-and-so-became-an-effective-mechanism-to-identify-deep-thought-ai-has-broken-this-system/>
- Sanderson, *If math is more than proof, we need to better celebrate the rest of it* (18 Sep): <https://terrytao.wordpress.com/2026/09/18/if-math-is-more-than-proof-we-need-to-better-celebrate-the-rest-of-it/>
- Tao, *Mathematics in the age of AI* (ICM 2026 essay): <https://arxiv.org/abs/2608.16753>
- Craven, *Where will all the papers go?* (19 Sep): <https://proofsandprompts.com/2026/09/19/where-will-all-the-papers-go/>
- AGMAI recommendations of 29 September: <https://agmai.org/general-sep29/>
- Hales, *What mathematicians should know about the Lean Theorem Prover: questions of reliability and AI* (9 Oct): <https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/> · de Moura, postmortem for the kernel soundness bug hunt (24 Aug): <https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/>
- Buzzard, *Human mathematicians are being outcounterexampled* (Xena Project, 20 Jul): <https://xenaproject.wordpress.com/2026/07/20/human-mathematicians-are-being-outcounterexampled>
- *Notices of the AMS*, "Fraudulent Publishing in the Mathematical Sciences" (Sep 2025), closing section on AI: <https://www.ams.org/journals/notices/202509/noti3217/noti3217.html>
- COPE position on authorship and AI tools: <https://publicationethics.org/guidance/cope-position/authorship-and-ai-tools> · Elsevier generative-AI policies for journals: <https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals>

*Nothing after 26 October 2026 is reflected. Corrections and additions: open an issue or PR.*
