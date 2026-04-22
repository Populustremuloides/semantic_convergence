# Drafting Rules: How Brian and I Work on Papers

This document captures what works when we edit together. It is written for future sessions, so it is meant to be picked up and applied without discussion.

## The central demand

Every sentence must be load-bearing. If a sentence can be removed without losing information a serious reader would care about, it must be removed. This rule subsumes most of the others; when in doubt, invoke it.

Load-bearing excludes: scene-setting, rhetorical throat-clearing, restatement of what was just proved, transitional phrases that don't transition, "notes on what we are about to do," and meta-commentary on the paper's own structure. It includes: a claim with consequences, a definition the rest of the paper will use, a warning about what is not being proved, a bridge that a careful reader could not construct unaided.

## Tonal rules

**Bold on what is new; humble on prior work.** Name the authors who supplied the individual pieces, credit them directly, and then explain what the assembly adds. Never minimize genuinely close neighbors; when a competitor paper is the closest neighbor, say so out loud.

**Honest, not defensive.** If a piece of prior work really does cover something we do, admit it, then explain what is still different. The sharpest positioning in our epiplexity paragraph came from asking for the honest take rather than the strategic one.

**Just a tinge optimistic.** Enough to give the reader a reason to care; not so much that it reads as marketing. Overclaim and the paper loses credibility at page 1.

**Approachable but never talking down.** The reader is sophisticated and skeptical. Skip the "as we all know" framing, and skip the "allow me to explain" framing too. Assume literacy; reward it.

**The contribution line must be audible, not implicit.** A reader who did not help write the paper cannot separate our claims from cited background unless we separate them. Terseness has a failure mode: it compresses novelty and prior art into the same sentence, so the reader cannot tell which is which. Signpost the distinction — not by announcing "our contribution is," but by naming the supplier (Solomonoff, Friston, Lindley) when we invoke prior work and naming the assembly or the theorem when we extend it. If a sentence would read the same whether the content is ours or theirs, it is too terse.

**Land the punchlines, do not bury them.** Unifications, surprising consequences, and load-bearing corollaries belong at theorem- or corollary-prominence, not at remark-prominence, when they carry the paper's "why does this matter" weight. A unification that merits a standalone corollary in the draft should not get demoted to a parenthetical in the revision, even when the technical content is preserved elsewhere. The surprise of a negative result (e.g., a near-miss) is calibrated by the strength of the positive content it negates; hiding the positive content makes the negative content look like a minor note instead of a substantive claim.

## The middle ground between terse and verbose

The first two rules above guard against terseness. They have a failure mode in the opposite direction: overcorrecting into verbose, announcement-heavy prose. The following rules keep the contribution line audible without drifting into marketing.

**Abstracts are one paragraph.** If the material demands paragraph breaks, the material is an intro draft in the abstract's slot. The fix is compression. The abstract has room for the problem, the target, the two or three load-bearing technical claims, and the headline result; nothing more. Figures, forward references to sections, and inventories of minor contributions belong in the introduction.

**Signal novelty through grammar, not announcement.** "Our first substantive contribution is," "We show that," "The main result of the paper is," and "Theorem X proves" are meta-commentary on the paper's structure. They are audible in a bad way: they call attention to the act of making a claim rather than to the claim. Replace them with the claim itself, using the sentence subject and the attached citation to carry the signaling. Cited work takes the form "X \citep{authors}" with the authors as grammatical agent; our work takes the form "X," "X is a theorem," or "Theorem n states X." The subject and the citation placement do the work.

**Ordinals are load-bearing only.** "First, second, third" belongs where the paper actually has parallel things the reader needs to track by number. Two unifications plus a near-miss is three things, but they do not need to be labeled "first," "second," "main negative contribution," and so on — the words "unification" and "near-miss" already distinguish them.

**Compression test.** Between every two adjacent sentences in the abstract and intro, ask: can these be combined into one without losing a load-bearing distinction? If yes, combine. Multi-paragraph abstracts fail this test by construction; they preserve paragraph seams where commas or single sentences would serve.

**Approachability is vocabulary, not length.** A sentence is approachable when every noun and verb is familiar and the referents are clear, not because it is short. Splitting one clear sentence into three shorter ones does not help. The terse-failure mode is abstract-noun-density too high per sentence, and the fix is at the vocabulary level; the verbose-failure mode is paragraph-count too high per idea, and the fix is at the compression level. These are distinct failures with distinct remedies — do not mix them.

**Formulations are contributions.** When the paper introduces a new object — a functional, a quantity, a construct — the introduction of the object is a contribution and must be positioned as one, even if the downstream theorems read as expected consequences once the object is fixed. A definition that silently introduces a new object is under-positioning, regardless of how brief the definition is. "We formulate X" and "X is the Gibbs-form functional whose reference measure is Y" are acceptable move-naming phrases; they do not violate the grammar rule against announcements because they name an object rather than claim a result. The positioning remark that follows such a definition should say what prior art has, what it lacks, and what the coupling adds — in three sentences or fewer.

## Structural commitments for formal papers

Include a **boxed problem statement** early, in standard terminology, one sentence, of the form "find/minimize/show ___ under ___." The rest of the paper is tuned to answer this question. Every section earns its place by contributing to the answer.

Every formal result (theorem, proposition, corollary) is followed by a **formal remark** that explains why the result is there. The remark does not restate the result. It places the result in the reader's intellectual economy: what would fail without it, which later result consumes it, which community's tradition it corresponds to.

Proofs go in the **appendix** unless the proof itself is the insight. Proof sketches in the main text are 2–4 sentences and point to the appendix. The main text leaves nothing undefined that the reader needs, but carries nothing a careful reader could look up.

**Page budgets are design pressure, not arbitrary constraints.** A 15-page main-text cap forces real choices about what the throughline is. Use it.

## The "who cares" test

Apply this at three levels:

1. **Individual result:** the remark must answer "why is this lemma/theorem here?" without restating it.
2. **Section:** the first and last paragraphs should together answer "why does this section exist in this paper?"
3. **Paper:** the abstract, the boxed problem, and the conclusion should together answer "what changes if the reader accepts this?"

If any level fails the test, the weakest element is the one to rewrite.

## Process rules

**One focused pass at a time.** A professionalism pass. A positioning pass. A structural pass (proofs-to-appendix, remarks-added). Each pass has a scope; the scope is respected. Do not mix line-editing with structural refactoring in the same pass.

**Compile and verify after each substantive change.** A clean compile with no undefined citations is a deliverable, not an afterthought. Warnings get resolved, not tolerated.

**Math is inviolate during prose passes.** When the instruction is "clean up the writing," the math stays verbatim. When the instruction is "strengthen the theorem," the prose around the theorem flexes to accommodate.

**Invite honest feedback on positioning.** When a close neighbor appears, ask for the most honest take, not the most defensible one. The honest take becomes the sharpest contribution.

## Lean-parity contract (adopted 2026-04-22)

The manuscript and the Lean formalization are a paired artifact. Every labeled environment — `definition`, `lemma`, `proposition`, `theorem`, `corollary` — in `algorithmic_free_energy_principle_award.v2.tex` has a 1-to-1 Lean counterpart recorded in `formalization_manifest.md` and the `manifestEntries` table in `AlgorithmicFreeEnergy/Manifest.lean`. This correspondence is load-bearing for the paper's credibility claim and must not be allowed to drift.

**The rule.** No change to the *statement* or *proof* of a labeled environment in the TeX may land without a simultaneous edit to the corresponding Lean declaration and a rerun of `scripts/generate_formalization_manifest.py` that leaves the `derived` status intact. The TeX label and the Lean `declName` listed in the manifest are immutable under prose passes; if either must change, it is a structural change and it must change on both sides in the same commit.

**What is in-scope for a prose pass.** Section titles, section ordering, introductions, section openers, paragraph framing, remark prose, the abstract, intro, conclusion, discussion, footnotes, citations, and forward/back-reference sentences. These carry no labels tracked by the manifest and are edit-safe as long as the `\ref{}` targets they name still exist.

**What is out-of-scope for a prose pass.** Rewording the *statement* inside a `theorem`/`proposition`/`lemma`/`corollary`/`definition` environment. Restating a hypothesis. Relabeling. Splitting or merging a labeled environment. Any of these is a math edit, not a prose edit, and invokes the Lean-parity rule above.

**Structural moves.** Relocating an entire labeled block (whole section, whole subsection, whole theorem with its remark) is permissible under a prose pass iff the labels, statements, and proof bodies move verbatim and the generated manifest still reports `paperFullyDerived = true`. Run the manifest script after any such move.

**Honest framing about formalization status.** The manifest tracks two axes. `paper-complete` (every manuscript item has a derived Lean counterpart) is currently `true`; `first-principles-complete` (every item is grounded in the concrete foundational stack rather than an abstract interface) is currently `false` — 1 of 106 items is on the concrete stack, 105 are on abstract interfaces. Any public claim about the Lean artifact must respect this distinction: "paper-complete machine verification" is supported; "fully machine-checked from first principles" is not yet supported and will overclaim if used. The audit files `formalization_audit.md` and `first_principles_target.md` define the targets.

## LLM-isms to avoid

These are the patterns that make text read like it was machine-generated, regardless of how it was actually written:

- "The slogan is simple," "The upshot is simple," "The point is simple"
- "Two entailments." "Three consequences." (as standalone paragraphs)
- "A skeptic who reads X is overreading"
- "is game-changing if taken seriously"
- Overuse of "the rhetoric that usually surrounds it"
- Opening gimmicks (medical vignettes, hypothetical scenarios, conversational openings) that do not earn their keep
- Meta-commentary on what the paper is about to do ("in what follows," "as we shall see")
- Repetition of the theorem statement inside the remark about the theorem

## What each formal remark does

A good remark is 2–4 sentences. It does exactly one of:

- Says what would fail without this result (necessity-framing)
- Points to which later result consumes this one (forward-reference)
- Names the community tradition this result corresponds to (positioning)
- Warns the reader about an available misreading (hedge)
- Converts a technical statement into a "so what" a reader would quote (translation)

It does not restate the theorem, and it does not apologize for the theorem.

## When positioning against competitors

Name the paper. Name the authors. Identify three or four load-bearing differences in the same paragraph. The differences are not weaknesses of the competitor; they are the axes along which our paper is different, and each axis should be one a reader can evaluate independently. End the positioning paragraph by saying, in one sentence, what the competitor supplies that we use (or could use) rather than pretending the overlap is zero.

## What this paper taught me

The boxed problem was the turning point. Once the question was stated in one sentence, every section had a clear test: does this paragraph help answer the question, or does it not? The remarks became easy to write because each theorem had a clear role in the answer. The trim to 15 pages was mostly automatic once the test was in place. The structural moves (proofs to appendix, remarks inserted, problem boxed) compounded: each made the next one easier.

The other lesson is about scope control. When you asked for a professionalism pass, the output was a professionalism pass; when you asked for positioning, the output was positioning. No pass tried to do everything. That is why each pass landed.
