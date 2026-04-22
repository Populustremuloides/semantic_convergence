# Narrative Pass — Achievements, Ranking, Sell-Quality, and Phased Surgical Plan

**Scope.** This pass is *prose-only*. The Lean formalization now pins the math in 1-to-1 correspondence with the TeX object ledger (see `formalization_manifest.md`), so every edit in the phases below is constrained to: (i) changing no theorem, proposition, lemma, corollary, or definition statement; (ii) changing no proof; (iii) changing no label that `formalization_manifest.md` references. Forwardand-back references, section order, section titles, paragraph-level framing, abstract/intro/conclusion rhetoric, and remark prose are all in-scope. Structural moves of entire blocks (e.g. relocating a subsection) are permissible iff labels and statements are preserved verbatim and the manifest still checks.

---

## 1. The Inventory of Achievements

Numbered for reference. Labels in parentheses are the canonical Lean-derived anchors.

1. **Master support theorem** (`thm:separating-support-convergence`): a single sufficient condition for posterior concentration on $[p^\star]$ — universal prior, Bayes/Gibbs belief, semantic separation, and divergent cumulative policy mass on separating actions. The paper's centerpiece.

2. **Master support rate** (`thm:separating-support-rate` + `cor:separating-support-finite-time`): the finite-time quantitative companion — explicit Azuma-style high-probability and expectation-form bounds under bounded log-likelihood ratios. Upgrades the centerpiece from asymptotic to quantitative.

3. **Four-observer / four-set organizing frame** (`def:observer`, `thm:strict-hierarchy`, `thm:factor-through-quotient`): the nested hierarchy $\{p^\star\}\subseteq[p^\star]\subseteq R_\pi(p^\star)\subseteq R_{h_t}(p^\star)$ as the indistinguishability classes of four observers, with the observable-quotient theorem pinning $[p^\star]$ as the theorem-level ceiling. The book-keeping frame that makes every other result legible.

4. **Three-tradition unification on the belief side** (`def:afe`, `lem:variational`, `lem:kl-necessity`, `cor:efe-specialization`): algorithmic free energy as the single variational object that couples the Solomonoff universal prior, the Gibbs variational form of active inference, and the information-gain criterion of Bayesian experimental design / compression-based curiosity.

5. **AFE near-miss** (`thm:afe-near-miss`): a same-architecture, arbitrary-horizon convergence-failure family under a substituted finite-support prior. Shows the three-way unification is not the whole story — it is the *half* that suffices on the belief side.

6. **Observer-promotion failure** (`thm:observer-promotion-failure`, `cor:observer-promotion-universal`): the observer-level reading of (5). The realized AFE policy induces $\omega_{\pi^\sharp}<\omega_{\mathrm{behav}}$ strictly, and this strict refinement gap is prior-independent. This is the failure's structural signature.

7. **Matched converse pair** (`cor:support-necessary`, `thm:summable-support-insufficient`): zero separating support makes uniform recovery impossible; summable separating support is insufficient. Together these show the master support condition is close to sharp.

8. **Three canonical realizations of the master support theorem**, each with a worked proof of the support-budget floor:
   - **Canonical selector** (`thm:semantic-convergence`, `def:semantic-rule`) — the class-against-complement rule at $\omega_A=\omega_{\mathrm{behav}}$.
   - **Exact kernel lift** (`thm:kernel-semantic-convergence`, `prop:kernel-functional-minimizer`) — the selector-free Gibbs kernel, the strongest *exact* variational realization.
   - **Amortized surrogate** (`thm:amortized-surrogate`, `prop:amortized-surrogate-minimizer`, `cor:amortized-surrogate-finite-time`) — a differentiable finite-latent-class loss that inherits the same guarantee under hypotheses (A1)–(A3). This is the theorem-facing bridge to implementable learners.

9. **Compact-action extension** (`cor:compact-action-kernel`, with `prop:kernel-functional-minimizer-compact`, `prop:compact-action-kernel-separation`): the exact kernel route survives on compact metric action spaces under explicit continuity and full-support hypotheses.

10. **Meeting-point theorem and the two-observer functional architecture** (`thm:meeting-point`, `def:two-observer-functional`, `prop:action-cap`): the admissible observer range $\omega_A\le\omega_{\mathrm{behav}}$, the structural reason AFE lives strictly above it, and the "observer dial" formalism that makes the boundary example legible as a boundary.

11. **Self-referential reduction of the computability gap** (`def:self-ref-rule`, `prop:self-ref-obstruction`, `thm:self-ref-convergence`, `thm:self-ref-sharp`, `thm:self-ref-exploratory`, `thm:self-ref-exploratory-rate`): the finitary proxy partition, the obstruction to unconditional eventual isolation, and the two escapes — deterministic splitting (sharpened) and divergent exploration (exploratory). The honest account of how far the self-referential rule can be pushed without an oracle.

12. **Full-support exploration floor → behavioral observer recovery** (`prop:full-support-behavioral`, `thm:exploration-floor-behavioral`): divergent cumulative exploration mass alone recovers $\omega_{\mathrm{behav}}$ and delivers semantic convergence for any $p^\star$. A clean standalone statement.

13. **Observer-promotion contrast on a single problem** (`cor:promotion-contrast`): runs AFE and any promotion-supporting rule on the same enlarged near-miss instance, with the AFE posterior ratio $q_t^\star(p'\mid H_t)/q_t^\star(p^\star\mid H_t)$ frozen at the prior ratio while the promotion-supporting rule expels $p'$. The single-problem comparative test.

14. **Chernoff/Pearl/Blackwell positioning**: the class-against-complement rule as a universal-prior, countable-hypothesis extension of Chernoff's asymptotically optimal sequential test; the knowability gap as an algorithmic analogue of Pearl's do-calculus identifiability; and Definition~\ref{def:observer}'s refinement preorder as a direct descendant of Blackwell comparison.

15. **Underdetermination formalization**: Theorem~\ref{thm:policy-gap} as a formalization of Quine's underdetermination; Theorem~\ref{thm:factor-through-quotient} as the formal content of van Fraassen's empirical adequacy thesis; Theorem~\ref{thm:semantic-convergence} as the Putnamian reference-fixing theorem for interactive learning. A legitimate, substantive philosophical payoff that follows from the observer frame, not a decorative aside.

16. **Lean formalization parity**: 106 core declarations, all `derived` in Lean 4, 1-to-1 with the TeX object ledger (see `formalization_manifest.md`, `formalization_audit.md`). This is a meta-achievement — not a theorem in the paper, but a structural fact about the paper that changes how it should be marketed in cover letters, advertisement sentences, and the conclusion.

---

## 2. Tiered Ranking

### Tier A — Must headline (title, abstract, introduction opener, problem-box neighborhood, conclusion)

- **#1** Master support theorem (the "central answer").
- **#2** Master support rate (turns the answer from asymptotic to finite-time).
- **#3** Four-observer / four-set hierarchy + observable-quotient ceiling (the organizing image every reader must carry out of the abstract).
- **#5** AFE near-miss (the rhetorical jaws — "the obvious unification does *not* suffice").
- **#4** Three-tradition unification on the belief side (the jaws' other half — "the obvious unification is exact here").

### Tier B — Highlight, but not in the top power positions

- **#7** Matched converse pair (the sharpness signal; currently badly undersold — see §3).
- **#8** Three canonical realizations (selector, kernel, amortized surrogate); the first two are well-placed, the amortized surrogate is badly undersold — see §3.
- **#9** Compact-action extension (currently well-placed in the abstract; keep).
- **#6** Observer-promotion failure as the structural reading of the near-miss (adjacent to Tier A; already well-positioned).
- **#12** Full-support exploration floor → behavioral observer recovery (currently lives inside Section 9 and the self-ref section; should be named more clearly in the abstract or intro as one of the three ways the support condition is met).
- **#16** Lean formalization parity (cover-letter-level claim; worth a single sentence in the abstract or conclusion announcing that the results are machine-checked to one-to-one correspondence).

### Tier C — Supporting (present in the body at appropriate granularity; do not contend for abstract or intro power positions)

- **#10** Two-observer functional + meeting-point theorem (the scaffold; keep as the architectural chapter but do not fight for headline space).
- **#11** Self-referential section (the honest-account chapter; do not over-sell — its results are conditional, and the exploration-completed escape already rides on #12).
- **#13** Observer-promotion contrast (one-problem comparative; an in-section quantitative punch for Section 10, not a headline).
- **#14** Chernoff/Pearl/Blackwell positioning (Discussion-level; already well-placed).
- **#15** Quine/van Fraassen/Putnam underdetermination (Discussion-level; already well-placed).

---

## 3. How Well Does the Manuscript Currently Sell Each Core Point?

Rated as **well-sold**, **adequate**, or **under-sold**, with specific location evidence.

| # | Achievement | Current Sell-Quality | Where it lives | What's wrong (if anything) |
|---|-------------|----------------------|----------------|----------------------------|
| 1 | Master support theorem | Well-sold | Abstract ("central answer is a single sufficiency theorem"), intro ("master support theorem"), Section 9 opener | Title is now "Sufficient Conditions…" which carries it; good. |
| 2 | Master support rate | Adequate | Abstract (1 sentence on "explicit finite-time high-probability lower bounds"), §sec:exp-rate | Abstract sentence is dry; does not convey that the bound is explicit and closed-form. The intro reiterates. |
| 3 | Four-observer / four-set hierarchy | Under-sold in abstract | Intro ¶2 (strong), §sec:hierarchy | The word "observer" does not appear in the abstract. The four-set nested chain is the frame every downstream claim depends on; it should be in the abstract in at least one sentence. |
| 4 | Three-tradition unification (belief side) | Well-sold | Abstract ("two unifications are exact"), intro ¶3, `rem:efe-unification` | Carries its weight; no surgery needed. |
| 5 | AFE near-miss | Adequate | Abstract ("Perhaps unintuitively… need not concentrate at any horizon"), intro ¶4 | The rhetorical jaws are softer than warranted. "Perhaps unintuitively" understates. The observer-level reading (#6) is mentioned in the intro but not the abstract. |
| 6 | Observer-promotion failure | Adequate | Intro ¶4, `thm:observer-promotion-failure`, `cor:observer-promotion-universal`, `rem:near-miss-universal` | Well-positioned in the boundary section; intro captures the one-liner. No surgery needed except ensuring the intro's statement stays crisp. |
| 7 | Converse pair | **Under-sold** | Intro brushes it ("matched converse theorems showing what fails when separating support is absent or only summable"), Discussion first paragraph gives a short summary | Not in the abstract at all. The symmetric pair (zero-support impossibility + summable-support insufficiency) is exactly what converts "a sufficient condition" into "a *sharp* sufficient condition", which is the headline claim most reviewers will stress-test. Abstract must acknowledge this. |
| 8 | Three canonical realizations | Selector + kernel well-sold; amortized surrogate **badly under-sold** | Abstract mentions kernel and selector; amortized surrogate only surfaces in `sec:amortized-surrogate` as a subsection of §sec:implications | The amortized surrogate (`thm:amortized-surrogate`, (A1)–(A3)) is the paper's bridge from the theorem to a practical latent-class / deep-learning-style learner. Burying it inside Implications means most readers will never see it. It deserves promotion to a subsection of Section 9 (Main) or a standalone section between §sec:main and §sec:near-miss, and a one-sentence mention in the abstract. |
| 9 | Compact-action extension | Well-sold | Abstract closing sentence; `cor:compact-action-kernel` | Fine as is. |
| 10 | Two-observer functional + meeting-point | Adequate (scaffold) | Section 5 opener; appears throughout | Should not fight for abstract space. Current balance is right. |
| 11 | Self-referential section | Under-sold honest / risk of over-sold dishonest | §sec:self-ref, 500 lines | The section is large and contains three escape routes (pure running-partition under eventual isolation; sharpened under deterministic splitting; exploration-completed). None of this is in the abstract. Probably the right call — the unconditional promise would be misleading — but the Conclusion should acknowledge the conditional escapes so the reader does not leave thinking we abandoned the self-referential thread. |
| 12 | Full-support exploration → behavioral recovery | Under-sold | `thm:exploration-floor-behavioral` inside §sec:main | This is a clean, unconditional escape: a divergent exploration budget alone delivers both observer promotion and posterior concentration. It is currently packaged as a theorem inside Section 9 with no abstract or intro air-time. At least a half-sentence mention in the abstract's "realizations" sentence would fix it. |
| 13 | Observer-promotion contrast (`cor:promotion-contrast`) | Adequate | Boundary section, `sec:promotion-contrast` | Good location. No surgery needed. |
| 14 | Pearl/Chernoff/Blackwell | Well-sold | Discussion ¶2 | Fine. |
| 15 | Quine/van Fraassen/Putnam | Well-sold | Discussion ¶3 | Fine. |
| 16 | Lean formalization parity | **Missing from the paper** | Only in `formalization_manifest.md` | The paper should announce this, since it is the single strongest credibility signal available for a 100+ page theoretical paper. One sentence in the abstract and one paragraph in the Conclusion referring readers to an appendix (or to the public Lean artifact) suffices. |

**Summary.** The manuscript sells the belief-side unification and the master support theorem reasonably well, and the realizations + converses are present in the body. It *under-sells*:

- the four-observer organizing frame at abstract granularity;
- the converse pair as a sharpness claim;
- the amortized surrogate, by burying it;
- the full-support exploration escape, by never naming it in the abstract;
- the Lean-parity meta-achievement, by not mentioning it at all.

---

## 4. Phased Surgical Prose Plan

Each phase is a narrow, reviewable diff. Phases are ordered so that later phases assume earlier ones have landed and not the reverse. No phase changes math. Any phase that moves a block preserves the label-verbatim rule.

### Editing contract update (proposed; awaiting sign-off)

Before Phase N1 lands, add the following to `drafting_rules.md`:

> **Lean-parity contract (added 2026-04-22).** No change to theorem, proposition, lemma, corollary, or definition *statements* or *proofs* may be made in `algorithmic_free_energy_principle_award.v2.tex` without a simultaneous edit to the corresponding Lean module(s) listed in `formalization_manifest.md`. Every PR/commit that touches a labeled environment must be accompanied by (i) the corresponding Lean edit, and (ii) a rerun of `scripts/generate_formalization_manifest.py` that leaves the `derived` status intact. Labels referenced by the manifest are immutable under prose-only passes. Section titles, ordering of sections/subsections, introductions, section openers, remarks, the abstract, intro, conclusion, and discussion are not labeled environments and are edit-safe under prose-only passes.

### Phase N1 — Abstract surgery

*Goal.* Make the abstract load-bear the six Tier-A items: master support theorem + rate (#1, #2), four-observer frame (#3), belief-side unification (#4), near-miss as symmetric counterpoint (#5), converse pair (#7). Add a half-sentence mention of the amortized surrogate (#8c), a half-sentence on Lean parity (#16), and a clause on the exploration floor (#12). No theorem restatements — the abstract is a rhetorical object.

*Scope.* L53–55 only. Roughly one-to-one replacement of the existing paragraph with a reorganized one. Word budget: stay within 10–15% of current length.

*Risk.* Low. Abstract is label-free.

### Phase N2 — Introduction surgery

*Goal.* Three edits.

1. Ensure intro ¶2 (the four-set hierarchy) lands with the observer-promotion thesis explicit. Current text already does this fairly well; tighten.
2. Ensure intro ¶4 (the near-miss) carries the observer-promotion-failure reading (`thm:observer-promotion-failure`) in the same paragraph, not deferred. Currently done, but ensure the language is crisp.
3. Insert a single sentence acknowledging the converse pair (#7) so the intro matches the revised abstract.
4. Insert a half-sentence forward-referencing the amortized surrogate (#8c) in the intro's final paragraph (the roadmap).

*Scope.* L57–84. Sentence-level edits across four paragraphs, no paragraph-level rewrite.

*Risk.* Low.

### Phase N3 — Elevate the amortized surrogate

*Decision needed.* Either:

- **Option 3a (conservative):** Leave the subsection where it is (inside §sec:implications) but (i) rename the subsection to signal it more prominently, (ii) add a forward-reference sentence in §sec:main's concluding remark, and (iii) add a backward-reference sentence in the Conclusion.
- **Option 3b (structural, but still label-preserving):** Move `sec:amortized-surrogate` as a whole block out of §sec:implications and promote it either to a standalone Section between §sec:near-miss and §sec:implications, or to a subsection of §sec:main. All labels, statements, and proofs move verbatim. Regenerate the manifest.

I recommend **3b with promotion to a standalone section after `sec:main` and before `sec:near-miss`**, because: it reads as the third realization of the master support theorem (selector, kernel, amortized surrogate), which is the right logical position; §sec:near-miss then runs against all three rather than just against the selector; and the formalization manifest already tracks it as a distinct theorem cluster.

*Scope.* L3697–3915 as a unit; plus two forward/back-reference sentences in §sec:main's closing remark and in the Conclusion.

*Risk.* Moderate. Must rerun `scripts/generate_formalization_manifest.py` and confirm every `derived` row still resolves. Must confirm no section-number cross-reference breaks.

### Phase N4 — Section 9 opener + `rem:functional-payoff` trim

*Goal.* The opening paragraph of §sec:main (L1678) is long and does the work of a mini-TOC. Tighten. Follow it with a one-line summary of the three realizations + two converses after Phase N3 lands.

Also trim `rem:functional-payoff` (currently 10+ lines dense), which does the same work twice.

*Scope.* L1676–1682 and the `rem:functional-payoff` block (around L2373–2376).

*Risk.* Low. Section opener is prose; remark is labeled but its content is exposition (labels immutable, prose editable).

### Phase N5 — Boundary-example section opener

*Goal.* The opener of §sec:near-miss already frames the AFE principle as a boundary, not a competitor. Check that the post-Phase-N1 abstract and post-Phase-N2 intro language is consistent with it; trim if redundant.

*Scope.* L3402–3406.

*Risk.* Low.

### Phase N6 — Conclusion surgery

*Goal.* Post-abstract reform, the Conclusion (currently one long paragraph at L3934–3937) should mirror the abstract's structure: four-set hierarchy → belief-side unification → near-miss → master support theorem and its three realizations → converse sharpness → Lean parity meta-claim. Consider breaking into two paragraphs, one for the answer and one for the frame.

Explicitly mention the Lean formalization in a closing sentence (reference `formalization_manifest.md` or a public artifact URL placeholder).

*Scope.* L3934–3937 only.

*Risk.* Low.

### Phase N7 — Discussion tightening

*Goal.* The Pearl/Chernoff/Blackwell paragraph (L3922) and the Quine/van Fraassen/Putnam paragraph (L3924) are strong. Verify they land cleanly against the post-Phase-N1 abstract. The "three open questions" paragraph (L3926–3932) reads well but the third open question references `sec:amortized-surrogate` — if Phase N3 moves it, update the cross-reference.

*Scope.* L3917–3932.

*Risk.* Low.

### Phase N8 — Title audit

*Goal.* The current title "Sufficient Conditions for Semantic Convergence in Interactive Learning" is accurate and sells the sufficiency pivot. Optional secondary title: consider a subtitle rather than a full replacement, e.g. "…: Algorithmic Free Energy, the Four-Observer Frame, and a Master Support Theorem." Verdict: probably leave as-is unless the rest of the pass reveals a cleaner option.

*Scope.* L45.

*Risk.* Near-zero.

### Phase N9 — Whole-document read-through

*Goal.* Read abstract → intro → Section 9 opener → amortized-surrogate section (new location) → boundary section → Discussion → Conclusion as a single narrative. Check: pronoun continuity, forward/back-reference integrity, no orphan claims, no tone mismatch between the reformed abstract and a not-yet-reformed body paragraph.

*Scope.* Full manuscript pass, read-only + sentence-level tweaks.

*Risk.* Low. This is the integration pass.

### Phase N10 — Lean-parity check

*Goal.* Run `scripts/generate_formalization_manifest.py`; diff the manifest against the pre-pass manifest; confirm that every theorem/proposition/lemma/corollary/definition label that was `derived` remains `derived` and is mapped to the same Lean declaration. If Phase N3 moved a subsection, only the section-number fields change — not the label-to-module map.

*Scope.* Script execution + manifest diff review.

*Risk.* Low if Phases N1–N9 honored the label-immutability rule; otherwise the manifest diff will surface violations.

---

## 5. Recommended execution order

The phases are already in execution order, but the decision-bearing gates are:

1. **Gate 1 — contract update.** Confirm the proposed Lean-parity contract language for `drafting_rules.md`.
2. **Gate 2 — amortized surrogate placement.** Confirm Option 3a vs. 3b for Phase N3 before starting abstract or intro surgery (the abstract's "three realizations" sentence depends on this choice).
3. **Gate 3 — Lean parity URL.** If the Conclusion is going to cite a public Lean artifact, supply the URL; otherwise the reference will be to the in-tree `formalization_manifest.md`.

Once those three gates are closed, Phases N1 → N10 can be executed in sequence with a single review per phase.
