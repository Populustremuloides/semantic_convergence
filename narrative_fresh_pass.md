# Fresh Narrative Pass — Independent Assessment + Surgical Edit Plan

*Author note: This is a fresh read of `algorithmic_free_energy_principle_award.v2.tex` against the Lean manifest and the existing `narrative_pass_plan.md`. It agrees with that plan on most specifics and differs in three places that are called out explicitly. The Lean-parity contract has been added to `drafting_rules.md`.*

*Ground truth consulted: abstract + intro (L53–84); sec:main opener (L1676–1682); sec:near-miss opener (L3402–3406) and AFE identification (L3406–3430); sec:self-ref opener (L2907–2945); sec:implications opener (L3684–3696) and amortized surrogate (L3697+); Discussion (L3917–3932); Conclusion (L3934–3937); `formalization_manifest.md`; `AlgorithmicFreeEnergy/Manifest.lean`; `AlgorithmicFreeEnergy/ConcreteCore.lean`; `first_principles_target.md`.*

---

## 0. Status snapshot

- TeX: 243 KB, 14 sections, 106 labeled environments, one-paragraph abstract, boxed problem after intro ¶4, bibliography attached.
- Lean: 106 manifest entries, all `derived`; 1 on `concrete-stack` (the `Observer` definition) and 105 on `abstract-interface`. `paperFullyDerived = true`; `fullyFirstPrinciples = false`.
- Drafting rules: Lean-parity contract added today. Math/statement edits now require simultaneous Lean edits and manifest regeneration.

---

## 1. What the paper actually achieves (ranked, load-bearing only)

Numbered for internal reference. Tiering reflects narrative power, not technical difficulty; some Tier-C items are harder than some Tier-A items.

### Tier A — must headline (abstract / intro opener / problem box / conclusion)

1. **Master support theorem** (`thm:separating-support-convergence`). One sufficient condition for almost-sure concentration on $[p^\star]$: universal prior + Bayes/Gibbs belief + semantic separation + divergent cumulative policy mass on separating actions. This is the paper's answer to the boxed problem.

2. **Master support rate** (`thm:separating-support-rate` + `cor:separating-support-finite-time` + `thm:exp-rate-concentration`). The quantitative companion: explicit Azuma-style finite-time high-probability lower bounds under bounded LLR. Turns the asymptotic answer into a finite-time guarantee.

3. **Four-observer frame and strict knowability hierarchy** (`def:observer`, `thm:strict-hierarchy`, `thm:factor-through-quotient`). The four nested sets $\{p^\star\}\subseteq[p^\star]\subseteq R_\pi(p^\star)\subseteq R_{h_t}(p^\star)$ as the indistinguishability classes of four observers at increasing observational power, with the observable-quotient theorem pinning $[p^\star]$ as the theorem-level ceiling. *This is the paper's organizing image.*

4. **Three-tradition unification on the belief side** (`def:afe`, `lem:variational`, `lem:kl-necessity`, `cor:efe-specialization`). Algorithmic free energy as the single variational object that exactly couples the Solomonoff universal prior, the Gibbs variational form of active inference, and the information-gain criterion of Bayesian experimental design / compression-based curiosity. The "exact" side of the paper's rhetorical jaw.

5. **AFE near-miss** (`thm:afe-near-miss`) + **observer-promotion failure** (`thm:observer-promotion-failure`, `cor:observer-promotion-universal`). Same Bayes/Gibbs/EFE architecture, substituted finite-support prior, arbitrary horizon, posterior on $[p^\star]$ frozen at prior mass. The failure's structural signature is that the realized policy induces $\omega_{\pi^\sharp}<\omega_{\mathrm{behav}}$ strictly, and that gap is prior-independent. The "fails" side of the jaw.

### Tier B — highlight in body power positions (section openers, dedicated remarks, one abstract/intro sentence each)

6. **Matched converse pair** (`cor:support-necessary`, `thm:summable-support-insufficient`). Zero separating support → uniform recovery impossible; summable separating support → can still fail with positive probability. Together with (1), these convert "a sufficient condition" into "a *sharp* sufficient condition."

7. **Three canonical realizations of the master theorem**:
   - **Canonical selector** (`thm:semantic-convergence`, `def:semantic-rule`) — class-against-complement at $\omega_A=\omega_{\mathrm{behav}}$.
   - **Exact kernel lift** (`thm:kernel-semantic-convergence`, `prop:kernel-functional-minimizer`) — the selector-free Gibbs kernel; strongest exact variational realization under finite actions.
   - **Amortized surrogate** (`thm:amortized-surrogate`, `prop:amortized-surrogate-minimizer`, `cor:amortized-surrogate-finite-time`) — differentiable finite-latent-class loss that inherits the same guarantee under (A1)–(A3). The theorem-facing bridge to implementable learners.

8. **Full-support exploration floor → behavioral recovery** (`prop:full-support-behavioral`, `thm:exploration-floor-behavioral`). Divergent cumulative exploration mass alone promotes the observer to $\omega_{\mathrm{behav}}$ and delivers semantic convergence for any $p^\star$. Clean, unconditional, one-line statement.

9. **Compact-action extension** (`cor:compact-action-kernel` + `prop:kernel-functional-minimizer-compact` + `prop:compact-action-kernel-separation`). Exact kernel route survives on compact metric action spaces under explicit continuity and full-support hypotheses. Addresses the "but actions are continuous" objection.

10. **Self-referential reduction of the computability gap** (`def:self-ref-rule`, `prop:self-ref-obstruction`, `thm:self-ref-convergence`, `thm:self-ref-sharp`, `thm:self-ref-exploratory`, `thm:self-ref-exploratory-rate`). The finitary proxy partition addresses the obvious "$[p^\star]$ is not computable" objection. Unconditional eventual isolation fails, but two escapes — deterministic splitting (sharpened) and divergent exploration (exploratory) — recover the main theorem's guarantee.

11. **Lean-parity meta-achievement** (`formalization_manifest.md`, `Manifest.lean`). 106-of-106 manuscript items have derived Lean counterparts; the paper and proof assistant agree statement-by-statement. *See §5 for honest framing.*

### Tier C — present in the body, do not fight for headline space

12. **Two-observer functional + meeting-point theorem** (`def:two-observer-functional`, `thm:meeting-point`, `prop:action-cap`, `cor:canonical-pair`). The architectural chapter that makes (1), (4), (5), and the admissible-range reading of AFE all legible. Essential scaffold; not the headline.

13. **Observer-promotion contrast on a single problem** (`cor:promotion-contrast`). The one-problem quantitative test comparing AFE and a promotion-supporting rule. A body-level punch, not a title-level one.

14. **Chernoff / Pearl / Blackwell positioning** (Discussion ¶2). Extension of Chernoff's sequential test; algorithmic analogue of Pearl's do-calculus identifiability; Definition~\ref{def:observer} as a descendant of Blackwell comparison. Discussion-level scholarship, not headline.

15. **Quine / van Fraassen / Putnam** (Discussion ¶3). Theorem~\ref{thm:policy-gap} as formal content of Quine's underdetermination; Theorem~\ref{thm:factor-through-quotient} as empirical-adequacy formalization; Theorem~\ref{thm:semantic-convergence} as a reference-fixing theorem. Substantive philosophical payoff; Discussion-level.

16. **Noise robustness** (`prop:noise-immunity`, `prop:noise-left-invertible`, `cor:noise-transfer`, `cor:noise-left-invertible-history-independent`). Transfer under decodable recodings and left-invertible finite noise. Present in body (Section 9), correctly placed, probably undersold but not urgent.

---

## 2. How well does the manuscript sell each item? (Independent read)

Rated against the same three-point scale: **well**, **adequate**, **under-sold**. Agreement / disagreement with `narrative_pass_plan.md` noted.

| # | Achievement | Sell quality | Evidence | Agreement |
|---|-------------|--------------|----------|-----------|
| 1 | Master support theorem | well | Abstract headlines it ("the paper's central answer is a single sufficiency theorem"); intro roadmap (L82) names it with full hypothesis list; §sec:main opener restates. Title carries it. | Agree with plan |
| 2 | Master support rate | adequate | Abstract has one dry sentence; intro repeats. Does not convey that the bound is explicit and closed-form. | Agree with plan |
| 3 | Four-observer frame | **under-sold in abstract, well-sold in intro** | The word "observer" does not appear in the abstract. Intro ¶2 is strong and names the promotion thesis. | Agree with plan |
| 4 | Belief-side unification | well | Abstract names "two unifications are exact"; intro ¶3 lays it out; `rem:efe-unification` lands it. | Agree with plan |
| 5 | AFE near-miss + observer-promotion failure | **adequate, but the rhetorical frame is soft** | Abstract says "Perhaps unintuitively… need not concentrate at any horizon." Intro ¶4 carries the observer reading. The jaws are real but understated. | Agree with plan |
| 6 | Matched converse pair | **under-sold — missing from abstract** | Intro touches it in the roadmap ("matched converse theorems showing what fails when separating support is absent or only summable"); Discussion has one sentence; Conclusion has one sentence. Abstract silent. | Agree with plan |
| 7a | Selector realization | well | Abstract + intro + sec:main opener all name it. | Agree |
| 7b | Exact kernel lift | well | Same; abstract specifically names "the exact minimizing class-action kernel of the kernel lift is the strongest exact variational realization." | Agree |
| 7c | Amortized surrogate | **badly under-sold — buried in §sec:implications** | Surfaces only in a subsection of Implications. Abstract silent. Intro silent. Conclusion has one sentence ("Section~\ref{sec:amortized-surrogate} records the implementation-facing version of the same theorem") which is a forward reference to a subsection that most readers never reach. This is the paper's bridge from Solomonoff-style theory to deep-learning-style practice; burying it is a real loss. | Agree with plan, and I second the 3b recommendation (promote to standalone section). |
| 8 | Full-support exploration floor | **under-sold** | Lives as a theorem inside §sec:main. No abstract or intro air-time. This is a *clean unconditional positive result* — an exploration budget alone recovers $\omega_{\mathrm{behav}}$ — and it belongs in the abstract's "realizations" sentence. | Agree with plan |
| 9 | Compact-action extension | well | Abstract's closing sentence; `cor:compact-action-kernel` in Section 9; Conclusion sentence. | Agree |
| 10 | Self-referential section | **adequate inside the paper, under-sold in framing** | The section itself is honest and careful. But no abstract/intro mention at all. *I differ with the prior plan here, which ranks this Tier C.* See §3. | **Disagreement** — I promote to Tier B. |
| 11 | Lean-parity meta-achievement | **absent from the manuscript** | No mention of Lean anywhere in the TeX. | Agree with plan |
| 12 | Two-observer functional | adequate scaffold | §sec:functional opens well; `rem:functional-payoff` does some heavy lifting; correctly doesn't fight for headline. | Agree |
| 13 | Observer-promotion contrast | adequate | Good location in `sec:promotion-contrast`. No surgery. | Agree |
| 14 | Chernoff/Pearl/Blackwell | well | Discussion ¶2. | Agree |
| 15 | Quine/van Fraassen/Putnam | well | Discussion ¶3. | Agree |
| 16 | Noise robustness | adequate | Section 9 subsection, correctly placed, no headline claim. | Agree |

### Summary of under-sells

Ranked by how much it costs the paper:

1. Amortized surrogate buried in Implications — #1 surgical priority.
2. Lean-parity absent from the manuscript — costs nothing to fix, buys a lot.
3. Matched converse pair absent from abstract — the sharpness claim is the thing reviewers stress-test.
4. Four-observer frame absent from abstract — the organizing image a reader should leave with.
5. Full-support exploration floor absent from abstract — a clean unconditional positive that reads well in one clause.
6. Self-referential reduction absent from abstract and intro — see §3.
7. Rhetorical jaw on the near-miss is soft — "Perhaps unintuitively" should go.

---

## 3. Three places I differ from `narrative_pass_plan.md`

**Disagreement 1 — self-referential reduction should be Tier B, not Tier C.** The existing plan argues the self-ref section is "conditional, over-selling is misleading." I read this differently. The honest version of the self-referential thread is: *the paper exposes where the class-against-complement rule hits a computability wall, formalizes a finitary proxy that the rule actually uses, and characterizes exactly when and how the proxy recovers the main theorem's guarantee.* That is a real contribution — it is the rigorous answer to the objection "but $[p^\star]$ is not computable, so the rule is an oracle rule." Leaving it silent in both abstract and intro cedes that objection. I propose ONE clause in the intro roadmap and ONE phrase in the Conclusion, both conditional in tone so they do not overclaim, e.g. in the roadmap: "Section~\ref{sec:self-ref} replaces the oracle at $\omega_{\mathrm{behav}}$ by a finitary running-partition proxy, with a convergence guarantee under eventual isolation (deterministic-splitting or exploration-completed)." Abstract stays silent — I agree that overloading the abstract with the conditional version is wrong.

**Disagreement 2 — ordering of phases.** The prior plan does N1 (abstract) → N2 (intro) → N3 (amortized-surrogate placement) in that order. I think N3 should come **first**. Reason: the abstract's "three realizations" sentence depends on whether the amortized surrogate becomes a section, and rewriting the abstract twice is wasteful. Reordered proposal below in §4.

**Disagreement 3 — honest framing of the Lean claim.** The prior plan proposes a one-sentence abstract mention of "machine-checked to one-to-one correspondence" and a Conclusion paragraph referring readers to `formalization_manifest.md`. This is fine as long as it says *paper-complete* rather than *first-principles complete*, or better, actively distinguishes the two. The manifest is explicit that only 1-of-106 items is on the concrete stack; 105 are on abstract interfaces. A reviewer who opens the Lean artifact will see this instantly. Overclaiming here would be the fastest way to lose credibility. Concrete proposal: the abstract sentence says "all 106 theorem, proposition, lemma, corollary, and definition statements are in machine-checked 1-to-1 correspondence with a Lean 4 formalization (artifact available on request)." The Conclusion paragraph names the distinction explicitly: "The formalization is paper-complete — every labeled environment has a derived Lean counterpart — but not yet fully grounded in a concrete foundational stack; the abstract-interface layer is currently the trust boundary." That is the honest version and it protects the credibility claim.

---

## 4. Phased surgical plan

Each phase is a narrow, reviewable diff. No phase changes math. The Lean-parity contract in `drafting_rules.md` governs; a phase that moves a labeled block verbatim preserves the manifest and requires only a rerun of the generator.

### Gate decisions (must close before any prose phase lands)

- **Gate 1 (closed):** Lean-parity contract added to `drafting_rules.md`.
- **Gate 2 (OPEN):** Amortized surrogate placement. Recommendation: **promote to a standalone section between `sec:main` and `sec:self-ref`**, titled e.g. *A Theorem-Facing Amortized Surrogate*. Narrative reads: "main theorem + two realizations (selector, kernel) → third realization (amortized surrogate) → self-referential reduction → boundary example." This is the same 3b option the prior plan proposed; I second it. *Brian signs off before Phase 0 starts.*
- **Gate 3 (OPEN):** Lean artifact citation. Choice: in-tree `formalization_manifest.md` URL placeholder, or external artifact URL (if there is one). Determines one sentence in the Conclusion.

### Phase 0 — Structural move (amortized surrogate)

*Goal.* Relocate `sec:amortized-surrogate` (currently L3697–3915) out of `sec:implications` and promote it to a standalone section between `sec:main` and `sec:self-ref`. Verbatim move: all labels, statements, proofs, remarks, equations unchanged.

*Scope.* Cut L3697–3915; paste at the end of `sec:main` as a new `\section{...}\label{sec:amortized-surrogate}` block. Re-title the subsection to a section header. Nothing else changes in Phase 0. No cross-reference updates yet (Phase 7 verifies).

*Risk.* Moderate. Run `scripts/generate_formalization_manifest.py`; confirm every `derived` row still resolves; confirm `paperFullyDerived = true` in the regenerated `Manifest.lean` (line counts inside `ManifestEntry` records will drift and must be updated — the script does this automatically). Confirm `lake build`.

*Acceptance.* Manifest regenerates cleanly. `paperFullyDerived_eq` and related theorems still type-check. Paper compiles. No `\ref{}` breaks.

### Phase 1 — Abstract surgery

*Goal.* One rewritten paragraph. Must load-bear:

- (1) master support theorem,
- (2) master support rate,
- (3) four-observer frame (one explicit sentence naming the observer hierarchy),
- (4) belief-side unification (kept),
- (5) near-miss (tightened; "perhaps unintuitively" deleted),
- (6) converse pair (one clause — "zero separating support is impossible and summable support is insufficient"),
- (7c) amortized surrogate (one clause: "…and a differentiable finite-latent-class surrogate that inherits the same guarantee"),
- (8) full-support exploration floor (one half-clause: "…and a divergent exploration budget suffices on its own"),
- (11) Lean parity (one sentence at the end, with the paper-complete qualifier).

*Scope.* L53–55. Word budget: stay within 110% of current length. Stay a single paragraph (drafting rule).

*Risk.* Low. Abstract is label-free.

*Acceptance.* Compression test (between every two sentences, the sentence can be combined); "grammar, not announcement" rule holds; no "our contribution is" / "we show that" framing.

### Phase 2 — Introduction surgery

*Goal.* Four sentence-level edits in four existing paragraphs. No paragraph-level rewrite.

1. ¶2 (four-set hierarchy): tighten; keep the promotion thesis; ensure `Definition~\ref{def:observer}` is cited where the word "observers" first appears. Currently fine; minor tweaks.
2. ¶4 (near-miss): ensure the observer-promotion-failure reading lands in the same paragraph (it currently does) and delete any residual "perhaps unintuitively"–style softening.
3. Insert ONE sentence after ¶4 naming the converse pair (mirrors the revised abstract).
4. Roadmap ¶ (currently final paragraph of §sec:intro): insert the amortized-surrogate section forward-reference (post–Phase 0, this is now a real section number). Also insert ONE conditional sentence on the self-referential thread (see Disagreement 1).

*Scope.* L57–84. Sentence-level edits across four paragraphs.

*Risk.* Low.

### Phase 3 — `sec:main` opener + `rem:functional-payoff` trim

*Goal.* Section 9 opener (L1678) runs long and does the job of a mini-TOC. Tighten to one paragraph naming: (i) the master theorem, (ii) the two realizations (selector, kernel) proved inside the section, (iii) the matched converses, (iv) the quantitative rate. With Phase 0 landed, the amortized surrogate becomes the *next* section and is not named in this opener.

Trim `rem:functional-payoff` (around L2373–2376) — currently 10+ lines dense, doing the same work twice. Keep the labeled environment (Lean-parity rule), edit the remark prose inside it.

*Scope.* L1676–1682 opener; `rem:functional-payoff` body.

*Risk.* Low.

### Phase 4 — `sec:near-miss` opener check

*Goal.* Opener at L3402–3406 already frames the AFE principle as a boundary rather than a competitor, and names Theorem~\ref{thm:afe-near-miss}, Theorem~\ref{thm:observer-promotion-failure}, Proposition~\ref{prop:action-cap}. Post–Phase 1 abstract will land the same "wrong-observer geometry" reading; confirm the opener does not now redundantly restate what the abstract just said. If there is redundancy, cut, do not restate.

*Scope.* L3402–3406.

*Risk.* Low.

### Phase 5 — Conclusion surgery

*Goal.* Current Conclusion is one long paragraph (L3934–3937). Mirror the revised abstract's structure. I propose two paragraphs:

- ¶A (the answer): four-observer frame → belief-side unification → near-miss as boundary → master support theorem → three realizations (selector, kernel, amortized surrogate) → converse sharpness.
- ¶B (the frame + meta-claim): observer-promotion as the organizing informal concept + the self-referential closure → the Lean-parity sentence with paper-complete qualifier → one closing sentence on what changes for the reader who accepts the paper.

*Scope.* L3934–3937.

*Risk.* Low. No labeled environments involved.

### Phase 6 — Discussion tightening

*Goal.* Discussion already strong (Chernoff/Pearl/Blackwell + Quine/van Fraassen/Putnam + three open questions). Two checks:

- The "three open questions" paragraph's third question references `sec:amortized-surrogate`; post–Phase 0, that cross-reference is now a section rather than a subsection. Update the sentence to read naturally under the new numbering.
- The first paragraph already mentions the converse pair; verify post–Phase 1 abstract does not make this Discussion paragraph redundant. If the abstract now says almost the same thing, trim the Discussion paragraph to focus on what the abstract did not say.

*Scope.* L3917–3932.

*Risk.* Low.

### Phase 7 — Whole-document read-through

*Goal.* Read abstract → intro → `sec:main` opener → (new) amortized-surrogate section opener → self-ref opener → near-miss opener → Discussion → Conclusion as one narrative. Catch pronoun mismatches, forward/back-reference integrity, tone drift between reformed abstract/intro/conclusion and not-yet-touched body paragraphs. Sentence-level tweaks only.

*Scope.* Full manuscript, read-only + sentence-level edits.

*Risk.* Low.

### Phase 8 — Lean-parity final check

*Goal.* Run `scripts/generate_formalization_manifest.py`. Diff the regenerated `formalization_manifest.md` and `Manifest.lean` against the pre-pass versions. Confirm: (i) label-to-module map unchanged (only line-number fields updated); (ii) every row that was `derived` is still `derived`; (iii) `paperFullyCovered_eq` and `paperFullyDerived_eq` still reduce by `native_decide`; (iv) `lake build` passes.

If Phase 0 moved the section verbatim and Phases 1–7 touched only prose, this should be a no-op except for line-number changes. If something drifted, the manifest diff surfaces it.

*Scope.* Script execution + manifest diff review.

*Risk.* Low if the Lean-parity contract was honored.

### Phase 9 — Title audit (optional, defer to end)

*Goal.* Current title "Sufficient Conditions for Semantic Convergence in Interactive Learning" carries the main theorem; it does not carry the observer frame or the AFE story. Two candidate alternatives:

- Keep as-is.
- Add a subtitle: "Sufficient Conditions for Semantic Convergence in Interactive Learning: Observer Promotion and the Algorithmic Free Energy Principle."

My recommendation: decide after Phase 7 read-through, not before. If the reformed abstract makes the observer/AFE framing feel load-bearing in the first reading, the subtitle earns its keep; otherwise leave it.

*Scope.* L45.

*Risk.* Near-zero.

---

## 5. Lean-parity claim language (for Phase 1 abstract and Phase 5 conclusion)

Two ready-to-drop sentences, calibrated to the honest state.

**Abstract sentence (candidate; Phase 1).**
> All 106 definitions, lemmas, propositions, theorems, and corollaries are in machine-checked 1-to-1 correspondence with a Lean 4 formalization; the artifact and manifest are available alongside this paper.

**Conclusion sentences (candidate; Phase 5).**
> The paper and its Lean 4 formalization are paired artifacts: every labeled environment has a derived Lean counterpart recorded in the manifest, and no manuscript item lacks a Lean proof. The formalization is paper-complete; reduction of the paper's abstract-interface layer to a concrete foundational stack is in progress.

Both sentences are supported by the current state of `Manifest.lean`: `paperFullyDerived = true` (abstract claim), `fullyFirstPrinciples = false` (qualifier).

---

## 6. What NOT to do in this pass

- Do not rewrite any theorem, proposition, lemma, corollary, or definition *statement*. Math is inviolate; Lean-parity contract binds.
- Do not split or merge labeled environments.
- Do not add new labeled environments ("just one more remark" is a math edit, requires a Lean change).
- Do not introduce new technical vocabulary in prose that is not already in a labeled definition.
- Do not rewrite paragraphs that already land; tighten or leave.
- Do not expand the abstract past one paragraph.

---

## 7. Execution checklist (for the actual edits, one item at a time)

1. [ ] Gate 2 sign-off (amortized-surrogate promotion: standalone section between `sec:main` and `sec:self-ref`).
2. [ ] Gate 3 sign-off (Lean artifact URL / citation form).
3. [ ] Phase 0 move + manifest regenerate + `lake build`.
4. [ ] Phase 1 abstract rewrite.
5. [ ] Phase 2 intro four-edit diff.
6. [ ] Phase 3 `sec:main` opener + `rem:functional-payoff` trim.
7. [ ] Phase 4 `sec:near-miss` opener check.
8. [ ] Phase 5 Conclusion rewrite (two paragraphs).
9. [ ] Phase 6 Discussion trim + cross-reference.
10. [ ] Phase 7 whole-document read-through.
11. [ ] Phase 8 Lean-parity final check.
12. [ ] Phase 9 title audit decision.
