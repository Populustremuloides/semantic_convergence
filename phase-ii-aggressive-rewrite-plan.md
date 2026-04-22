# Phase II: Aggressive (Observer-First) Rewrite Plan

**Goal.** Restructure the paper around $\mathcal J_t^{\omega_B, \omega_A}$ and the meeting-point theorem (Proposition I.10) as the central structural content. AFE is demoted from the spine to a boundary example. The main convergence theorem is restated as $\mathcal J_t^{\omega_{\mathrm{behav}}}$-minimization. **We turn the highest-yield stones** from the Phase I review — enough to make the paper's thesis land harder — and leave the remainder as explicit future-work items so we don't dilute focus. "Highest-yield" means: sharpens the core thesis, answers a likely reviewer objection, or closes an open question from the current paper, at low-to-moderate cost.

**Backup.** User has a snapshot of the current manuscript. Every phase below leaves the repository in a compilable state so we can back off mid-rewrite if needed.

**Working principle.** No text is deleted until its replacement is drafted and compiling. Rewrite is additive-then-subtractive within each phase: add the new version, verify, remove the superseded version.

---

## Target architecture

### New section list

1. Introduction (rewritten last; meeting-point framing)
2. Formal Setup (light edits only)
3. The Knowability Hierarchy (mostly unchanged; cross-reference updates; strict hierarchy reframed as corollary of the lattice)
4. **The Two-Observer Functional and the Meeting-Point Theorem** (new spine)
5. Belief at $\omega_{\mathrm{syn}}$: Universal Bayes (rewrite of current Section 4)
6. Action at $\omega_{\mathrm{behav}}$: Class-Against-Complement (rewrite of current Section 6)
7. Convergence: Sufficient Conditions as $\mathcal J_t^{\omega_{\mathrm{behav}}}$-Minimization (recast of current Section 7; hosts exponential rate and near-necessity of (C3) as corollaries)
8. **Self-Referential Convergence** (new short section; running $\omega_\pi^t$-quotient replaces the incomputable $\omega_{\mathrm{behav}}$-quotient)
9. AFE as a Boundary Example (recast of current Section 5; substantially shortened; AIXI positioned here too)
10. Implications (expanded with lattice reading)
11. Discussion (philosophical theses pivot on I.10; light remarks land here)
12. Conclusion

### Title (locked)

**A Variational Principle for Semantic Convergence in Interactive Learning.**

Every term in the title is defined in the paper: "semantic convergence" is the posterior-mass-on-$[p^\star]$ convergence of the boxed problem statement; "interactive learning" is the paper's framing; "variational principle" names the answer as a single object. Not a compound title. Does not use meta-vocabulary ("meeting point," "observer promotion," "lattice") that the abstract would have to explain.

### Architectural commitment: problem → variational principle → answer

The paper's current boxed problem statement in Section 2 is retained verbatim:

> **Problem.** Give sufficient conditions on the learner's prior, belief rule, and action rule under which the posterior mass on $[p^\star]$ converges almost surely to one.

The new Section 4 opens by announcing that the paper's answer to this box is a single object — the two-observer variational functional $\mathcal J_t^{\omega_B, \omega_A}$ — whose minimizer is exactly the (prior, belief rule, action rule) triple the box asks for, at the observer choice fixed by the meeting-point theorem. Every subsequent section is organized around this answer: Section 5 identifies the belief-side minimizer, Section 6 identifies the action-side minimizer, Section 7 proves the convergence claim the box asks for, Section 8 extends the convergence claim to the self-referential (computable-quotient) case, Section 9 reads AFE as the wrong-observer instance of the same functional.

The title circles this commitment: *A variational principle* (Section 4's functional) *for semantic convergence* (the box's conclusion) *in interactive learning* (the box's setting).

### Key invariants across the rewrite

**Mathematical content.**

- Formal content of the knowability hierarchy (Theorems 11, 13) is preserved; Theorem 13 is re-presented as a corollary of the lattice meeting-point structure.
- Main theorem's proof of convergence is unchanged; only the setup and framing are recast.
- AFE's variational identity and the KL-necessity lemma are preserved but relocated.
- The existing observer refinement preorder, realized observer, supremum identity, and ceiling theorem are the foundation and are not modified.
- Bibliography updated with new references for AIXI (Hutter) and MDL (Li–Vitányi) as needed.

**Spine preservation (the four-set hierarchy must keep shining through).**

- *Four-set Introduction paragraph preserved.* The existing paragraph introducing $\{p^\star\} \subseteq [p^\star] \subseteq R_\pi(p^\star) \subseteq R_{h_t}(p^\star)$ stays structurally in the rewritten Introduction, in the same position, *before* the variational principle is introduced. The functional is motivated by the hierarchy, not a replacement for it.
- *Observer–set parallelism, used everywhere.* Every observer named in the rewrite is accompanied by its indistinguishability class of $p^\star$: $\omega_{h_t} \leftrightarrow R_{h_t}(p^\star)$, $\omega_\pi \leftrightarrow R_\pi(p^\star)$, $\omega_{\mathrm{behav}} \leftrightarrow [p^\star]$, $\omega_{\mathrm{syn}} \leftrightarrow \{p^\star\}$. When the abstract says "the relation fixing $[p^\star]$," the paper uses consistent vocabulary downstream.
- *Section 4 opens on the hierarchy.* The new Section 4 on the two-observer functional begins by recalling the four-set hierarchy and identifying the two observer indices on $\mathcal J_t$ as the observers of specific sets in the hierarchy. A reader who skips straight to Section 4 still sees the setup.
- *Implications retains set-indexed paragraphs.* The current Implications section organizes learning theories by target set (one paragraph per set); this structure survives the rewrite. The lattice reading is added on top, not substituted.
- *Philosophical theses keep set-level formulation.* Quine's underdetermination maps to $[p^\star] \subsetneq R_\pi(p^\star)$; van Fraassen's empirical adequacy maps to $[p^\star]$ as the ceiling of history-recoverability; Putnam's use/reference maps to "use fixes reference up to $[p^\star]$." Set-level claims remain primary; the lattice reading sharpens rather than replaces.
- *Optional diagram.* A small figure in Section 3 or 4 aligning observer, set, and defining property in four rows. One-eighth page or less; cheap insurance that the parallelism stays visible at a glance.

**Abstract-level reminder.** When we workshop the abstract later, check whether the four-set hierarchy deserves one more sentence in it. The current draft names $[p^\star]$ by its defining property but does not show the other three sets; that may be acceptable if the Introduction carries the weight.

### Stone disposition (highest-yield subset turned; remainder deferred)

The 13 stones from the Phase I review split into a high-yield subset we turn in this paper and a deferred set we flag as future work. "Yield" weighs sharpening of the core thesis, answering a likely reviewer objection, or closing an open question, against cost and risk of dilution.

**Turned in this paper:**

| Stone | Turned as | Phase | Rationale |
|---|---|---|---|
| a. Self-referential convergence | New theorem (Section 8) | 6a | Resolves the computational objection that $\omega_{\mathrm{behav}}$ is uncomputable. Highest-yield single stone. |
| g. Exponential rate (expectation form) | Proposition in Section 7 | 4 | Closes paper's own open question 2; cheap corollary of the main proof. |
| c. AIXI as AFE-type near-miss for reward | Proposition + discussion in Section 9 | 6c | Extends the structural critique from FEP to the canonical universal agent. |
| d. Leibniz identity | Remark in Section 4 | 6d | Cleanest philosophical reading; one paragraph. |
| j. Strict hierarchy as lattice corollary | Remark at end of Section 3 | 6d | Unifies existing results under new framing; one paragraph. |
| b. MDL / Kolmogorov reading | Remark in Section 5 | 6d | Connects universal prior to class-level MDL; one paragraph. |
| m. Near-necessity of (C3) | Short proposition / sharpening of existing corollary in Section 7 | 6d | Promotes the existing "separation is required" corollary to a near-necessity statement. |

**Deferred (flagged as explicit future work in Discussion):**

| Stone | Reason deferred |
|---|---|
| e. Open texture / Waismann | Largely redundant with the policy-gap theorem; low marginal yield. |
| f. Three-observer pragmatic meeting | Ambitious and speculative; risks dilution. Future-paper scope. |
| h. PAC sample complexity | Requires auxiliary moment hypothesis; expectation-form rate (stone g) already in paper. Mention in Discussion. |
| i. Rényi-$\alpha$ spectrum | Adds notational load for modest conceptual gain. Mention in Discussion. |
| k. Continuous actions | Measurability detail belongs in a follow-up technical note. |
| l. Multi-agent shared $\omega_{\mathrm{behav}}$ | Trivial consequence of Proposition I.9; drop unless needed. |

---

## Phase 0: Decisions to lock before writing

**Goal.** Fix the scaffolding so subsequent phases have no moving targets.

**Locked decisions.**

1. **Title:** *A Variational Principle for Semantic Convergence in Interactive Learning*.
2. **Section list:** 12 sections (Intro, Formal Setup, Knowability Hierarchy, Two-Observer Functional and Meeting-Point Theorem, Belief at $\omega_{\mathrm{syn}}$, Action at $\omega_{\mathrm{behav}}$, Convergence, Self-Referential Convergence, AFE as a Boundary Example, Implications, Discussion, Conclusion).
3. **Renumbering strategy:** ambient, section-indexed — each section shares a single counter across theorem/proposition/lemma/corollary environments, rendered as "Theorem 4.2", etc. Extends the current paper's convention.
4. **Notation:**
   - Functional carries belief observer first: $\mathcal J_t^{\omega_B, \omega_A}$.
   - Shorthand $\mathcal J_t^{\omega_{\mathrm{behav}}} := \mathcal J_t^{\omega_{\mathrm{syn}}, \omega_{\mathrm{behav}}}$ (meeting-point specialization). Convention stated once in Section 4.
   - Two distinct functionals for Bhattacharyya and MI action terms (cleaner statement of the AFE identity proposition I.1).
5. **Stone list:** high-yield subset — a, b, c, d, g, j, m turned; e, f, h, i, k, l deferred. See disposition table above.
6. **File strategy:** sidecar rewrite. Develop in `algorithmic_free_energy_principle_award.v2.tex`; keep v1 untouched; swap at the end of Phase 10.
7. **Length target:** 25–28 pages; no hard cap.
8. **Phase 6 ordering within the trimmed set:** 6a (self-referential convergence) first for risk triage, then 6d (four short remarks) for fast wins, then 6c (AIXI proposition) last.
9. **Abstract syllogism (for reference during Phase 8 writing).** Six steps:
   - The problem box asks for the triple (prior, belief rule, action rule) that converges to $[p^\star]$.
   - The four-set hierarchy identifies $[p^\star]$ as the finest history-recoverable target; AFE falls short.
   - Below the target observer, Bayes on classes is ill-typed; above it, behaviorally-equivalent classes have frozen posterior ratios.
   - The target is the unique fixed point where these two admissibility ranges — belief-typed from above, action-useful from below — meet.
   - A principle that reaches the target couples belief at or above with action at or below; this is a variational functional with two observer indices.
   - Its minimizer is (universal prior, Bayes belief, class-against-complement action); minimization drives the posterior to $[p^\star]$ a.s.

**Exit criterion.** Plan doc reflects locked decisions; abstract prose drafted in Phase 8; no Phase 1 writing yet.

**Estimated scope.** One working session.

**Risk.** Low. This phase is cheap insurance against mid-rewrite rework.

---

## Phase 1: Insert the new Section 4 (two-observer functional) as an additive block

**Goal.** Draft the new central section without touching existing content. The paper still compiles with current Section 4 onward; the new section sits adjacent as "Section 3.5" or in a scratch file.

**Deliverables.**

1. Boxed definition of $\mathcal J_t^{\omega_B, \omega_A}[q, \pi; h_t]$ in both Bhattacharyya and MI variants.
2. Proposition I.9 (belief-observer invariance) with proof.
3. Proposition I.9' (belief-observer ill-typing) with proof.
4. Proposition I.2 (action-observer cap) with proof.
5. **Theorem (Meeting Point)** = I.10, stated as the synthesis with one-paragraph proof that cites 1-4.
6. Corollary I.10' (canonical two-observer choice: $(\omega_{\mathrm{syn}}, \omega_{\mathrm{behav}})$).
7. Proposition I.3 (goal-dialed convergence) stated; proof deferred or inline depending on length.
8. Forward-reference blocks indicating where Sections 5, 6, 7 will land under this lens.
9. Remark (Leibniz identification) — stone d — placed after the meeting-point theorem: $\sim_{\mathrm{behav}}$ is the interactive-learning analogue of Leibniz equivalence; the meeting-point theorem identifies the Leibniz invariant as a lattice fixed point.

**Dependencies.** Phase 0 decisions locked.

**Exit criterion.** Paper compiles with the new section inserted between current Section 3 and current Section 4. Old Section 4 onward is unmodified.

**Estimated scope.** 3-4 pages of new math. Two working sessions.

**Risk.** Medium. Proofs in the phase-i note are audit-ready, but LaTeX formatting of the meeting-point theorem and its lattice diagram may take iteration.

**Status.** Complete. New Section 4 drafted in `algorithmic_free_energy_principle_award.v2.tex` with: (i) boxed Definition 4.2 of $\mathcal J_t^{\omega_B,\omega_A}$ (Bhattacharyya variant) and named MI variant; (ii) shorthand $\mathcal J_t^{\omega_{\mathrm{behav}}}$ (Def 4.3); (iii) Proposition 4.4 (belief-observer invariance above $\omega_{\mathrm{behav}}$) with proof; (iv) Proposition 4.5 (belief-observer ill-typing below $\omega_{\mathrm{behav}}$) with proof; (v) Proposition 4.6 (action-observer cap) with proof; (vi) Corollary 4.7 (behavioral-twins frozen ratio) with proof; (vii) Theorem 4.8 (meeting point) with synthesis proof; (viii) Corollary 4.9 (canonical two-observer pair); (ix) Remark 4.10 (Leibniz identification, stone d); (x) Proposition 4.11 (goal-dialed convergence) with proof sketch pointing to Theorem~\ref{thm:semantic-convergence}; (xi) forward-reference subsection mapping Sections 5, 6, 7, 9 to belief-minimizer, action-minimizer, convergence payoff, and wrong-observer near-miss respectively. Compiles cleanly with zero undefined references; paper is 28 pages total. Downstream section labels (sec:belief, sec:near-miss, sec:semantic-action, sec:main, sec:implications, sec:discussion, sec:conclusion) resolve correctly under their shifted numbering. The four-set-hierarchy preservation commitment is honored: Section 4 opens by recalling the four-set hierarchy explicitly, every observer introduced is paired with its indistinguishability class, and the Leibniz remark is formulated in set-level language. Ready for Phase 2.

---

## Phase 2: Rewrite the belief-side section

**Goal.** Recast current Section 4 ("Universal Bayesian Belief") as "Belief at $\omega_{\mathrm{syn}}$" — the top-of-lattice specialization of $\mathcal J_t$'s belief term.

**Deliverables.**

1. Reframed section opener: "We now instantiate the belief side of $\mathcal J_t$ at $\omega_B = \omega_{\mathrm{syn}}$."
2. Universal prior definition — unchanged.
3. Machine-invariance lemma — unchanged.
4. Positive-prior-mass lemma — unchanged.
5. Algorithmic free energy definition — relabeled as "the belief term of $\mathcal J_t$ at $\omega_B = \omega_{\mathrm{syn}}$."
6. Variational identity (Lemma) — unchanged content, recast as "belief-side minimizer of $\mathcal J_t$ at $\omega_{\mathrm{syn}}$ is the Gibbs posterior."
7. KL-necessity lemma — unchanged.
8. Predictive merging lemma — unchanged.

**Dependencies.** Phase 1 complete and compiling.

**Exit criterion.** Belief-side content reads as a specialization of $\mathcal J_t$; all existing belief-side theorems retained with updated framing.

**Estimated scope.** Mostly rhetorical editing. One working session.

**Risk.** Low.

**Status.** Complete. Current §5 is now titled "Belief at $\omega_{\mathrm{syn}}$: Universal Bayesian Belief." Four targeted framing edits landed: (i) section opener rewritten to instantiate Corollary~\ref{cor:canonical-pair} at $\omega_B=\omega_{\mathrm{syn}}$, naming the belief side of $\mathcal J_t^{\omega_{\mathrm{syn}},\omega_A}$ as the object and mapping its ingredients to the four-set hierarchy ($R_{h_t}(p^\star)$ reached by belief alone); (ii) the AFE subsection title now reads "Algorithmic free energy as the belief term of $\mathcal J_t$ at $\omega_B=\omega_{\mathrm{syn}}$"; Definition~\ref{def:afe} carries an added sentence naming $\Fcal_t$ as the $q$-dependent part of $\mathcal J_t^{\omega_{\mathrm{syn}},\omega_A}$; (iii) the unification Remark after Lemma~\ref{lem:variational} now leads with the belief-side-minimizer identification (uniform in $\pi$ and $\omega_A$) and then gives the Friston/Solomonoff-Hutter commentary; (iv) the predictive-merging Remark now reads the result as "belief alone reaches the outermost set $R_{h_t}(p^\star)$ / observer $\omega_{h_t}$"; the two remaining strict inclusions $R_{h_t}(p^\star)\supsetneq R_\pi(p^\star)\supsetneq[p^\star]$ are named as the gap closed by the action side. Four-set hierarchy and observer parallelism preserved throughout. All belief-side theorems unchanged in content. v2 compiles cleanly at 28 pages with zero undefined references and zero warnings. Checkpoint saved as `algorithmic_free_energy_principle_award.v2.phase2.tex`. Ready for Phase 3.

---

## Phase 3: Rewrite the action-side section  ✅ COMPLETE (2026-04-21)

**Status.** Complete. Sidecar compiles to 30 pages with bibtex clean. Checkpoint saved as `algorithmic_free_energy_principle_award.v2.phase3.tex`.

**Landed edits.**
1. Section title changed to "Action at $\omega_{\mathrm{behav}}$: Class-Against-Complement"; opener rewritten to invoke Thm 4.8, Prop 4.6, Prop 4.11 and stage the section as exhibiting the action-side minimizer of $\mathcal J_t^{\omega_B,\omega_{\mathrm{behav}}}$.
2. Remark after Def of class-complement predictive law (`rem:class-complement-is-omega-behav`) identifying $\Qcal_t^{-c}$ with the $\omega_A=\omega_{\mathrm{behav}}$ specialization of $\Qcal_t^{-c,\omega_A}$ from Section 4.
3. Remark after Def of semantic separation (`rem:B-is-B-omega-behav`) identifying $B_t$ with $B_t^{\omega_{\mathrm{behav}}}$ of Definition 4.1.
4. New Proposition (Chernoff–Bhattacharyya correspondence, `prop:chernoff-correspondence`): (i) $B_t = \tfrac{1}{2}D_{1/2}$; (ii) $\mathrm{KL}\ge 2B_t$ via Rényi monotonicity (cites new `vanErvenHarremoes2014`); (iii) one-step Bayes-error Chernoff bound.
5. New Proposition (Noise-channel immunity, `prop:noise-immunity`): Cauchy–Schwarz data-processing inequality for $B_t$ under any Markov kernel $K$; transfer of Theorem 6 to the post-channel setting.
6. New Remark (`rem:against-entropy-bonus`) contrasting $B_t$-driven action with entropy-bonus curiosity and MI-variant EFE.

**Four-set hierarchy preservation.** No changes to existing theorems or labels; all four-set references and observer-set parallelism preserved.

---

## Phase 3: Rewrite the action-side section  (original plan)

**Goal.** Recast current Section 6 ("Class-Against-Complement Action") as "Action at $\omega_{\mathrm{behav}}$" — the meeting-point specialization of $\mathcal J_t$'s action term.

**Deliverables.**

1. Reframed section opener connecting to Theorem I.10.
2. Class-complement predictive law, semantic gain, posterior-odds identity — unchanged.
3. Semantic separation definition — unchanged; remark added that this is the $\omega_{\mathrm{behav}}$-class Bhattacharyya / half of Rényi-1/2.
4. Semantic action rule, promotion-supporting rule — unchanged.
5. Semantic rule is promotion-supporting — unchanged.
6. **New proposition (Chernoff correspondence)** = Proposition I.6 — states $B_t = \tfrac{1}{2} D_{1/2}$, KL $\ge 2 B_t$, Chernoff bound.
7. **New proposition (Noise-channel immunity)** = Proposition I.8.

**Dependencies.** Phase 2 complete and compiling.

**Exit criterion.** Action-side reads as the $\omega_A = \omega_{\mathrm{behav}}$ instantiation of $\mathcal J_t$; two new propositions added.

**Estimated scope.** Two new propositions + rhetorical framing. One to two working sessions.

**Risk.** Low to medium. Proposition I.6's placement may force minor Rényi notation additions to the preliminaries.

---

## Phase 4: Recast the main theorem  ✅ COMPLETE (2026-04-21)

**Status.** Complete. Sidecar compiles to 32 pages with bibtex clean. Checkpoint saved as `algorithmic_free_energy_principle_award.v2.phase4.tex`.

**Landed edits.**
1. Section-main opener rewritten around the two-observer construction payoff; names the canonical pair $(\omega_{\mathrm{syn}},\omega_{\mathrm{behav}})$ and the functional-minimization reading of Theorem 6.
2. Added `rem:functional-payoff` right after Theorem 6 giving the explicit $\mathcal J_t^{\omega_{\mathrm{behav}}}$-minimization reading (belief-side minimizer = Bayes/Gibbs; action-side minimizer = class-against-complement; $(q,\pi)$-simultaneous minimizer claim).
3. Added `lem:one-step-drift` (new Lemma) with proof threading Proposition 2.6(ii) (KL $\ge 2B_t$) and Proposition 5.8 (promotion support) into a single conditional drift $\ge 2\hat\eta\epsilon\bar w(c^\star)$.
4. Added `prop:exp-rate` (Exponential rate, expectation form = Prop I.7): $\E[Z_t]\ge Z_0+\mu_0 t$ with explicit $\mu_0 := 2\hat\eta\epsilon\bar w(c^\star)$; plus Jensen corollary on expected odds ratio.
5. Added `rem:exp-rate-concentration` flagging the concentration-form upgrade Prop I.7' under a likelihood-ratio regularity hypothesis.
6. Added `cor:goal-dialed-payoff` stating the goal-dialed convergence + rate transfer for $\omega_A\le\omega_{\mathrm{behav}}$ (observer dial).
7. Open Question 2 in Discussion updated to name Proposition I.7 as the partial answer.

**Four-set hierarchy preservation.** No existing theorem, definition, or label modified; all cross-references remain valid; observer-set parallelism preserved (rate transfer to $\omega_A\le\omega_{\mathrm{behav}}$ is observer-set symmetric).

**Stone g (Exponential rate) landed.** Answers part of open question 2 in the paper.

---

## Phase 4: Recast the main theorem  (original plan)

**Goal.** Restate current Section 7's main theorem and its corollaries as "$\mathcal J_t^{\omega_{\mathrm{behav}}}$-minimization drives $q_t^\star([p^\star]_{\mathrm{behav}} \mid H_t) \to 1$ a.s."

**Deliverables.**

1. Reframed section opener establishing the theorem as the payoff of the two-observer construction.
2. Semantic separation condition (C3), conditional Borel–Cantelli, cumulative-separation lemma — unchanged.
3. **Main theorem, recast statement:** Under (C1)-(C4), $\mathcal J_t^{\omega_{\mathrm{behav}}}$-minimization yields $q_t^\star([p^\star] \mid H_t) \to 1$ a.s. Proof unchanged.
4. Finite-class deterministic specialization, separating-interventions corollary, observer-promotion contrast corollary — unchanged.
5. **New proposition (Exponential rate, expectation form)** = Proposition I.7 — closes open question 2 in expectation form. **Stone g.**
6. **New corollary (Goal-dialed convergence)** = Proposition I.3 — the observer dial.

**Dependencies.** Phase 3 complete and compiling.

**Exit criterion.** Main theorem framed as variational principle payoff; rate proposition added; goal-dial corollary stated.

**Estimated scope.** One new proposition with proof (Prop I.7); one corollary stated without new proof. One to two working sessions.

**Risk.** Medium. Prop I.7's proof uses the supermartingale structure already implicit in the main proof; wiring needs to be explicit.

---

## Phase 5: Demote AFE to boundary example

**Goal.** Current Section 5 ("The AFE Principle and Its Near-Miss") becomes Section 9 ("AFE as a Boundary Example"), substantially shortened. The near-miss is read as $\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$-minimization — the wrong action observer — rather than as a standalone failure.

**Deliverables.**

1. Rewritten section opener positioning AFE as the top-of-lattice specialization of $\mathcal J_t$'s action side, blocked by the cap theorem.
2. Expected free energy definition — retained.
3. Risk-minus-information-gain lemma — retained.
4. EFE-as-unifying-principle corollary — retained but reframed.
5. Information decomposition lemma — retained.
6. AFE principle definition — relabeled as "$\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$-minimizing agent."
7. **Proposition I.1 (AFE near-miss as boundary):** statement placed here.
8. Near-miss theorem (existing Theorem 23): proof retained; restated as witness for Proposition I.1.
9. Observer-promotion failure theorem, universal-prior corollary: retained.

**Dependencies.** Phase 4 complete.

**Exit criterion.** AFE content retained, reframed as boundary example downstream of the main theorem. Paper compiles.

**Estimated scope.** Rhetorical restructure; content retention is high. One working session.

**Risk.** Medium-high. This is the phase where the paper's flow changes most visibly. Opening paragraph must do the work of signposting that AFE content is preserved.

**Completion notes (executed 2026-04-21).** Executed as planned.

- AFE section (`\section{The Algorithmic Free Energy Principle and Its Near-Miss}`, 232 lines) moved physically from between the belief and semantic-action sections to between the main theorem and Implications. Section title retitled "The Algorithmic Free Energy Principle as Boundary Example" with both new label `sec:boundary-example` and retained label `sec:near-miss` for backward reference compatibility.
- New section opener frames AFE as the wrong-observer instance of the two-observer functional at $\omega_A=\omega_{\mathrm{syn}}$, placed strictly above the meeting point by Proposition~\ref{prop:action-cap}.
- New subsection "Boundary identification" added at the top of the section with **Proposition~\ref{prop:boundary-identity} (Boundary identity)** stating that the AFE principle is the minimizer of $\mathcal J_t^{\omega_{\mathrm{syn}},\mathrm{MI}}$ at $\beta=1$, plus the converse that $\mathcal J_t^{\omega_{\mathrm{behav}}}$ at $\beta,\gamma>0$ yields the promotion-supporting triple of Section~\ref{sec:main}. Proof pulls Lemmas~\ref{lem:variational} and~\ref{lem:risk-ig} together with Proposition~\ref{prop:action-cap} and Theorem~\ref{thm:semantic-convergence}.
- Accompanying **Remark~\ref{rem:boundary-identity} (Reading under the functional)** explicates: belief-side unification of Section~\ref{sec:belief} unchanged; the change is on the action side (MI at $\omega_{\mathrm{syn}}$ vs.\ Bhattacharyya at $\omega_{\mathrm{behav}}$); the admissible range $\omega_A\le\omega_{\mathrm{behav}}$ excludes the AFE setting exactly.
- **Remark~\ref{rem:afe-as-functional-minimizer}** added immediately after Definition~\ref{def:afe-principle} to relabel the principle as "$\mathcal J_t^{\omega_{\mathrm{syn}},\mathrm{MI}}$-minimizing agent," item-by-item matching (i)–(iii) to the functional's universal prior, $q$-minimization of $\Fcal_t$, and $\pi$-minimization of the action-MI term.
- Retained unchanged: Definition~\ref{def:efe} (expected free energy), Lemma~\ref{lem:risk-ig}, Corollary~\ref{cor:efe-specialization}, Remark~\ref{rem:efe-unification}, Lemma~\ref{lem:info-decomp}, Theorem~\ref{thm:afe-near-miss}, Theorem~\ref{thm:observer-promotion-failure}, Corollary~\ref{cor:observer-promotion-universal}, Remark~\ref{rem:near-miss}, Remark~\ref{rem:near-miss-universal}.
- Moved to end of section under new subsection "Observer-promotion contrast: AFE vs.\ promotion-supporting rule": Corollary~\ref{cor:promotion-contrast} and Remark~\ref{rem:promotion-contrast-interpretation} (cut from the main theorem section).
- Forward-references updated:
  - Introduction roadmap (Section~\ref{sec:intro}): reordered to announce sections in the new physical order, with the boundary-example section named last before Implications.
  - Hierarchy closing paragraph (Section~\ref{sec:hierarchy}): reordered to describe the convergence payoff first (Sections~\ref{sec:semantic-action}, \ref{sec:main}) and the boundary-example failure second.
  - Action-section opener (Section~\ref{sec:semantic-action}): "near-miss of Section~\ref{sec:near-miss} already isolated..." rephrased as "the relevant comparison at $\omega_A=\omega_{\mathrm{behav}}$ is the one the boundary example of Section~\ref{sec:near-miss} will spell out the failure of..." to reflect that the near-miss now comes later in the paper.
  - Main-theorem opener paragraph 2 (Section~\ref{sec:main}): "The symmetry with Section~\ref{sec:near-miss}..." adjusted to "Section~\ref{sec:near-miss} below reads the symmetric contrast..." as forward reference.
- Section-functional forward-plan paragraph (Section~\ref{sec:functional}, line ~560) was already written in the new correct order (belief → semantic-action → main → near-miss) from Phase 1 and required no change.
- Compile: clean (33 pages, +1 over Phase 4's 32). No multiply-defined labels, no undefined references; single residual pdfTeX warning about subsection destinations disappears after the final pass. Checkpoint saved as `algorithmic_free_energy_principle_award.v2.phase5.tex` (124 KB).
- Four-set hierarchy preservation check: $\{p^\star\}$ 13×, $[p^\star]$ 101×, $R_\pi(p^\star)$ 26×, $R_{h_t}(p^\star)$ 20×; $\omega_{\mathrm{syn}}$ 45×, $\omega_{\mathrm{behav}}$ 122×, $\omega_\pi$ 7×, $\omega_{h_t}$ 6×. Hierarchy and observer-set parallelism preserved.
- New section order verified by grep: Intro, Setup, Hierarchy, Functional, Belief, Action, Main, Boundary Example (AFE), Implications, Discussion, Conclusion.

---

## Phase 6: Stone-turning (high-yield subset)

**Goal.** Produce formal results or targeted remarks for the seven high-yield stones (a, b, c, d, g, j, m). Stone g is already handled in Phase 4; the rest land in Phase 6. The single new section is Section 8 "Self-Referential Convergence" for stone a; everything else is a remark or short proposition integrated into existing sections.

**Phase 6 subphases.** 6a is the ambitious one (new theorem); 6c is a short proposition; 6d bundles four short remarks/corollaries.

### 6a. Self-referential convergence (stone a)

**Target statement.** Define $\omega_\pi^t := \omega_{\pi \mid h_t}$, the realized observer at time $t$ under policy $\pi$ and history $h_t$; this is computable from $(\pi, h_t)$ at every finite step. Define the *self-referential semantic rule* as the semantic rule of Definition~\ref{def:semantic-rule} with $\omega$-classes replaced by $\omega_\pi^t$-classes at each step. Under (C1)-(C3) and the self-referential rule:
- $\omega_\pi^t \to \omega_{\mathrm{behav}}$ a.s. (the running observer supremum equals the behavioral observer);
- $q_t^\star([p^\star]_{\mathrm{behav}} \mid H_t) \to 1$ a.s.

**Proof sketch.** Every pair of behaviorally-distinct programs admits a separating action by (C3). The self-referential rule eventually plays some separating action for each such pair with positive probability by the promotion-supporting structure. Along the sample path, $\omega_\pi^t$ monotonically refines toward $\omega_{\mathrm{behav}}$. Apply the goal-dialed convergence theorem (Proposition I.3) at each $t$ to $\omega_\pi^t$-classes, noting that $[p^\star]_{\omega_\pi^t} \supseteq [p^\star]_{\mathrm{behav}}$ monotonically shrinks to $[p^\star]_{\mathrm{behav}}$.

**Novelty.** Resolves the tension that the semantic rule formally requires $\omega_{\mathrm{behav}}$-classes (incomputable) but a learner has only $\omega_\pi^t$-classes (computable). This is the most philosophically important of the turned stones; it converts a latent objection into a positive result.

**Scope.** Two to three working sessions. Proof requires a small new lemma on the $\omega_\pi^t$-monotonicity under the self-referential rule.

**Risk.** Medium-high. Proof is plausible but has not been carried out end-to-end; there may be measurability or adversarial-policy subtleties. If the full theorem does not close, fall back to a conditional statement under a mild hypothesis on the richness of $\Pcal$.

**Status: done (2026-04-21).** New Section 8 "Self-Referential Convergence: Closing the Computability Gap" inserted between `sec:main` and `sec:near-miss`, labeled `sec:self-ref`. Contents (+128 lines): opening paragraph; §8.1 finite-time policy observer (`def:finite-time-policy-observer`, `lem:monotone-refinement`); §8.2 self-referential semantic rule (`def:self-ref-rule`, `rem:self-reference-scope`); §8.3 observer promotion (`lem:exploration-reachability`, `prop:observer-promotion-sr`); §8.4 self-referential convergence (`thm:self-ref-convergence` with proof sketch, `rem:self-ref-computability`, `rem:self-ref-vs-goal-dialed`). Proof closes end-to-end via countable-additivity over $\Pcal^2$; convergence proof sketch uses Lemma~\ref{lem:one-step-drift} transferred to the running partition plus dominated convergence over the countable posterior support outside $[p^\star]$. Compile clean at 36 pages (up from 33). Four-set hierarchy preserved: $\{p^\star\}$ 29×, $[p^\star]$ 118×, $R_\pi(p^\star)$ 26×, $R_{h_t}(p^\star)$ 20×; four observers preserved: syn 49×, behav 143×, $\pi$ 27× (up from 7), $h_t$ 6×. Checkpoint saved at `algorithmic_free_energy_principle_award.v2.phase6a.tex`.

### 6c. AIXI as AFE-type near-miss for reward (stone c)

**Target statement.** Let $\omega_R$ be the reward observer (two programs equivalent iff they induce the same expected reward under all policies). The AIXI agent \citep{Hutter2005} pairs universal-prior Bayes belief with expected-reward-maximizing action. Its convergence target is $[p^\star]_{\omega_R}$; under $\omega_R \le \omega_{\mathrm{behav}}$ (generic for nontrivial reward functions), AIXI does not in general converge to $[p^\star]_{\mathrm{behav}}$. Proposition I.1's observer-mismatch analysis extends directly with $(\mathrm{MI}, \omega_{\mathrm{syn}})$ replaced by $(\mathrm{reward}, \omega_R)$.

**Placement.** Proposition in Section 9 (AFE boundary example) or Discussion.

**Scope.** One session. Requires brief discussion of AIXI's formal setup to make the observer identification rigorous.

**Risk.** Low to medium. The Hutter 2005 formalism has particulars that may require careful translation.

### 6d. Bundled short remarks (stones b, d, j, m)

Four short remarks or micro-propositions, each one to a few lines of text. Grouped in one subphase because collectively they are one working session and they share the pattern of small additions to existing sections.

1. **Remark (Leibniz identification, stone d), Section 4.** $p_1 \sim_{\mathrm{behav}} p_2$ iff indiscernible under every interactive probing — Leibniz equivalence on $\Pcal$. $[p^\star]_{\mathrm{behav}}$ is the Leibniz invariant of $p^\star$. The meeting-point theorem identifies this invariant as a lattice fixed point rather than a pragmatic stipulation.
2. **Remark (Strict hierarchy from the lattice, stone j), end of Section 3.** Theorem~\ref{thm:strict-hierarchy} reads, under the new framing, as a corollary of the lattice meeting-point structure plus strict refinement. Forward-references Section 4.
3. **Remark (MDL at the class level, stone b), Section 5.** $\bar w([p^\star]) = \sum_{p \in [p^\star]} 2^{-K(p)}$ is within a constant factor of $2^{-K([p^\star])}$ for $K([p^\star]) := \min_{p \in [p^\star]} K(p)$. Posterior convergence on $[p^\star]$ is therefore MDL convergence at the class level.
4. **Proposition (Near-necessity of (C3), stone m), Section 7.** Sharpens the existing "support on separating interventions is necessary" corollary: if $\sup_a B_t(c^\star, a; h_t) = 0$ persists on the sub-tree consistent with $c^\star$, then $q_t^\star(c^\star \mid H_t) \not\to 1$. Proof is a one-paragraph reading of the cumulative-separation lemma in the zero-separation direction.

**Placement.** Four different locations as listed.

**Scope.** One working session total.

**Risk.** Low.

**Dependencies for Phase 6.** Phase 5 complete.

**Exit criterion.** High-yield stones turned: 6a theorem stated and proved, 6c AIXI proposition stated, 6d four remarks in place. Paper compiles.

**Estimated scope for Phase 6 (all subphases).** Four to five working sessions, of which the bulk is 6a.

**Risk (Phase 6 aggregate).** Medium. 6a carries most of the risk; if its proof does not fully close, fall back to a conditional statement under a richness hypothesis on $\Pcal$. 6c, 6d are straightforward.

---

## Phase 7: Refresh Implications and Discussion

**Goal.** Current Implications and Discussion sections are built around AFE-as-near-miss framing. Refresh so they pivot on the meeting-point theorem.

**Deliverables.**

1. Implications section: each four-set-hierarchy item gets a one-sentence lattice reading referring to I.10.
2. Discussion:
   - Pearl paragraph: retained but softened per phase-i note (analogy not theorem).
   - Chernoff paragraph: retained; sharpened with Proposition I.6 pointer.
   - Blackwell paragraph: retained; noted as dynamic-experiment extension.
   - Philosophical paragraph (Quine / vF / Putnam): rewritten to pivot on I.10. Van Fraassen's empirical adequacy becomes a theorem-level statement: the lattice meeting point is the interactive analogue of empirical adequacy.
   - Open questions: rate is answered in expectation (Prop I.7); self-referential convergence resolved (Phase 6a); tractable approximations (unchanged); add deferred stones as explicit future-work items — three-observer pragmatic meeting (stone f), PAC concentration under a moment bound (stone h), Rényi-$\alpha$ spectrum (stone i), continuous actions (stone k). Frame each in one or two sentences.

**Dependencies.** Phase 6 complete.

**Exit criterion.** Discussion reads the paper's new shape without residual AFE-centrism.

**Estimated scope.** One working session.

**Risk.** Low.

---

## Phase 8: Introduction, abstract, conclusion (written last)

**Goal.** New front matter advertises the paper as it actually ended up being written — observer-first spine, high-yield stones turned.

**Deliverables.**

1. Abstract: 180–220 word version centered on meeting-point theorem, convergence-as-lattice-invariant, self-referential resolution, and rate.
2. Introduction: seven-paragraph structure.
   - Para 1: Interactive learning and the four-observer hierarchy.
   - Para 2: Two-observer functional $\mathcal J_t$; belief and action admissibility.
   - Para 3: Meeting-point theorem (I.10) as the central structural claim.
   - Para 4: Main convergence theorem as $\mathcal J_t^{\omega_{\mathrm{behav}}}$-minimization; exponential rate in expectation.
   - Para 5: Self-referential convergence (Phase 6a) as the computational reconciliation — answers the "$\omega_{\mathrm{behav}}$ is uncomputable" objection.
   - Para 6: AFE and AIXI as boundary examples / near-misses.
   - Para 7: Philosophical payoff — Quine, van Fraassen, Putnam; Leibniz reading.
3. Conclusion: three-to-four-paragraph version centered on the lattice meeting point.
4. Title update (decision locked in Phase 0).

**Dependencies.** Phases 1–7 complete.

**Exit criterion.** Front matter and back matter read the paper's new shape cleanly. Paper compiles.

**Estimated scope.** Two working sessions.

**Risk.** Medium. Abstract-length constraint is real; multiple revisions likely.

---

## Phase 9: Adversarial review

**Goal.** Apply the same adversarial-review discipline used on the current manuscript to the rewritten paper, now including the turned stones.

**Checklist.**

1. Every new proposition's hypotheses are stated explicitly and the proof uses only what is stated.
2. No claim labeled "theorem" that is in fact interpretive (Pearl, Blackwell, Quine, vF, Putnam are remarks).
3. Proposition I.9's proof correctly handles the case $\omega = \omega_{\mathrm{behav}}$ (identity; trivial).
4. Proposition I.10's "unique" claim is proved, not asserted.
5. Phase 6a (self-referential convergence) proof is end-to-end rigorous — especially the $\omega_\pi^t \nearrow \omega_{\mathrm{behav}}$ step.
6. AIXI proposition (Phase 6c) distinguishes formal statement from rhetorical framing.
7. Proposition I.7's moment-bound footnote explicit; PAC mentioned in Discussion without claim of proof.
8. All cross-references updated to new theorem numbering.
9. Title and abstract claims are backed by the paper's content, not overstated.
10. For each turned stone: correct placement, correct label (theorem vs proposition vs corollary vs remark), and no over-claim. For each deferred stone: clearly flagged as open question, not hinted at as theorem.

**Deliverables.** A fix list, then the fixes themselves.

**Dependencies.** Phase 8 complete.

**Exit criterion.** Adversarial pass produces zero critical issues and at most minor edits.

**Estimated scope.** Two working sessions.

**Risk.** Medium. Phase 6a is the likeliest source of issues.

---

## Phase 10: Final compile, length audit, polish

**Goal.** Compile cleanly, audit length, polish prose.

**Deliverables.**

1. Clean `pdflatex` + `bibtex` + `pdflatex` $\times$ 2 compile.
2. Page count within target (locked in Phase 0). If over, candidates for trimming: compression of Phase 6d remarks (Leibniz / MDL / strict hierarchy), shortening of Section 9 (AFE) recast.
3. Cross-reference audit via `\ref` tracer.
4. Citation audit — all new references resolve (Hutter for AIXI, Li–Vitányi for MDL, possibly Leibniz).
5. One final prose pass for tone consistency.

**Dependencies.** Phase 9 complete.

**Exit criterion.** Paper is submission-ready.

**Estimated scope.** One working session.

**Risk.** Low to medium. Length risk is lower than the maximal plan but still real.

---

## Cross-cutting notes

**Session checkpointing.** Sidecar file is `algorithmic_free_energy_principle_award.v2.tex`. After each phase, save a dated copy (`algorithmic_free_energy_principle_award.v2.phaseN.tex`) before starting the next. The v1 file is not modified until Phase 10's final swap.

**Plan-doc discipline.** This document is the Phase II equivalent of the phase-i note. Update at the end of each phase with what actually happened — including notation changes, stone decisions, and any rework.

**Minimum-viable-rewrite checkpoints.**

- *After Phase 4.* Observer-first core is in place; meeting-point theorem and expected-rate proposition stated; paper is already a defensible aggressive rewrite with no stones turned beyond g. If time pressure forces a ship, this is the earliest defensible stop.
- *After Phase 6.* Highest-yield stones turned (a, c, d and companion remarks). Self-referential convergence resolves the main computational objection. Paper reads as intended.
- *After Phase 10.* Fully polished ship.

**Rollback triggers.**

- If Phase 1's meeting-point theorem uncovers a gap in Proposition I.9 or I.10 that was missed in Phase I, halt and reprove before continuing.
- If Phase 5's AFE demotion breaks the narrative irrecoverably, revert to the observer-lens (moderate) structure.
- If Phase 6a's self-referential convergence proof does not close end-to-end, fall back to a conditional theorem under a richness hypothesis, or reduce to a formal sketch with open-question framing; do not ship an unproved theorem.
- If Phase 9 uncovers more than three critical issues, halt and reassess scope before Phase 10.

**Estimated total scope.** Twelve to sixteen working sessions (two to three weeks of focused time), with Phase 6a as the single most expensive unit.

---

## Immediate next step

Phase 0. Lock the following before any writing:

1. Title choice.
2. Section list (as above, with Section 8 "Self-Referential Convergence" as the only new dedicated section).
3. Renumbering strategy.
4. Length target (likely 25–28 pages; confirm or amend).
5. Phase 6 ordering within the trimmed set (recommendation: 6a first for risk triage, then 6d remarks as fast wins, then 6c AIXI proposition).
6. Working-file strategy (in-place with checkpoints vs. sidecar rewrite).

Once Phase 0 is locked, Phase 1 is the first writing phase.
