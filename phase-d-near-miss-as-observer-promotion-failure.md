# Phase D: Near-Miss as Observer-Promotion Failure

**Goal of Phase D.** Recast the near-miss (paper's Theorem 5.7) in observer language: the AFE principle's realized policy induces an observer strictly below $\omega_{\mathrm{behav}}$, and the posterior-stuck-at-$\alpha_0$ conclusion is the Bayesian shadow of this strict refinement. The AFE principle's failure, under Phase D's reading, is a failure of *action-side observer promotion* — the primitive the action rule selects never probes the gap between the fixed-policy observer and the behavioral observer.

**Dependencies.** Phase A (observer formalism, refinement preorder, the four observers). Phase B's Theorem 1.2 (strict refinement $\omega_\pi < \omega_{\mathrm{behav}}$) supplies the key structural input. Phase C is not required but the Pearl bridge sharpens Remark D.4.

**Scope discipline.** Phase D does not introduce new formal objects beyond Phase A. A single theorem, a short proof, and three remarks. The near-miss's construction and conclusion are unchanged; Phase D reads them in a different vocabulary.

---

## 1. The realized policy in the near-miss

In the proof of Theorem~\ref{thm:afe-near-miss}, the AFE-principle learner selects $a^{\mathrm{ref}}$ at every time $t \in \{1, \ldots, T\}$ on every sample path. Let $\pi^\sharp$ denote the fixed policy that plays $a^{\mathrm{ref}}$ at every time: $\pi^\sharp_t(a^{\mathrm{ref}} \mid h) = 1$ for every $h$ and every $t \ge 1$.

On every sample path of the near-miss, the AFE-principle's realized actions through horizon $T$ coincide with those of $\pi^\sharp$. In particular, for every history $h_t$ with $t \le T$ and $\mathbb{P}_{p^\star, \pi^\sharp}(H_t = h_t) > 0$, the AFE-principle learner's realized-up-to-$t$ action profile agrees with $\pi^\sharp$ on $h_t$. This is what the "induction on $t$" in the near-miss proof (lines 653–658 of the paper) establishes.

*Terminological note.* We use "realized policy" informally to denote the deterministic action assignment the AFE principle produces on the near-miss. For the Phase D theorem, we work with the fixed policy $\pi^\sharp$, which agrees with the realized policy on every reachable history through horizon $T$. This avoids the technical subtlety that an AFE-principle action rule is history-dependent but in the near-miss happens to be constant.

---

## 2. The observer-promotion failure

**Theorem 2.1 (Observer-promotion failure of the AFE principle).** In the near-miss construction of Theorem~\ref{thm:afe-near-miss}, the fixed policy $\pi^\sharp$ — which agrees with the AFE-principle's realized policy on every reachable history through horizon $T$ — satisfies
$$\omega_{\pi^\sharp} < \omega_{\mathrm{behav}}$$
strictly in the refinement preorder. Explicitly, there exists $p' \in \Pcal$ with $p' \in R_{\pi^\sharp}(p^\star) \setminus [p^\star]$.

**Proof.** Construct $p' \in \Pcal$ with action-conditioned law
$$\mu_{p'}(o \mid h_{t-1}, a) = \begin{cases} \mu_{p^\star}(o \mid h_{t-1}, a^{\mathrm{ref}}), & a = a^{\mathrm{ref}}, \\ \one\{o = S_0\}, & a = a^{\mathrm{sep}}. \end{cases}$$
Such a $p'$ exists in $\Pcal$: $p^\star$'s $a^{\mathrm{ref}}$-law is computable, and replacing its $a^{\mathrm{sep}}$-conditional with a fixed point-mass emission yields another computable environment.

*$p' \in R_{\pi^\sharp}(p^\star)$.* Under $\pi^\sharp$, every action is $a^{\mathrm{ref}}$, so every reachable pair is of the form $(h, a^{\mathrm{ref}})$. At every such pair, $\mu_{p'}(\cdot \mid h, a^{\mathrm{ref}}) = \mu_{p^\star}(\cdot \mid h, a^{\mathrm{ref}})$. Factoring the induced history law (Lemma~\ref{lem:observable-quotient}), $\mathbb{P}_{p', \pi^\sharp} = \mathbb{P}_{p^\star, \pi^\sharp}$.

*$p' \notin [p^\star]$.* The pair $(\varepsilon, a^{\mathrm{sep}})$ is reachable under both $p^\star$ and $p'$ (empty history is always reachable, and any single-action extension is reachable). At this pair, $\mu_{p'}(\cdot \mid \varepsilon, a^{\mathrm{sep}}) = \delta_{S_0} \ne \delta_{S_1} = \mu_{p^\star}(\cdot \mid \varepsilon, a^{\mathrm{sep}})$. By the reachability-respecting reading of kernel equality (Section~\ref{sec:setup}, Convention 1.2), $\mu_{p'} \ne \mu_{p^\star}$.

Therefore $p' \in R_{\pi^\sharp}(p^\star) \setminus [p^\star]$, which by Phase A's definition of the refinement order gives $\omega_{\pi^\sharp} < \omega_{\mathrm{behav}}$. $\square$

**Corollary 2.2 (Universal-prior case).** Theorem 2.1 applies to the AFE principle with the universal interactive prior in place of the near-miss's finite-support prior $w$, at every history on which the universal-prior learner's realized action is $a^{\mathrm{ref}}$. In particular, on the initial segment over which Remark~\ref{rem:near-miss-universal}'s weakened version of the near-miss holds, the universal-prior AFE principle's realized observer is strictly below $\omega_{\mathrm{behav}}$.

**Proof.** The refinement gap $\omega_{\pi^\sharp} < \omega_{\mathrm{behav}}$ is a statement about the policy $\pi^\sharp$, not about the learner's prior. The universal-prior learner's realized policy, restricted to the initial segment on which $a^{\mathrm{ref}}$ is selected, agrees with $\pi^\sharp$ on every reachable history in that segment. $\square$

---

## 3. Interpretive remarks

**Remark 3.1 (Prior-independence of the failure).** Theorem 2.1 is a statement about the action rule alone. Corollary 2.2 makes this concrete: the same observer-promotion failure holds for the universal-prior AFE principle at every time on which the realized policy plays $a^{\mathrm{ref}}$. Swapping the near-miss's finite-support prior for the universal prior changes when the AFE rule starts diverging from $\pi^\sharp$, not whether the observer-promotion failure occurs while it plays $\pi^\sharp$.

**Remark 3.2 (Bayesian shadow).** Theorem~\ref{thm:afe-near-miss}'s conclusion — the posterior on $[p^\star]$ frozen at $\alpha_0$ through horizon $T$ — is a Bayesian shadow of Theorem 2.1. The learner's posterior on $c^\star$ can't separate from the posterior mass on the complement $\bigcup_\sigma c_\sigma$ because, under $\pi^\sharp$, the mixture of surviving $p_\sigma$'s reproduces $p^\star$'s predictive law exactly (the uniform-over-$N$ marginal computed at line 634 of the paper). Under $\omega_{\mathrm{behav}}$, no such mimicry is possible — the two mixtures disagree at $a^{\mathrm{sep}}$. The near-miss is the statement that a posterior computed against a realized observer cannot rule out hypotheses that the realized observer cannot distinguish; Theorem 2.1 is the statement that the realized observer in question is in fact coarser than $\omega_{\mathrm{behav}}$.

**Remark 3.3 (Forward reference to Section~\ref{sec:main}).** The main convergence theorem (Theorem~\ref{thm:semantic-convergence}) is, in the observer reading, an *observer-promotion success*: the class-against-complement primitive realizes (in the limit, along the learned trajectory) an observer equal to $\omega_{\mathrm{behav}}$ in the sense that the posterior on $[p^\star]$ concentrates. The class-against-complement primitive is, informally, an action rule that selects $a^{\mathrm{sep}}$-analogues — actions whose observations discriminate $c^\star$ from the aggregate complement — precisely where the AFE rule selects refining actions. Phase E formalizes the promotion.

---

## 4. What Phase D gives us

- **Observer-language recast of the near-miss.** The AFE principle fails at the observer level, not just the posterior level. The failure is a structural fact about the realized policy's coarseness, not an accident of the near-miss's prior.
- **Bridge to Phase E.** The paper's negative result (near-miss) and positive result (main theorem) are unified under one observer-promotion frame: the AFE rule fails to promote the observer; the class-against-complement rule succeeds.
- **Prior-independence.** Corollary 2.2 extends the observer-promotion failure to the universal-prior AFE principle. The paper's universal-prior caveat in Remark~\ref{rem:near-miss-universal} becomes a structural statement rather than a technical footnote.
- **Zero new formal objects.** Phase D uses only Phase A's observers and Phase B's strict-refinement structure (indirectly, through the explicit witness $p'$). No new definitions enter the paper.

---

## 5. What this looks like in the paper

Phase D's integration is about a third of a page:

1. **Theorem 2.1** and its short proof go into Section~\ref{sec:near-miss} as a standalone theorem immediately following Theorem~\ref{thm:afe-near-miss}. Title: "Observer-promotion failure of the AFE principle." Proof: as above, three short paragraphs.
2. **Corollary 2.2** is one sentence immediately after Theorem 2.1, linking to Remark~\ref{rem:near-miss-universal}.
3. **Remarks 3.1–3.2** are absorbed into the existing `rem:near-miss`. Specifically, the current remark's sentence "Under the adversarial reading of Remark~\ref{rem:four-observers}, expected-free-energy action does not give the learner the policy-varying probe power of the full-behavioral observer..." already gestures at Phase D's content. Phase D's job is to promote that gesture to a formal statement: the adversarial reading has a name ($\omega$-indistinguishability), the policy-varying probe power has a name ($\omega_{\mathrm{behav}}$), and the non-promotion is a theorem ($\omega_{\pi^\sharp} < \omega_{\mathrm{behav}}$). The remark body becomes a two- or three-sentence pointer to Theorem 2.1 rather than a prose restatement of it.
4. **Remark 3.3** becomes a one-line forward reference to Section~\ref{sec:main}, tying the near-miss to the eventual positive theorem under the observer-promotion frame.

---

## 6. Open questions

1. *Theorem 2.1 statement.* I've stated Theorem 2.1 in terms of the fixed policy $\pi^\sharp$ with a terminological note tying it to the AFE-principle's realized policy. The alternative is to state it directly about the realized policy, introducing a "realized policy" definition that handles path-dependence. My lean: keep $\pi^\sharp$; the terminological note is tight, and introducing a "realized policy" object risks upstaging Phase A's definitions. Your call.

2. *Where Theorem 2.1 sits.* Section~\ref{sec:near-miss}, immediately after `thm:afe-near-miss`, is the natural home — the observer-promotion failure is content the reader needs while the near-miss is still on the page. An alternative is Section~\ref{sec:hierarchy}, as an application of Phase A/B content. My lean: Section~\ref{sec:near-miss}. The theorem earns its weight by being the observer-language recast of a theorem three inches above it, not by sitting in an abstract-observer section detached from the near-miss.

3. *Corollary 2.2's prominence.* Corollary 2.2 says the universal-prior AFE principle fails at the observer level too. This is a structural strengthening of `rem:near-miss-universal`. My lean: keep it as a corollary (not absorbed into a remark), because it earns corollary-prominence in the drafting rules' sense — a unification punchline that sharpens the paper's negative result. If it stays a remark, the observer-promotion failure looks prior-specific when it is in fact prior-independent.

4. *Amount of rewriting to `rem:near-miss`.* The existing `rem:near-miss` has "expected-free-energy action does not give the learner the policy-varying probe power of the full-behavioral observer" and "the adversary's swap agrees with $p^\star$ on every action EFE selects and differs only where EFE does not probe, leaving the posterior stuck at the $R_\pi$-indistinguishable level." Both sentences are Phase D's content stated informally. My lean: replace `rem:near-miss`'s middle sentences with a pointer to Theorem 2.1 ("Theorem 2.1 formalizes this"), and keep the opening and closing sentences that do the load-bearing framing. The remark becomes tighter; the theorem carries the weight.

5. *Relation to Phase E.* Phase D sets up Phase E (class-against-complement primitive as observer-promotion success) but does not execute it. Remark 3.3 is a single forward reference. My lean: keep the forward reference minimal, so Phase D doesn't preview Phase E's content. Phase E will land with its own weight when drafted.

6. *Observer-promotion as an organizing label.* Phase D introduces "observer promotion" as a term. This term will recur in Phases E–G (main-theorem recast, discussion). Is the term crisp enough to live in the paper's vocabulary? My lean: yes — it names what the action rule is supposed to do (promote the learner from a weaker observer to a stronger one) and lets the near-miss and main theorem be contrasted as promotion-failure and promotion-success. If the term lands heavily, we can swap to "observer strengthening" or "observer advancement." My recommended default: observer promotion.

---

## 7. A note on scope

Phase D is intentionally lighter than Phases A–C. It adds one theorem, one corollary, touches one existing remark, and adds one forward reference. The observer formalism from Phases A–C is what makes Theorem 2.1 possible; Phase D's job is not to introduce more formalism but to make the existing formalism do work inside Section~\ref{sec:near-miss}. If Phase D needed three new definitions and two new lemmas, it would be the wrong phase of the plan — the observer formalism would be upstaging the paper's existing near-miss. As drafted, Phase D adds material the way a clarifying lemma adds material: the near-miss is already a theorem; Phase D tells the reader what kind of theorem it is.
