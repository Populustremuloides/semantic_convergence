# Phase C: The Pearl Bridge

**Goal of Phase C.** Prove the interventional equivalence theorem $\bigcap_\pi R_\pi(p^\star) = [p^\star]$, equivalently $\omega_{\mathrm{behav}} = \bigvee_\pi \omega_\pi$. Establish the Pearl bridge: the behavioral observer is the algorithmic analogue of Pearl's interventional observer, with policies as interventions and reachable history-action pairs as intervenable nodes.

**Dependencies.** Phase A (observer formalism, four observers, refinement chain). Phase B (strict refinement, ceiling theorem) is not strictly required for Phase C's content but informs the sharpness remarks.

**Scope discipline.** Phase C establishes the supremum identity at the observer level and draws the Pearl connection. It does not prove that $\omega_{\mathrm{behav}} \in \mathcal{E}$ (the empirical closure) as a single realizable observer — that requires Solomonoff consistency and is a Phase E consequence of the main convergence theorem.

---

## 1. Reachability and kernel equality

Phase C's main theorem requires us to be precise about what "$\mu_p = \mu_{p^\star}$" means. The paper's current Definition 3.3 reads "$[p^\star] := \{p \in \mathcal{P} : \mu_p = \mu_{p^\star}\}$," which leaves the meaning of the right-hand side open: equality as kernels at every $(h, a)$, or equality only at pairs that can actually be visited?

Kernels at *unreachable* pairs have no observable consequence. If $p^\star$ never produces an observation prefix $h$, and $p$ never produces $h$ either, then the values $\mu_p(\cdot \mid h, a)$ and $\mu_{p^\star}(\cdot \mid h, a)$ are not probed by any policy. Declaring such programs inequivalent would create distinctions no observer can see.

**Definition 1.1 (Reachable pair).** A history-action pair $(h, a)$ is *reachable under $p$* iff $\mu_p(o_{1:|h|} \mid a_{1:|h|}) > 0$, where $h = (a_{1:|h|}, o_{1:|h|})$. Equivalently, there exists a policy $\pi$ with $\mathbb{P}_{p, \pi}(H_{|h|} = h) > 0$.

**Convention 1.2 (Kernel equality up to reachability).** We interpret $\mu_p = \mu_{p^\star}$ as
$$\mu_p(\cdot \mid h, a) = \mu_{p^\star}(\cdot \mid h, a) \quad\text{for every } (h, a) \text{ reachable under } p \text{ or under } p^\star.$$
Equivalently, $p$ and $p^\star$ assign the same conditional distribution to every observation-action pair that either program has positive probability of producing.

**Remark 1.3 (Consistency with existing proofs).** Convention 1.2 is compatible with every construction in the current paper. The policy-gap construction (paper's Theorem 3.6) produces $p'$ differing from $p^\star$ at $(h_{t_0}, b)$ where $h_{t_0}$ is reachable under $p^\star$ (hypothesis: $\mathbb{P}_{p^\star, \pi}(H_{t_0} = h_{t_0}) > 0$). The fit-gap construction (paper's Lemma 3.5) produces $p$ differing at $(h_t, a)$ where $h_t$ is reachable and $\pi_{t+1}(a \mid h_t) > 0$. The syntactic-gap lemma concerns distinct programs with equal kernels, which under Convention 1.2 means equal at reachable pairs — a weaker but more natural condition.

**Remark 1.4 (What the convention fixes).** Under strict kernel equality (the literal reading of $\mu_p = \mu_{p^\star}$), two programs that agree on every reachable pair but disagree at some jointly unreachable pair would be placed in different classes — a distinction no observer can witness. Convention 1.2 eliminates this artefact. The paper's current $[p^\star]$ becomes a well-defined equivalence class of observationally meaningful behaviors.

*Paper-side implication: one clarifying sentence near Definition 3.3 saying "we interpret kernel equality at reachable pairs; unreachable pairs are irrelevant because they have no observable consequence."*

---

## 2. Joins in the observer preorder

**Definition 2.1 (Join of observers).** Given a family $\{\omega_i\}_{i \in I}$ of observers, the *join* $\bigvee_i \omega_i$ is the observer with view space $\prod_i \Omega_{\omega_i}$ and view map $V(p) := (V_{\omega_i}(p))_i$.

**Lemma 2.2 (Join is a least upper bound).** $\bigvee_i \omega_i$ is the least upper bound of $\{\omega_i\}$ in the refinement preorder: $\omega_i \le \bigvee_j \omega_j$ for every $i$, and if $\omega_i \le \omega'$ for every $i$ then $\bigvee_i \omega_i \le \omega'$.

**Proof.** Upper bound: the projection $\pi_i : \prod_j \Omega_{\omega_j} \to \Omega_{\omega_i}$ witnesses $V_{\omega_i} = \pi_i \circ V_{\bigvee_j \omega_j}$, so $\omega_i \le \bigvee_j \omega_j$.

Least: suppose $\omega_i \le \omega'$ for every $i$, with witness $\phi_i : \Omega_{\omega'} \to \Omega_{\omega_i}$ such that $V_{\omega_i} = \phi_i \circ V_{\omega'}$. Define $\phi : \Omega_{\omega'} \to \prod_i \Omega_{\omega_i}$ by $\phi(x) := (\phi_i(x))_i$. Then $V_{\bigvee_j \omega_j}(p) = (V_{\omega_i}(p))_i = (\phi_i(V_{\omega'}(p)))_i = \phi(V_{\omega'}(p))$, so $\bigvee_i \omega_i \le \omega'$. $\square$

**Corollary 2.3 (Join of policy observers).** The observer $\bigvee_\pi \omega_\pi$ has view map $V(p) = (\mathbb{P}_{p, \pi})_{\pi}$ — the full profile of history laws under every policy — and is the least observer refining $\omega_\pi$ for every $\pi$.

---

## 3. The interventional equivalence theorem

**Theorem 3.1 (Interventional equivalence).** Under Convention 1.2, for every $p^\star \in \mathcal{P}$,
$$\bigcap_\pi R_\pi(p^\star) = [p^\star].$$

**Proof.** We prove the two inclusions.

*($\supseteq$): $[p^\star] \subseteq \bigcap_\pi R_\pi(p^\star)$.*

This is the paper's current Lemma 3.3 (Observable quotient) combined with Convention 1.2. If $p \in [p^\star]$, then $\mu_p(\cdot \mid h, a) = \mu_{p^\star}(\cdot \mid h, a)$ for every pair reachable under $p$ or $p^\star$. For any policy $\pi$ and any history $h_t$,
$$\mathbb{P}_{p, \pi}(H_t = h_t) = \prod_{i=1}^t \pi_i(a_i \mid h_{i-1}) \, \mu_p(o_i \mid h_{i-1}, a_i).$$
If any factor $\mu_p(o_i \mid h_{i-1}, a_i) = 0$ because $(h_{i-1}, a_i)$ is unreachable under $p$, then the preceding factors are zero too, so $\mathbb{P}_{p, \pi}(H_t = h_t) = 0 = \mathbb{P}_{p^\star, \pi}(H_t = h_t)$ (since unreachability is symmetric under Convention 1.2). Otherwise every $(h_{i-1}, a_i)$ is reachable, and kernel equality gives $\mu_p(o_i \mid h_{i-1}, a_i) = \mu_{p^\star}(o_i \mid h_{i-1}, a_i)$ pointwise, so the products are equal. Hence $\mathbb{P}_{p, \pi} = \mathbb{P}_{p^\star, \pi}$, giving $p \in R_\pi(p^\star)$ for every $\pi$.

*($\subseteq$): $\bigcap_\pi R_\pi(p^\star) \subseteq [p^\star]$.*

Suppose $p \in \bigcap_\pi R_\pi(p^\star)$, i.e., $\mathbb{P}_{p, \pi} = \mathbb{P}_{p^\star, \pi}$ for every $\pi$. We show $\mu_p$ and $\mu_{p^\star}$ agree at every reachable pair.

Fix any policy $\pi$ with full support: $\pi_t(a \mid h) > 0$ for every $(h, a, t)$. (Such policies exist: uniform over a finite subset of $\mathcal{A}$, or any fixed full-support distribution at each step.) Equality of $\mathbb{P}_{p, \pi}$ and $\mathbb{P}_{p^\star, \pi}$ on every cylinder gives, for every history $h_t$,
$$\prod_{i=1}^t \pi_i(a_i \mid h_{i-1}) \, \mu_p(o_i \mid h_{i-1}, a_i) = \prod_{i=1}^t \pi_i(a_i \mid h_{i-1}) \, \mu_{p^\star}(o_i \mid h_{i-1}, a_i).$$
The policy factor $\prod_i \pi_i(a_i \mid h_{i-1})$ is strictly positive by full support. Dividing,
$$\mu_p(o_{1:t} \mid a_{1:t}) = \mu_{p^\star}(o_{1:t} \mid a_{1:t}) \quad\text{for every sequence } (a_{1:t}, o_{1:t}). \tag{$\ast$}$$

We now extract kernel equality from the joint-likelihood equality ($\ast$). Induct on $t$.

*Base ($t = 1$).* For every $(a_1, o_1)$, $(\ast)$ gives $\mu_p(o_1 \mid \varepsilon, a_1) = \mu_{p^\star}(o_1 \mid \varepsilon, a_1)$. The pair $(\varepsilon, a_1)$ is reachable under both programs (the empty history is always reachable), so kernel equality at $(\varepsilon, a_1)$ holds.

*Inductive step.* Suppose kernel equality holds at every reachable pair $(h, a)$ with $|h| \le t - 1$. Fix a history $h_t = (a_{1:t}, o_{1:t})$ and an action $a_{t+1}$ with $(h_t, a_{t+1})$ reachable under $p^\star$ or $p$. Reachability means $\mu_{p^\star}(o_{1:t} \mid a_{1:t}) > 0$ or $\mu_p(o_{1:t} \mid a_{1:t}) > 0$; by $(\ast)$ the two conditions coincide, and we denote their common positive value $L_t > 0$. Apply $(\ast)$ at length $t + 1$:
$$L_t \cdot \mu_p(o_{t+1} \mid h_t, a_{t+1}) = \mu_p(o_{1:t+1} \mid a_{1:t+1}) = \mu_{p^\star}(o_{1:t+1} \mid a_{1:t+1}) = L_t \cdot \mu_{p^\star}(o_{t+1} \mid h_t, a_{t+1}).$$
Dividing by $L_t$ gives $\mu_p(o_{t+1} \mid h_t, a_{t+1}) = \mu_{p^\star}(o_{t+1} \mid h_t, a_{t+1})$ for every $o_{t+1}$. So kernels agree at $(h_t, a_{t+1})$.

By induction, kernels agree at every reachable pair. By Convention 1.2, $p \in [p^\star]$. $\square$

**Corollary 3.2 (Supremum identity for observers).** $\omega_{\mathrm{behav}} = \bigvee_\pi \omega_\pi$ in the refinement preorder.

**Proof.** By Lemma 2.2, it suffices to show $\sim_{\mathrm{behav}} \;=\; \bigcap_\pi \sim_{\omega_\pi}$ as equivalence relations on $\mathcal{P}$. But $(p, p') \in \sim_{\mathrm{behav}} \Leftrightarrow \mu_p = \mu_{p'} \Leftrightarrow p \in [p']$; and $(p, p') \in \bigcap_\pi \sim_{\omega_\pi} \Leftrightarrow \mathbb{P}_{p, \pi} = \mathbb{P}_{p', \pi}$ for every $\pi \Leftrightarrow p \in \bigcap_\pi R_\pi(p')$. Theorem 3.1 gives the equality. $\square$

---

## 4. The Pearl bridge

Theorem 3.1 has a direct reading in causal-inference terms.

**Remark 4.1 (Policies as interventions).** In Pearl's causal-inference formalism, two structural causal models are *interventionally equivalent* iff they induce the same post-intervention distribution under every do-operator. The analogue in the interactive-learning setting: policies $\pi$ are the interventions, and the post-intervention distribution is $\mathbb{P}_{p, \pi}$. Theorem 3.1 states that two programs are interventionally equivalent iff their action-conditioned kernels agree at every reachable pair. Reachable pairs are the *intervenable nodes* — the points where an intervention (policy) can probe the program.

**Remark 4.2 (The observational-interventional gap).** The paper's strict refinement $\omega_\pi < \omega_{\mathrm{behav}}$ (Theorem 1.2 of Phase B) is the algorithmic analogue of Pearl's observational-interventional gap: a fixed-policy observer sees only the law that that policy induces, while the interventional observer sees every policy-induced law. The gap is closed by varying the policy. Theorem 3.1 makes this closure exact: $\bigvee_\pi \omega_\pi = \omega_{\mathrm{behav}}$.

**Remark 4.3 (What is new relative to Pearl).** Pearl's interventional equivalence theorem is about finite directed-graphical models with parametric structural equations. The result is substantive there because interventional distributions are *not* in general determined by the observational distribution, and graphical conditions (do-calculus) are needed to read off interventional distributions from observational ones. In our setting, the result is phrased at the level of algorithmically specified interactive environments with uncountably many possible policies, and the equivalence is between kernel equality at reachable pairs and induced-law equality under every policy. The forward direction is trivial; the reverse direction is the content, and it relies on the full-support policy construction (existence of a $\pi$ that reaches every finite prefix with positive probability).

**Remark 4.4 (Connection to Blackwell's comparison of experiments).** A deeper ancestor of this circle of ideas is Blackwell's comparison-of-experiments framework, which orders experiments by a sufficiency-type relation. The refinement order on observers is, loosely, a Blackwell-style comparison on the informational content of policies. Theorem 3.1 says the policy-class supremum attains the Blackwell-maximum among empirical probes. We can mention Blackwell in the discussion but not press the analogy; the Pearl bridge is the more direct audience hook.

---

## 5. What Phase C gives us

Phase C completes the observer-formalism content of the paper:

- **Supremum identity.** $\omega_{\mathrm{behav}} = \bigvee_\pi \omega_\pi$ (Corollary 3.2). The behavioral observer is not a new object outside the policy family; it is the least upper bound of that family.
- **Pearl bridge.** The $\omega_\pi \to \omega_{\mathrm{behav}}$ promotion is the algorithmic observational-interventional gap (Remark 4.2). Theorem 3.1 closes it.
- **Reachability clarification.** The paper's $[p^\star]$ is made precise via Convention 1.2. One clarifying sentence in Section 3 handles this.

**Sharpness of the ceiling theorem.** Phase B established $\omega \le \omega_{\mathrm{behav}}$ for every $\omega \in \mathcal{E}$ (the empirical closure). Phase C tells us the policy-observer family is already enough to span up to $\omega_{\mathrm{behav}}$: for every refinement $\omega < \omega_{\mathrm{behav}}$ (equivalently, $\omega \not\ge \omega_{\mathrm{behav}}$), there is some policy $\pi$ with $\omega_\pi \not\le \omega$. The ceiling is sharp *in the supremum sense*: no refinement strictly below $\omega_{\mathrm{behav}}$ is an upper bound for the policy family.

Whether $\omega_{\mathrm{behav}}$ itself is in $\mathcal{E}$ as a single realizable observer — i.e., whether some single estimation procedure's induced observer equals $\omega_{\mathrm{behav}}$ — is a different question. A Solomonoff learner with a universal prior, running an appropriate adaptive policy, realizes (in the limit) an observer that matches $\omega_{\mathrm{behav}}$ modulo prior support. We can state this cleanly in Phase E as a consequence of the main convergence theorem; it does not need its own phase.

---

## 6. What this looks like in the paper

Phase C's integration is lighter than Phases A and B: one theorem, one corollary, two remarks, one convention. Proposed placement:

1. **Convention 1.2** goes into Section 2 or near Definition 3.3 — one sentence clarifying kernel equality.
2. **Theorem 3.1 (Interventional equivalence)** goes into Section 3 after the current Theorem 3.7 (Factor-through-quotient), as a new theorem titled "Interventional characterization of the semantic class." The proof (the full-support policy construction + induction) fits in about a half page.
3. **Corollary 3.2** is an immediate rephrasing at the observer level; goes adjacent to Theorem 3.1.
4. **Remarks 4.1–4.3** become a single "Remark (Pearl bridge)" of two or three sentences, naming Pearl and locating our result as the algorithmic analogue.
5. A forward reference in the abstract or introduction: "The behavioral observer is characterized as the supremum of the policy-observer family, making $[p^\star]$ the algorithmic analogue of Pearl's interventional equivalence class."

This is about a half page of new main-text material plus the one-sentence convention.

---

## 7. Open questions

1. *The reachability convention.* Convention 1.2 is a clarification, not a change — but it is a load-bearing one. If we state it explicitly in the paper, it should be in Section 2 (setup) rather than Section 3 (hierarchy), so the reader sees it before encountering $[p^\star]$. My lean: put it in Section 2 as a one-sentence remark following the factorization of $\mu_p$. Your call on placement.

2. *Pearl citation.* The Pearl bridge deserves a direct reference. Natural citations: Pearl's *Causality* (2009 2nd edition) for the do-calculus; Pearl & Bareinboim's later interventional-equivalence results for the sharper version. Do you want one citation or several? My lean: one, Pearl 2009, for the generic do-calculus framing. We can elaborate in the discussion.

3. *Blackwell.* Remark 4.4 mentions Blackwell's comparison of experiments. This is a distant but real ancestor. We can mention it once in the discussion or not at all. My lean: one sentence in the discussion. Skip if you want a tighter paper.

4. *Supremum-sharp vs. element-sharp.* Phase C establishes supremum-sharpness of the ceiling; element-sharpness (Solomonoff consistency) is deferred to Phase E. Do we want to state supremum-sharpness in Section 3 as its own theorem, or let it come out as a remark? My lean: a remark after Theorem 3.1 — "The policy-observer family spans up to the behavioral ceiling; no strictly weaker observer bounds the family uniformly." Not worth its own theorem, and doesn't need Phase E to finish it.

5. *Naming.* Now that Phase C is done, we have a concrete content reason to rename $\omega_{\mathrm{behav}}$ to $\omega_{\mathrm{int}}$ (interventional). My lean: keep $\omega_{\mathrm{behav}}$ in the body as the neutral name and use "interventional observer" in prose. Dual naming handles the Pearl reader without a formal rename.
