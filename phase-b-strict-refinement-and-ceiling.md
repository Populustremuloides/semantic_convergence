# Phase B: Strict Refinement and the Observable-Quotient Upgrade

**Goal of Phase B.** Establish that the refinement chain is strict at every link, recast the paper's observable-quotient theorem as an upper-bound theorem on observers induced by estimation procedures, and prove the bolder *ceiling theorem*: $\omega_{\mathrm{behav}}$ is a universal upper bound for the entire class of empirically realizable observers.

**Dependencies.** Phase A (Definitions 1.1, 2.1, 3.1–3.4; Lemmas 2.2, 2.3; Proposition 4.1).

**Scope discipline.** Phase B does not prove the converse direction (that every observer bounded by $\omega_{\mathrm{behav}}$ is empirically realizable) — that is a sharpness claim belonging to Phase C, where it follows from universal-prior consistency. Phase B does not address the intersection-of-policy-observers identity $\omega_{\mathrm{behav}} = \bigvee_\pi \omega_\pi$ — also Phase C.

---

## 1. Strict refinement at every link

The strict-separation results currently in the paper (fit gap, policy gap, syntactic gap) each construct a pair of programs that a weaker observer cannot distinguish but a stronger observer can. Under the Phase A formalism these constructions witness strict refinement exactly.

**Theorem 1.1 (Syntactic strictly refines behavioral).** Suppose there exist distinct $p, p' \in \mathcal{P}$ with $\mu_p = \mu_{p'}$. Then $\omega_{\mathrm{behav}} < \omega_{\mathrm{syn}}$.

**Proof.** $\omega_{\mathrm{behav}} \le \omega_{\mathrm{syn}}$ by Proposition 4.1. For strictness, the hypothesis gives $p, p'$ with $V_{\mathrm{syn}}(p) = p \neq p' = V_{\mathrm{syn}}(p')$ and $V_{\mathrm{behav}}(p) = \mu_p = \mu_{p'} = V_{\mathrm{behav}}(p')$. Hence $(p, p') \in\,\sim_{\mathrm{behav}}\setminus\sim_{\mathrm{syn}}$, so by Lemma 2.2(3) $\omega_{\mathrm{syn}} \not\le \omega_{\mathrm{behav}}$. $\square$

*This is the paper's syntactic-gap lemma under the observer reading; the hypothesis is automatic in the Solomonoff setting.*

**Theorem 1.2 (Behavioral strictly refines policy).** Assume $|\mathcal{A}| \ge 2$. Let $\pi$ be a policy for which there exist a history $h_{t_0}$ with $\mathbb{P}_{p^\star, \pi}(H_{t_0} = h_{t_0}) > 0$, an action $b \in \mathcal{A}$ with $\pi_{t_0 + 1}(b \mid h_{t_0}) = 0$, and an observation $y \in \mathcal{O}$ with $\mu_{p^\star}(y \mid h_{t_0}, b) < 1$. Then $\omega_\pi < \omega_{\mathrm{behav}}$.

**Proof.** $\omega_\pi \le \omega_{\mathrm{behav}}$ by Proposition 4.1. For strictness, the current Theorem 3.6 of the paper (policy gap) constructs $p' \in R_\pi(p^\star) \setminus [p^\star]$. Equivalently, $V_\pi(p') = V_\pi(p^\star)$ and $V_{\mathrm{behav}}(p') \neq V_{\mathrm{behav}}(p^\star)$. Hence $(p', p^\star) \in\,\sim_\pi\setminus\sim_{\mathrm{behav}}$, so $\omega_{\mathrm{behav}} \not\le \omega_\pi$. $\square$

*The constructed $p'$ is the adversary's move: it agrees with $p^\star$ on every pair the $\pi$-fixed observer sees and disagrees only at the pair $(h_{t_0}, b)$ the observer never queries. This is the central strict refinement of the hierarchy.*

**Theorem 1.3 (Policy strictly refines history).** Assume $|\mathcal{O}| \ge 2$, fix a policy $\pi$, a history $h_t$ with $\mathbb{P}_{p^\star, \pi}(H_t = h_t) > 0$, and a next action $a$ with $\pi_{t+1}(a \mid h_t) > 0$ and $\mu_{p^\star}(\cdot \mid h_t, a)$ not a point mass. Then $\omega_{h_t} < \omega_\pi$.

**Proof.** $\omega_{h_t} \le \omega_\pi$ by Proposition 4.1. For strictness, the current Lemma 3.5 of the paper (fit gap) constructs $p \in R_{h_t}(p^\star) \setminus R_\pi(p^\star)$. Equivalently, $V_{h_t}(p) = V_{h_t}(p^\star)$ and $V_\pi(p) \neq V_\pi(p^\star)$. Hence $\omega_\pi \not\le \omega_{h_t}$. $\square$

**Corollary 1.4 (Strict chain).** Under the combined hypotheses of Theorems 1.1–1.3,
$$\omega_{h_t} \;<\; \omega_\pi \;<\; \omega_{\mathrm{behav}} \;<\; \omega_{\mathrm{syn}},$$
equivalently $\{p^\star\} \subsetneq [p^\star] \subsetneq R_\pi(p^\star) \subsetneq R_{h_t}(p^\star)$.

*This recovers the paper's Theorem 3.9 (Strict knowability hierarchy) exactly. The indistinguishability-class containments are the current statement; the observer-level strictness is the new content.*

---

## 2. Estimation procedures and the observers they induce

To state the observable-quotient upgrade cleanly, we formalize the class of observers a learner can realize by estimating from histories.

**Definition 2.1 (Estimation procedure).** An *estimation procedure* is a tuple $E = (\pi, (\Omega_E, d_E), (\hat\tau_t)_{t \ge 1})$ where:

- $\pi$ is a history-based policy (each $\pi_t$ depends only on $h_{t-1}$),
- $(\Omega_E, d_E)$ is a metric space (the *estimation range*),
- $\hat\tau_t : (\mathcal{A} \times \mathcal{O})^t \to \Omega_E$ is measurable for each $t \ge 1$,
- For every $p \in \mathcal{P}$, the random variables $\hat\tau_t(H_t)$ converge in probability under $(p, \pi)$ to some limit $\tau_E(p) \in \Omega_E$.

The *induced observer of $E$* is $\omega_E := (\Omega_E, \tau_E)$, with view map $\tau_E : \mathcal{P} \to \Omega_E$.

**Remark 2.2 (Measurability).** The only measurability needed is that each $\hat\tau_t$ is a measurable function of $H_t$ under the product $\sigma$-algebra on $(\mathcal{A} \times \mathcal{O})^t$; the law-level machinery is standard.

**Remark 2.3 (Generality).** Definition 2.1 covers every form of history-based estimation: point estimates of real-valued targets (classical estimators), posterior-mass estimators, predictive-law estimators, class-membership probabilities, and so on. It does not cover procedures that use $p$ itself — those are not empirical.

---

## 3. The observable-quotient upgrade

**Theorem 3.1 (Observable-quotient upgrade).** For every estimation procedure $E$, $\omega_E \le \omega_{\mathrm{behav}}$.

**Proof.** By Lemma 2.2(2), it suffices to show that $V_{\mathrm{behav}}(p) = V_{\mathrm{behav}}(p')$ implies $\tau_E(p) = \tau_E(p')$ — i.e., $\mu_p = \mu_{p'}$ implies equal limits of $\hat\tau_t(H_t)$ under $(p, \pi)$ and $(p', \pi)$.

Suppose $\mu_p = \mu_{p'}$. By the observable-quotient lemma (Lemma 3.3 of the paper: if $p \equiv p'$ then $\mathbb{P}_{p, \pi} = \mathbb{P}_{p', \pi}$ for every policy $\pi$), the law of $H_t$ under $(p, \pi)$ equals the law of $H_t$ under $(p', \pi)$ for every $t$. Since $\hat\tau_t$ is a measurable function of $H_t$, the law of $\hat\tau_t(H_t)$ is the same under $(p, \pi)$ and $(p', \pi)$. By definition of convergence in probability, $\hat\tau_t(H_t) \to \tau_E(p)$ in probability under $(p, \pi)$ and $\hat\tau_t(H_t) \to \tau_E(p')$ in probability under $(p', \pi)$; equality of laws transports each convergence to the other, and uniqueness of in-probability limits in the metric space $(\Omega_E, d_E)$ gives $\tau_E(p) = \tau_E(p')$. $\square$

**Corollary 3.2 (Paper's Theorem 3.7 recovered).** Every history-recoverable target $\tau : \mathcal{P} \to \mathcal{T}$ factors through the semantic quotient: there exists a unique $\bar\tau : \mathcal{C} \to \mathcal{T}$ with $\tau = \bar\tau \circ [\cdot]$.

**Proof.** Let $E = (\pi, (\mathcal{T}, d_\mathcal{T}), (\hat\tau_t))$ be the estimation procedure witnessing history-recoverability of $\tau$, so $\tau_E(p) = \tau(p)$ for every $p$. By Theorem 3.1, $\omega_E \le \omega_{\mathrm{behav}}$, so by Lemma 2.2(2), $p \equiv p'$ implies $\tau(p) = \tau(p')$. Define $\bar\tau([p]) := \tau(p)$; uniqueness is immediate. $\square$

---

## 4. The ceiling theorem

Theorem 3.1 says each individually induced observer is bounded above by $\omega_{\mathrm{behav}}$. The stronger claim — the one that settles $\omega_{\mathrm{behav}}$'s role as *the* empirical ceiling — is that no combination, iteration, or joint realization of estimation procedures can escape the bound.

**Definition 4.1 (Empirical closure).** The *empirical closure* $\mathcal{E}$ is the smallest class of observers containing every induced observer $\omega_E$ (Definition 2.1) and closed under arbitrary joins in the observer preorder: if $\{\omega_i\}_{i \in I} \subseteq \mathcal{E}$, then the observer $\omega_\vee$ with view space $\prod_{i \in I} \Omega_{\omega_i}$ and view map $V_{\omega_\vee}(p) := (V_{\omega_i}(p))_{i \in I}$ is also in $\mathcal{E}$.

**Remark 4.2 (What joins capture).** The join $\bigvee_i \omega_i$ is the observer who sees every view in the family simultaneously. Closing under joins captures learners that run multiple estimation procedures and combine their outputs — adaptively or not, jointly or not. Any empirically realizable observer, constructed by any combination of histories, estimators, and policy choices, lives in $\mathcal{E}$.

**Theorem 4.3 (Ceiling theorem).** For every $\omega \in \mathcal{E}$, $\omega \le \omega_{\mathrm{behav}}$.

**Proof.** By induction on the construction of $\mathcal{E}$. The base case $\omega = \omega_E$ for some estimation procedure $E$ is Theorem 3.1. For the closure step, suppose $\omega_i \le \omega_{\mathrm{behav}}$ for every $i \in I$ and $\omega_\vee := \bigvee_i \omega_i$. We show $\omega_\vee \le \omega_{\mathrm{behav}}$.

By Lemma 2.2(2), suppose $V_{\mathrm{behav}}(p) = V_{\mathrm{behav}}(p')$. Then for each $i \in I$, $\omega_i \le \omega_{\mathrm{behav}}$ gives $V_{\omega_i}(p) = V_{\omega_i}(p')$. Hence $V_{\omega_\vee}(p) = (V_{\omega_i}(p))_i = (V_{\omega_i}(p'))_i = V_{\omega_\vee}(p')$. $\square$

**Corollary 4.4 (No learner exceeds the behavioral ceiling).** Let a learner execute any (possibly adaptive, possibly history-dependent) collection of estimation procedures on a single environment $p^\star$. The effective observer — the observer whose view is the full tuple of whatever the learner's estimators eventually resolve to — lies in $\mathcal{E}$ and is therefore bounded above by $\omega_{\mathrm{behav}}$. In particular, no history-based learner can distinguish programs within $[p^\star]$ from $p^\star$ itself, regardless of how many estimators it runs or how it combines them.

*This is the theorem-level status the paper's observable-quotient section has been gesturing at. The current Theorem 3.7 is about single target maps; Theorem 4.3 is about the whole lattice of empirical observers. The content of "$[p^\star]$ is the theorem-level ceiling" is now a ceiling-of-a-closed-class theorem.*

---

## 5. What Phase B gives us

Phase B has upgraded the paper's Section 3 content to observer-language status:

- The strict-knowability-hierarchy theorem is now a strict-refinement theorem at every link of the observer chain (Corollary 1.4).
- The observable-quotient theorem is now a universal upper bound on observers induced by estimation procedures (Theorem 3.1).
- The "$[p^\star]$ as theorem-level ceiling" remark is now a ceiling theorem on the entire empirical closure (Theorem 4.3).

What is now fully set up for Phases D and E:

- The near-miss can be phrased as "the AFE principle's realized observer $\omega_{\mathrm{AFE}}$ is an element of $\mathcal{E}$ that does not attain $\omega_{\mathrm{behav}}$ — specifically, it stalls at $\omega_{\pi^{\mathrm{AFE}}}$ for an EFE-chosen policy $\pi^{\mathrm{AFE}}$ with unqueried reachable pairs."
- The main theorem can be phrased as "class-against-complement + separation + universal prior delivers a realized observer $\omega_{\mathrm{CAC}} \in \mathcal{E}$ that attains $\omega_{\mathrm{behav}}$ along the realized trajectory, modulo prior support."

Phase C will close the picture by proving that $\omega_{\mathrm{behav}}$ is the *supremum* of the policy-observer family, $\omega_{\mathrm{behav}} = \bigvee_\pi \omega_\pi$, making the ceiling sharp and drawing the explicit Pearl bridge: the "full-behavioral observer" is the algorithmic analogue of Pearl's interventional observer.

---

## 6. Open questions

1. *Tightness companion to Theorem 3.1.* The bound in Theorem 3.1 is established; a natural companion claim is that the bound is attained — for every $\omega \le \omega_{\mathrm{behav}}$, there exists an estimation procedure $E$ with $\omega_E$ equivalent to $\omega$ modulo prior support. This is genuinely a Solomonoff-consistency / universal-prior result and I am keeping it in Phase C. Flagging because you might prefer to handle tightness in Phase B for narrative balance — let me know if so and I'll move it forward.

2. *Scope of "estimation procedure."* Definition 2.1 requires in-probability convergence to some limit for *every* $p \in \mathcal{P}$. An alternative would allow almost-sure convergence, or convergence along a subsequence, or convergence only for $p$ in some class (e.g., the support of the prior). The in-probability choice matches the paper's current history-recoverability definition exactly. If you want to broaden this in the formal version, the ceiling theorem still holds — only the notion of "induced observer" changes. My lean: keep in-probability, matching the paper.

3. *The join closure.* Definition 4.1 takes arbitrary joins. For the paper's purposes, countable joins would suffice (any learner realizes countably many estimators). Arbitrary joins are cleaner to state and don't cost anything in the proof. My lean: arbitrary joins. Flagging only because a careful reader might ask.

4. *Naming: $\mathcal{E}$ versus "empirical observers."* The class $\mathcal{E}$ has no standard name in the literature (to my knowledge). Alternatives: $\mathrm{Obs}_{\mathrm{emp}}$, $\mathcal{O}_{\mathrm{emp}}$, "history-realizable observers." My lean: use $\mathcal{E}$ in the math and "empirical observers" in the prose — the two-register convention mirrors how the paper uses $\mathcal{P}$ and "programs."
