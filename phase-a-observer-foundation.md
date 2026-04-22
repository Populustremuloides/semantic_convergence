# Phase A: Observer Foundation

**Goal of Phase A.** Fix the definition of observer, the refinement order, and the four specific observers of the hierarchy, and verify that they form a chain in the refinement order. Strict refinement, upper-bound theorems for estimators, and the interventional-equivalence theorem are deferred to later phases.

**Scope discipline.** This phase introduces mathematical objects and proves the basic order-theoretic facts about them. It does not re-derive any of the paper's existing theorems. It does not touch measurability (introduced in Phase B where needed). It does not state strict refinement (Phase B). It does not state $\bigvee_\pi \omega_\pi = \omega_{\text{behav}}$ (Phase C).

---

## 1. The observer

Fix the setup of Section 2 of the paper: countable action alphabet $\mathcal{A}$, countable observation alphabet $\mathcal{O}$, universal prefix machine $U$, and $\mathcal{P}$ the set of programs in the prefix-free domain of $U$ that induce interactive environment models. Each $p \in \mathcal{P}$ defines an action-conditioned chronological law $\mu_p$.

**Definition 1.1 (Observer).** An *observer* is a pair $\omega = (\Omega_\omega, V_\omega)$ where $\Omega_\omega$ is a set and $V_\omega : \mathcal{P} \to \Omega_\omega$ is a function. The function $V_\omega$ is the *view map* of $\omega$; the set $\Omega_\omega$ is its *view space*.

Two programs $p, p' \in \mathcal{P}$ are *$\omega$-indistinguishable*, written $p \sim_\omega p'$, iff $V_\omega(p) = V_\omega(p')$. The *$\omega$-indistinguishability class of $p$* is
$$[p]_\omega := V_\omega^{-1}(V_\omega(p)) = \{\, p' \in \mathcal{P} : V_\omega(p') = V_\omega(p) \,\}.$$

**Remark 1.2 (Adversarial reading).** Equivalently, $[p]_\omega$ is the set of programs an adversary could substitute for $p$ without the $\omega$-observer detecting the substitution: the substitute is caught iff the adversary changes the value of $V_\omega$.

**Remark 1.3 (On abstraction).** Definition 1.1 imposes no structure on $\Omega_\omega$ — no topology, no measurability, no algebra. This is deliberate. Phase B will require measurable view spaces when we combine observers with probability (specifically: when the view map is a limit in probability of estimators). For Phase A the order-theoretic facts are clean at the level of plain set maps.

---

## 2. The refinement order

**Definition 2.1 (Refinement).** Let $\omega, \omega'$ be observers. We say $\omega'$ *refines* $\omega$, written $\omega \le \omega'$, iff there exists a function $\phi : \Omega_{\omega'} \to \Omega_\omega$ such that
$$V_\omega = \phi \circ V_{\omega'}.$$

We write $\omega < \omega'$ iff $\omega \le \omega'$ and $\omega' \not\le \omega$; call this *strict refinement*.

**Lemma 2.2 (Four equivalent characterizations).** For observers $\omega, \omega'$, the following are equivalent.

1. $\omega \le \omega'$.
2. For every $p, p' \in \mathcal{P}$, if $V_{\omega'}(p) = V_{\omega'}(p')$, then $V_\omega(p) = V_\omega(p')$.
3. $\sim_{\omega'}\;\subseteq\;\sim_\omega$ as subsets of $\mathcal{P} \times \mathcal{P}$.
4. For every $p \in \mathcal{P}$, $[p]_{\omega'} \subseteq [p]_\omega$.

**Proof.**
*(1) ⇒ (2).* Suppose $\omega \le \omega'$ via $\phi$, and $V_{\omega'}(p) = V_{\omega'}(p')$. Then $V_\omega(p) = \phi(V_{\omega'}(p)) = \phi(V_{\omega'}(p')) = V_\omega(p')$.

*(2) ⇔ (3).* Direct from the definition of $\sim$: $(p, p') \in\, \sim_\omega \Leftrightarrow V_\omega(p) = V_\omega(p')$.

*(3) ⇔ (4).* Standard: a containment of equivalence relations holds iff each class of the finer relation is contained in the corresponding class of the coarser.

*(2) ⇒ (1).* Assume (2). Define $\phi$ on $V_{\omega'}(\mathcal{P})$ by
$$\phi(V_{\omega'}(p)) := V_\omega(p).$$
This is well-defined by (2): if $V_{\omega'}(p) = V_{\omega'}(p')$ then $V_\omega(p) = V_\omega(p')$, so the assignment does not depend on the representative. Extend $\phi$ arbitrarily to $\Omega_{\omega'} \setminus V_{\omega'}(\mathcal{P})$. Then $V_\omega = \phi \circ V_{\omega'}$. $\square$

**Reading.** Lemma 2.2 is what makes the refinement order intuitive: "$\omega'$ refines $\omega$" means the finer observer $\omega'$ has a finer indistinguishability partition, equivalently smaller indistinguishability classes. The adversarial reading: anything the weaker observer catches, the stronger observer also catches.

**Lemma 2.3 (Preorder).** The refinement relation $\le$ is reflexive and transitive.

**Proof.**
*Reflexivity.* $\omega \le \omega$ via $\phi = \mathrm{id}_{\Omega_\omega}$.

*Transitivity.* Suppose $\omega \le \omega'$ via $\phi$ and $\omega' \le \omega''$ via $\psi$. Then $V_\omega = \phi \circ V_{\omega'} = \phi \circ \psi \circ V_{\omega''}$, so $\omega \le \omega''$ via $\phi \circ \psi$. $\square$

**Remark 2.4 (Antisymmetry up to equivalence).** $\omega \le \omega'$ and $\omega' \le \omega$ iff $\sim_\omega\; = \;\sim_{\omega'}$, i.e., iff the two observers induce the same indistinguishability partition of $\mathcal{P}$. Hence $\le$ is a partial order on the set of partitions of $\mathcal{P}$ that arise from observers, not on observers themselves. When we say "the refinement chain," we mean the chain in this partition-level partial order, equivalently the chain of observers modulo partition-equivalence.

---

## 3. The four observers of the hierarchy

We specify four observers, each with an explicit view map.

**Definition 3.1 (Source observer $\omega_{\mathrm{syn}}$).** $\Omega_{\mathrm{syn}} := \mathcal{P}$ and $V_{\mathrm{syn}}(p) := p$.

**Definition 3.2 (Behavioral observer $\omega_{\mathrm{behav}}$).** Let $\mathcal{M}$ denote the set of action-conditioned chronological laws, i.e., the set of functions
$$\mu : (\mathcal{A} \times \mathcal{O})^* \times \mathcal{A} \to \Delta(\mathcal{O})$$
satisfying, for each history $h$ and action $a$, $\sum_{o \in \mathcal{O}} \mu(o \mid h, a) = 1$. Let $\Omega_{\mathrm{behav}} := \mathcal{M}$ and $V_{\mathrm{behav}}(p) := \mu_p$.

**Definition 3.3 (Policy observer $\omega_\pi$, for each policy $\pi$).** For a policy $\pi = (\pi_t)_{t \ge 1}$ with $\pi_t(a_t \mid h_{t-1})$ the kernel at step $t$, let $\Omega_\pi$ be the set of probability measures on $(\mathcal{A} \times \mathcal{O})^\mathbb{N}$ under the product $\sigma$-algebra. Let $V_\pi(p) := \mathbb{P}_{p, \pi}$, the joint law of $(A_t, O_t)_{t \ge 1}$ under $(p, \pi)$.

**Definition 3.4 (History observer $\omega_{h_t}$, for each realized history $h_t = (a_{1:t}, o_{1:t})$).** Let $\Omega_{h_t} := [0, 1]$ and $V_{h_t}(p) := \mu_p(o_{1:t} \mid a_{1:t})$.

**Remark 3.5 (Indistinguishability classes recover the hierarchy).** With these definitions, $[p^\star]_{\omega_{h_t}} = R_{h_t}(p^\star)$, $[p^\star]_{\omega_\pi} = R_\pi(p^\star)$, $[p^\star]_{\omega_{\mathrm{behav}}} = [p^\star]$, and $[p^\star]_{\omega_{\mathrm{syn}}} = \{p^\star\}$. The paper's four sets are exactly the indistinguishability classes at $p^\star$ of the four observers of Definitions 3.1–3.4.

---

## 4. The refinement chain

**Proposition 4.1 (Refinement chain).** For any $p^\star \in \mathcal{P}$, any policy $\pi$, and any history $h_t$ with $\prod_{i=1}^t \pi_i(a_i \mid h_{i-1}) > 0$,
$$\omega_{h_t} \;\le\; \omega_\pi \;\le\; \omega_{\mathrm{behav}} \;\le\; \omega_{\mathrm{syn}}.$$

**Proof.** We exhibit factorization maps $\phi$ for each inequality.

*$\omega_{\mathrm{behav}} \le \omega_{\mathrm{syn}}$.* Define $\phi_{\mathrm{syn} \to \mathrm{behav}} : \mathcal{P} \to \mathcal{M}$ by $\phi_{\mathrm{syn} \to \mathrm{behav}}(p) := \mu_p$. Then
$$V_{\mathrm{behav}}(p) = \mu_p = \phi_{\mathrm{syn} \to \mathrm{behav}}(p) = \phi_{\mathrm{syn} \to \mathrm{behav}}(V_{\mathrm{syn}}(p)),$$
so $V_{\mathrm{behav}} = \phi_{\mathrm{syn} \to \mathrm{behav}} \circ V_{\mathrm{syn}}$.

*$\omega_\pi \le \omega_{\mathrm{behav}}$.* The law $\mathbb{P}_{p, \pi}$ is determined by $\mu_p$ and $\pi$. Specifically, for any cylinder event $H_T = h_T$,
$$\mathbb{P}_{p, \pi}(H_T = h_T) = \prod_{t=1}^T \pi_t(a_t \mid h_{t-1}) \, \mu_p(o_t \mid h_{t-1}, a_t).$$
Since $\pi$ is fixed, the map
$$\Phi_\pi : \mathcal{M} \to \Omega_\pi, \qquad \mu \mapsto \text{the law on } (\mathcal{A} \times \mathcal{O})^\mathbb{N} \text{ with cylinder probabilities } \prod_t \pi_t(a_t \mid h_{t-1}) \mu(o_t \mid h_{t-1}, a_t)$$
is well-defined (Kolmogorov extension gives the measure on the product $\sigma$-algebra from the consistent family of cylinder probabilities). Then $V_\pi(p) = \Phi_\pi(\mu_p) = \Phi_\pi(V_{\mathrm{behav}}(p))$.

*$\omega_{h_t} \le \omega_\pi$.* The observer $\omega_{h_t}$ sees the scalar $\mu_p(o_{1:t} \mid a_{1:t})$. From the policy observer's view $\mathbb{P}_{p, \pi}$, this scalar is recoverable: evaluate the cylinder probability $\mathbb{P}_{p, \pi}(H_t = h_t)$ and divide by the (positive) policy factor,
$$\mu_p(o_{1:t} \mid a_{1:t}) = \frac{\mathbb{P}_{p, \pi}(H_t = h_t)}{\prod_{i=1}^t \pi_i(a_i \mid h_{i-1})}.$$
Define $\Psi_{\pi, h_t} : \Omega_\pi \to [0, 1]$ by
$$\Psi_{\pi, h_t}(\mathbb{P}) := \frac{\mathbb{P}(H_t = h_t)}{\prod_{i=1}^t \pi_i(a_i \mid h_{i-1})}.$$
Then $V_{h_t}(p) = \Psi_{\pi, h_t}(V_\pi(p))$, so $V_{h_t} = \Psi_{\pi, h_t} \circ V_\pi$. $\square$

**Remark 4.2 (What the chain does not yet say).** Proposition 4.1 establishes the existence of factorization maps, hence containment of indistinguishability classes at $p^\star$: $\{p^\star\} \subseteq [p^\star] \subseteq R_\pi(p^\star) \subseteq R_{h_t}(p^\star)$. The paper's current Lemma 3.4 (Nesting) is recovered exactly. Strictness of each inclusion — $\omega_{h_t} < \omega_\pi$, $\omega_\pi < \omega_{\mathrm{behav}}$, $\omega_{\mathrm{behav}} < \omega_{\mathrm{syn}}$ — is a separate claim reserved for Phase B, to be witnessed by the current fit-gap, policy-gap, and syntactic-gap constructions.

**Remark 4.3 (The chain is a chain in $\pi$- and $h_t$-dependent senses).** Proposition 4.1 holds for each fixed policy $\pi$ and each fixed realized history $h_t$ with positive policy-induced probability. Different policies give incomparable policy observers in general ($\omega_\pi$ and $\omega_{\pi'}$ need not be $\le$-related). What is uniform is that every policy observer is dominated by the behavioral observer, $\omega_\pi \le \omega_{\mathrm{behav}}$, and every history observer is dominated by the policy observer along whose induced law the history arose. Phase C will show that the behavioral observer is the supremum of the policy observers across all $\pi$ — equivalently, $\bigcap_\pi R_\pi(p^\star) = [p^\star]$.

---

## 5. What Phase A gives us

The observer formalism is now rigorous at the level we need for the rest of the development. We have:

- A clean definition of observer, view map, indistinguishability class, refinement order.
- Four canonical observers with explicit view maps, and a verification that Definition 3.1–3.4 reproduces the paper's four sets exactly as indistinguishability classes at $p^\star$.
- The refinement chain $\omega_{h_t} \le \omega_\pi \le \omega_{\mathrm{behav}} \le \omega_{\mathrm{syn}}$, which subsumes the current nesting lemma.
- An adversarial reading of every indistinguishability class as "programs an adversary could substitute without the observer detecting the swap" (Remark 1.2).

What Phase A does not yet give us:

- Strict refinement at each link of the chain (Phase B: strict-separation theorems recast).
- A theorem saying that any history-based estimator's observer is bounded above by $\omega_{\mathrm{behav}}$ (Phase B: observable-quotient upgraded).
- The identity $\omega_{\mathrm{behav}} = \bigvee_\pi \omega_\pi$, i.e., $[p^\star] = \bigcap_\pi R_\pi(p^\star)$ (Phase C: the Pearl bridge).
- Any recasting of the near-miss or the main convergence theorem (Phases D, E).

**Proposed paper-side action for Phase A (not yet executed).** When we are ready to integrate, Definitions 1.1, 2.1, 3.1–3.4, Lemma 2.2, Lemma 2.3, Proposition 4.1 go into a new Section 3.1 titled "Observers and the refinement order." The current Lemma 3.4 (Nesting) becomes a corollary of Proposition 4.1 (one line). Everything else in Section 3 stays where it is until Phases B–C deliver their content.

---

## Open questions for Brian

1. *View space of the history observer.* Definition 3.4 uses $\Omega_{h_t} = [0, 1]$ and $V_{h_t}(p) = \mu_p(o_{1:t} \mid a_{1:t})$: the view is the scalar joint likelihood. This matches the paper's $R_{h_t}$ exactly. An alternative would be $V^{\mathrm{prefix}}_{h_t}(p) := (\mu_p(o_i \mid h_{i-1}, a_i))_{i \le t}$ — the full sequence of one-step conditionals along the realized history. The prefix-conditional observer is strictly finer than the scalar-likelihood observer: distinct one-step conditionals can produce the same joint likelihood ($0.6 \cdot 0.4 = 0.8 \cdot 0.3$). Sticking with the scalar definition keeps Definition 3.4 in one-to-one correspondence with the paper's $R_{h_t}$. Flagging for your sign-off; if you want the prefix-conditional observer instead, the paper's $R_{h_t}$ would need to be redefined accordingly.

2. *Naming.* I am using $\omega_{\mathrm{behav}}$ for the behavioral observer. Alternatives: $\omega_{\mu}$, $\omega_{\mathrm{int}}$ (for interventional), $\omega_{\infty}$. My lean: $\omega_{\mathrm{behav}}$ until Phase C, at which point "behavioral" is revealed to be synonymous with "interventional" and we may want to rename. Or we commit to $\omega_{\mathrm{int}}$ from the start to signal the Pearl connection. Your call.

3. *Notation clash.* The paper uses $\omega$ for no prior purpose; $\pi$ is already a policy; $\Omega$ is unused. No clashes. But I'm using $\Phi_\pi$ and $\Psi_{\pi, h_t}$ for the factorization maps in Proposition 4.1; these names are purely local to the proof and do not need to survive into the paper. Flagging only so you know.
