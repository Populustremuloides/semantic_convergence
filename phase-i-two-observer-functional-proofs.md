# Phase I: Rigorous Proofs for Two-Observer Functional Implications

**Goal of Phase I.** Before writing the Section 8 subsection that boxes the two-observer functional $\mathcal J_t$, prove each of the implications claimed for it. Many of the claims I made in conversation were structural or interpretive; this note separates what admits a proof from what is an interpretive extension, and provides the proofs for the former.

**Dependencies.** Phase A (observers, refinement preorder); Phase B (strict refinement, ceiling); Phase C (supremum identity $\omega_{\mathrm{behav}}=\bigvee_\pi \omega_\pi$); Phase D (observer-promotion failure = near-miss); Phase E (main theorem as observer-promotion success); Phases G, H (philosophical framing; observer-formalism audit).

**Scope discipline.** Phase I does not add theorems to the paper. It is due-diligence on the $\mathcal J_t$ writeup: which of the implications are formally downstream of existing results, which need new proofs, which are interpretive corollaries, and which are analogies better stated as remarks than as theorems.

---

## 0. Setup

**Two-observer functional.** For $\omega_A \in \{\omega_{\mathrm{syn}}, \omega_{\pi}, \omega_{\mathrm{behav}}\}$ and positive scalars $\beta, \gamma$, define the action-bonus functional
$$\mathcal A_t^{\omega_A}[\pi; h_t, q] := \mathbb{E}_{C \sim \nu_t^\pi}\bigl[B_t^{\omega_A}(C, A_\pi; h_t)\bigr],$$
where $\nu_t^\pi(\cdot \mid h_t)$ is the class-targeting distribution induced by $\pi$ on the $\omega_A$-quotient $\Pcal/\!\sim_{\omega_A}$, and $B_t^{\omega_A}(c, a; h_t)$ is the Bhattacharyya separation (Definition~\ref{def:semantic-separation}) computed with classes at observer $\omega_A$. Let
$$\mathcal J_t^{\omega_A}[q, \pi; h_t] := \underbrace{\mathbb{E}_q[L_t(p;h_t)] + \KL(q\|w)}_{\Fcal_t[q;h_t]} \; - \; \beta \cdot \mathcal A_t^{\omega_A}[\pi; h_t, q] \; + \; \gamma \cdot \KL\!\bigl(\nu_t^\pi \,\|\, \bar w^{\omega_A}\bigr),$$
where $\bar w^{\omega_A}(c) := \sum_{p \in c} w(p)$ is the push-forward of the universal prior to the $\omega_A$-quotient.

**Action-MI variant** (for capturing AFE). A parallel functional uses expected information gain in the action term:
$$\mathcal J_t^{\omega_A, \mathrm{MI}}[q, \pi; h_t] := \Fcal_t[q;h_t] \; - \; \beta \cdot I_q(C^{\omega_A}; O \mid A_\pi, h_t),$$
where $C^{\omega_A}$ is the random variable coding the $\omega_A$-class of the true program under $q$. At $\omega_A = \omega_{\mathrm{syn}}$, $C^{\omega_A} = P$ and this recovers the standard EFE mutual-information term.

**Claim list.** From the previous conversation, eight implications were advanced. I restate each, then adjudicate and prove as needed.

1. AFE near-miss is a boundary regime of $\mathcal J_t$.
2. Two-observer structure is structurally forced ("design theorem").
3. Observer dial generalizes to goal-dependent convergence.
4a. Blackwell passive limit is $\mathcal J_t$ at fixed $\pi$ with $\beta=\gamma=0$.
4b. Pearl intervention analogy.
4c. Chernoff correspondence of $B_t$.
5. Exponential rate of convergence.
6. Noise-channel / dark-room immunity.
7. Philosophical theses (Quine/van Fraassen/Putnam) are load-bearing on the functional.
8. Relationship to active inference / FEP is surgical.

---

## 1. Claim 1: AFE near-miss is a boundary regime of $\mathcal J_t$

**Status.** Structural identity. Provable as stated if we allow the action term to vary between Bhattacharyya and mutual-information forms.

**Proposition I.1 (Boundary identity).** The algorithmic free energy principle's (belief, action) pair coincides with the minimizer of $\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$ at $\beta = 1$. The observer-promotion failure (Theorem~\ref{thm:observer-promotion-failure}) shows this minimizer induces $\omega_{\pi^\sharp} < \omega_{\mathrm{behav}}$ strictly. Conversely, the minimizer of $\mathcal J_t^{\omega_{\mathrm{behav}}}$ at $\beta, \gamma > 0$ is (Bayes posterior, promotion-supporting rule), which under (C1)–(C3) yields $q_t^\star([p^\star] \mid H_t) \to 1$ a.s. (Theorem~\ref{thm:semantic-convergence}).

**Proof.**
(a) *AFE as $\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$ minimizer.* By Lemma~\ref{lem:variational}, the unique $q$-minimizer of $\Fcal_t$ is the Bayes/Gibbs posterior $q_t^\star$. The AFE principle's action rule (expected free energy minimization) selects $a_{t+1} = \arg\min_a G(a; h_t, q_t^\star)$ where $G = -I_{q_t^\star}(P; O \mid a, h_t) + \text{pragmatic}$. With the pragmatic term suppressed (matching the near-miss construction's epistemic-only regime), this is exactly $\arg\min_a (-I_{q_t^\star})$, the MI term of $\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$. Hence the AFE (belief, action) pair is the minimizer of $\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$.

(b) *Near-miss.* Theorem~\ref{thm:afe-near-miss} exhibits a hypothesis class, prior, and pair $p^\star, p'$ with $p' \notin [p^\star]$ and $w(p'), w(p^\star) > 0$, such that the AFE-minimizing policy $\pi^\sharp$ satisfies $q_t^\star(p' \mid H_t) \not\to 0$. By Theorem~\ref{thm:observer-promotion-failure}, the realized observer $\omega_{\pi^\sharp}$ satisfies $\omega_{\pi^\sharp} < \omega_{\mathrm{behav}}$ strictly.

(c) *$\mathcal J_t^{\omega_{\mathrm{behav}}}$ minimizer is promotion-supporting.* Minimizing $\mathcal J_t^{\omega_{\mathrm{behav}}}$ over $\pi$ with $q$ fixed at $q_t^\star$ is, after standard variational calculus (see, e.g., the Gibbs-variational identity), the class-Gibbs distribution
$$\nu_t^{\pi^\star}(c \mid h_t) \propto \bar w(c)\exp\!\Bigl(\tfrac{\beta}{\gamma}\,B_t^{\omega_{\mathrm{behav}}}(c, a_t^c(h_t); h_t)\Bigr),$$
paired with the $c$-separating selectors $a_t^c$ (per Definition~\ref{def:semantic-rule}). Since $B_t \ge 0$, the Gibbs form satisfies
$$\nu_t^{\pi^\star}(c \mid h_t) \;\ge\; \bar w(c) \cdot \frac{1}{Z_t} \;\ge\; \bar w(c) \cdot \frac{1}{\exp(\tfrac{\beta}{\gamma} B_{\max})}$$
for every class $c$, where $B_{\max} := \sup_{c, a, h_t} B_t(c, a; h_t)$. If $B_{\max} < \infty$, this is a constant lower bound $\delta \bar w(c)$ with $\delta := e^{-\beta B_{\max}/\gamma} > 0$; the minimizer is therefore promotion-supporting in the sense of Definition~\ref{def:promotion-supporting}. By Remark~\ref{rem:promotion-support}, the conclusion of Theorem~\ref{thm:semantic-convergence} applies. $\square$

**Caveat.** The assumption $B_{\max} < \infty$ is natural but not automatic. If some action drives $\mathcal Q_t^{-c}$'s support to disjoint from $\mu_c$'s, $B_t = +\infty$ and the Gibbs normalizer may be degenerate. Two workable fixes: (i) truncate $B_t$ at a cap $B^\ast$ (the convergence argument uses only $B_t \ge \hat\eta$, not unboundedness); (ii) use the semantic rule's explicit mixture form $\nu_t^\pi = (1-\epsilon)q_t^\star + \epsilon \bar w$ instead of the Gibbs form, which has $\delta = \epsilon$ directly. Option (ii) decouples the exploration floor from the $\beta/\gamma$ ratio and is closer to the paper's existing Definition~\ref{def:semantic-rule}; option (i) is truer to the variational spirit of $\mathcal J_t$. Either grounds Proposition I.1.

**Remark.** Strictly, the claim "AFE = $\mathcal J_t$ at $\beta = 0$" (as stated in conversation) is incorrect. $\beta = 0$ annihilates the action term and leaves the action rule undefined; AFE minimizes a specific action objective. The correct statement is that AFE is $\mathcal J_t$ at *action observer $\omega_{\mathrm{syn}}$* with the MI action term. The "boundary" structure is observer-indexed, not $\beta$-indexed.

---

## 2. Claim 2: Meeting-point theorem for the two-observer structure

**Status.** Three propositions. The two-observer structure is forced by two admissibility ranges that converge on $\omega_{\mathrm{behav}}$:

- *Belief admissibility*: $\omega \ge \omega_{\mathrm{behav}}$. Below this, likelihoods are not $\omega$-constant and Bayes at $\omega$ is ill-typed (Proposition I.9'). Above this, all choices produce identical $\omega_{\mathrm{behav}}$-class posteriors (Proposition I.9).
- *Action admissibility*: $\omega \le \omega_{\mathrm{behav}}$. Above this, the action bonus is capped (Proposition I.2). Below this, the choice parameterizes the target observer (Proposition I.3).
- *Meeting point*: $\omega_{\mathrm{behav}}$ is the unique observer admissible as both belief and action observer (Proposition I.10).

### 2.1 Belief observer: Bayes–quotient commutation

**Proposition I.9 (Belief-observer invariance above $\omega_{\mathrm{behav}}$).** Let $w$ be any prior on $\Pcal$, and let $\omega$ be any observer with $\omega \ge \omega_{\mathrm{behav}}$. Within each $\omega$-class, likelihoods are well-defined as $\mu_c := \mu_p$ for any $p \in c$ (constancy follows from $c$ being a subset of a behavioral class when $\omega \ge \omega_{\mathrm{behav}}$). Let $q_t^\omega(\cdot \mid h_t)$ denote Bayes at observer $\omega$ with pushforward prior $\bar w^\omega$. Then for every behavioral class $c_{\mathrm{behav}} \in \Pcal/\!\sim_{\mathrm{behav}}$:
$$\sum_{c \in \Ccal^\omega,\; c \subseteq c_{\mathrm{behav}}} q_t^\omega(c \mid h_t) \;=\; q_t^{\omega_{\mathrm{behav}}}(c_{\mathrm{behav}} \mid h_t).$$

**Proof.** Direct computation:
$$\sum_{c \subseteq c_{\mathrm{behav}}} q_t^\omega(c \mid h_t) = \sum_{c \subseteq c_{\mathrm{behav}}} \frac{\bar w^\omega(c) \mu_c(h_t)}{\bar\xi(h_t)} = \frac{\mu_{c_{\mathrm{behav}}}(h_t)}{\bar\xi(h_t)} \sum_{c \subseteq c_{\mathrm{behav}}} \bar w^\omega(c) = \frac{\bar w^{\omega_{\mathrm{behav}}}(c_{\mathrm{behav}}) \mu_{c_{\mathrm{behav}}}(h_t)}{\bar\xi(h_t)} = q_t^{\omega_{\mathrm{behav}}}(c_{\mathrm{behav}} \mid h_t),$$
where $\mu_c = \mu_{c_{\mathrm{behav}}}$ on each $c \subseteq c_{\mathrm{behav}}$ because $\omega \ge \omega_{\mathrm{behav}}$. $\square$

**Proposition I.9' (Belief-observer ill-typing below $\omega_{\mathrm{behav}}$).** If $\omega < \omega_{\mathrm{behav}}$, there exists an $\omega$-class $c \in \Ccal^\omega$ containing two programs $p_1, p_2 \in c$ with $\mu_{p_1} \ne \mu_{p_2}$. Consequently the $\omega$-class likelihood $\mu_c$ is not well-defined as a single distribution, and $\omega$-level Bayes on classes is ill-typed without auxiliary within-class sub-posterior structure.

**Proof.** $\omega < \omega_{\mathrm{behav}}$ means $\omega_{\mathrm{behav}} \not\le \omega$ (in the refinement preorder), i.e., the identity $p \sim_\omega p'$ fails to imply $p \sim_{\mathrm{behav}} p'$. Pick witnesses $p_1, p_2$ with $p_1 \sim_\omega p_2$ but $p_1 \not\sim_{\mathrm{behav}} p_2$; they belong to the same $\omega$-class but have $\mu_{p_1} \ne \mu_{p_2}$ at some $(h_t, a)$. The mapping $c \mapsto \mu_c$ is then multi-valued on $c = [p_1]_\omega$. $\square$

**Interpretation.** Proposition I.9 says: above the behavioral observer, any belief observer you pick produces identical class-posterior dynamics on $\omega_{\mathrm{behav}}$-classes. Syntactic-level Bayes and behavioral-level Bayes give the same answer where it counts. Proposition I.9' says: below the behavioral observer, class-level Bayes is not a single procedure — you cannot state Bayes for a coarser observer without auxiliary structure. The behavioral observer is therefore the lower boundary of belief admissibility.

### 2.2 Action observer: cap theorem

**Proposition I.2 (Action-observer cap).** Let $\omega$ be an observer with $\omega > \omega_{\mathrm{behav}}$, i.e., there exist $\omega$-classes $c_1, c_2 \in \Pcal/\!\sim_\omega$ with $c_1 \ne c_2$ but $c_1 \cup c_2 \subseteq c^{\mathrm{behav}}$ for some behavioral class $c^{\mathrm{behav}}$. Fix any history $h_t$ with $q_t^\star(c_1 \mid h_t), q_t^\star(c_2 \mid h_t) > 0$. Then for every action $a$,
$$B_t^\omega(c_1, a; h_t) \;\le\; \tfrac{1}{2}\log\!\Bigl(\frac{1 - q_t^\star(c_1 \mid h_t)}{q_t^\star(c_2 \mid h_t)}\Bigr),$$
a bound independent of $a$. Consequently, the semantic separation condition (Definition~\ref{def:sep-condition}) cannot hold at $c_1$ uniformly in $t$ if the posterior ratio $q_t^\star(c_2 \mid h_t) / (1 - q_t^\star(c_1 \mid h_t))$ stays bounded below.

**Proof.** Let $\alpha := q_t^\star(c_2 \mid h_t) / (1 - q_t^\star(c_1 \mid h_t)) \in (0, 1]$. Since $c_1, c_2$ lie in the same behavioral class, $\mu_{c_1}(o \mid h_t, a) = \mu_{c_2}(o \mid h_t, a) =: \mu(o)$ for every $o, a$. The complement likelihood is
$$\Qcal_t^{-c_1}(o \mid h_t, a) = \alpha \cdot \mu(o) + (1 - \alpha) \cdot \Rcal(o),$$
where $\Rcal$ is the posterior mixture over $\omega$-classes other than $c_1, c_2$. Then
$$\sum_o \sqrt{\mu_{c_1}(o) \cdot \Qcal_t^{-c_1}(o)} = \sum_o \sqrt{\mu(o)(\alpha \mu(o) + (1-\alpha) \Rcal(o))} \ge \sum_o \sqrt{\alpha} \mu(o) = \sqrt{\alpha},$$
using $\sqrt{\alpha\mu + (1-\alpha)\Rcal} \ge \sqrt{\alpha \mu}$ pointwise. Taking $-\log$ of both sides:
$$B_t^\omega(c_1, a; h_t) \le -\log\sqrt{\alpha} = \tfrac{1}{2}\log(1/\alpha) = \tfrac{1}{2}\log\!\Bigl(\frac{1 - q_t^\star(c_1)}{q_t^\star(c_2)}\Bigr). \qquad \square$$

**Corollary I.2' (Posterior cannot concentrate past $\omega_{\mathrm{behav}}$).** At observer $\omega > \omega_{\mathrm{behav}}$, behaviorally-equivalent classes $c_1, c_2$ have posterior ratio frozen at the prior ratio:
$$\frac{q_t^\star(c_1 \mid h_t)}{q_t^\star(c_2 \mid h_t)} = \frac{w(c_1)}{w(c_2)}$$
for every $t, h_t$. Consequently $q_t^\star(c_1 \mid H_t) \not\to 1$ a.s. for any single $\omega$-class $c_1$ that has behavioral twins with positive prior mass.

**Proof.** The Bayes update for classes $c_1, c_2$ under history $h_t = (a_1, o_1, \dots, a_t, o_t)$ is
$$q_t^\star(c_i \mid h_t) = \frac{w(c_i) \mu_{c_i}(o_1 \dots o_t \mid a_1 \dots a_t)}{\bar\xi(o_{1:t} \mid a_{1:t})}.$$
Since $\mu_{c_1} = \mu_{c_2}$ pointwise, the ratio $q_t^\star(c_1)/q_t^\star(c_2) = w(c_1)/w(c_2)$ at every history. Hence each $q_t^\star(c_i)$ is bounded above by $1 - w(c_j)/(w(c_i)+w(c_j)) < 1$ for the twin $c_j$. $\square$

### 2.3 The meeting-point theorem

**Proposition I.10 (Meeting point).** In the $\mathcal J_t$ framework, belief-observer admissibility and action-observer usefulness are bounded on opposite sides of the refinement lattice, and meet at a single observer:

- *Belief lower bound*: $\omega_{\mathrm{behav}} \le \omega$ is required for $\omega$-level Bayes to be well-defined as a single procedure on $\omega$-classes (Proposition I.9').
- *Belief upper freedom*: for any $\omega \ge \omega_{\mathrm{behav}}$, $\omega$-level Bayes produces identical $\omega_{\mathrm{behav}}$-class posterior trajectories to $\omega_{\mathrm{behav}}$-level Bayes (Proposition I.9).
- *Action upper bound*: $\omega \le \omega_{\mathrm{behav}}$ is required for the semantic separation condition to hold with unbounded $\sup_a B_t$ (Proposition I.2).
- *Action lower freedom*: for any $\omega \le \omega_{\mathrm{behav}}$, $\omega$-level action minimization of $\mathcal J_t$ yields convergence of $q_t^\star([p^\star]_\omega \mid H_t) \to 1$ a.s. (Proposition I.3).

$\omega_{\mathrm{behav}}$ is the unique observer at which belief admissibility meets action usefulness: the minimum admissible belief observer equals the maximum useful action observer.

**Corollary I.10' (Canonical two-observer choice).** If the framework requires a single-observer specification, $\omega_{\mathrm{behav}}$ is forced. If the framework allows separate belief and action observers, the canonical choice is $(\omega_{\mathrm{syn}}, \omega_{\mathrm{behav}})$: $\omega_{\mathrm{syn}}$ is the top of the refinement lattice (quotient-free; no exogenous equivalence stipulated) and $\omega_{\mathrm{behav}}$ is the meeting point. The functional $\mathcal J_t^{\omega_{\mathrm{syn}}, \omega_{\mathrm{behav}}}$ is therefore the canonical representative of the family $\{\mathcal J_t^{\omega_B, \omega_{\mathrm{behav}}} : \omega_B \ge \omega_{\mathrm{behav}}\}$, all of which produce identical $\omega_{\mathrm{behav}}$-class dynamics by Proposition I.9.

**Interpretation.** The two-observer design is not a stylistic choice between two reasonable options. It is structurally forced: the refinement lattice has a single fixed point where the belief-side admissibility range (closed above $\omega_{\mathrm{behav}}$) meets the action-side usefulness range (closed below $\omega_{\mathrm{behav}}$). The functional's two-observer indexing records where each half of the learning problem lives. $\omega_{\mathrm{behav}}$ is a lattice-theoretic invariant of the paper's framework, not a design choice.

**Consequence for the Section 8 writeup.** Proposition I.10 is the punchline: "belief at $\omega_{\mathrm{syn}}$, action at $\omega_{\mathrm{behav}}$" becomes "two admissibility ranges meet at $\omega_{\mathrm{behav}}$; $\omega_{\mathrm{syn}}$ is the canonical quotient-free lift of the belief observer." This is substantially stronger than "we chose two observers and here's why."

---

## 3. Claim 3: Goal-dialed convergence

**Status.** Theorem. Direct generalization of the main theorem.

**Proposition I.3 (Goal-dialed convergence).** Fix any observer $\omega$ with $\omega \le \omega_{\mathrm{behav}}$. Let $\Ccal^\omega := \Pcal/\!\sim_\omega$ denote the $\omega$-quotient, $\bar w^\omega(c) := \sum_{p \in c} w(p)$ the induced prior, and $B_t^\omega$ the Bhattacharyya separation at $\omega$-classes. Suppose:

- **(C1$^\omega$)** the universal prior $w$, so $\bar w^\omega(c) > 0$ for every $c \in \Ccal^\omega$;
- **(C2)** belief is the Bayes/Gibbs posterior;
- **(C3$^\omega$)** for every class $c \in \Ccal^\omega$ with $0 < q_t^\star(c \mid h_t) < 1$, $\sup_a B_t^\omega(c, a; h_t) \ge \eta^\omega(c) > 0$;
- **(C4$^\omega$)** action follows the $\omega$-semantic rule (Definition~\ref{def:semantic-rule} applied with $\Ccal^\omega$ in place of $\Ccal$).

Then $q_t^\star([p^\star]_\omega \mid H_t) \to 1$ almost surely, where $[p^\star]_\omega := \{p \in \Pcal : p \sim_\omega p^\star\}$.

**Proof.** The proof of Theorem~\ref{thm:semantic-convergence} uses the following ingredients:

1. Positivity of $\bar w^{\omega_{\mathrm{behav}}}(c)$ for each class — from (C1). Here: $\bar w^\omega(c) > 0$ by the same argument ($w$ universal, every $\omega$-class contains a computable program).
2. The semantic separation condition — (C3). Here: (C3$^\omega$).
3. The conditional Borel–Cantelli Lemma (Lemma~\ref{lem:conditional-bc}). Does not depend on $\omega$.
4. The contraction Lemma (Lemma~\ref{lem:contraction}): $\sum_t B_t(c^\star, A_{t+1}; H_t) = \infty$ a.s. implies $q_t^\star(c^\star) \to 1$. Does not depend on $\omega$; it uses only that $B_t$ is a Rényi-1/2 divergence and that Rényi bounds $\log$-posterior drift.
5. The semantic rule targets $c^\star$ with probability $\ge \epsilon \bar w^{\omega_{\mathrm{behav}}}(c^\star) > 0$ (Proposition~\ref{prop:semantic-is-promotion-supporting}). Here: same with $\bar w^\omega(c^\star)$.

Each ingredient transfers directly from $\omega_{\mathrm{behav}}$ to any $\omega \le \omega_{\mathrm{behav}}$. The only place the choice $\omega = \omega_{\mathrm{behav}}$ is load-bearing is the cap theorem (Proposition I.2), which excludes $\omega > \omega_{\mathrm{behav}}$; for $\omega \le \omega_{\mathrm{behav}}$ no cap applies. $\square$

**Consequence.** $\mathcal J_t^\omega$ for $\omega \le \omega_{\mathrm{behav}}$ is a family indexed by the target observer: minimizing it drives $q_t^\star([p^\star]_\omega \mid H_t) \to 1$ a.s. $\omega_{\mathrm{behav}}$ is the finest allowable choice (the knowability ceiling); coarser choices correspond to targeting coarser properties of programs.

---

## 4a. Claim 4a: Blackwell passive limit is the fixed-$\pi$ restriction

**Status.** Already a theorem in the paper (Theorem~\ref{thm:policy-gap}). Claim is reinterpretive, not new.

**Observation.** At a fixed policy $\pi$, the action rule is exogenous. In $\mathcal J_t^\omega$ the $\pi$-minimization is constrained to $\{\pi\}$, and the $\beta, \gamma$ terms contribute constants independent of the free variables. Minimization reduces to $q$-minimization of $\Fcal_t$, yielding $q_t^\star$.

**Proposition I.4 (Passive limit identification ceiling).** Under a fixed policy $\pi$, Theorem~\ref{thm:policy-gap} gives: there exist $p' \in R_\pi(p^\star) \setminus [p^\star]$ with $w(p') > 0$ such that $q_t^\star(p' \mid H_t) \not\to 0$. Consequently, $q_t^\star([p^\star] \mid H_t) \not\to 1$ in general.

**Correspondence to Blackwell.** Blackwell's sufficiency (1951) and comparison-of-experiments framework shows that a fixed experiment's information is bounded by the ordering-ceiling of its sufficient statistic. In the interactive setting, the sufficient statistic of a fixed $\pi$ is its realized observer $\omega_\pi$; no Bayesian procedure can identify past $\omega_\pi$ under fixed $\pi$. Theorem~\ref{thm:policy-gap} is the interactive analogue. The $\mathcal J_t$ framework exposes the gap: the belief term alone caps at $\omega_\pi$; the $\beta, \gamma$ terms (with $\omega_A = \omega_{\mathrm{behav}}$) lift the ceiling to $\omega_{\mathrm{behav}}$.

**Caveat.** The correspondence is a reading of Blackwell in the interactive setting, not a theorem derived from Blackwell's original framework. Blackwell's framework presumes fixed experiment; extending to adaptive experiments via $\omega_\pi \nearrow \omega_{\mathrm{behav}}$ is this paper's contribution. I would write this as a *remark*, not a *corollary*.

---

## 4b. Claim 4b: Pearl intervention analogy

**Status.** Interpretive analogy. Not a theorem. I was too loose in conversation.

**What's true.** $\mathcal J_t$ with $\beta = \gamma = 0$ (passive) cannot identify past $\omega_\pi$; with $\beta, \gamma > 0$ (active) it can. This parallels Pearl's distinction between $P(Y \mid X)$ (passive) and $P(Y \mid \mathrm{do}(X))$ (active intervention): intervention identifies causal structure that conditioning cannot.

**What's not established.** Pearl's framework is for causal graphs with confounders; the hypothesis space is $\{G : G \text{ is a DAG compatible with observed data}\}$, and identification is up to Markov equivalence classes. The paper's framework is for computable programs with action-observation dynamics; identification is up to $\omega_{\mathrm{behav}}$. A formal mapping between these frameworks would require embedding Pearl's DAG models in $\Pcal$ and showing $\sim_{\mathrm{behav}}$ coincides with Markov equivalence under a specific action set. This is not established in the paper.

**Treatment.** State as remark. Do not claim "Pearl's theorem is a corollary of $\mathcal J_t$." Claim only: the functional exposes structure parallel to Pearl's passive/active distinction, at a different level of abstraction.

---

## 4c. Claim 4c: Chernoff correspondence

**Status.** Theorem (correspondence between $B_t$ and Rényi-1/2 / Chernoff). Provable directly.

**Definitions.** Rényi divergence of order $\alpha \in (0, 1) \cup (1, \infty)$:
$$D_\alpha(P \| Q) := \tfrac{1}{\alpha - 1} \log \sum_o P(o)^\alpha Q(o)^{1-\alpha}.$$
Chernoff information:
$$C(P, Q) := -\log\min_{\lambda \in [0,1]} \sum_o P(o)^\lambda Q(o)^{1-\lambda}.$$

**Proposition I.6 (Chernoff-Bhattacharyya identity).** For any distributions $P, Q$ on $\Ocal$:

1. $B_t(P, Q) := -\log\sum_o \sqrt{P(o) Q(o)} = \tfrac{1}{2} D_{1/2}(P \| Q)$.
2. $C(P, Q) \ge B_t(P, Q)$, with equality iff the Chernoff-optimal $\lambda^\star = 1/2$.
3. Rényi monotonicity: $D_\alpha$ is non-decreasing in $\alpha$, so $\KL(P \| Q) = D_1(P \| Q) \ge D_{1/2}(P \| Q) = 2 B_t(P, Q)$.

**Proof.**
1. $D_{1/2}(P\|Q) = \tfrac{1}{-1/2}\log\sum P^{1/2} Q^{1/2} = -2 \log \sum\sqrt{PQ} = 2 B_t$.
2. $\sum P^\lambda Q^{1-\lambda}$ is convex in $\lambda$ (standard — derivative in $\lambda$ of $\log$-moment). Minimum is attained; $\lambda = 1/2$ is a feasible point, so $\min_\lambda \le $ value at $1/2$, hence $C \ge $ value at $1/2$ equals $B_t$.
3. Standard (e.g., van Erven & Harremoës, "Rényi Divergence and Kullback–Leibler Divergence," 2014). $\square$

**Consequence for $\mathcal J_t$.** The action term $-\beta \mathcal A_t^{\omega_{\mathrm{behav}}}$ is $-\tfrac{\beta}{2} \mathbb{E}_{C\sim\nu}[D_{1/2}(\mu_C \| \Qcal^{-C})]$ — a regularized Rényi-1/2-divergence maximization over class-targeted experimental design. By Proposition I.6.2, this lower-bounds the Chernoff-optimal experimental design (achieving it when the Chernoff-optimal test is the symmetric likelihood-ratio test, i.e., when $\lambda^\star = 1/2$). By Proposition I.6.3, it also lower-bounds the KL-optimal information-gain design.

**What this gets us.** Proposition I.6 is a formal bridge between the paper's $B_t$ and the classical Chernoff-exponent / Rényi-divergence family. The action bonus is not ad hoc — it is a Rényi divergence, identifiable with a specific error-exponent interpretation. This is a corollary-strength statement that the paper could include.

---

## 5. Claim 5: Exponential rate of convergence

**Status.** Theorem. Follows from the Lyapunov/supermartingale structure of the proof. Clean statement requires a moment-boundedness hypothesis.

**Setup.** Let $Z_t := \log \tfrac{q_t^\star(c^\star \mid H_t)}{1 - q_t^\star(c^\star \mid H_t)}$ (log-odds of the true class). Let $\Delta_t := Z_{t+1} - Z_t$.

**Lemma I.7a (One-step drift).** Under $p^\star$ and the semantic action rule,
$$\mathbb{E}[\Delta_t \mid \mathcal F_t] \ge 2 \cdot \mathbb{E}[B_t(c^\star, A_{t+1}; H_t) \mid \mathcal F_t] \ge 2 \hat\eta \epsilon \bar w(c^\star).$$

**Proof.** Direct calculation of the Bayes update for class probability yields
$$\mathbb{E}[\Delta_t \mid \mathcal F_t, A_{t+1} = a] = \KL\!\bigl(\mu_{c^\star}(\cdot \mid H_t, a) \,\|\, \Qcal_t^{-c^\star}(\cdot \mid H_t, a)\bigr).$$
By Proposition I.6.3, $\KL \ge 2 B_t$. Taking outer expectation over $A_{t+1} \mid \mathcal F_t$:
$$\mathbb{E}[\Delta_t \mid \mathcal F_t] \ge 2 \mathbb{E}[B_t(c^\star, A_{t+1}; H_t) \mid \mathcal F_t].$$
Under the semantic rule with exploration floor $\epsilon$:
$$\Prob(C_t = c^\star \mid \mathcal F_t) \ge \epsilon \bar w(c^\star),$$
and on $\{C_t = c^\star\}$ the selector satisfies $B_t(c^\star, a_t^{c^\star}; H_t) \ge \hat\eta$ by (C3). Hence
$$\mathbb{E}[B_t(c^\star, A_{t+1}; H_t) \mid \mathcal F_t] \ge \hat\eta \epsilon \bar w(c^\star). \qquad \square$$

**Proposition I.7 (Exponential rate, expectation form).** Under (C1)–(C4),
$$\mathbb{E}[Z_t] \ge Z_0 + \mu_0 \cdot t, \qquad \mu_0 := 2 \hat\eta \epsilon \bar w(c^\star) > 0.$$
In particular, $\mathbb{E}[Z_t] \to \infty$ linearly.

**Proof.** Telescope Lemma I.7a. $\square$

**From expectation to concentration.** The standard route is a martingale concentration inequality. The difficulty: $\Delta_t$ can be unbounded (likelihood ratios may be extreme). Under the additional assumption
$$\exists\, M < \infty: \; \mathbb{E}[\Delta_t^2 \mid \mathcal F_t] \le M \quad \text{a.s.} \qquad \text{(moment condition)}$$
one obtains, via Azuma–Hoeffding applied to the compensated process $Z_t - \mathbb{E}[Z_t]$ (which has bounded conditional variance and mean zero), a sub-Gaussian concentration
$$\Prob\!\bigl(Z_t \le \mu_0 t / 2\bigr) \le 2 \exp\!\bigl(-c t\bigr), \qquad c = c(\mu_0, M) > 0,$$
whence $\Prob(q_t^\star(c^\star \mid H_t) < 1 - \delta) \le 2 \exp(-c' t)$ for $c' = c'(\delta, \mu_0, M)$.

**Proposition I.7' (Exponential rate, concentration form).** Under (C1)–(C4) and the moment condition, there exist constants $c, c' > 0$ depending on $(\epsilon, \bar w(c^\star), \hat\eta, M)$ such that
$$\Prob\!\bigl(q_t^\star([p^\star] \mid H_t) < 1 - e^{-c t}\bigr) \le 2 e^{-c' t}.$$

**Caveats.**
1. The moment condition $\mathbb{E}[\Delta_t^2 \mid \mathcal F_t] \le M$ is *not* automatic. It fails, for instance, if $\mu_c(o \mid a, h_t)$ is ever arbitrarily small at an observation $o$ with positive complement likelihood. A sufficient condition: the likelihood ratios $\mu_{c^\star}(o)/\Qcal_t^{-c^\star}(o)$ are bounded above and below by $m \le \cdot \le 1/m$ uniformly in $(o, a, h_t)$ for some $m > 0$.
2. Without the moment condition, the proof still gives $Z_t \to \infty$ a.s. (by the Borel–Cantelli argument in Theorem~\ref{thm:semantic-convergence}) but not a rate.
3. The expectation-form rate (Proposition I.7) is unconditional; the concentration-form rate (Proposition I.7') is conditional on the moment bound.

**Recommendation for paper.** Include Proposition I.7 (expectation-form, unconditional, clean). State Proposition I.7' as a corollary under a named regularity hypothesis, without proof, to keep the main paper from ballooning. Open question 2 in the paper already gestures at this — Proposition I.7 partially answers it.

---

## 6. Claim 6: Noise-channel immunity

**Status.** Theorem. Direct calculation.

**Proposition I.8 (Noise-channel immunity).** Suppose $a^{\mathrm{noise}} \in \Acal$ is a *noise channel*: $\mu_c(o \mid h_t, a^{\mathrm{noise}}) = \mu^{\mathrm{noise}}(o \mid h_t)$ for every $c \in \Ccal$, $o \in \Ocal$, and $h_t$. Then:

1. $B_t^{\omega_{\mathrm{behav}}}(c, a^{\mathrm{noise}}; h_t) = 0$ for every $c$ with $0 < q_t^\star(c \mid h_t) < 1$.
2. The action term $-\beta \mathcal A_t^{\omega_{\mathrm{behav}}}[\pi; h_t, q]$ provides no bonus to policies that play $a^{\mathrm{noise}}$: any policy $\pi^{\mathrm{sep}}$ with $\mathcal A_t^{\omega_{\mathrm{behav}}}[\pi^{\mathrm{sep}}] > 0$ strictly dominates $\pi^{\mathrm{noise}}$ on $\mathcal J_t$ at fixed $\nu_t^\pi$.
3. The information-gain term of $\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$ at $a^{\mathrm{noise}}$: $I_{q_t^\star}(P; O \mid a^{\mathrm{noise}}, h_t) = H(O \mid a^{\mathrm{noise}}, h_t) - H(O \mid P, a^{\mathrm{noise}}, h_t) = 0$ as well (since $O \perp P$ at $a^{\mathrm{noise}}$). So even the syntactic MI bonus correctly sees no information gain at a pure noise channel.
4. *Where noise channels can trap*: they can trap MI-based agents only when combined with dependent components (e.g., "pseudo-noise" channels where $O$ has high marginal entropy despite low conditional MI). $\mathcal J_t^{\omega_{\mathrm{behav}}}$ with the Bhattacharyya action term is immune to this failure mode because the entropy of $O$ does not appear in $B_t$ — only the separation between class-conditional distributions does.

**Proof.**
1. At $a^{\mathrm{noise}}$: $\mu_c(o) = \Qcal_t^{-c}(o) = \mu^{\mathrm{noise}}(o)$ since all classes induce the same marginal. Hence $\sum_o \sqrt{\mu_c \Qcal_t^{-c}} = \sum_o \mu^{\mathrm{noise}}(o) = 1$, and $B_t = -\log 1 = 0$.
2. Direct consequence of (1) combined with the linearity of the $\beta$-term in $B_t$.
3. $I(P; O \mid a, h_t) = H(O \mid a, h_t) - H(O \mid P, a, h_t)$. At $a^{\mathrm{noise}}$, $P(O \mid a, h_t) = \mu^{\mathrm{noise}}$ regardless of $P$, so $H(O \mid P, a, h_t) = H(\mu^{\mathrm{noise}}) = H(O \mid a, h_t)$. Subtraction gives zero.
4. Follows from the fact that $B_t$ depends only on class-conditional distributions, not on their entropy. Pseudo-noise channels (where the marginal is high-entropy but classes agree) satisfy the noise-channel condition and are immune. $\square$

**Comparison to naive curiosity.** In RL, intrinsic-motivation bonuses of the form $-\log p(o \mid h_t)$ (prediction error) or $H(O \mid h_t)$ (state entropy) can be driven to large values by noise channels — the "noisy TV problem." $\mathcal J_t$'s action bonus $-B_t$ cannot, because it measures *class separation*, not *observation entropy*. This is a concrete structural advantage of the $\omega_{\mathrm{behav}}$-indexed formulation over generic entropy-bonus formulations.

**What this does *not* say.** It does not say $\mathcal J_t$ is immune to all pathologies of active inference. Specifically, if classes are mislabeled (i.e., $\Ccal$ does not correspond to the true behavioral equivalence), the separation bonus can drive the agent toward distinguishing artifacts of the wrong quotient. This is not a noise-channel failure but a model-misspecification failure, which the paper's framework presumes away by working at $\omega_{\mathrm{behav}}$ directly.

---

## 7. Claim 7: Philosophical theses (Quine / van Fraassen / Putnam)

**Status.** Interpretive. Not theorems. The paper's Discussion paragraph (Phase G addition) already frames each thesis in terms of the paper's formal results. $\mathcal J_t$ makes the framing sharper but does not add logical content.

**Summary of framing.**

- **Quine (underdetermination of theory by data).** At $\beta = 0$ in $\mathcal J_t$ (passive Bayes), the posterior is stuck at $\omega_\pi$-refinement by Theorem~\ref{thm:policy-gap}. This is Quine's underdetermination in the interactive setting.
- **van Fraassen (constructive empiricism).** The knowability ceiling at $\omega_{\mathrm{behav}}$ (Theorem~\ref{thm:factor-through-quotient}) is the formal analogue of van Fraassen's "empirical adequacy." Science aims at behavioral classes, not at syntactic truth.
- **Putnam (model-theoretic argument).** At $\beta = 0$, the use–reference map is underdetermined (Quine's gap + Putnam's model-theoretic twins). At $\beta, \gamma > 0$ in $\mathcal J_t^{\omega_{\mathrm{behav}}}$, use fixes reference up to $\omega_{\mathrm{behav}}$ by Theorem~\ref{thm:semantic-convergence}.

**What $\mathcal J_t$ adds.** A single functional whose corners / $\beta$-limits correspond to each thesis. Without $\mathcal J_t$, the Discussion paragraph has to gesture at three separate theorems and interpret them philosophically. With $\mathcal J_t$, the philosophical paragraph is commentary on a single object.

**Treatment.** No new proofs needed. Phase G paragraph stands; $\mathcal J_t$ is the referent that makes it land.

---

## 8. Claim 8: Active inference / FEP relationship is surgical

**Status.** Interpretive + structural. No new proofs beyond Claim 1.

**What's provable.** The AFE principle is $\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$ minimizer (Proposition I.1). The main convergence principle is $\mathcal J_t^{\omega_{\mathrm{behav}}}$ minimizer. These differ by (i) action observer ($\omega_{\mathrm{syn}} \to \omega_{\mathrm{behav}}$), and (ii) action functional (expected MI $\to$ expected $B_t$, plus exploration regularizer). Both differences are minimal: (i) swaps the index, (ii) swaps one Rényi divergence (KL, in the MI term) for another (Rényi-1/2, in the $B_t$ term), both supported by the existing class structure.

**What's interpretive.** Whether this constitutes a "surgical fix" to Friston-style FEP is a framing question about reception. The mathematical content: two-term replacement. Whether readers of the active-inference literature accept this as an extension rather than a rejection is rhetorical.

**Treatment.** State as a remark in the paper, not as a theorem. The remark can say: "The two-observer functional $\mathcal J_t^{\omega_{\mathrm{behav}}}$ differs from the AFE functional $\mathcal J_t^{\omega_{\mathrm{syn}}, \mathrm{MI}}$ in two minimal respects: the action-observer index is lifted from $\omega_{\mathrm{syn}}$ to $\omega_{\mathrm{behav}}$, and the action bonus is replaced by its Rényi-1/2 counterpart with an exploration regularizer." This is a precise, defensible summary.

---

## 9. Ledger of what the paper can claim

| Claim | Status | Paper treatment |
|---|---|---|
| 1. AFE near-miss as boundary | Provable (Prop I.1) | State as proposition after $\mathcal J_t$ |
| 2a. Belief-observer invariance (above $\omega_{\mathrm{behav}}$) | Theorem (Prop I.9) | State as short proposition |
| 2a'. Belief-observer ill-typing (below $\omega_{\mathrm{behav}}$) | Theorem (Prop I.9') | State as short proposition |
| 2b. Action observer cap | Theorem (Prop I.2) | State as lemma with proof |
| 2c. Meeting-point theorem | Theorem (Prop I.10) | State as the synthesis / punchline |
| 3. Goal-dialed convergence | Theorem (Prop I.3) | State as corollary |
| 4a. Blackwell passive limit | Re-reading | Remark referencing Theorem~\ref{thm:policy-gap} |
| 4b. Pearl intervention | Analogy | Remark, soften language |
| 4c. Chernoff correspondence | Theorem (Prop I.6) | State as identity/remark |
| 5. Exponential rate (expectation) | Theorem (Prop I.7) | State as proposition (answers open question 2) |
| 5'. Exponential rate (concentration) | Conditional theorem (Prop I.7') | State as corollary under moment hypothesis |
| 6. Noise-channel immunity | Theorem (Prop I.8) | State as proposition, 3-4 lines |
| 7. Quine/vF/Putnam | Interpretive | Phase G paragraph stands; sharpened by I.10' |
| 8. AFE/FEP surgical fix | Interpretive | One-sentence remark |

---

## 10. Writeup plan for Section 8 subsection

Based on the ledger, the Section 8 subsection "A variational principle for observer promotion" should include:

1. **Definition of $\mathcal J_t^{\omega_A}$** — the boxed line, observer-indexed.
2. **Proposition (AFE/Main correspondence)** = Proposition I.1 — the boundary identity, explaining both near-miss and main theorem as different-observer restrictions of the same functional.
3. **Proposition (Belief-observer invariance)** = Proposition I.9 + I.9' — belief above $\omega_{\mathrm{behav}}$ is invariant; below is ill-typed. Three-line proofs.
4. **Lemma (Action-observer cap)** = Proposition I.2 — why $\omega_A > \omega_{\mathrm{behav}}$ fails. Six-line proof.
5. **Theorem (Meeting point)** = Proposition I.10 — the synthesis. No new proof (combines I.9, I.9', I.2, I.3).
6. **Corollary (Goal-dialed convergence)** = Proposition I.3 — the observer dial.
7. **Proposition (Chernoff correspondence)** = Proposition I.6 — positions $B_t$ in the Rényi family.
8. **Proposition (Exponential rate)** = Proposition I.7 — the linear-in-$t$ expectation bound.
9. **Proposition (Noise-channel immunity)** = Proposition I.8 — the structural exploration-safety result.
10. **Remark (Two-observer design)** — the "lattice meeting point" framing; cf. Proposition I.10.
11. **Remark (Philosophical reading)** — tie to Quine/vF/Putnam (Phase G); AFE as boundary; Proposition I.9 formalizes the Putnam response.

Estimated length: 1.5–2 pages. The meeting-point theorem (I.10) replaces the original "two-observer design" remark with a theorem statement, substantially strengthening the subsection's rigor at modest length cost.

---

## 11. Flags for next step

- **Claim 1: expected-MI framing confirmed.** AFE side is expressed as expected MI; main-theorem side as expected Bhattacharyya. Remark notes both are Rényi divergences, preserving the two-observer reading.
- **Claim 5': expectation-form only.** Include Proposition I.7 (unconditional); omit I.7' (concentration-form) from the paper to keep Section 8 contained. Open question 2 in the paper can reference Proposition I.7 for partial progress.
- **Claim 2a: now a theorem.** Revised from earlier draft — belief-observer invariance (Proposition I.9) is a three-line theorem, not a design argument. The "$\omega_{\mathrm{syn}}$ as canonical lift" reading is now a corollary of the meeting-point theorem (Proposition I.10), not a standalone heuristic.
- **Claim 4b (Pearl) stays as analogy.** No formal embedding attempted. Remark only.

No further proofs needed before writing. The proofs above are audit-ready, and Propositions I.9, I.9', I.10 close the structural-force argument that was previously hand-waved.
