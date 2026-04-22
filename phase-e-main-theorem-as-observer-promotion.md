# Phase E: Main Theorem as Observer-Promotion Success

**Goal of Phase E.** Recast Theorem~\ref{thm:semantic-convergence} as the positive partner to Phase D's observer-promotion failure: the class-against-complement primitive makes the learner's realized action profile promotion-supporting, and promotion support is exactly what drives the posterior on $[p^\star]$ to 1. The main theorem does not change; Phase E names what its proof does in observer language, identifies the minimal property of the action rule on which the proof depends, and contrasts promotion-failure (Phase D) with promotion-success in a single concrete witness pair.

**Dependencies.** Phase A (observers, refinement preorder), Phase B (strict refinement; ceiling theorem), Phase C (supremum identity: $\omega_{\mathrm{behav}} = \bigvee_\pi \omega_\pi$), Phase D (observer-promotion failure). Phase E is the first phase in which the observer framework is used as an organizing frame for an existing positive result rather than as scaffolding around a negative one.

**Scope discipline.** Phase E adds one definition, one proposition, one remark upgraded to a corollary (the Phase D contrast), and two formal remarks (the Pearl/Blackwell positioning and the main-theorem-generalizes note). No new theorem. The main theorem retains its climax position; Phase E sharpens what it says without replacing it.

---

## 1. The observer reading of the main theorem

The main theorem (Theorem~\ref{thm:semantic-convergence}) gives $q_t^\star([p^\star] \mid H_t) \to 1$ almost surely. This is a posterior-concentration statement. Phase E's observation is that the same statement, under the observer framework, says something stronger and more structural: the learner's realized trajectory, under the semantic action rule, asymptotically resolves every $\omega_{\mathrm{behav}}$-class of positive prior mass. Equivalently, every program $p' \in \Pcal$ with $w(p') > 0$ and $p' \notin [p^\star]$ satisfies $q_t^\star(p' \mid H_t) \to 0$.

In the language of Phases A–C, this is observer-promotion success: the learner starts at $\omega_{\pi}$-level for whatever realized policy $\pi$ it produces, and ends (in posterior terms) at $\omega_{\mathrm{behav}}$-level. Phase D showed that the AFE principle's realized policy is stuck at a strict refinement below $\omega_{\mathrm{behav}}$ (Theorem D.2.1); Phase E shows the class-against-complement primitive lifts the learner to $\omega_{\mathrm{behav}}$ in posterior resolution.

---

## 2. Promotion-supporting action rules

To make this structural, we name the property of the semantic rule that drives the proof.

**Definition 2.1 (Promotion-supporting action rule).** An (history-dependent, possibly randomized) action rule is *promotion-supporting* if there exists $\delta > 0$ such that for every history $h_t$ and every class $c \in \Ccal$ with $0 < q_t^\star(c \mid h_t) < 1$,
$$\Prob\bigl(A_{t+1} = a_t^c(h_t) \mid H_t = h_t\bigr) \ge \delta \bar w(c),$$
where $a_t^c(h_t)$ is the $B_t(c, \cdot; h_t)$-separating selector of Definition~\ref{def:semantic-rule}.

In observer-formalism terms, Definition 2.1 says: at every history with non-degenerate posterior, the action rule places positive probability on the class-$c$-separating probe for every class $c$ in positive-posterior support. This is the minimum structure an action rule needs to exploit the $\omega_{\pi} < \omega_{\mathrm{behav}}$ gap: it must, at every decision point, be willing to play the action that separates $c$ from its complement, for every class that still has uncertain posterior mass.

**Proposition 2.2 (The semantic rule is promotion-supporting).** The semantic action rule of Definition~\ref{def:semantic-rule} is promotion-supporting with $\delta = \epsilon$.

**Proof.** Fix $h_t$ and $c \in \Ccal$ with $0 < q_t^\star(c \mid h_t) < 1$. By Definition~\ref{def:semantic-rule}, the rule samples $C_t \sim \nu_t(\cdot \mid h_t)$ and plays $a_{t+1} = a_t^{C_t}(h_t)$. Conditioning on $C_t = c$:
$$\Prob(A_{t+1} = a_t^c(h_t) \mid H_t = h_t) \ge \Prob(C_t = c \mid H_t = h_t) = \nu_t(c \mid h_t) = (1-\epsilon) q_t^\star(c \mid h_t) + \epsilon \bar w(c) \ge \epsilon \bar w(c).$$
Setting $\delta := \epsilon$ gives the claim. $\square$

*Remark 2.3 (Lemma~\ref{lem:true-class-support} as a special case).* Proposition 2.2 specializes at $c = c^\star$ to Lemma~\ref{lem:true-class-support} of the paper. Phase E observes that the true-class-support lemma is an instance of a more general promotion-support property, which is what the proof of Theorem~\ref{thm:semantic-convergence} actually requires.

---

## 3. The main theorem as promotion success

**Theorem 3.1 (Restatement of Theorem~\ref{thm:semantic-convergence} in promotion language).** Under (C1) universal prior, (C2) Bayes/Gibbs posterior, (C3) semantic separation condition (Definition~\ref{def:sep-condition}), and (C4') a promotion-supporting action rule, for every $p^\star \in \Pcal$,
$$q_t^\star([p^\star] \mid H_t) \longrightarrow 1 \quad \text{almost surely under the law generated by } (p^\star, \text{the action rule}).$$
Moreover, for every $p' \in \Pcal$ with $w(p') > 0$ and $p' \notin [p^\star]$,
$$q_t^\star(p' \mid H_t) \longrightarrow 0 \quad \text{almost surely.}$$

*The main theorem's hypothesis (C4) implies (C4') via Proposition 2.2, so Theorem 3.1 is logically equivalent to Theorem~\ref{thm:semantic-convergence} plus the trivial corollary that concentration on $[p^\star]$ implies posterior zero on every program outside it.*

**Proof sketch.** The proof is the proof of Theorem~\ref{thm:semantic-convergence} with Lemma~\ref{lem:true-class-support} replaced by Definition 2.1's bound. Let $\mathcal{F}_t := \sigma(H_t)$ and $T_{t+1} := \{A_{t+1} = a_t^{c^\star}(H_t)\} \cap E_t$ where $E_t := \{q_t^\star(c^\star \mid H_t) < 1\}$. Promotion support gives $\Prob(T_{t+1} \mid \mathcal{F}_t) \ge \delta \bar w(c^\star) \one_{E_t}$. By conditional Borel–Cantelli (Lemma~\ref{lem:conditional-bc}), $T_{t+1}$ occurs infinitely often on $\{E_t \text{ i.o.}\}$. Whenever $T_{t+1}$ holds, $B_t(c^\star, A_{t+1}; H_t) \ge \hat\eta$ by the semantic separation condition applied to the $c^\star$-separating selector. Cumulative separation diverges, and Lemma~\ref{lem:contraction} gives $q_t^\star(c^\star \mid H_t) \to 1$. The second conclusion follows from $\{p'\} \subseteq \Pcal \setminus [p^\star]$ and the class-level concentration. $\square$

*Remark 3.2 (The main theorem generalizes).* Theorem 3.1's proof uses the semantic action rule only through its promotion-support property. Any action rule satisfying (C4') obeys the same conclusion. This is a minor strengthening of Theorem~\ref{thm:semantic-convergence}, and locates the class-against-complement primitive as one instance of a broader class of observer-promoting action rules. The paper body can either state Theorem~\ref{thm:semantic-convergence} as originally written and add a remark after the proof — "the proof uses only promotion support" — or state (C4') and get the semantic rule as an instance. My lean: the former, to avoid upstaging. See §6.

---

## 4. The promotion contrast (Phase D vs. Phase E)

**Corollary 4.1 (Observer-promotion contrast on the Phase D witness).** Consider the near-miss construction of Theorem~\ref{thm:afe-near-miss} modified by extending the prior $w$ to assign positive mass $w(p') \in (0, 1)$ to the Phase D witness $p'$ (with corresponding renormalization of the other masses). Then:

- *(Failure.)* Under the AFE principle (Definition~\ref{def:afe-principle}), the realized policy through horizon $T$ is $\pi^\sharp$ (plays $a^{\mathrm{ref}}$), and the posterior ratio $q_t^\star(p' \mid H_t) / q_t^\star(p^\star \mid H_t) = w(p') / \alpha_0$ is constant on every sample path for $t \le T$. No evidence separates $p'$ from $[p^\star]$.
- *(Success.)* Under any promotion-supporting action rule satisfying (C1)–(C3), Theorem 3.1 gives $q_t^\star(p' \mid H_t) \to 0$ almost surely.

**Proof.** Failure: under $\pi^\sharp$, $p'$ and $p^\star$ induce identical $\mu(\cdot \mid h, a^{\mathrm{ref}})$ at every reachable history, so their likelihood ratio along realized histories is 1, and their posterior ratio is constant. Success: Theorem 3.1. $\square$

*Remark 4.2 (What the contrast says).* Corollary 4.1 is a structural statement about action rules. The $p'$ of Phase D is in $R_{\pi^\sharp}(p^\star) \setminus [p^\star]$: the policy-observer gap $R_{\pi^\sharp}(p^\star) \supsetneq [p^\star]$ contains programs with positive prior mass. Under an action rule that never plays $a^{\mathrm{sep}}$, the gap is not probed, and the posterior respects the gap by keeping these programs in play. Under a promotion-supporting rule, $a^{\mathrm{sep}}$ is played with positive probability on every history, the gap is probed infinitely often, and the posterior resolves the gap. The set inclusion $[p^\star] \subsetneq R_\pi(p^\star)$ of the knowability hierarchy is exactly the structure the AFE rule respects and the class-against-complement rule closes.

---

## 5. Positioning against connected theories

The observer-promotion frame lets Phase E locate the main theorem alongside three traditions the paper already cites.

**Remark 5.1 (Pearl's interventional identification).** The supremum identity $\omega_{\mathrm{behav}} = \bigvee_\pi \omega_\pi$ (Phase C) is the algorithmic analogue of Pearl's observational-interventional gap. Phase D's observer-promotion failure is that gap unclosed by the AFE rule; Phase E's observer-promotion success is that gap closed by the class-against-complement rule. Pearl's do-calculus identifies conditions under which interventional distributions are determined by observational ones, using graphical structure. In our setting, the interventional distributions are determined by active play under a class-targeted action rule, using posterior structure. The paper's Theorem~\ref{thm:semantic-convergence} is therefore the algorithmic analogue of Pearl's active-identification theorems for interventional equivalence classes.

**Remark 5.2 (Chernoff's optimal sequential tests).** The class-against-complement criterion — at each step, select the action maximizing the Hellinger/KL separation of the target class from the aggregate posterior complement — is the algorithmic-prior analogue of \citet{Chernoff1959}'s asymptotic-optimal sequential testing rule: select the design that maximizes the separation of the current most-likely hypothesis from the closest alternative. Chernoff's rule is formulated for finite parametric families; the class-against-complement rule extends it to countable hypothesis classes with a universal prior. In the observer-promotion language, Chernoff's rule is finitary observer promotion and the semantic rule is its algorithmic extension.

**Remark 5.3 (Blackwell's comparison of experiments).** \citet{Blackwell1953} orders experiments by a sufficiency-type relation that is the statistical ancestor of Phase A's refinement preorder. The ceiling theorem (Phase B, Theorem 4.3) says $\omega_{\mathrm{behav}}$ is the Blackwell-maximal experiment among induced observers; Phase E's observer-promotion success says the class-against-complement rule is Blackwell-rate-attaining among promotion-supporting rules. The connection is suggestive rather than sharp; one sentence in the discussion section handles it.

---

## 6. What this looks like in the paper

Phase E's integration is lighter than Phases A–D and sits entirely in Sections~\ref{sec:semantic-action} and \ref{sec:main}:

1. **Definition 2.1** (promotion-supporting action rule) goes into Section~\ref{sec:semantic-action} immediately after Definition~\ref{def:semantic-rule}. Two sentences.
2. **Proposition 2.2** (semantic rule is promotion-supporting) is a one-sentence proposition with a two-sentence proof, replacing the current Lemma~\ref{lem:true-class-support} in Section~\ref{sec:semantic-action}. The replacement strengthens the lemma from class $c^\star$ to all $c$, at no proof cost.
3. **Theorem~\ref{thm:semantic-convergence}** stays as written (same hypotheses, same proof, same climax prominence). Phase E does not restate it.
4. **Remark 3.2** ("the proof uses only promotion support") becomes a one-sentence remark after the main theorem's proof.
5. **Corollary 4.1** (observer-promotion contrast) goes into Section~\ref{sec:main} after the main theorem's corollaries. About half a page of proof sketch; tied explicitly to Phase D's witness.
6. **Remark 4.2** (what the contrast says) replaces or extends the current Corollary~\ref{cor:support-necessary} positioning. Remark 4.2 names the set-inclusion $[p^\star] \subsetneq R_\pi(p^\star)$ as the structural gap and calls the observer-promotion contrast a statement about action rules closing that gap.
7. **Remarks 5.1–5.3** become sentences in the discussion section (Section~\ref{sec:discussion}), not new remarks in Sections~\ref{sec:semantic-action}–\ref{sec:main}. One sentence each for Pearl, Chernoff, Blackwell.

Total new main-text material: about ⅓ page in Sections~\ref{sec:semantic-action}–\ref{sec:main}, plus three sentences in the discussion.

---

## 7. What Phase E gives us

- **The main theorem has a name in observer language:** it is the observer-promotion success theorem, the positive partner to Phase D's observer-promotion failure theorem.
- **The semantic action rule has a structural characterization:** promotion-supporting. This names what the rule does in observer terms — probes every class at every uncertain history — without changing what it is.
- **The AFE/semantic contrast is a theorem, not just a juxtaposition:** Corollary 4.1 states the contrast as a single concrete witness-pair statement. The set-inclusion $[p^\star] \subsetneq R_\pi(p^\star)$ is the structural object both rules are reacting to; one respects it, the other closes it.
- **The paper's three traditions are visibly connected:** Pearl's do-calculus (algorithmic active identification), Chernoff's sequential tests (optimal class-vs-complement probing), Blackwell's comparison (refinement as statistical-sufficiency ancestor). The discussion section gets one sentence for each.
- **Main theorem is unchanged:** its statement, hypotheses, and proof are untouched. Phase E is additive.

---

## 8. Open questions

1. *Promotion-supporting as (C4')*. Should the paper state (C4') as an alternative to (C4) in the main theorem, so the semantic rule is one instance of a broader class of promotion-supporting rules? Pro: the observer-promotion frame becomes load-bearing in the theorem statement. Con: the main theorem's current statement is tight and names the semantic rule directly; adding a layer of abstraction could weaken its climax feel. My lean: state the main theorem as currently written with (C4), and add Remark 3.2 noting the proof generalizes to any promotion-supporting rule. Keeps the climax; adds the observer framing in a remark.

2. *Proposition 2.2 replacing Lemma~\ref{lem:true-class-support}*. Proposition 2.2 subsumes Lemma~\ref{lem:true-class-support} (restricted to $c = c^\star$). Do we promote the lemma to a proposition with the broader statement, or add Proposition 2.2 alongside and keep the lemma? My lean: replace the lemma with Proposition 2.2. The broader statement is a free strengthening (same proof), and the single-$c^\star$ version becomes a special case in the theorem's proof.

3. *Corollary 4.1's prior modification*. Corollary 4.1 modifies the near-miss prior to include $p'$ with positive mass, so the AFE-vs-semantic contrast lands on a single concrete witness. This modification is prior-side, not environment-side — the environment is the same near-miss instance. Do we need to check that the semantic separation condition still holds for the modified prior? The condition is about classes, and the modification adds a class $[p']$ that is separable from $c^\star$ with infinite $B$ (via $a^{\mathrm{sep}}$ giving disjoint point masses). So the condition holds trivially for the added class and is unaffected for existing classes. My lean: include a one-line parenthetical verifying this in the corollary's proof. No separate lemma needed.

4. *Depth of the Pearl/Chernoff/Blackwell remarks*. Remarks 5.1–5.3 are one-sentence positioning statements for the discussion section. Chernoff's sequential-test rule is the closest technical analogue of the class-against-complement rule and deserves more than one sentence if anyone cares. My lean: one sentence each for Pearl and Blackwell (they belong in the broader discussion), two or three sentences for Chernoff (the technical analogue earns it). The paper already cites \citet{Chernoff1959} and \citet{BoxHill1967} in the sequential-rates question at the end of the discussion; strengthening the Chernoff connection in Phase E's integration is natural.

5. *Naming "observer promotion"*. The term was introduced in Phase D; Phase E uses it throughout. Per your direction #4 (yes, promote and tie to set inclusions and connected theories), this is now a committed vocabulary choice. Two follow-on choices: (a) do we use "promotion" as a verb in the paper ("the action rule promotes the observer") or only as a noun ("observer promotion")? My lean: noun form only in the formal statements; verb form once or twice in prose bridges. (b) Is "observer promotion" the right term, or should it be "observer advancement" or "observer strengthening"? My lean: promotion is the crispest — it evokes a learner climbing a hierarchy rather than an observer upgrading equipment, and the hierarchy-climbing metaphor fits the paper's four-set structure. Final call yours.

6. *Future formalization of beliefs and actions.* You mentioned you'd be open to a future phase formalizing beliefs and actions more rigorously, in the same observer spirit. Phase E's promotion-support notion is compatible with that: a belief-action formalism would naturally include an "action observer" (what the action rule, as a map from posterior to action, can distinguish) and a "belief observer" (what the posterior, as a map from history to distribution over classes, can distinguish). Promotion support would be the structural property linking them. Out of scope for Phase E but worth flagging as a coherent extension.
