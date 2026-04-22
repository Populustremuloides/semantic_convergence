# V2 Foundational Audit for Lean Readiness

Source frozen: `algorithmic_free_energy_principle_award.v2.tex`

This audit treats "zsf set theory" as ZF-style grounding for later Lean work. The TeX source is taken as fixed. The purpose of this document is to identify the exact foundational objects, quotient boundaries, measurability requirements, existence lemmas, and hidden hypotheses that a Lean formalization will force into the open.

## Base Ontology

The paper can be normalized against the following base layer.

1. `A` and `O` are countable sets with discrete measurable structures unless the paper later chooses richer ones.
2. `Hist_t := (A x O)^t`, `Hist := coproduct_t Hist_t`, and `h_t` is a finite tagged interaction history. `h_0 = epsilon`.
3. A policy is a family of kernels `pi_t : Hist_t -> Prob(A)`.
4. `P` is a countable prefix-free subset of finite bitstrings determined by a universal prefix machine `U`.
5. Each program `p : P` induces a kernel `mu_p : Hist x A -> Prob(O)` plus the derived finite-prefix chronological law `mu_p(o_{1:t} || a_{1:t})`.
6. `Prob_{p,pi}` is the induced measure on the canonical path space `(A x O)^N`, obtained from the kernels `pi_t` and `mu_p` by an Ionescu-Tulcea / Kolmogorov-extension construction.
7. Every quotient in the paper is a quotient of the countable set `P` by an explicitly proved equivalence relation.
8. Every pushed-forward prior or posterior is a countable sum over equivalence classes of `P`.

This base layer is enough for the whole paper, but several sections currently rely on it implicitly rather than naming it.

## Highest-Priority Findings

1. The reachable-pair convention for kernel equality at `v2.tex:108` is load-bearing and needs a dedicated equivalence-relation lemma. As written, many later quotient objects rely on it without an explicit proof that it is reflexive, symmetric, and transitive.
2. `omega_behav` and `omega_pi` are presented as measurable observers, but the measurable spaces of interactive laws and path measures are not named. Lean will require concrete codomains.
3. The class likelihood `mu_c` is only valid above `omega_behav`; this is correctly stated in prose at `v2.tex:352`, but every later use needs an explicit representative-independence lemma.
4. `nu_t^pi` is introduced in `v2.tex:373` before the paper gives a fully explicit construction. This is fine mathematically, but it is a forward declaration that will need an existence/typing bridge in Lean.
5. The self-referential promotion result `prop:observer-promotion-sr` uses a stronger recurrence claim than the stated assumptions `(C1)-(C3)` obviously provide. This is the sharpest theorem-level foundational gap in the file.
6. The computability remark `rem:self-ref-computability` makes semicomputability claims that are stronger than what the preceding formal statements establish. These should be treated as a separate proof task, not as fallout from the main theorem.
7. The expected-free-energy layer depends on a common finite feasible observation set, action-independent uniform preferences, and measurable tie-breaking. Those assumptions are present, but they are narrower than the general notation around `G_t` initially suggests.
8. Several local proof objects reuse notation already used globally: `F_t` is both free energy and a filtration, `S_t` is both semantic gain and cumulative separation, and `Z` appears as a normalizing constant, an indicator, and a log-odds process. This is not a correctness defect, but it matters for Lean naming and for the object ledger.

## Layer Audit

### 1. Formal Setup (`v2.tex:86-127`)

Definitions and objects introduced in this section:

- `A`, `O`, `h_t`, `h_0`, `pi_t`, `pi`, `(A_t,O_t)`, `H_t`, `P`, `mu_p`, the reachable-pair equality convention, the prior `w`, the posterior `q_t`, set-mass notation `q_t(R | h_t)`, and the predictive posterior `q_{t+1}`.

Foundational obligations:

- The history type should be made explicit as finite sequences of alternating action and observation coordinates, or as `(A x O)^t`.
- Policies and environment laws should be typed as kernels, not merely as display equations.
- The induced path law `Prob_{p,pi}` is used later but not constructed here; Lean will need an explicit theorem that the stepwise kernels determine a unique path measure.
- Posterior denominators are already guarded by positivity assumptions; these should become named lemmas because they recur in class-level posterior updates.

Audit judgment:

- The setup is close to Lean-ready once the path-law construction and the reachable-pair equality lemma are made explicit.

### 2. Hierarchy and Observer Layer (`v2.tex:136-334`)

Definitions:

- `def:history-compat` (`136-143`): depends on `P`, `mu_p`, and a fixed history. No quotient issue.
- `def:policy-pred` (`146-153`): depends on `Prob_{p,pi}` on the full history path space. Needs the induced-path-law construction.
- `def:int-sem-class` (`156-163`): depends on the reachable-pair equality convention on interactive laws. Needs the equality relation on laws to be proved an equivalence.
- `def:observer` (`168-175`): depends on measurable spaces on codomains `Omega_omega` and measurable view maps `V_omega`. Lean will need explicit measurable spaces for source code, interactive laws, fixed-policy laws, and realized-history statistics.
- `def:history-recoverable` (`225-233`): depends on history spaces, measurable estimators, and convergence in probability in a metric space.

Results:

- `lem:nesting` (`180-195`): hidden hypothesis is positivity of the policy factor along the realized history so the division step is legal.
- `prop:refinement-chain` (`196-208`): needs measurable factor maps from source code to interactive laws, from interactive laws to fixed-policy path laws, and from path laws to the realized-history statistic.
- `lem:observable-quotient` (`210-223`): depends on the reachable-pair equality convention plus the history factorization identity for path probabilities.
- `thm:factor-through-quotient` (`235-242`): needs uniqueness of weak limits in metric spaces and a representative-independence argument to justify `bar_tau([p]) := tau(p)`.
- `lem:fit-gap` (`250-257`): uses existence of a modified computable program that copies `p*` on one finite prefix and then overrides a single conditional. This should become a reusable "finite override preserves computability" lemma.
- `thm:policy-gap` (`259-280`): same finite-override lemma, plus the fact that zero-support actions under the policy erase those conditionals from the induced path law.
- `lem:syntactic-gap` (`286-293`): foundationally trivial once semantic equivalence is an equivalence relation.
- `thm:strict-hierarchy` (`299-309`): fully reduced to earlier lemmas once the hierarchy objects are well-typed.

Main findings:

- The observer language is conceptually clean, but the measurable codomains of `omega_behav` and `omega_pi` should be fixed before Lean work starts.
- The quotient lift `tau = bar_tau o [.]` is correct, but it needs an explicit "constant on equivalence classes implies quotient lift exists and is unique" lemma.
- The finite-override constructions in `lem:fit-gap` and `thm:policy-gap` should be formalized once and then reused later in the near-miss section.

### 3. Two-Observer Functional Layer (`v2.tex:342-561`)

Definitions and local quotient data:

- `C^omega`, `bar w^omega`, `q_t^*(c | h_t)`, `mu_c`, `mu_c^{q_t^*}`, `Q_t^{-c,omega}`, and `nu_t^pi` are introduced at `344-373`.
- `def:bhat-omega` (`364-371`) defines `B_t^omega(c,a;h_t)` for `0 < q_t^*(c|h_t) < 1`.
- `def:two-observer-functional` (`380-397`) defines `J_t^{omega_B,omega_A}`.
- `def:meeting-point-shorthand` (`406-409`) defines the canonical specialization `J_t^{omega_behav}`.

Results:

- `prop:belief-invariance-above` (`418-435`): depends on representative-independence of `mu_c` for classes above `omega_behav`.
- `prop:belief-illtyped-below` (`438-448`): depends on the refinement order being defined via factor maps.
- `prop:action-cap` (`454-474`): needs class-level posteriors with positive mass and the well-typed complement law `Q_t^{-c,omega_A}`.
- `cor:twins-frozen-ratio` (`476-488`): depends on identical class likelihoods above a too-fine action observer.
- `thm:meeting-point` (`498-512`): structurally correct once the admissibility propositions are established.
- `cor:canonical-pair` (`514-520`): immediate from the meeting-point theorem.
- `prop:goal-dialed` (`531-545`): only a proof sketch is given. For Lean purposes this is a deferred theorem proof, not a finished derivation.

Main findings:

- `mu_c` is the central quotient boundary in the paper. Every later use of class likelihoods above `omega_behav` should depend on a single representative-independence lemma.
- `nu_t^pi` is forward-declared before construction. The paper is consistent about later instantiating it, but the audit should treat this as a separate existence/typing obligation.
- `def:two-observer-functional` says `F_t` is "referenced by the belief observer through its pushforward" while the displayed formula is still program-level in `q`. This is conceptually harmless, but it means the bridge between class-level Bayes and program-level Bayes should be stated explicitly, not left to prose.

### 4. Belief Layer (`v2.tex:563-724`)

Definitions:

- `def:universal-prior` (`571-583`): raw weights `tilde w`, normalizing constant `Z`, normalized prior `w`, and universal mixture `bar_xi`.
- `def:afe` (`625-632`): algorithmic free energy `F_t[q;h_t]`.

Results:

- `lem:prior-invariance` (`585-606`): depends on translator programs between universal machines and on the prefix-free normalization factors being nonzero.
- `lem:prior-necessity` (`608-623`): depends on dominance of a computable interactive law by the mixture and on the class pushforward of the prior.
- `lem:variational` (`634-657`): depends on positivity of `bar_xi(o_{1:t} || a_{1:t})`; uniqueness uses positivity of KL away from the minimizer.
- `lem:kl-necessity` (`665-684`): imports convex analysis on `ell^1(P)` and `ell^infty(P)`. This is formalizable, but it is substantially heavier than the rest of the paper and should be isolated in Lean.
- `lem:merging` (`692-717`): depends on mixture dominance and on the predictive law `Q_t^O`.

Main findings:

- This is the cleanest part of the paper. Once `P` is countable and the mixture is explicit, the belief-side objects are foundationally straightforward.
- `lem:kl-necessity` is the one place where the foundational burden is functional-analytic rather than probabilistic. It deserves its own formalization track.

### 5. Action and Convergence Layer (`v2.tex:725-1141`)

Definitions:

- `def:class-complement` (`731-740`): defines `Q_t^{-c}` for `0 < q_t^*(c|h_t) < 1`.
- `def:semantic-gain` (`747-758`): defines `S_t(c,a;h_t)`.
- `def:semantic-separation` (`783-794`): defines `B_t(c,a;h_t)`.
- `def:semantic-rule` (`846-859`): defines `bar w(c)`, exploration parameter `epsilon`, the selector `a_t^c(h_t)`, the class-targeting distribution `nu_t(c|h_t)`, the sampled class `C_t`, and the action rule.
- `def:promotion-supporting` (`863-870`): defines the lower-bound property with constant `delta`.
- `def:sep-condition` (`925-931`): defines the semantic separation hypothesis via `eta(c)`.

Results:

- `lem:odds-identity` (`760-781`): needs class-level Bayes updates to be well-defined.
- `lem:zero-criterion` (`801-815`): straightforward once KL and Hellinger affinity are defined on probability distributions.
- `prop:chernoff-correspondence` (`817-842`): depends on the Renyi divergence family and the one-step class/complement laws being honest probability measures.
- `prop:semantic-is-promotion-supporting` (`872-887`): depends on every semantic class having positive pushforward mass under the universal prior.
- `prop:noise-immunity` (`889-911`): the monotonicity claim is sound; the transfer of positivity in the final sentence is stronger than what the proof itself shows and should be isolated as its own condition on the channel.
- `lem:conditional-bc` (`933-940`): imported external lemma.
- `lem:contraction` (`942-973`): defines local proof objects `R_t^-`, `G_t`, cumulative `S_t`, and `M_t`; depends on the class-complement law and on nonnegative-martingale convergence.
- `thm:semantic-convergence` (`975-1005`): depends on the promotion-supporting lower bound and the separation condition. The theorem is structurally sound once the earlier objects are in place.
- `cor:finite-maximin` (`1017-1032`): introduces `U_t(a;H_t)` locally. Needs finiteness of `C` and the selector existence argument over a finite minimum.
- `cor:support-necessary` (`1034-1052`): depends on `thm:policy-gap` plus positive prior mass on both semantic classes.
- `lem:one-step-drift` (`1064-1101`): introduces `Z_t`, `Delta_t`, `hat_eta`, and a proof filtration `F_t`; uses the KL-vs-Bhattacharyya inequality.
- `prop:exp-rate` (`1103-1120`): depends on the drift lemma and Jensen.
- `cor:goal-dialed-payoff` (`1127-1139`): depends on the earlier proof sketch for `prop:goal-dialed`; this is another place where Lean will need the missing details supplied, not just cited.

Main findings:

- The action side is mathematically coherent, but it relies heavily on countability for selector existence and on quotient well-definedness for class laws.
- `prop:noise-immunity` should be split conceptually into two statements in Lean: monotonicity of separation under channels, and a separate criterion for preserving strictly positive separation.
- Local notation reuse is concentrated here: `S_t` and `F_t` are reused in ways that are harmless on paper but should be normalized before Lean declaration names are chosen.

### 6. Self-Referential and Boundary Layer (`v2.tex:1143-1549`)

Definitions:

- `def:finite-time-policy-observer` (`1153-1160`): defines `omega_pi^t` via the length-`t` marginal of `Prob_{p,pi}`.
- `def:self-ref-rule` (`1183-1186`): defines the self-referential policy `pi^sr`.
- `def:efe` (`1302-1316`): defines `Q_t^{PO}`, `Q_t^O`, `rho_t`, `c_t(a;h_t)`, and `G_t(a;h_t)`.
- `def:afe-principle` (`1350-1358`): packages the universal prior, Bayes/Gibbs posterior, and expected-free-energy action.

Results:

- `lem:monotone-refinement` (`1162-1176`): depends on Kolmogorov extension / equality of measures from agreement on all finite-dimensional marginals.
- `lem:exploration-reachability` (`1200-1211`): depends on the self-referential rule applying the same semantic-rule construction at each running partition.
- `prop:observer-promotion-sr` (`1213-1235`): this is the weakest proof in the file from a foundational standpoint. The proof appeals to infinitely many returns to a separating history and to a conditional Borel-Cantelli argument that is not implied by `(C1)-(C3)` alone. This theorem should be marked `needs hypothesis` unless a stronger reachability/recurrence lemma is added.
- `thm:self-ref-convergence` (`1242-1257`): explicitly a proof sketch. It depends on `prop:observer-promotion-sr`; until that proposition is repaired, this theorem remains conditional.
- `prop:boundary-identity` (`1280-1293`): clean once the expected-free-energy specialization is fixed.
- `lem:risk-ig` (`1318-1332`): depends on the mutual-information identity for the predictive law `Q_t^{PO}`.
- `cor:efe-specialization` (`1334-1341`): requires zero action cost, a common finite feasible observation set, and action-independent uniform preferences.
- `lem:info-decomp` (`1367-1383`): straightforward chain-rule decomposition, but note the local reuse of the notation `Z`.
- `thm:afe-near-miss` (`1393-1491`): depends on the finite-override computable-program lemma already needed earlier, plus countability/infinitude assumptions on `O` and the existence of finitely many chosen observations.
- `thm:observer-promotion-failure` (`1493-1512`): structurally clean. It depends on the reachable-pair equality convention and the fixed policy `pi^sharp`.
- `cor:observer-promotion-universal` (`1514-1521`): immediate once the witness pair `(p*,p')` is prior-independent.
- `cor:promotion-contrast` (`1538-1545`): clean once the main theorem and the near-miss are established.

Main findings:

- The finite-time observer `omega_pi^t` is well motivated and formalizable, but it needs an explicit measurable codomain of measures on `Hist_t`.
- The self-referential branch should be treated as a separate proof program. It is not just a routine corollary of the earlier convergence argument.
- The boundary example section is otherwise strong. It uses explicit finite constructions and is much closer to Lean-ready than the self-referential section.

## Definition and Result Checklist

The checklist below is the minimal dependency map another engineer could use when starting a Lean declaration order.

### Hierarchy

- `def:history-compat`: needs `P`, `mu_p`, finite histories.
- `def:policy-pred`: needs induced path law `Prob_{p,pi}`.
- `def:int-sem-class`: needs equality of interactive laws on reachable pairs.
- `def:observer`: needs measurable codomains and measurable view maps.
- `lem:nesting`: needs policy-factor positivity at the realized history.
- `prop:refinement-chain`: needs factor maps between observer codomains.
- `lem:observable-quotient`: needs history-factorization identity and reachable-pair equality.
- `def:history-recoverable`: needs measurable estimators on `Hist_t`.
- `thm:factor-through-quotient`: needs quotient-lift existence and uniqueness in metric codomains.
- `lem:fit-gap`: needs computable finite override.
- `thm:policy-gap`: needs computable finite override plus zero-support policy argument.
- `lem:syntactic-gap`: trivial once semantic equivalence is defined.
- `thm:strict-hierarchy`: packages the previous items.

### Functional layer

- `def:bhat-omega`: needs well-defined class predictive and complement laws.
- `def:two-observer-functional`: needs program-level free energy, action term, and class-targeting distribution.
- `def:meeting-point-shorthand`: alias only.
- `prop:belief-invariance-above`: needs `mu_c` representative-independence.
- `prop:belief-illtyped-below`: needs refinement order on observers.
- `prop:action-cap`: needs positive class masses and well-defined complement law.
- `cor:twins-frozen-ratio`: needs identical likelihoods for behavioral twins.
- `thm:meeting-point`: packages previous admissibility results.
- `cor:canonical-pair`: alias consequence.
- `prop:goal-dialed`: currently proof-sketched; will need a real transferred proof.

### Belief layer

- `def:universal-prior`: needs countable `P` and a nonzero normalizing constant.
- `lem:prior-invariance`: needs translator programs and machine universality.
- `lem:prior-necessity`: needs dominance and class pushforward.
- `def:afe`: needs finite expected loss and finite KL.
- `lem:variational`: needs positive evidence `bar_xi(...) > 0`.
- `lem:kl-necessity`: needs convex duality on `ell^1/ell^infty`.
- `lem:merging`: needs mixture dominance and predictive law `Q_t^O`.

### Action and convergence layer

- `def:class-complement`: needs `0 < q_t^*(c|h_t) < 1`.
- `def:semantic-gain`: needs `Q_t^{-c}` and `mu_c`.
- `lem:odds-identity`: needs class-level posterior update.
- `def:semantic-separation`: needs class/complement laws.
- `lem:zero-criterion`: needs KL/Hellinger zero criteria.
- `prop:chernoff-correspondence`: needs Renyi divergence library.
- `def:semantic-rule`: needs countable-action measurable selector existence.
- `def:promotion-supporting`: alias property.
- `prop:semantic-is-promotion-supporting`: needs positive class prior mass.
- `prop:noise-immunity`: needs channel composition and a separate positivity-preservation criterion if strict positivity is required.
- `def:sep-condition`: needs class-wise positive lower bounds.
- `lem:conditional-bc`: imported probability theorem.
- `lem:contraction`: needs supermartingale construction on posterior odds.
- `thm:semantic-convergence`: needs the four standing hypotheses plus the contraction lemma.
- `cor:finite-maximin`: needs finite class set and local maximin selector.
- `cor:support-necessary`: needs the policy-gap witness and positive prior mass.
- `lem:one-step-drift`: needs KL lower bound by `2B_t`.
- `prop:exp-rate`: needs telescoping expected drift.
- `cor:goal-dialed-payoff`: needs the earlier observer-indexed transfer proof.

### Self-referential and boundary layer

- `def:finite-time-policy-observer`: needs measurable space of laws on `Hist_t`.
- `lem:monotone-refinement`: needs marginalization plus equality from all finite marginals.
- `def:self-ref-rule`: needs inductive measurability/well-posedness.
- `lem:exploration-reachability`: needs positive class pushforward at every running partition.
- `prop:observer-promotion-sr`: needs an additional recurrence/reachability hypothesis or a repaired proof.
- `thm:self-ref-convergence`: depends on the repaired promotion theorem.
- `prop:boundary-identity`: needs `lem:variational` and `lem:risk-ig`.
- `def:efe`: needs predictive joint law and posterior update under action `a`.
- `lem:risk-ig`: needs MI identity.
- `cor:efe-specialization`: needs zero cost, common finite feasible set, uniform preferences.
- `def:afe-principle`: needs measurable tie-breaking in the action argmin.
- `lem:info-decomp`: needs class indicator as a measurable function of `P`.
- `thm:afe-near-miss`: needs finite explicit construction of programs and priors.
- `thm:observer-promotion-failure`: needs fixed-policy witness `p'`.
- `cor:observer-promotion-universal`: prior-independent witness.
- `cor:promotion-contrast`: packages near-miss and main-theorem conclusions.

## Declaration Order for Lean

The smallest sensible declaration order is:

1. Countable measurable types `A`, `O`.
2. Finite history types and the canonical path space.
3. Program space `P` and universal machine assumptions.
4. Environment kernels `mu_p`.
5. Policies `pi_t` and induced path law `Prob_{p,pi}`.
6. Reachable-pair equality and semantic equivalence.
7. Hierarchy sets and observer structure.
8. Quotients `C`, `C^omega`, and pushed-forward priors/posteriors.
9. Class predictive laws and Bhattacharyya separation.
10. Free-energy functional and Bayes/Gibbs minimizer.
11. Semantic action rule and promotion-supporting property.
12. Main convergence theorem.
13. Finite-time policy observers and self-referential branch.
14. Expected free energy and boundary example.

## Proof-Obligation Queue

Before Lean implementation, the following lemmas should be promoted from implicit paper reasoning to explicit foundational statements.

1. `reachable_kernel_eq_is_equivalence`
2. `path_law_exists_from_policy_and_environment`
3. `observer_view_map_measurable` for each canonical observer
4. `class_likelihood_well_defined_above_behavioral`
5. `class_predictive_and_complement_are_probability_measures`
6. `quotient_lift_exists_for_class-constant_maps`
7. `finite_override_of_computable_program_is_computable`
8. `semantic_selector_exists_and_is_measurable`
9. `finite_time_policy_observer_is_measurable`
10. `self_ref_recurrence_or_return_hypothesis` or a replacement proof of `prop:observer-promotion-sr`
11. `efe_specialization_requires_common_finite_feasible_set`
12. `strict_positive_separation_survives_non-collapsing_channels`

## Overall Assessment

The paper is already close to formalization-ready on the hierarchy, belief, main action, and near-miss sides. The quotient structure is the central technical spine, and once its representative-independence lemmas are named explicitly, most of the document becomes a clean countable-measure and kernel development. The one place that should be treated as an active proof gap rather than a packaging issue is the self-referential promotion theorem and the computability claims attached to it.
