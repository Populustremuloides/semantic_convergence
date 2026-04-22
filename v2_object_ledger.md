# V2 Object Ledger

Source frozen: `algorithmic_free_energy_principle_award.v2.tex`

Status tags used in this ledger:

- `grounded`
- `needs hypothesis`
- `needs quotient lemma`
- `needs measurability lemma`
- `needs existence lemma`
- `ambiguous`

No entry below is left as `ambiguous`; unresolved issues are classified more specifically.

## 1. `(\Acal, \Ocal)`

- Informal name: action and observation alphabets
- Kind: countable sets
- Ambient carrier/type: countable measurable types
- Definition site: `v2.tex:88`
- Upstream dependencies: none
- Set-theoretic realization: choose countable sets `A`, `O`
- Lean realization sketch: `A : Type u`, `O : Type v`, `[Countable A] [Countable O] [MeasurableSpace A] [MeasurableSpace O]`
- Well-definedness obligations: fix sigma-algebras; the discrete measurable structure is the natural default
- Downstream uses: all histories, kernels, policies, observers, path laws, posteriors
- Status: `grounded`

## 2. `(h_t, h_0, H_t)`

- Informal name: deterministic finite history and random history
- Kind: finite tuples / random variables
- Ambient carrier/type: `Hist_t := (A x O)^t`, `Hist := Sigma t, Hist_t`
- Definition site: `v2.tex:88-98`
- Upstream dependencies: `A`, `O`
- Set-theoretic realization: tagged finite sequences of alternating action and observation coordinates
- Lean realization sketch: `Hist : Nat -> Type`, plus `H_t : Omega -> Hist t`
- Well-definedness obligations: choose one canonical finite-history representation and keep it fixed
- Downstream uses: policy kernels, posterior updates, all observer and path-law constructions
- Status: `grounded`

## 3. `(pi_t, pi)`

- Informal name: policy kernels and full policy
- Kind: sequence of stochastic kernels
- Ambient carrier/type: `forall t, Hist t -> Prob(A)`
- Definition site: `v2.tex:94`
- Upstream dependencies: `A`, `Hist_t`
- Set-theoretic realization: measurable family of probability measures on actions indexed by histories
- Lean realization sketch: `pi : forall t, Kernel (Hist t) A`
- Well-definedness obligations: measurable structure on histories and actions; policy-adaptedness in time index
- Downstream uses: induced process `(A_t,O_t)`, `Prob_{p,pi}`, policy observer `omega_pi`, finite-time policy observers
- Status: `needs measurability lemma`

## 4. `\Pcal`

- Informal name: program space
- Kind: countable set of codes
- Ambient carrier/type: subset of finite bitstrings / prefix codes
- Definition site: `v2.tex:100`
- Upstream dependencies: universal prefix machine `U`
- Set-theoretic realization: prefix-free domain of `U` restricted to programs that induce interactive environment models
- Lean realization sketch: subtype of `List Bool` or `BitVec` together with a realizability predicate
- Well-definedness obligations: prove countability and keep the realizability predicate explicit
- Downstream uses: every quotient, prior, posterior, observer, theorem
- Status: `grounded`

## 5. `\mu_p`

- Informal name: program-indexed interactive law
- Kind: family of kernels / chronological laws
- Ambient carrier/type: `P -> Hist x A -> Prob(O)` plus derived finite-prefix laws
- Definition site: `v2.tex:100-107`
- Upstream dependencies: `P`, `Hist_t`, `A`, `O`
- Set-theoretic realization: one-step kernel with finite-prefix product factorization
- Lean realization sketch: `mu : P -> Kernel (HistAct) O` together with a recursive finite-prefix law
- Well-definedness obligations: measurable structure on history-action pairs; compatibility between one-step and finite-prefix laws
- Downstream uses: semantic equivalence, posteriors, observers, all convergence statements
- Status: `needs hypothesis`

## 6. `\mu_p = \mu_{p'}`

- Informal name: reachable-pair equality of interactive laws
- Kind: binary relation on `P`
- Ambient carrier/type: relation on programs via equality of kernels at reachable pairs
- Definition site: `v2.tex:108`
- Upstream dependencies: `\mu_p`, finite-prefix likelihoods, reachability
- Set-theoretic realization: `p ~ p'` iff the one-step kernels agree whenever the finite prefix is reachable under either program
- Lean realization sketch: custom relation `ReachEq : P -> P -> Prop`
- Well-definedness obligations: prove reflexivity, symmetry, transitivity; prove observational irrelevance of jointly unreachable pairs
- Downstream uses: semantic classes, behavioral observer, policy-gap witness, observer-promotion failure theorem
- Status: `needs hypothesis`

## 7. `(w, q_t, q_t(\Rcal | h_t), q_{t+1})`

- Informal name: prior, posterior, set-mass posterior, predictive posterior
- Kind: probability measures and conditional updates
- Ambient carrier/type: probability mass functions on countable `P`
- Definition site: `v2.tex:110-127`
- Upstream dependencies: `P`, `\mu_p`, histories
- Set-theoretic realization: countable Bayesian updates by likelihood reweighting
- Lean realization sketch: `PMF P` or `Measure P` with countable support
- Well-definedness obligations: positive normalizing constants for both updates; sigma-additivity on countable `P`
- Downstream uses: all class pushforwards, free energy, expected free energy, convergence proofs
- Status: `needs hypothesis`

## 8. `R_{h_t}(p^\star)`

- Informal name: history-compatible set
- Kind: subset of `P`
- Ambient carrier/type: `Set P`
- Definition site: `v2.tex:136-143`
- Upstream dependencies: `P`, `\mu_p`, fixed history `h_t`
- Set-theoretic realization: programs with identical realized-prefix likelihood
- Lean realization sketch: `def historyCompat (pstar : P) (h : Hist t) : Set P := ...`
- Well-definedness obligations: none beyond the chronological law
- Downstream uses: knowability hierarchy, fit-gap lemma, strict-hierarchy theorem
- Status: `grounded`

## 9. `R_\pi(p^\star)`

- Informal name: policy-predictable set
- Kind: subset of `P`
- Ambient carrier/type: `Set P`
- Definition site: `v2.tex:146-153`
- Upstream dependencies: `Prob_{p,pi}`
- Set-theoretic realization: programs with identical induced path law under fixed policy `pi`
- Lean realization sketch: `def policyPredictable (pi) (pstar : P) : Set P := ...`
- Well-definedness obligations: induced path law must be defined first
- Downstream uses: hierarchy, policy-gap theorem, observer-promotion failure theorem
- Status: `needs existence lemma`

## 10. `([p^\star], \equiv, \Ccal)`

- Informal name: semantic class, semantic equivalence, quotient of programs
- Kind: equivalence classes and quotient set
- Ambient carrier/type: quotient of `P` by reachable-pair equality of interactive laws
- Definition site: `v2.tex:156-163`
- Upstream dependencies: relation `\mu_p = \mu_{p'}`
- Set-theoretic realization: quotient `P / equiv`
- Lean realization sketch: `Quot semanticSetoid`
- Well-definedness obligations: prove the relation is an equivalence; make the quotient map explicit
- Downstream uses: target theorem, class priors/posteriors, class-complement laws, main convergence theorem
- Status: `needs hypothesis`

## 11. `\omega = (\Omega_\omega, V_\omega)` and `\le`

- Informal name: observer and refinement preorder
- Kind: measurable-space object and preorder
- Ambient carrier/type: measurable codomain plus measurable map `P -> Omega_omega`
- Definition site: `v2.tex:168-175`
- Upstream dependencies: `P`, measurable spaces
- Set-theoretic realization: observer fibers are preimages under `V_\omega`; refinement is factorization through a measurable map
- Lean realization sketch: structure with fields `Omega`, `instMeasurable`, `view`, `measurable_view`
- Well-definedness obligations: explicit measurable codomains and factor maps
- Downstream uses: hierarchy, meeting-point theorem, self-referential observer promotion
- Status: `needs measurability lemma`

## 12. `(\omega_{\mathrm{syn}}, \omega_{\mathrm{behav}}, \omega_\pi, \omega_{h_t})`

- Informal name: canonical observers
- Kind: specific observer instances
- Ambient carrier/type: observers with codomains of source codes, interactive laws, fixed-policy laws, and realized-history statistics
- Definition site: `v2.tex:174-178`
- Upstream dependencies: observer structure, `P`, `\mu_p`, `Prob_{p,pi}`, histories
- Set-theoretic realization: identity-on-programs observer; map to interactive laws; map to path laws under fixed policy; map to realized-prefix likelihood
- Lean realization sketch: four `Observer` instances
- Well-definedness obligations: measurable spaces for interactive laws and path measures; measurability of each view map
- Downstream uses: refinement-chain proposition, meeting-point theorem, discussion-level framing
- Status: `needs measurability lemma`

## 13. `(\tau, \bar\tau)`

- Informal name: history-recoverable target and quotient lift
- Kind: target map and descended map on quotient classes
- Ambient carrier/type: `P -> T` and `C -> T`
- Definition site: `v2.tex:225-242`
- Upstream dependencies: metric space `T`, semantic quotient `C`
- Set-theoretic realization: map constant on equivalence classes descends uniquely to the quotient
- Lean realization sketch: `Quotient.lift` once constancy on classes is proved
- Well-definedness obligations: quotient-lift lemma; convergence-in-probability uniqueness argument
- Downstream uses: theorem `thm:factor-through-quotient`, knowability ceiling
- Status: `needs quotient lemma`

## 14. `(\sim_\omega, \Ccal^\omega, \bar w^\omega, q_t^\star(c | h_t))`

- Informal name: observer-indexed quotient data
- Kind: equivalence relation, quotient, pushed-forward prior, class posterior
- Ambient carrier/type: quotient of `P`, plus probability masses on that quotient
- Definition site: `v2.tex:344-350`
- Upstream dependencies: observer `omega`, prior `w`, posterior `q_t^\star`
- Set-theoretic realization: pushforward of countable measures along the quotient map
- Lean realization sketch: `Quot (observerSetoid omega)` with pushforward `PMF.map`
- Well-definedness obligations: observer-induced relation should be an equivalence; class sums should be countable and normalized
- Downstream uses: class likelihoods, Bhattacharyya separation, action term, goal-dialed convergence
- Status: `grounded`

## 15. `(\mu_c, \mu_c^{q_t^\star}, \Qcal_t^{-c,\omega}, B_t^\omega)`

- Informal name: class likelihoods, class predictive law, complement law, observer-indexed Bhattacharyya separation
- Kind: class-level probability laws and a divergence-like statistic
- Ambient carrier/type: kernels on observations indexed by classes, histories, and actions
- Definition site: `v2.tex:352-370`
- Upstream dependencies: observer quotient data, `\mu_p`, posterior `q_t^\star`
- Set-theoretic realization: either representative-independent class law above `omega_behav` or posterior-weighted averaged law at general `omega`
- Lean realization sketch: `muClass`, `muClassAvg`, `Qminus`, `BhatSep`
- Well-definedness obligations: prove representative independence of `mu_c` above `omega_behav`; prove denominator positivity for `Qminus`; prove the averaged law is a probability measure
- Downstream uses: admissibility propositions, class-against-complement rule, convergence proofs
- Status: `needs quotient lemma`

## 16. `\nu_t^\pi`

- Informal name: class-targeting distribution induced by a policy
- Kind: probability mass function on classes
- Ambient carrier/type: `Hist_t -> PMF (C^{omega_A})`
- Definition site: `v2.tex:373`
- Upstream dependencies: observer-indexed class space, policy `pi`
- Set-theoretic realization: first sample a class, then target an action for that class
- Lean realization sketch: explicit `PMF` attached to policies of the relevant form
- Well-definedness obligations: existence is only asserted here and provided later for the semantic rule; Lean should treat this as a parameterized construction, not a global object
- Downstream uses: `J_t`, action term, promotion-supporting statements
- Status: `needs existence lemma`

## 17. `(\ell_t, \mathcal F_t, \mathcal A_t^{\omega_A}, \mathcal J_t^{\omega_B,\omega_A}, \mathcal J_t^{\omega_B,\omega_A,\mathrm{MI}}, C^{\omega_A}, \mathcal J_t^{\omega_{\mathrm{behav}}})`

- Informal name: two-observer functional package
- Kind: loss, free-energy term, action term, total functional, MI variant, class random variable, canonical specialization
- Ambient carrier/type: real-valued functionals on `(q, pi)` plus an observer-indexed random variable
- Definition site: `v2.tex:380-409`
- Upstream dependencies: posteriors, class-targeting distribution, Bhattacharyya separation, KL divergence
- Set-theoretic realization: program-level expected codelength plus KL minus expected class separation plus regularizer on class targeting
- Lean realization sketch: definitions over `PMF P` and suitably typed policies
- Well-definedness obligations: `nu_t^pi` must be typed; `C^{omega_A}` must be realized as the quotient-map image of latent `P`; local notation clash with the later filtration `F_t`
- Downstream uses: meeting-point theorem, boundary identification, functional reading of the main theorem
- Status: `needs measurability lemma`

## 18. `(|p|, \widetilde w, Z, \bar\xi, K_U(\nu))`

- Informal name: code length, raw prior, normalization constant, universal mixture, semantic complexity
- Kind: nat-valued code length, weights, scalar, mixture law, minimization over realizers
- Ambient carrier/type: `Nat`, `P -> R`, `R`, finite-prefix law, `Law -> Nat`
- Definition site: `v2.tex:571-606`
- Upstream dependencies: `P`, universal machine `U`, `\mu_p`
- Set-theoretic realization: Kraft-style weights and minimum program length among all realizers of a law
- Lean realization sketch: `length : P -> Nat`, `rawWeight`, `Z`, `barXi`, `semanticComplexity`
- Well-definedness obligations: `Z > 0`; existence of a realizing program for `K_U(\nu)` whenever the complexity is invoked
- Downstream uses: universal prior, invariance lemma, belief layer
- Status: `needs existence lemma`

## 19. `(L_t, q_t^\star, \Qcal_t^O)`

- Informal name: history loss, canonical Bayes/Gibbs posterior, predictive observation law
- Kind: loss function, posterior, predictive law
- Ambient carrier/type: `P -> EnnReal`, `PMF P`, kernel on observations
- Definition site: `v2.tex:617-717`
- Upstream dependencies: `\bar\xi`, prior `w`, `\mu_p`, posterior update
- Set-theoretic realization: negative log likelihood, reweighted posterior, posterior predictive mixture on observations
- Lean realization sketch: `L_t`, `qStar`, `QObs`
- Well-definedness obligations: positive evidence for `q_t^\star`; finite or infinite value convention for `L_t`
- Downstream uses: variational identity, predictive merging, expected free energy
- Status: `needs hypothesis`

## 20. `(\Qcal_t^{-c}, S_t(c,a;h_t), B_t(c,a;h_t))`

- Informal name: class-against-complement law, semantic gain, semantic separation
- Kind: class-level law and two separation statistics
- Ambient carrier/type: probability law on observations and real-valued functionals
- Definition site: `v2.tex:731-794`
- Upstream dependencies: class posterior, class likelihood `\mu_c`
- Set-theoretic realization: posterior-weighted complement mixture plus KL and Bhattacharyya statistics against the true class
- Lean realization sketch: `QminusClass`, `semanticGain`, `semanticSep`
- Well-definedness obligations: denominator positivity when `0 < q_t^\star(c|h_t) < 1`; representative independence of `\mu_c`
- Downstream uses: odds identity, zero criterion, semantic rule, main convergence theorem
- Status: `needs hypothesis`

## 21. `(\bar w(c), \epsilon, a_t^c(h_t), \nu_t(c | h_t), C_t)`

- Informal name: semantic-rule data
- Kind: class prior, scalar exploration floor, measurable selector, class-targeting distribution, sampled latent target class
- Ambient carrier/type: real scalar, measurable function, PMF on classes, random variable
- Definition site: `v2.tex:846-859`
- Upstream dependencies: `C`, class posterior `q_t^\star(c|h_t)`, semantic separation `B_t`
- Set-theoretic realization: convex mixture of posterior and prior over classes, then deterministic action selection after class sampling
- Lean realization sketch: `selector`, `nuSemantic`, `C_t`
- Well-definedness obligations: existence and measurability of `a_t^c(h_t)` over countable actions; normalization of `nu_t`
- Downstream uses: promotion-supporting property, main convergence theorem, self-referential rule
- Status: `needs existence lemma`

## 22. `\delta`

- Informal name: promotion-support lower-bound constant
- Kind: positive scalar parameter
- Ambient carrier/type: real number
- Definition site: `v2.tex:863-870`
- Upstream dependencies: semantic-rule selectors and class priors
- Set-theoretic realization: uniform lower bound on the probability of playing the class-separating action
- Lean realization sketch: positive real parameter in a predicate on action rules
- Well-definedness obligations: positivity and independence from the current history except through the displayed inequality
- Downstream uses: theorem `thm:semantic-convergence`, remark on promotion-support generality
- Status: `grounded`

## 23. `(K, \widetilde\Ocal, \widetilde\mu_c, \widetilde\Qcal_t^{-c}, \widetilde B_t)`

- Informal name: noise-channel package
- Kind: Markov kernel, post-channel laws, post-channel separation
- Ambient carrier/type: `O -> Prob(\widetilde O)` and induced pushforwards
- Definition site: `v2.tex:889-910`
- Upstream dependencies: class/complement laws on observations
- Set-theoretic realization: post-compose both laws with a channel kernel and recompute Bhattacharyya separation
- Lean realization sketch: `Kernel O Otilde` plus pushforward composition
- Well-definedness obligations: measurable structure on `\widetilde O`; if strict positivity after corruption is needed, add a separate non-collapsing hypothesis
- Downstream uses: noise-immunity proposition and its transfer claim
- Status: `needs hypothesis`

## 24. `(\eta(c), R_t^-, \mathcal G_t, S_t, M_t, E_t, T_{t+1})`

- Informal name: separation and local convergence proof objects
- Kind: class-wise positive constants, posterior-odds process, sigma-algebra, cumulative separation, martingale, events
- Ambient carrier/type: real-valued functions and measurable events/processes
- Definition site: `v2.tex:925-1004`
- Upstream dependencies: semantic separation, posterior `q_t^\star`, class-complement law
- Set-theoretic realization: local proof scaffolding for the main convergence theorem
- Lean realization sketch: theorem-local definitions inside the convergence namespace
- Well-definedness obligations: event measurability, positivity of class prior, nonnegative-martingale convergence, notation clash between this filtration `G_t`/`F_t` and earlier `F_t`
- Downstream uses: `lem:contraction`, `thm:semantic-convergence`
- Status: `needs hypothesis`

## 25. `(\hat\eta, Z_t, \Delta_t, \mu_0, U_t)`

- Informal name: rate and finite-class corollary package
- Kind: lower-bound constant, log-odds process, increments, linear rate, maximin utility
- Ambient carrier/type: real-valued functions/processes
- Definition site: `v2.tex:1019-1135`
- Upstream dependencies: main convergence objects, semantic separation, semantic rule
- Set-theoretic realization: theorem-local scalar/process definitions
- Lean realization sketch: theorem-local abbreviations
- Well-definedness obligations: `Z_t` requires a convention at posterior values `0` and `1`; `U_t` uses a finite minimum over unresolved classes
- Downstream uses: drift lemma, expectation-form rate proposition, finite-class specialization
- Status: `needs hypothesis`

## 26. `(\omega_\pi^t, [p^\star]_{\omega_\pi^t})`

- Informal name: finite-time policy observer and its class of `p^\star`
- Kind: observer and quotient class
- Ambient carrier/type: observer with codomain equal to laws on `Hist_t`
- Definition site: `v2.tex:1153-1178`
- Upstream dependencies: `Prob_{p,pi}`, observer structure, history spaces
- Set-theoretic realization: view map `p |-> law(H_t)` under fixed `pi`
- Lean realization sketch: observer whose codomain is `Measure (Hist t)`
- Well-definedness obligations: measurable structure on laws over `Hist_t`; equality of full laws from equality of all finite marginals in `lem:monotone-refinement`
- Downstream uses: self-referential rule, observer-promotion proposition
- Status: `needs measurability lemma`

## 27. `(\pi^{\mathrm{sr}}, \Ccal^{\omega_{\pi^{\mathrm{sr}}}^t}, T_{p_1,p_2}, T_{p'})`

- Informal name: self-referential rule package
- Kind: inductively defined policy, running partitions, random separation times
- Ambient carrier/type: recursive policy and theorem-local stopping times
- Definition site: `v2.tex:1183-1261`
- Upstream dependencies: finite-time observers, semantic rule, running partitions
- Set-theoretic realization: recursively defined sequence of policies using the partition induced by the rule's own past behavior
- Lean realization sketch: recursion on `t` producing `pi_sr t`
- Well-definedness obligations: inductive measurability of the recursion; theorem `prop:observer-promotion-sr` additionally needs a recurrence/return hypothesis or a repaired proof
- Downstream uses: self-referential convergence theorem and computability remark
- Status: `needs existence lemma`

## 28. `(\Qcal_t^{PO}, \rho_t, c_t(a;h_t), \Gcal_t(a;h_t))`

- Informal name: expected-free-energy package
- Kind: joint predictive law, preference distribution, action cost, expected free energy
- Ambient carrier/type: joint law on `P x O`, kernels / scalar functions
- Definition site: `v2.tex:1302-1339`
- Upstream dependencies: canonical posterior `q_t^\star`, `\mu_p`, posterior update `q_{t+1}`
- Set-theoretic realization: predictive joint law of latent program and next observation together with a variational action objective
- Lean realization sketch: `QPO`, `rho`, `cost`, `G`
- Well-definedness obligations: posterior update under action `a` must be defined on the support of the predictive law; finite feasible observation set must be fixed before the specialization corollary is applied
- Downstream uses: boundary identity, expected-free-energy specialization, AFE principle
- Status: `needs hypothesis`

## 29. `\text{AFE principle}`

- Informal name: algorithmic free energy principle
- Kind: bundled learning architecture
- Ambient carrier/type: predicate on learners / tuple `(w, q^\star, action rule)`
- Definition site: `v2.tex:1350-1362`
- Upstream dependencies: universal prior, Bayes/Gibbs posterior, expected free energy
- Set-theoretic realization: conjunction of three clauses on prior, belief update, and action selection
- Lean realization sketch: structure or predicate collecting the three properties
- Well-definedness obligations: measurable tie-breaking in the action argmin
- Downstream uses: boundary identity, near-miss theorem
- Status: `grounded`

## 30. `Z := \one\{P \in c^\star\}`

- Informal name: class-membership indicator in the information decomposition
- Kind: Bernoulli random variable
- Ambient carrier/type: measurable function of latent program `P`
- Definition site: `v2.tex:1369`
- Upstream dependencies: quotient class `c^\star`, latent program random variable `P`
- Set-theoretic realization: indicator of semantic-class membership
- Lean realization sketch: `Z : P -> Bool` or `Indicator`
- Well-definedness obligations: none beyond measurability of the quotient map
- Downstream uses: `lem:info-decomp`
- Status: `grounded`

## 31. `(\Sigma_T, a^{\mathrm{ref}}, a^{\mathrm{sep}}, p_\sigma, c_\sigma, \beta_t, \lambda_t)`

- Informal name: near-miss construction package
- Kind: finite index set, distinguished actions, constructed programs/classes, conditional and marginal predictive distributions
- Ambient carrier/type: finite product set, specific programs in `P`, explicit probability vectors
- Definition site: `v2.tex:1405-1483`
- Upstream dependencies: infinitely many observations in `O`, at least two actions in `A`, finite-override computable-program construction
- Set-theoretic realization: explicit finite family of programs indexed by strings in `Sigma_T`
- Lean realization sketch: finite `Finset`-indexed construction
- Well-definedness obligations: existence of each `p_sigma` in `P`; proof that the resulting classes are pairwise distinct
- Downstream uses: near-miss theorem and promotion-contrast corollary
- Status: `needs existence lemma`

## 32. `\pi^\sharp`

- Informal name: fixed refining-only policy
- Kind: deterministic policy
- Ambient carrier/type: policy that always selects `a^{ref}`
- Definition site: `v2.tex:1495`
- Upstream dependencies: distinguished action `a^{ref}`
- Set-theoretic realization: constant deterministic kernel at every history
- Lean realization sketch: `piSharp : forall t, Hist t -> PMF A`
- Well-definedness obligations: none once deterministic policies are allowed
- Downstream uses: observer-promotion failure theorem and its universal-prior corollary
- Status: `grounded`

## 33. `p'`

- Informal name: behavioral-twin witness against `\pi^\sharp`
- Kind: explicitly modified program
- Ambient carrier/type: element of `P`
- Definition site: `v2.tex:1503-1511`
- Upstream dependencies: `p^\star`, distinguished action `a^{ref}`, finite override of a computable program
- Set-theoretic realization: agrees with `p^\star` on all `a^{ref}`-reachable pairs and differs at `a^{sep}`
- Lean realization sketch: explicit override construction inside `P`
- Well-definedness obligations: reuse the same finite-override existence lemma needed earlier
- Downstream uses: observer-promotion failure theorem and promotion-contrast corollary
- Status: `grounded`
