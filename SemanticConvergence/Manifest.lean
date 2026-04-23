namespace SemanticConvergence

/-- Generated status marker for each manuscript item. -/
inductive FormalizationStatus where
  | declared
  | wrapped
  | derived
deriving Repr, DecidableEq

/-- Generated first-principles status marker for each manuscript item. -/
inductive FirstPrinciplesStatus where
  | abstractInterface
  | concreteStack
deriving Repr, DecidableEq

/-- Generated concrete-migration status marker for each manuscript item. -/
inductive MigrationStatus where
  | pendingConcreteMigration
  | migratedToConcrete
deriving Repr, DecidableEq

/-- Generated proof-shape classification for one manuscript declaration. -/
inductive ProofKind where
  | definition
  | substantive
  | singleLemmaApplication
  | definitionalUnfold
  | fieldProjection
  | constructiveExistential
  | rateComposition
  | placeholderTruth
  | heuristicOther
deriving Repr, DecidableEq

/-- Generated metadata for one core manuscript declaration. -/
structure ManifestEntry where
  texLabel : String
  kind : String
  title : String
  startLine : Nat
  endLine : Nat
  leanModule : String
  declName : String
  qualifiedDeclName : String
  status : FormalizationStatus
  firstPrinciplesStatus : FirstPrinciplesStatus
  migrationStatus : MigrationStatus
  proofKind : ProofKind
deriving Repr, DecidableEq

/-- Generated coverage list for the canonical TeX source. -/
def manifestEntries : List ManifestEntry :=
  [
    { texLabel := "def:history-compat"
      kind := "definition"
      title := "History-compatible set"
      startLine := 184
      endLine := 192
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "def_history_compat"
      qualifiedDeclName := "SemanticConvergence.def_history_compat"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "def:policy-pred"
      kind := "definition"
      title := "Policy-predictable set"
      startLine := 194
      endLine := 202
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "def_policy_pred"
      qualifiedDeclName := "SemanticConvergence.def_policy_pred"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "def:int-sem-class"
      kind := "definition"
      title := "Interventional semantic class"
      startLine := 204
      endLine := 216
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "def_int_sem_class"
      qualifiedDeclName := "SemanticConvergence.def_int_sem_class"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "def:observer"
      kind := "definition"
      title := "Observer"
      startLine := 220
      endLine := 223
      leanModule := "SemanticConvergence.Foundations"
      declName := "def_observer"
      qualifiedDeclName := "SemanticConvergence.def_observer"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:nesting"
      kind := "lemma"
      title := "Nesting"
      startLine := 232
      endLine := 238
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "lem_nesting"
      qualifiedDeclName := "SemanticConvergence.lem_nesting"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:refinement-chain"
      kind := "proposition"
      title := "Refinement chain"
      startLine := 248
      endLine := 254
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "prop_refinement_chain"
      qualifiedDeclName := "SemanticConvergence.prop_refinement_chain"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "lem:observable-quotient"
      kind := "lemma"
      title := "Interventional semantic classes are the observable quotient"
      startLine := 262
      endLine := 265
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "lem_observable_quotient"
      qualifiedDeclName := "SemanticConvergence.lem_observable_quotient"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:history-recoverable"
      kind := "definition"
      title := "History-recoverable target"
      startLine := 277
      endLine := 285
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "def_history_recoverable"
      qualifiedDeclName := "SemanticConvergence.def_history_recoverable"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "thm:factor-through-quotient"
      kind := "theorem"
      title := "Every history-recoverable target factors through the semantic quotient"
      startLine := 287
      endLine := 290
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "thm_factor_through_quotient"
      qualifiedDeclName := "SemanticConvergence.thm_factor_through_quotient"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "lem:fit-gap"
      kind := "lemma"
      title := "{Fit gap: $R_\\pi(p^\\star)\\subsetneq R_{h_t}(p^\\star)$}"
      startLine := 302
      endLine := 305
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "lem_fit_gap"
      qualifiedDeclName := "SemanticConvergence.lem_fit_gap"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:policy-gap"
      kind := "theorem"
      title := "{Policy gap: $[p^\\star"
      startLine := 311
      endLine := 314
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "thm_policy_gap"
      qualifiedDeclName := "SemanticConvergence.thm_policy_gap"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "lem:syntactic-gap"
      kind := "lemma"
      title := "{Syntactic gap: $\\{p^\\star\\}\\subsetneq [p^\\star"
      startLine := 338
      endLine := 341
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "lem_syntactic_gap"
      qualifiedDeclName := "SemanticConvergence.lem_syntactic_gap"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:strict-hierarchy"
      kind := "theorem"
      title := "Strict knowability hierarchy"
      startLine := 351
      endLine := 357
      leanModule := "SemanticConvergence.Hierarchy"
      declName := "thm_strict_hierarchy"
      qualifiedDeclName := "SemanticConvergence.thm_strict_hierarchy"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:bhat-omega"
      kind := "definition"
      title := "Bhattacharyya separation at observer $\\omega$"
      startLine := 416
      endLine := 423
      leanModule := "SemanticConvergence.Functional"
      declName := "def_bhat_omega"
      qualifiedDeclName := "SemanticConvergence.def_bhat_omega"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "def:raw-two-observer-functional"
      kind := "definition"
      title := "Raw policy-coupled scaffold"
      startLine := 432
      endLine := 447
      leanModule := "SemanticConvergence.Functional"
      declName := "def_raw_two_observer_functional"
      qualifiedDeclName := "SemanticConvergence.def_raw_two_observer_functional"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "def:two-observer-functional"
      kind := "definition"
      title := "Two-observer variational functional"
      startLine := 456
      endLine := 474
      leanModule := "SemanticConvergence.Functional"
      declName := "def_two_observer_functional"
      qualifiedDeclName := "SemanticConvergence.def_two_observer_functional"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:two-observer-minimizer"
      kind := "proposition"
      title := "Exact global minimizer of the two-observer functional"
      startLine := 476
      endLine := 486
      leanModule := "SemanticConvergence.Functional"
      declName := "prop_two_observer_minimizer"
      qualifiedDeclName := "SemanticConvergence.prop_two_observer_minimizer"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:kernel-functional"
      kind := "definition"
      title := "Kernel lift of the two-observer functional"
      startLine := 511
      endLine := 521
      leanModule := "SemanticConvergence.Functional"
      declName := "def_kernel_functional"
      qualifiedDeclName := "SemanticConvergence.def_kernel_functional"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:kernel-functional-minimizer"
      kind := "proposition"
      title := "Exact global minimizer of the kernel lift"
      startLine := 523
      endLine := 533
      leanModule := "SemanticConvergence.Functional"
      declName := "prop_kernel_functional_minimizer"
      qualifiedDeclName := "SemanticConvergence.prop_kernel_functional_minimizer"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "prop:kernel-functional-minimizer-compact"
      kind := "proposition"
      title := "Exact global minimizer of the compact-action kernel lift"
      startLine := 556
      endLine := 577
      leanModule := "SemanticConvergence.Functional"
      declName := "prop_kernel_functional_minimizer_compact"
      qualifiedDeclName := "SemanticConvergence.prop_kernel_functional_minimizer_compact"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "def:meeting-point-shorthand"
      kind := "definition"
      title := "Meeting-point specialization"
      startLine := 605
      endLine := 616
      leanModule := "SemanticConvergence.Functional"
      declName := "def_meeting_point_shorthand"
      qualifiedDeclName := "SemanticConvergence.def_meeting_point_shorthand"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:belief-invariance-above"
      kind := "proposition"
      title := "Belief-observer invariance above $\\omega_{\\mathrm{behav}}$"
      startLine := 625
      endLine := 632
      leanModule := "SemanticConvergence.Functional"
      declName := "prop_belief_invariance_above"
      qualifiedDeclName := "SemanticConvergence.prop_belief_invariance_above"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:belief-illtyped-below"
      kind := "proposition"
      title := "Belief-observer ill-typing below $\\omega_{\\mathrm{behav}}$"
      startLine := 645
      endLine := 648
      leanModule := "SemanticConvergence.Functional"
      declName := "prop_belief_illtyped_below"
      qualifiedDeclName := "SemanticConvergence.prop_belief_illtyped_below"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:action-cap"
      kind := "proposition"
      title := "Action-observer cap"
      startLine := 661
      endLine := 669
      leanModule := "SemanticConvergence.Functional"
      declName := "prop_action_cap"
      qualifiedDeclName := "SemanticConvergence.prop_action_cap"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:twins-frozen-ratio"
      kind := "corollary"
      title := "Behavioral twins have frozen posterior ratio"
      startLine := 683
      endLine := 690
      leanModule := "SemanticConvergence.Functional"
      declName := "cor_twins_frozen_ratio"
      qualifiedDeclName := "SemanticConvergence.cor_twins_frozen_ratio"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:meeting-point"
      kind := "theorem"
      title := "Meeting point"
      startLine := 705
      endLine := 715
      leanModule := "SemanticConvergence.Functional"
      declName := "thm_meeting_point"
      qualifiedDeclName := "SemanticConvergence.thm_meeting_point"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:canonical-pair"
      kind := "corollary"
      title := "Canonical two-observer choice"
      startLine := 721
      endLine := 724
      leanModule := "SemanticConvergence.Functional"
      declName := "cor_canonical_pair"
      qualifiedDeclName := "SemanticConvergence.cor_canonical_pair"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:goal-dialed"
      kind := "proposition"
      title := "Goal-dialed convergence"
      startLine := 738
      endLine := 748
      leanModule := "SemanticConvergence.Functional"
      declName := "prop_goal_dialed"
      qualifiedDeclName := "SemanticConvergence.prop_goal_dialed"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:universal-prior"
      kind := "definition"
      title := "Universal interactive prior"
      startLine := 780
      endLine := 792
      leanModule := "SemanticConvergence.Belief"
      declName := "def_universal_prior"
      qualifiedDeclName := "SemanticConvergence.def_universal_prior"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:prior-invariance"
      kind := "lemma"
      title := "Machine invariance"
      startLine := 794
      endLine := 803
      leanModule := "SemanticConvergence.Belief"
      declName := "lem_prior_invariance"
      qualifiedDeclName := "SemanticConvergence.lem_prior_invariance"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "lem:prior-necessity"
      kind := "lemma"
      title := "{Positive prior mass on $[p^\\star"
      startLine := 817
      endLine := 820
      leanModule := "SemanticConvergence.Belief"
      declName := "lem_prior_necessity"
      qualifiedDeclName := "SemanticConvergence.lem_prior_necessity"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:afe"
      kind := "definition"
      title := "Algorithmic free energy"
      startLine := 834
      endLine := 841
      leanModule := "SemanticConvergence.Belief"
      declName := "def_afe"
      qualifiedDeclName := "SemanticConvergence.def_afe"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:variational"
      kind := "lemma"
      title := "Variational identity"
      startLine := 843
      endLine := 856
      leanModule := "SemanticConvergence.Belief"
      declName := "lem_variational"
      qualifiedDeclName := "SemanticConvergence.lem_variational"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "lem:kl-necessity"
      kind := "lemma"
      title := "KL is forced by the exact Gibbs variational formula"
      startLine := 874
      endLine := 883
      leanModule := "SemanticConvergence.Belief"
      declName := "lem_kl_necessity"
      qualifiedDeclName := "SemanticConvergence.lem_kl_necessity"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "lem:merging"
      kind := "lemma"
      title := "Predictive merging"
      startLine := 901
      endLine := 916
      leanModule := "SemanticConvergence.Belief"
      declName := "lem_merging"
      qualifiedDeclName := "SemanticConvergence.lem_merging"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:class-complement"
      kind := "definition"
      title := "Class-complement predictive law"
      startLine := 940
      endLine := 949
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_class_complement"
      qualifiedDeclName := "SemanticConvergence.def_class_complement"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "def:semantic-gain"
      kind := "definition"
      title := "Semantic gain"
      startLine := 956
      endLine := 967
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_semantic_gain"
      qualifiedDeclName := "SemanticConvergence.def_semantic_gain"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:odds-identity"
      kind := "lemma"
      title := "Posterior-odds identity"
      startLine := 969
      endLine := 980
      leanModule := "SemanticConvergence.Semantic"
      declName := "lem_odds_identity"
      qualifiedDeclName := "SemanticConvergence.lem_odds_identity"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:semantic-separation"
      kind := "definition"
      title := "Semantic separation"
      startLine := 992
      endLine := 1003
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_semantic_separation"
      qualifiedDeclName := "SemanticConvergence.def_semantic_separation"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:zero-criterion"
      kind := "lemma"
      title := "Zero criterion"
      startLine := 1010
      endLine := 1020
      leanModule := "SemanticConvergence.Semantic"
      declName := "lem_zero_criterion"
      qualifiedDeclName := "SemanticConvergence.lem_zero_criterion"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:chernoff-correspondence"
      kind := "proposition"
      title := "Chernoff--Bhattacharyya correspondence"
      startLine := 1026
      endLine := 1037
      leanModule := "SemanticConvergence.Semantic"
      declName := "prop_chernoff_correspondence"
      qualifiedDeclName := "SemanticConvergence.prop_chernoff_correspondence"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:semantic-rule"
      kind := "definition"
      title := "Semantic action rule"
      startLine := 1055
      endLine := 1077
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_semantic_rule"
      qualifiedDeclName := "SemanticConvergence.def_semantic_rule"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "def:promotion-supporting"
      kind := "definition"
      title := "Promotion-supporting action rule"
      startLine := 1081
      endLine := 1088
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_promotion_supporting"
      qualifiedDeclName := "SemanticConvergence.def_promotion_supporting"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:semantic-is-promotion-supporting"
      kind := "proposition"
      title := "Semantic rule is promotion-supporting"
      startLine := 1090
      endLine := 1101
      leanModule := "SemanticConvergence.Semantic"
      declName := "prop_semantic_is_promotion_supporting"
      qualifiedDeclName := "SemanticConvergence.prop_semantic_is_promotion_supporting"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:kernel-semantic-rule"
      kind := "definition"
      title := "Kernel semantic action rule"
      startLine := 1119
      endLine := 1126
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_kernel_semantic_rule"
      qualifiedDeclName := "SemanticConvergence.def_kernel_semantic_rule"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:kernel-promotion-support"
      kind := "proposition"
      title := "Kernel rule has reference-mass promotion support"
      startLine := 1128
      endLine := 1137
      leanModule := "SemanticConvergence.Semantic"
      declName := "prop_kernel_promotion_support"
      qualifiedDeclName := "SemanticConvergence.prop_kernel_promotion_support"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:kernel-promotion-support-compact"
      kind := "proposition"
      title := "Compact-action kernel rule has reference-mass promotion support"
      startLine := 1160
      endLine := 1172
      leanModule := "SemanticConvergence.Semantic"
      declName := "prop_kernel_promotion_support_compact"
      qualifiedDeclName := "SemanticConvergence.prop_kernel_promotion_support_compact"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:decodable-channel"
      kind := "definition"
      title := "Decodable observation channel"
      startLine := 1198
      endLine := 1213
      leanModule := "SemanticConvergence.Noise"
      declName := "def_decodable_channel"
      qualifiedDeclName := "SemanticConvergence.def_decodable_channel"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:noise-immunity"
      kind := "proposition"
      title := "Pointwise noise-channel monotonicity"
      startLine := 1215
      endLine := 1223
      leanModule := "SemanticConvergence.Noise"
      declName := "prop_noise_immunity"
      qualifiedDeclName := "SemanticConvergence.prop_noise_immunity"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:left-invertible-channel"
      kind := "definition"
      title := "Left-invertible finite observation channel"
      startLine := 1239
      endLine := 1248
      leanModule := "SemanticConvergence.Noise"
      declName := "def_left_invertible_channel"
      qualifiedDeclName := "SemanticConvergence.def_left_invertible_channel"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:noise-left-invertible"
      kind := "proposition"
      title := "Uniform positive separation under left-invertible finite noise"
      startLine := 1250
      endLine := 1278
      leanModule := "SemanticConvergence.Noise"
      declName := "prop_noise_left_invertible"
      qualifiedDeclName := "SemanticConvergence.prop_noise_left_invertible"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "prop:noise-decoding"
      kind := "proposition"
      title := "Exact preservation under decodable recodings"
      startLine := 1324
      endLine := 1345
      leanModule := "SemanticConvergence.Noise"
      declName := "prop_noise_decoding"
      qualifiedDeclName := "SemanticConvergence.prop_noise_decoding"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:noise-transfer"
      kind := "corollary"
      title := "Exact transfer under decodable observation recodings"
      startLine := 1415
      endLine := 1437
      leanModule := "SemanticConvergence.Noise"
      declName := "cor_noise_transfer"
      qualifiedDeclName := "SemanticConvergence.cor_noise_transfer"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:noise-left-invertible-history-independent"
      kind := "corollary"
      title := "Left-invertible noisy transfer in the history-independent setting"
      startLine := 1510
      endLine := 1539
      leanModule := "SemanticConvergence.Semantic"
      declName := "cor_noise_left_invertible_history_independent"
      qualifiedDeclName := "SemanticConvergence.cor_noise_left_invertible_history_independent"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:sep-condition"
      kind := "definition"
      title := "Semantic separation condition"
      startLine := 1683
      endLine := 1689
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_sep_condition"
      qualifiedDeclName := "SemanticConvergence.def_sep_condition"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "def:uniform-history-independent-separation"
      kind := "definition"
      title := "Uniform history-independent semantic separation"
      startLine := 1691
      endLine := 1713
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_uniform_history_independent_separation"
      qualifiedDeclName := "SemanticConvergence.def_uniform_history_independent_separation"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:uniform-history-independent-implies-semantic"
      kind := "proposition"
      title := "Uniform history-independent separation implies semantic separation"
      startLine := 1715
      endLine := 1718
      leanModule := "SemanticConvergence.Semantic"
      declName := "prop_uniform_history_independent_implies_semantic"
      qualifiedDeclName := "SemanticConvergence.prop_uniform_history_independent_implies_semantic"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:kl-implies-semantic-separation"
      kind := "corollary"
      title := "Uniform KL class-vs.-complement separation implies semantic separation"
      startLine := 1745
      endLine := 1757
      leanModule := "SemanticConvergence.Semantic"
      declName := "cor_kl_implies_semantic_separation"
      qualifiedDeclName := "SemanticConvergence.cor_kl_implies_semantic_separation"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:event-witness-implies-semantic-separation"
      kind := "corollary"
      title := "Event-witness separation implies semantic separation"
      startLine := 1771
      endLine := 1787
      leanModule := "SemanticConvergence.Semantic"
      declName := "cor_event_witness_implies_semantic_separation"
      qualifiedDeclName := "SemanticConvergence.cor_event_witness_implies_semantic_separation"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:kernel-sep-condition"
      kind := "definition"
      title := "Kernel semantic separation condition relative to $\\lambda$"
      startLine := 1825
      endLine := 1831
      leanModule := "SemanticConvergence.Semantic"
      declName := "def_kernel_sep_condition"
      qualifiedDeclName := "SemanticConvergence.def_kernel_sep_condition"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "prop:finite-action-kernel-separation"
      kind := "proposition"
      title := "Finite-action lift of semantic separation"
      startLine := 1833
      endLine := 1843
      leanModule := "SemanticConvergence.Semantic"
      declName := "prop_finite_action_kernel_separation"
      qualifiedDeclName := "SemanticConvergence.prop_finite_action_kernel_separation"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:compact-action-kernel-separation"
      kind := "proposition"
      title := "Compact-action lift of semantic separation"
      startLine := 1853
      endLine := 1875
      leanModule := "SemanticConvergence.Semantic"
      declName := "prop_compact_action_kernel_separation"
      qualifiedDeclName := "SemanticConvergence.prop_compact_action_kernel_separation"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "lem:conditional-bc"
      kind := "lemma"
      title := "Conditional Borel--Cantelli"
      startLine := 1919
      endLine := 1922
      leanModule := "SemanticConvergence.Semantic"
      declName := "lem_conditional_bc"
      qualifiedDeclName := "SemanticConvergence.lem_conditional_bc"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "lem:contraction"
      kind := "lemma"
      title := "Cumulative separation drives posterior odds to zero"
      startLine := 1928
      endLine := 1937
      leanModule := "SemanticConvergence.Semantic"
      declName := "lem_contraction"
      qualifiedDeclName := "SemanticConvergence.lem_contraction"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "prop:full-support-behavioral"
      kind := "proposition"
      title := "Full-support policies recover the behavioral observer"
      startLine := 1961
      endLine := 1973
      leanModule := "SemanticConvergence.Semantic"
      declName := "prop_full_support_behavioral"
      qualifiedDeclName := "SemanticConvergence.prop_full_support_behavioral"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    /-
    `thm:separating-support-convergence` names the countable probabilistic
    Section 6 theorem on `CountablePrefixMachine` and realized trajectory laws.
    Its current proof path is first-principles: the probabilistic theorem
    is derived from the deterministic `ConcretePrefixMachine` soft-substrate
    contraction through the explicit bridge layer in
    `ConcreteSubstrateBridge`, and the selector/kernel realizations are
    then rethreaded through that bridged theorem stack.
    -/
    { texLabel := "thm:separating-support-convergence"
      kind := "theorem"
      title := "Sufficient conditions for semantic recovery"
      startLine := 2014
      endLine := 2043
      leanModule := "SemanticConvergence.Semantic"
      declName := "thm_separating_support_convergence"
      qualifiedDeclName := "SemanticConvergence.thm_separating_support_convergence"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:exploration-floor-behavioral"
      kind := "theorem"
      title := "Full-support exploration floors recover the behavioral target"
      startLine := 2075
      endLine := 2097
      leanModule := "SemanticConvergence.Semantic"
      declName := "thm_exploration_floor_behavioral"
      qualifiedDeclName := "SemanticConvergence.thm_exploration_floor_behavioral"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "thm:separating-support-rate"
      kind := "theorem"
      title := "Rates from cumulative separating-action support"
      startLine := 2126
      endLine := 2181
      leanModule := "SemanticConvergence.Semantic"
      declName := "thm_separating_support_rate"
      qualifiedDeclName := "SemanticConvergence.thm_separating_support_rate"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:separating-support-finite-time"
      kind := "corollary"
      title := "Explicit finite-time recovery guarantee"
      startLine := 2272
      endLine := 2284
      leanModule := "SemanticConvergence.Semantic"
      declName := "cor_separating_support_finite_time"
      qualifiedDeclName := "SemanticConvergence.cor_separating_support_finite_time"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:semantic-convergence"
      kind := "theorem"
      title := "Canonical selector realization of semantic convergence"
      startLine := 2323
      endLine := 2338
      leanModule := "SemanticConvergence.Semantic"
      declName := "thm_semantic_convergence"
      qualifiedDeclName := "SemanticConvergence.thm_semantic_convergence"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:kernel-semantic-convergence"
      kind := "theorem"
      title := "Kernel-functional semantic convergence"
      startLine := 2383
      endLine := 2398
      leanModule := "SemanticConvergence.Semantic"
      declName := "thm_kernel_semantic_convergence"
      qualifiedDeclName := "SemanticConvergence.thm_kernel_semantic_convergence"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:compact-action-kernel"
      kind := "corollary"
      title := "Compact-action extension of the kernel theorem and rates"
      startLine := 2421
      endLine := 2455
      leanModule := "SemanticConvergence.Semantic"
      declName := "cor_compact_action_kernel"
      qualifiedDeclName := "SemanticConvergence.cor_compact_action_kernel"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:finite-maximin"
      kind := "corollary"
      title := "Finite-class deterministic specialization"
      startLine := 2489
      endLine := 2500
      leanModule := "SemanticConvergence.Semantic"
      declName := "cor_finite_maximin"
      qualifiedDeclName := "SemanticConvergence.cor_finite_maximin"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:support-necessary"
      kind := "theorem"
      title := "Zero separating support makes semantic recovery impossible"
      startLine := 2521
      endLine := 2529
      leanModule := "SemanticConvergence.Semantic"
      declName := "cor_support_necessary"
      qualifiedDeclName := "SemanticConvergence.cor_support_necessary"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "thm:summable-support-insufficient"
      kind := "theorem"
      title := "Summable separating support is insufficient"
      startLine := 2546
      endLine := 2572
      leanModule := "SemanticConvergence.Semantic"
      declName := "thm_summable_support_insufficient"
      qualifiedDeclName := "SemanticConvergence.thm_summable_support_insufficient"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "lem:one-step-drift"
      kind := "lemma"
      title := "Canonical selector one-step drift"
      startLine := 2644
      endLine := 2656
      leanModule := "SemanticConvergence.Rates"
      declName := "lem_one_step_drift"
      qualifiedDeclName := "SemanticConvergence.lem_one_step_drift"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.singleLemmaApplication },
    { texLabel := "prop:exp-rate"
      kind := "proposition"
      title := "Positive-floor exponential rate, expectation form"
      startLine := 2683
      endLine := 2702
      leanModule := "SemanticConvergence.Rates"
      declName := "prop_exp_rate"
      qualifiedDeclName := "SemanticConvergence.prop_exp_rate"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.singleLemmaApplication },
    { texLabel := "lem:one-step-drift-kernel"
      kind := "lemma"
      title := "Kernel one-step drift"
      startLine := 2714
      endLine := 2726
      leanModule := "SemanticConvergence.Rates"
      declName := "lem_one_step_drift_kernel"
      qualifiedDeclName := "SemanticConvergence.lem_one_step_drift_kernel"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:kernel-exp-rate"
      kind := "proposition"
      title := "Same-view transfer of the positive-floor exponential rate"
      startLine := 2757
      endLine := 2777
      leanModule := "SemanticConvergence.Rates"
      declName := "prop_kernel_exp_rate"
      qualifiedDeclName := "SemanticConvergence.prop_kernel_exp_rate"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.rateComposition },
    { texLabel := "thm:exp-rate-concentration"
      kind := "theorem"
      title := "Finite-time positive-floor rate transfer"
      startLine := 2789
      endLine := 2823
      leanModule := "SemanticConvergence.Rates"
      declName := "thm_exp_rate_concentration"
      qualifiedDeclName := "SemanticConvergence.thm_exp_rate_concentration"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.rateComposition },
    { texLabel := "cor:goal-dialed-payoff"
      kind := "corollary"
      title := "Goal-dialed convergence"
      startLine := 2891
      endLine := 2899
      leanModule := "SemanticConvergence.Semantic"
      declName := "cor_goal_dialed_payoff"
      qualifiedDeclName := "SemanticConvergence.cor_goal_dialed_payoff"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:finite-time-policy-observer"
      kind := "definition"
      title := "Finite-time policy observer"
      startLine := 2917
      endLine := 2924
      leanModule := "SemanticConvergence.SelfReference"
      declName := "def_finite_time_policy_observer"
      qualifiedDeclName := "SemanticConvergence.def_finite_time_policy_observer"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:monotone-refinement"
      kind := "lemma"
      title := "Monotone refinement toward $\\omega_\\pi$"
      startLine := 2926
      endLine := 2936
      leanModule := "SemanticConvergence.SelfReference"
      declName := "lem_monotone_refinement"
      qualifiedDeclName := "SemanticConvergence.lem_monotone_refinement"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:self-ref-rule"
      kind := "definition"
      title := "Self-referential semantic rule"
      startLine := 2947
      endLine := 2950
      leanModule := "SemanticConvergence.SelfReference"
      declName := "def_self_ref_rule"
      qualifiedDeclName := "SemanticConvergence.def_self_ref_rule"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:exploration-reachability"
      kind := "lemma"
      title := "Promotion-floor reachability"
      startLine := 2964
      endLine := 2979
      leanModule := "SemanticConvergence.SelfReference"
      declName := "lem_exploration_reachability"
      qualifiedDeclName := "SemanticConvergence.lem_exploration_reachability"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "prop:observer-promotion-sr"
      kind := "proposition"
      title := "Eventual isolation criterion"
      startLine := 2985
      endLine := 3009
      leanModule := "SemanticConvergence.SelfReference"
      declName := "prop_observer_promotion_sr"
      qualifiedDeclName := "SemanticConvergence.prop_observer_promotion_sr"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:self-ref-convergence"
      kind := "theorem"
      title := "Self-referential convergence under eventual isolation"
      startLine := 3022
      endLine := 3035
      leanModule := "SemanticConvergence.SelfReference"
      declName := "thm_self_ref_convergence"
      qualifiedDeclName := "SemanticConvergence.thm_self_ref_convergence"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:self-ref-obstruction"
      kind := "proposition"
      title := "Unconditional eventual isolation fails"
      startLine := 3068
      endLine := 3084
      leanModule := "SemanticConvergence.SelfReference"
      declName := "prop_self_ref_obstruction"
      qualifiedDeclName := "SemanticConvergence.prop_self_ref_obstruction"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:self-ref-exploratory"
      kind := "definition"
      title := "Exploration-completed self-referential rule"
      startLine := 3168
      endLine := 3183
      leanModule := "SemanticConvergence.SelfReference"
      declName := "def_self_ref_exploratory"
      qualifiedDeclName := "SemanticConvergence.def_self_ref_exploratory"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "thm:self-ref-exploratory"
      kind := "theorem"
      title := "Exploration-completed self-reference with divergent exploration budget"
      startLine := 3185
      endLine := 3198
      leanModule := "SemanticConvergence.SelfReference"
      declName := "thm_self_ref_exploratory"
      qualifiedDeclName := "SemanticConvergence.thm_self_ref_exploratory"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:self-ref-exploratory-rate"
      kind := "theorem"
      title := "Rates for exploration-completed self-reference"
      startLine := 3210
      endLine := 3249
      leanModule := "SemanticConvergence.SelfReference"
      declName := "thm_self_ref_exploratory_rate"
      qualifiedDeclName := "SemanticConvergence.thm_self_ref_exploratory_rate"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:self-ref-one-step-split"
      kind := "proposition"
      title := "One-step splitting criterion"
      startLine := 3278
      endLine := 3302
      leanModule := "SemanticConvergence.SelfReference"
      declName := "prop_self_ref_one_step_split"
      qualifiedDeclName := "SemanticConvergence.prop_self_ref_one_step_split"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "thm:self-ref-sharp"
      kind := "theorem"
      title := "Sharpened self-referential convergence under deterministic splitting"
      startLine := 3339
      endLine := 3369
      leanModule := "SemanticConvergence.SelfReference"
      declName := "thm_self_ref_sharp"
      qualifiedDeclName := "SemanticConvergence.thm_self_ref_sharp"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:boundary-identity"
      kind := "proposition"
      title := "Boundary identification under Bayes/Gibbs belief"
      startLine := 3411
      endLine := 3415
      leanModule := "SemanticConvergence.Boundary"
      declName := "prop_boundary_identity"
      qualifiedDeclName := "SemanticConvergence.prop_boundary_identity"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:efe"
      kind := "definition"
      title := "Expected free energy"
      startLine := 3434
      endLine := 3448
      leanModule := "SemanticConvergence.Boundary"
      declName := "def_efe"
      qualifiedDeclName := "SemanticConvergence.def_efe"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:risk-ig"
      kind := "lemma"
      title := "Risk minus information gain"
      startLine := 3450
      endLine := 3460
      leanModule := "SemanticConvergence.Boundary"
      declName := "lem_risk_ig"
      qualifiedDeclName := "SemanticConvergence.lem_risk_ig"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:efe-specialization"
      kind := "corollary"
      title := "Expected free energy as a unifying epistemic principle"
      startLine := 3466
      endLine := 3469
      leanModule := "SemanticConvergence.Boundary"
      declName := "cor_efe_specialization"
      qualifiedDeclName := "SemanticConvergence.cor_efe_specialization"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "def:afe-principle"
      kind := "definition"
      title := "Algorithmic free energy principle"
      startLine := 3482
      endLine := 3490
      leanModule := "SemanticConvergence.Boundary"
      declName := "def_afe_principle"
      qualifiedDeclName := "SemanticConvergence.def_afe_principle"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.definition },
    { texLabel := "lem:info-decomp"
      kind := "lemma"
      title := "Information decomposition"
      startLine := 3499
      endLine := 3507
      leanModule := "SemanticConvergence.Boundary"
      declName := "lem_info_decomp"
      qualifiedDeclName := "SemanticConvergence.lem_info_decomp"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:afe-near-miss"
      kind := "theorem"
      title := "Near-miss: the algorithmic free energy principle does not imply semantic convergence"
      startLine := 3525
      endLine := 3533
      leanModule := "SemanticConvergence.Boundary"
      declName := "thm_afe_near_miss"
      qualifiedDeclName := "SemanticConvergence.thm_afe_near_miss"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:observer-promotion-failure"
      kind := "theorem"
      title := "Observer-promotion failure of the AFE principle"
      startLine := 3625
      endLine := 3632
      leanModule := "SemanticConvergence.Boundary"
      declName := "thm_observer_promotion_failure"
      qualifiedDeclName := "SemanticConvergence.thm_observer_promotion_failure"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:observer-promotion-universal"
      kind := "corollary"
      title := "Universal-prior case"
      startLine := 3646
      endLine := 3649
      leanModule := "SemanticConvergence.Boundary"
      declName := "cor_observer_promotion_universal"
      qualifiedDeclName := "SemanticConvergence.cor_observer_promotion_universal"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "cor:promotion-contrast"
      kind := "corollary"
      title := "Observer-promotion contrast"
      startLine := 3670
      endLine := 3673
      leanModule := "SemanticConvergence.Boundary"
      declName := "cor_promotion_contrast"
      qualifiedDeclName := "SemanticConvergence.cor_promotion_contrast"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "prop:amortized-surrogate-minimizer"
      kind := "proposition"
      title := "Exact action-side minimizer of the amortized surrogate"
      startLine := 3744
      endLine := 3757
      leanModule := "SemanticConvergence.Surrogate"
      declName := "prop_amortized_surrogate_minimizer"
      qualifiedDeclName := "SemanticConvergence.prop_amortized_surrogate_minimizer"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
    { texLabel := "thm:amortized-surrogate"
      kind := "theorem"
      title := "Semantic-recovery guarantee for the amortized surrogate"
      startLine := 3763
      endLine := 3818
      leanModule := "SemanticConvergence.Surrogate"
      declName := "thm_amortized_surrogate"
      qualifiedDeclName := "SemanticConvergence.thm_amortized_surrogate"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.constructiveExistential },
    { texLabel := "cor:amortized-surrogate-finite-time"
      kind := "corollary"
      title := "Finite-time guarantee for the amortized surrogate"
      startLine := 3879
      endLine := 3906
      leanModule := "SemanticConvergence.Surrogate"
      declName := "cor_amortized_surrogate_finite_time"
      qualifiedDeclName := "SemanticConvergence.cor_amortized_surrogate_finite_time"
      status := FormalizationStatus.derived
      firstPrinciplesStatus := FirstPrinciplesStatus.concreteStack
      migrationStatus := MigrationStatus.migratedToConcrete
      proofKind := ProofKind.substantive },
  ]

def manifestEntryCount : Nat := manifestEntries.length

theorem manifestEntryCount_eq : manifestEntryCount = 106 := rfl

def derivedEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.status = FormalizationStatus.derived)

def wrappedEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.status = FormalizationStatus.wrapped)

def declaredEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.status = FormalizationStatus.declared)

def concreteStackEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.firstPrinciplesStatus = FirstPrinciplesStatus.concreteStack)

def abstractInterfaceEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.firstPrinciplesStatus = FirstPrinciplesStatus.abstractInterface)

def migratedToConcreteEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.migrationStatus = MigrationStatus.migratedToConcrete)

def pendingConcreteMigrationEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.migrationStatus = MigrationStatus.pendingConcreteMigration)

def substantiveEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.substantive)

def definitionProofEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.definition)

def constructiveExistentialEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.constructiveExistential)

def rateCompositionEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.rateComposition)

def singleLemmaApplicationEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.singleLemmaApplication)

def definitionalUnfoldEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.definitionalUnfold)

def fieldProjectionEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.fieldProjection)

def placeholderTruthEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.placeholderTruth)

def heuristicOtherEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.proofKind = ProofKind.heuristicOther)

def manifestDefinitionEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.kind = "definition")

def manifestDefinitionEntriesTaggedAsDefinitionCount : Nat :=
  manifestEntries.countP (fun entry =>
    entry.kind = "definition" && entry.proofKind = ProofKind.definition)

def manifestTheoremLikeEntryCount : Nat :=
  manifestEntries.countP (fun entry => entry.kind ≠ "definition")

def manifestTheoremLikeSemanticallyAuditedEntryCount : Nat :=
  manifestEntries.countP (fun entry =>
    entry.kind ≠ "definition" &&
      (entry.proofKind = ProofKind.substantive ||
        entry.proofKind = ProofKind.constructiveExistential ||
        entry.proofKind = ProofKind.rateComposition))

def suspiciousManifestEntryCount : Nat :=
  manifestEntries.countP (fun entry =>
    entry.proofKind = ProofKind.singleLemmaApplication ||
      entry.proofKind = ProofKind.definitionalUnfold ||
      entry.proofKind = ProofKind.fieldProjection ||
      entry.proofKind = ProofKind.placeholderTruth ||
      entry.proofKind = ProofKind.heuristicOther)

def concreteSubstrateModuleCount : Nat := 11

def bridgeReadyAbstractEntryCount : Nat :=
  manifestEntries.countP (fun entry =>
    entry.firstPrinciplesStatus = FirstPrinciplesStatus.abstractInterface &&
      match entry.leanModule with
      | "SemanticConvergence.Belief" => true
      | "SemanticConvergence.Boundary" => true
      | "SemanticConvergence.Foundations" => true
      | "SemanticConvergence.Functional" => true
      | "SemanticConvergence.Hierarchy" => true
      | "SemanticConvergence.Noise" => true
      | "SemanticConvergence.Rates" => true
      | "SemanticConvergence.SelfReference" => true
      | "SemanticConvergence.Semantic" => true
      | "SemanticConvergence.Surrogate" => true
      | _ => false)

def unlabeledEntryCount : Nat :=
  manifestEntries.foldl
    (fun acc entry => if entry.texLabel.startsWith "auto__" then acc + 1 else acc)
    0

theorem derivedEntryCount_eq : derivedEntryCount = 106 := by
  native_decide

theorem wrappedEntryCount_eq : wrappedEntryCount = 0 := by
  native_decide

theorem declaredEntryCount_eq : declaredEntryCount = 0 := by
  native_decide

theorem concreteStackEntryCount_eq : concreteStackEntryCount = 106 := by
  native_decide

theorem abstractInterfaceEntryCount_eq : abstractInterfaceEntryCount = 0 := by
  native_decide

theorem migratedToConcreteEntryCount_eq : migratedToConcreteEntryCount = 106 := by
  native_decide

theorem pendingConcreteMigrationEntryCount_eq : pendingConcreteMigrationEntryCount = 0 := by
  native_decide

theorem substantiveEntryCount_eq : substantiveEntryCount = 64 := by
  native_decide

theorem definitionProofEntryCount_eq : definitionProofEntryCount = 28 := by
  native_decide

theorem constructiveExistentialEntryCount_eq : constructiveExistentialEntryCount = 10 := by
  native_decide

theorem rateCompositionEntryCount_eq : rateCompositionEntryCount = 2 := by
  native_decide

theorem singleLemmaApplicationEntryCount_eq : singleLemmaApplicationEntryCount = 2 := by
  native_decide

theorem definitionalUnfoldEntryCount_eq : definitionalUnfoldEntryCount = 0 := by
  native_decide

theorem fieldProjectionEntryCount_eq : fieldProjectionEntryCount = 0 := by
  native_decide

theorem placeholderTruthEntryCount_eq : placeholderTruthEntryCount = 0 := by
  native_decide

theorem heuristicOtherEntryCount_eq : heuristicOtherEntryCount = 0 := by
  native_decide

theorem manifestDefinitionEntryCount_eq : manifestDefinitionEntryCount = 28 := by
  native_decide

theorem manifestDefinitionEntriesTaggedAsDefinitionCount_eq : manifestDefinitionEntriesTaggedAsDefinitionCount = 28 := by
  native_decide

theorem manifestTheoremLikeEntryCount_eq : manifestTheoremLikeEntryCount = 78 := by
  native_decide

theorem manifestTheoremLikeSemanticallyAuditedEntryCount_eq : manifestTheoremLikeSemanticallyAuditedEntryCount = 76 := by
  native_decide

theorem suspiciousManifestEntryCount_eq : suspiciousManifestEntryCount = 2 := by
  native_decide

theorem concreteSubstrateModuleCount_eq : concreteSubstrateModuleCount = 11 := rfl

theorem bridgeReadyAbstractEntryCount_eq : bridgeReadyAbstractEntryCount = 0 := by
  native_decide

def moduleAbstractInterfaceEntryCount (moduleName : String) : Nat :=
  manifestEntries.countP (fun entry =>
    entry.leanModule = moduleName &&
      entry.firstPrinciplesStatus = FirstPrinciplesStatus.abstractInterface)

def modulePendingConcreteMigrationEntryCount (moduleName : String) : Nat :=
  manifestEntries.countP (fun entry =>
    entry.leanModule = moduleName &&
      entry.migrationStatus = MigrationStatus.pendingConcreteMigration)

def moduleFirstPrinciplesClosed (moduleName : String) : Bool :=
  modulePendingConcreteMigrationEntryCount moduleName = 0

theorem unlabeledEntryCount_eq : unlabeledEntryCount = 0 := by
  native_decide

def paperFullyCovered : Bool :=
  declaredEntryCount = 0 && unlabeledEntryCount = 0

def paperFullyDerived : Bool :=
  wrappedEntryCount = 0 && paperFullyCovered

def semanticAuditClosed : Bool :=
  suspiciousManifestEntryCount = 0 &&
    manifestDefinitionEntriesTaggedAsDefinitionCount = manifestDefinitionEntryCount &&
    manifestTheoremLikeSemanticallyAuditedEntryCount = manifestTheoremLikeEntryCount

def fullyCovered : Bool :=
  paperFullyCovered

def fullyDerived : Bool :=
  paperFullyDerived

def fullyFirstPrinciples : Bool :=
  abstractInterfaceEntryCount = 0 && paperFullyDerived && semanticAuditClosed

theorem paperFullyCovered_eq : paperFullyCovered = true := by
  native_decide

theorem paperFullyDerived_eq : paperFullyDerived = true := by
  native_decide

theorem semanticAuditClosed_eq : semanticAuditClosed = false := by
  native_decide

theorem fullyCovered_eq : fullyCovered = paperFullyCovered := rfl

theorem fullyDerived_eq : fullyDerived = paperFullyDerived := rfl

theorem fullyFirstPrinciples_eq : fullyFirstPrinciples = false := by
  native_decide

end SemanticConvergence
