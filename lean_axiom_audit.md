# Lean Axiom Audit

This file is generated from the actual output of:

`lake env lean SemanticConvergence/AxiomAudit.lean`

- Manifest-tracked declarations audited: `112`
- Canonical baseline: `['propext', 'Classical.choice', 'Quot.sound']`
- Rows matching the canonical baseline: `78`
- Rows using the expected `native_decide` auxiliary `SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2`: `25`
- Rows lighter than the canonical baseline: `9`
- Rows with genuine unexpected axiom drift: `0`
- While substantive sources still use `native_decide`, the generated audit treats the compiled helper axiom as expected rather than as genuine drift.

## Expected `native_decide` Auxiliary Dependencies

These rows differ from the canonical baseline only by the compiled helper axiom introduced by `native_decide`; they are expected until the underlying `native_decide` proofs are removed.

| Label | Qualified declaration | Axioms |
| --- | --- | --- |
| `def:class-complement` | `SemanticConvergence.def_class_complement` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `def:semantic-separation` | `SemanticConvergence.def_semantic_separation` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `def:semantic-gain` | `SemanticConvergence.def_semantic_gain` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `lem:odds-identity` | `SemanticConvergence.lem_odds_identity` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `lem:zero-criterion` | `SemanticConvergence.lem_zero_criterion` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `prop:chernoff-correspondence` | `SemanticConvergence.prop_chernoff_correspondence` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `prop:noise-immunity` | `SemanticConvergence.prop_noise_immunity` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `cor:noise-transfer` | `SemanticConvergence.zeroOutRatePackage_decodableNoiseTransfer` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `def:sep-condition` | `SemanticConvergence.def_sep_condition` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `def:uniform-history-independent-separation` | `SemanticConvergence.def_uniform_history_independent_separation` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `prop:uniform-history-independent-implies-semantic` | `SemanticConvergence.prop_uniform_history_independent_implies_semantic` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `cor:kl-implies-semantic-separation` | `SemanticConvergence.cor_kl_implies_semantic_separation` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `cor:event-witness-implies-semantic-separation` | `SemanticConvergence.cor_event_witness_implies_semantic_separation` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `def:kernel-sep-condition` | `SemanticConvergence.def_kernel_sep_condition` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `prop:finite-action-kernel-separation` | `SemanticConvergence.prop_finite_action_kernel_separation` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `def:zero-out-rate-package` | `SemanticConvergence.ZeroOutRatePackage` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `thm:separating-support-rate` | `SemanticConvergence.zeroOutRatePackage_residualRate` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `cor:separating-support-finite-time` | `SemanticConvergence.zeroOutRatePackage_posteriorShareFiniteTime` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `cor:support-necessary` | `SemanticConvergence.cor_support_necessary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `thm:summable-support-insufficient` | `SemanticConvergence.thm_summable_support_insufficient` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `lem:one-step-drift` | `SemanticConvergence.zeroOutRatePackage_oneStepResidual` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `prop:exp-rate` | `SemanticConvergence.zeroOutRatePackage_expRate` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `prop:kernel-exp-rate` | `SemanticConvergence.zeroOutRatePackage_sameViewResidualRate` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `thm:exp-rate-concentration` | `SemanticConvergence.zeroOutRatePackage_sameViewPosteriorShareFiniteTime` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |
| `cor:amortized-surrogate-finite-time` | `SemanticConvergence.cor_amortized_surrogate_finite_time_zeroOutPackage` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` |

## Lighter-than-Baseline Dependencies

These rows depend on a strict subset of the canonical baseline axioms, so they are benign deviations rather than new trust-boundary growth.

| Label | Qualified declaration | Axioms |
| --- | --- | --- |
| `def:observer` | `SemanticConvergence.def_observer` | `[]` |
| `def:semantic-rule` | `SemanticConvergence.def_semantic_rule` | `['propext', 'Quot.sound']` |
| `def:promotion-supporting` | `SemanticConvergence.def_promotion_supporting` | `['propext', 'Quot.sound']` |
| `def:kernel-semantic-rule` | `SemanticConvergence.def_kernel_semantic_rule` | `['propext', 'Quot.sound']` |
| `def:decodable-channel` | `SemanticConvergence.def_decodable_channel` | `['propext', 'Quot.sound']` |
| `def:left-invertible-channel` | `SemanticConvergence.def_left_invertible_channel` | `['propext', 'Quot.sound']` |
| `prop:noise-left-invertible` | `SemanticConvergence.prop_noise_left_invertible` | `['propext', 'Quot.sound']` |
| `prop:noise-decoding` | `SemanticConvergence.prop_noise_decoding` | `['propext', 'Quot.sound']` |
| `prop:full-support-behavioral` | `SemanticConvergence.prop_full_support_behavioral` | `['propext', 'Quot.sound']` |

## Genuine Unexpected Dependencies

Only rows in this section count as real axiom drift beyond the published baseline.

None.

## Per-Declaration Table

| Label | Kind | Module | Qualified declaration | Proof kind | Axiom status | Axioms | Matches canonical baseline |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `def:history-compat` | `definition` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.def_history_compat` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:policy-pred` | `definition` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.def_policy_pred` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:int-sem-class` | `definition` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.def_int_sem_class` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:observer` | `definition` | `SemanticConvergence.Foundations` | `SemanticConvergence.def_observer` | `definition` | `lighter-than-baseline` | `[]` | `no` |
| `lem:nesting` | `lemma` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.lem_nesting` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:refinement-chain` | `proposition` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.prop_refinement_chain` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:observable-quotient` | `lemma` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.lem_observable_quotient` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:history-recoverable` | `definition` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.def_history_recoverable` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:factor-through-quotient` | `theorem` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.thm_factor_through_quotient` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:strict-hierarchy-witnesses` | `definition` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.HierarchyWitnesses` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:fit-gap` | `lemma` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.lem_fit_gap` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:policy-gap` | `theorem` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.thm_policy_gap` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:syntactic-gap` | `lemma` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.lem_syntactic_gap` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:strict-hierarchy` | `theorem` | `SemanticConvergence.Hierarchy` | `SemanticConvergence.thm_strict_hierarchy` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:bhat-omega` | `definition` | `SemanticConvergence.Functional` | `SemanticConvergence.def_bhat_omega` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:raw-two-observer-functional` | `definition` | `SemanticConvergence.Functional` | `SemanticConvergence.def_raw_two_observer_functional` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:two-observer-functional` | `definition` | `SemanticConvergence.Functional` | `SemanticConvergence.def_two_observer_functional` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:two-observer-minimizer` | `proposition` | `SemanticConvergence.Belief` | `SemanticConvergence.prop_two_observer_minimizer` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:kernel-functional` | `definition` | `SemanticConvergence.Functional` | `SemanticConvergence.def_kernel_functional` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:kernel-functional-minimizer` | `proposition` | `SemanticConvergence.Belief` | `SemanticConvergence.prop_kernel_functional_minimizer` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:kernel-functional-minimizer-compact` | `proposition` | `SemanticConvergence.Belief` | `SemanticConvergence.prop_kernel_functional_minimizer_compact` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:meeting-point-shorthand` | `definition` | `SemanticConvergence.Functional` | `SemanticConvergence.def_meeting_point_shorthand` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:belief-invariance-above` | `proposition` | `SemanticConvergence.Functional` | `SemanticConvergence.prop_belief_invariance_above` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:belief-illtyped-below` | `proposition` | `SemanticConvergence.Functional` | `SemanticConvergence.prop_belief_illtyped_below` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:action-cap` | `proposition` | `SemanticConvergence.Functional` | `SemanticConvergence.prop_action_cap` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:twins-frozen-ratio` | `corollary` | `SemanticConvergence.Functional` | `SemanticConvergence.cor_twins_frozen_ratio` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:meeting-point` | `theorem` | `SemanticConvergence.Functional` | `SemanticConvergence.thm_meeting_point` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:canonical-pair` | `corollary` | `SemanticConvergence.Functional` | `SemanticConvergence.cor_canonical_pair` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:goal-dialed` | `proposition` | `SemanticConvergence.Functional` | `SemanticConvergence.prop_goal_dialed` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:universal-prior` | `definition` | `SemanticConvergence.Functional` | `SemanticConvergence.def_universal_prior` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:prior-invariance` | `lemma` | `SemanticConvergence.Belief` | `SemanticConvergence.lem_prior_invariance` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:prior-necessity` | `lemma` | `SemanticConvergence.Belief` | `SemanticConvergence.lem_prior_necessity` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:afe` | `definition` | `SemanticConvergence.Functional` | `SemanticConvergence.def_afe` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:variational` | `lemma` | `SemanticConvergence.Belief` | `SemanticConvergence.lem_variational` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:kl-necessity` | `lemma` | `SemanticConvergence.Belief` | `SemanticConvergence.lem_kl_necessity` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:merging` | `lemma` | `SemanticConvergence.Belief` | `SemanticConvergence.lem_merging` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:class-complement` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_class_complement` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `def:semantic-separation` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_semantic_separation` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `def:semantic-gain` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_semantic_gain` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `lem:odds-identity` | `lemma` | `SemanticConvergence.Semantic` | `SemanticConvergence.lem_odds_identity` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `lem:zero-criterion` | `lemma` | `SemanticConvergence.Semantic` | `SemanticConvergence.lem_zero_criterion` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `prop:chernoff-correspondence` | `proposition` | `SemanticConvergence.Semantic` | `SemanticConvergence.prop_chernoff_correspondence` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `def:semantic-rule` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_semantic_rule` | `definition` | `lighter-than-baseline` | `['propext', 'Quot.sound']` | `no` |
| `def:promotion-supporting` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_promotion_supporting` | `definition` | `lighter-than-baseline` | `['propext', 'Quot.sound']` | `no` |
| `prop:semantic-is-promotion-supporting` | `proposition` | `SemanticConvergence.Semantic` | `SemanticConvergence.prop_semantic_is_promotion_supporting` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:kernel-semantic-rule` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_kernel_semantic_rule` | `definition` | `lighter-than-baseline` | `['propext', 'Quot.sound']` | `no` |
| `prop:kernel-promotion-support` | `proposition` | `SemanticConvergence.Semantic` | `SemanticConvergence.prop_kernel_promotion_support` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:kernel-promotion-support-compact` | `proposition` | `SemanticConvergence.Semantic` | `SemanticConvergence.prop_kernel_promotion_support_compact` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:decodable-channel` | `definition` | `SemanticConvergence.Noise` | `SemanticConvergence.def_decodable_channel` | `definition` | `lighter-than-baseline` | `['propext', 'Quot.sound']` | `no` |
| `prop:noise-immunity` | `proposition` | `SemanticConvergence.Noise` | `SemanticConvergence.prop_noise_immunity` | `substantive` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `def:left-invertible-channel` | `definition` | `SemanticConvergence.Noise` | `SemanticConvergence.def_left_invertible_channel` | `definition` | `lighter-than-baseline` | `['propext', 'Quot.sound']` | `no` |
| `prop:noise-left-invertible` | `proposition` | `SemanticConvergence.Noise` | `SemanticConvergence.prop_noise_left_invertible` | `constructive-existential` | `lighter-than-baseline` | `['propext', 'Quot.sound']` | `no` |
| `prop:noise-decoding` | `proposition` | `SemanticConvergence.Noise` | `SemanticConvergence.prop_noise_decoding` | `substantive` | `lighter-than-baseline` | `['propext', 'Quot.sound']` | `no` |
| `cor:noise-transfer` | `corollary` | `SemanticConvergence.Noise` | `SemanticConvergence.zeroOutRatePackage_decodableNoiseTransfer` | `rate-composition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `cor:noise-left-invertible-history-independent` | `corollary` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_support_left_invertible_noisy_transfer` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:sep-condition` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_sep_condition` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `def:uniform-history-independent-separation` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_uniform_history_independent_separation` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `prop:uniform-history-independent-implies-semantic` | `proposition` | `SemanticConvergence.Semantic` | `SemanticConvergence.prop_uniform_history_independent_implies_semantic` | `substantive` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `cor:kl-implies-semantic-separation` | `corollary` | `SemanticConvergence.Semantic` | `SemanticConvergence.cor_kl_implies_semantic_separation` | `substantive` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `cor:event-witness-implies-semantic-separation` | `corollary` | `SemanticConvergence.Semantic` | `SemanticConvergence.cor_event_witness_implies_semantic_separation` | `substantive` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `def:kernel-sep-condition` | `definition` | `SemanticConvergence.Semantic` | `SemanticConvergence.def_kernel_sep_condition` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `prop:finite-action-kernel-separation` | `proposition` | `SemanticConvergence.Semantic` | `SemanticConvergence.prop_finite_action_kernel_separation` | `substantive` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `prop:compact-action-kernel-separation` | `proposition` | `SemanticConvergence.Semantic` | `SemanticConvergence.prop_compact_action_kernel_separation` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:conditional-bc` | `lemma` | `SemanticConvergence.Semantic` | `SemanticConvergence.lem_conditional_bc` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:hellinger-spine` | `definition` | `SemanticConvergence.MartingaleContraction` | `SemanticConvergence.HellingerConvergenceSpine` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:contraction` | `lemma` | `SemanticConvergence.Semantic` | `SemanticConvergence.lem_contraction` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:full-support-behavioral` | `proposition` | `SemanticConvergence.Semantic` | `SemanticConvergence.prop_full_support_behavioral` | `substantive` | `lighter-than-baseline` | `['propext', 'Quot.sound']` | `no` |
| `def:semantic-learning-package` | `definition` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.def_semantic_learning_package` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `ass:main-verified-package` | `assumptions` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.ass_main_verified_package` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:separating-support-convergence` | `theorem` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_verified_semantic_learning_package_converges` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:infinite-affinity-hellinger-bridge` | `theorem` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_infinite_affinity_hellinger_bridge` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:zero-out-rate-package` | `definition` | `SemanticConvergence.Rates` | `SemanticConvergence.ZeroOutRatePackage` | `definition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `thm:exploration-floor-behavioral` | `theorem` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_exploration_floor_behavioral` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:separating-support-rate` | `theorem` | `SemanticConvergence.Rates` | `SemanticConvergence.zeroOutRatePackage_residualRate` | `rate-composition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `cor:separating-support-finite-time` | `corollary` | `SemanticConvergence.Rates` | `SemanticConvergence.zeroOutRatePackage_posteriorShareFiniteTime` | `rate-composition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `thm:semantic-convergence` | `theorem` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_semantic_convergence` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:kernel-semantic-convergence` | `theorem` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_kernel_semantic_convergence` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:compact-action-kernel` | `corollary` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_compact_action_kernel` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:finite-maximin` | `corollary` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_finite_maximin` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:support-necessary` | `theorem` | `SemanticConvergence.Semantic` | `SemanticConvergence.cor_support_necessary` | `constructive-existential` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `thm:summable-support-insufficient` | `theorem` | `SemanticConvergence.Semantic` | `SemanticConvergence.thm_summable_support_insufficient` | `constructive-existential` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `lem:one-step-drift` | `lemma` | `SemanticConvergence.Rates` | `SemanticConvergence.zeroOutRatePackage_oneStepResidual` | `rate-composition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `prop:exp-rate` | `proposition` | `SemanticConvergence.Rates` | `SemanticConvergence.zeroOutRatePackage_expRate` | `rate-composition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `lem:one-step-drift-kernel` | `lemma` | `SemanticConvergence.Rates` | `SemanticConvergence.lem_one_step_drift_kernel` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:kernel-exp-rate` | `proposition` | `SemanticConvergence.Rates` | `SemanticConvergence.zeroOutRatePackage_sameViewResidualRate` | `rate-composition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `thm:exp-rate-concentration` | `theorem` | `SemanticConvergence.Rates` | `SemanticConvergence.zeroOutRatePackage_sameViewPosteriorShareFiniteTime` | `rate-composition` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
| `cor:goal-dialed-payoff` | `corollary` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_goal_dialed_payoff` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:finite-time-policy-observer` | `definition` | `SemanticConvergence.SelfReference` | `SemanticConvergence.def_finite_time_policy_observer` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:monotone-refinement` | `lemma` | `SemanticConvergence.SelfReference` | `SemanticConvergence.lem_monotone_refinement` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:self-ref-rule` | `definition` | `SemanticConvergence.SelfReference` | `SemanticConvergence.def_self_ref_rule` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:exploration-reachability` | `lemma` | `SemanticConvergence.SelfReference` | `SemanticConvergence.lem_exploration_reachability` | `constructive-existential` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:observer-promotion-sr` | `proposition` | `SemanticConvergence.SelfReference` | `SemanticConvergence.prop_observer_promotion_sr` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:self-ref-convergence` | `theorem` | `SemanticConvergence.SelfReference` | `SemanticConvergence.thm_self_ref_convergence` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:self-ref-obstruction` | `proposition` | `SemanticConvergence.SelfReference` | `SemanticConvergence.prop_self_ref_obstruction` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:self-ref-exploratory` | `definition` | `SemanticConvergence.SelfReference` | `SemanticConvergence.def_self_ref_exploratory` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:self-ref-exploratory` | `theorem` | `SemanticConvergence.SelfReference` | `SemanticConvergence.thm_self_ref_exploratory` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:self-ref-exploratory-rate` | `theorem` | `SemanticConvergence.SelfReference` | `SemanticConvergence.thm_self_ref_exploratory_rate` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:self-ref-one-step-split` | `proposition` | `SemanticConvergence.SelfReference` | `SemanticConvergence.prop_self_ref_one_step_split` | `constructive-existential` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:self-ref-sharp` | `theorem` | `SemanticConvergence.SelfReference` | `SemanticConvergence.thm_self_ref_sharp` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:boundary-identity` | `proposition` | `SemanticConvergence.Boundary` | `SemanticConvergence.prop_boundary_identity` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:efe` | `definition` | `SemanticConvergence.Boundary` | `SemanticConvergence.def_efe` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:risk-ig` | `lemma` | `SemanticConvergence.Boundary` | `SemanticConvergence.lem_risk_ig` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:efe-specialization` | `corollary` | `SemanticConvergence.Boundary` | `SemanticConvergence.cor_efe_specialization` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `def:afe-principle` | `definition` | `SemanticConvergence.Boundary` | `SemanticConvergence.def_afe_principle` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `lem:info-decomp` | `lemma` | `SemanticConvergence.Boundary` | `SemanticConvergence.lem_info_decomp` | `definition` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:afe-near-miss` | `theorem` | `SemanticConvergence.Boundary` | `SemanticConvergence.thm_afe_near_miss` | `constructive-existential` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:observer-promotion-failure` | `theorem` | `SemanticConvergence.Boundary` | `SemanticConvergence.thm_observer_promotion_failure` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:observer-promotion-universal` | `corollary` | `SemanticConvergence.Boundary` | `SemanticConvergence.cor_observer_promotion_universal` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:promotion-contrast` | `corollary` | `SemanticConvergence.Boundary` | `SemanticConvergence.cor_promotion_contrast` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `prop:amortized-surrogate-minimizer` | `proposition` | `SemanticConvergence.Surrogate` | `SemanticConvergence.prop_amortized_surrogate_minimizer` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `thm:amortized-surrogate` | `theorem` | `SemanticConvergence.Ontology` | `SemanticConvergence.Ontology.Coupling.h10_amortized_surrogate` | `substantive` | `canonical-baseline` | `['propext', 'Classical.choice', 'Quot.sound']` | `yes` |
| `cor:amortized-surrogate-finite-time` | `corollary` | `SemanticConvergence.Surrogate` | `SemanticConvergence.cor_amortized_surrogate_finite_time_zeroOutPackage` | `substantive` | `expected-native-decide-auxiliary` | `['propext', 'Classical.choice', 'Quot.sound', 'SemanticConvergence.listWeightedSum_ne_zero_exists._native.native_decide.ax_1_2']` | `no` |
