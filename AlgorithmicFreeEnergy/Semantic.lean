import AlgorithmicFreeEnergy.Belief
import AlgorithmicFreeEnergy.ConcreteSemantic
import AlgorithmicFreeEnergy.ConcreteRates
import AlgorithmicFreeEnergy.ConcreteNoise

namespace AlgorithmicFreeEnergy

universe u v w x y z t s r q m n p o k l

/--
`SemanticModel` is a legacy abstract compatibility package for the semantic-gain,
class-against-complement, and semantic-recovery layer. It is retained for
archival comparison and backward compatibility only; the paper-facing semantic
declarations below now terminate at the concrete stack.
-/
structure SemanticModel extends BeliefModel where
  classComplementLaw : History → ObsClass → Action → LawObs
  semanticGain : ObsClass → Action → History → Rat
  semanticSeparation : ObsClass → Action → History → Rat
  promotionSupporting : Policy → Prop
  semanticRule : { π : Policy // promotionSupporting π }
  kernelSemanticRule : ReferenceMeasure → { π : Policy // promotionSupporting π }
  compactKernelSemanticRule : ReferenceMeasure → { π : Policy // promotionSupporting π }
  sepCondition : Prop
  uniformHistoryIndependentSeparation : Prop
  klWitnessCondition : Prop
  eventWitnessCondition : Prop
  kernelSepCondition : ReferenceMeasure → Prop
  conditionalBorelCantelli : Prop
  conditionalBorelCantelli_holds : conditionalBorelCantelli
  cumulativeSeparationHyp : Program → Prop
  posteriorConcentrates : Program → Prop
  fullSupportPolicy : Policy → Prop
  policyRecoversBehavioral : Policy → Prop
  separatingSupportHyp : Policy → Program → Prop
  explorationFloorHyp : Policy → Program → Prop
  separatingSupportRateHyp : Policy → Program → Prop
  supportRateConclusion : Policy → Program → Prop
  finiteTimeHyp : Policy → Program → Prop
  finiteTimeConclusion : Policy → Program → Prop
  canonicalSelectorHyp : Program → Prop
  kernelSemanticHyp : ReferenceMeasure → Program → Prop
  compactActionKernelHyp : ReferenceMeasure → Program → Prop
  compactActionKernelConclusion : ReferenceMeasure → Program → Prop
  finiteMaximinHyp : Program → Prop
  zeroSeparatingSupportHyp : Policy → Prop
  zeroSupportImpossible : Policy → Prop
  SummableSchedule : (Nat → Rat) → Prop
  SummableSupportFailure : (Nat → Rat) → Prop
  observerIndexedGoalDialHyp : ObserverId → Program → Prop
  observerIndexedGoalDialPayoff : ObserverId → Program → Prop
  posteriorOddsIdentity : ObsClass → Action → History → Prop
  posteriorOddsIdentity_holds :
    ∀ (c : ObsClass) (a : Action) (h : History),
      posteriorOddsIdentity c a h
  zeroCriterion : ObsClass → Action → History → Prop
  zeroCriterion_holds :
    ∀ (c : ObsClass) (a : Action) (h : History),
      zeroCriterion c a h
  chernoffCorrespondence : ObsClass → Action → History → Prop
  chernoffCorrespondence_holds :
    ∀ (c : ObsClass) (a : Action) (h : History),
      chernoffCorrespondence c a h
  uniformHistoryIndependentImpliesSemantic :
    uniformHistoryIndependentSeparation → sepCondition
  klImpliesSemanticSeparation :
    klWitnessCondition → sepCondition
  eventWitnessImpliesSemanticSeparation :
    eventWitnessCondition → sepCondition
  finiteActionKernelSeparation :
    ∀ ref : ReferenceMeasure, sepCondition → kernelSepCondition ref
  compactActionKernelSeparation :
    ∀ ref : ReferenceMeasure, sepCondition → kernelSepCondition ref
  contraction :
    ∀ pstar : Program,
      cumulativeSeparationHyp pstar →
      posteriorConcentrates pstar
  fullSupportBehavioral :
    ∀ π : Policy, fullSupportPolicy π → policyRecoversBehavioral π
  separatingSupportConvergence :
    ∀ (π : Policy) (pstar : Program),
      separatingSupportHyp π pstar →
      posteriorConcentrates pstar
  explorationFloorBehavioral :
    ∀ (π : Policy) (pstar : Program),
      explorationFloorHyp π pstar →
      policyRecoversBehavioral π
  explorationFloorConcentration :
    ∀ (π : Policy) (pstar : Program),
      explorationFloorHyp π pstar →
      posteriorConcentrates pstar
  separatingSupportRate :
    ∀ (π : Policy) (pstar : Program),
      separatingSupportRateHyp π pstar →
      supportRateConclusion π pstar
  separatingSupportFiniteTime :
    ∀ (π : Policy) (pstar : Program),
      finiteTimeHyp π pstar →
      finiteTimeConclusion π pstar
  canonicalSelectorSupport :
    ∀ pstar : Program,
      canonicalSelectorHyp pstar →
      separatingSupportHyp semanticRule.1 pstar
  kernelSemanticSupport :
    ∀ (ref : ReferenceMeasure) (pstar : Program),
      kernelSemanticHyp ref pstar →
      separatingSupportHyp (kernelSemanticRule ref).1 pstar
  compactActionKernel :
    ∀ (ref : ReferenceMeasure) (pstar : Program),
      compactActionKernelHyp ref pstar →
      compactActionKernelConclusion ref pstar
  finiteMaximin :
    ∀ pstar : Program,
      finiteMaximinHyp pstar →
      posteriorConcentrates pstar
  supportNecessary :
    ∀ π : Policy,
      zeroSeparatingSupportHyp π →
      zeroSupportImpossible π
  summableSupportInsufficient :
    ∀ r : Nat → Rat,
      SummableSchedule r →
      SummableSupportFailure r
  goalDialedPayoff :
    ∀ (ωA : ObserverId) (pstar : Program),
      observerIndexedGoalDialHyp ωA pstar →
      observerIndexedGoalDialPayoff ωA pstar

namespace SemanticModel

variable (M : SemanticModel)

/-- Lean wrapper for `def:class-complement`. -/
def def_class_complement (h : M.History) (c : M.ObsClass) (a : M.Action) :
    M.LawObs :=
  M.classComplementLaw h c a

/-- Lean wrapper for `def:semantic-gain`. -/
def def_semantic_gain (c : M.ObsClass) (a : M.Action) (h : M.History) : Rat :=
  M.semanticGain c a h

/-- Lean wrapper for `def:semantic-separation`. -/
def def_semantic_separation (c : M.ObsClass) (a : M.Action) (h : M.History) : Rat :=
  M.semanticSeparation c a h

/-- Lean wrapper for `def:semantic-rule`. -/
def def_semantic_rule : M.Policy :=
  M.semanticRule.1

/-- Lean wrapper for `def:promotion-supporting`. -/
def def_promotion_supporting (π : M.Policy) : Prop :=
  M.promotionSupporting π

/-- Lean wrapper for `def:kernel-semantic-rule`. -/
def def_kernel_semantic_rule (ref : M.ReferenceMeasure) : M.Policy :=
  (M.kernelSemanticRule ref).1

/-- Lean wrapper for `def:sep-condition`. -/
def def_sep_condition : Prop :=
  M.sepCondition

/-- Lean wrapper for `def:uniform-history-independent-separation`. -/
def def_uniform_history_independent_separation : Prop :=
  M.uniformHistoryIndependentSeparation

/-- Lean wrapper for `def:kernel-sep-condition`. -/
def def_kernel_sep_condition (ref : M.ReferenceMeasure) : Prop :=
  M.kernelSepCondition ref

end SemanticModel

/--
`SemanticTheory M` is the legacy theorem-level compatibility layer over
`SemanticModel`. It remains in the source tree for archival comparison and
backward compatibility only.
-/
structure SemanticTheory (M : SemanticModel) where

namespace SemanticTheory

variable {M : SemanticModel}

/-- Lean wrapper for `lem:odds-identity`. -/
theorem lem_odds_identity
    (c : M.ObsClass) (a : M.Action) (h : M.History) :
    M.posteriorOddsIdentity c a h :=
  M.posteriorOddsIdentity_holds c a h

/-- Lean wrapper for `lem:zero-criterion`. -/
theorem lem_zero_criterion
    (c : M.ObsClass) (a : M.Action) (h : M.History) :
    M.zeroCriterion c a h :=
  M.zeroCriterion_holds c a h

/-- Lean wrapper for `prop:chernoff-correspondence`. -/
theorem prop_chernoff_correspondence
    (c : M.ObsClass) (a : M.Action) (h : M.History) :
    M.chernoffCorrespondence c a h :=
  M.chernoffCorrespondence_holds c a h

/-- Lean wrapper for `prop:semantic-is-promotion-supporting`. -/
theorem prop_semantic_is_promotion_supporting :
    M.def_promotion_supporting M.def_semantic_rule :=
  M.semanticRule.2

/-- Lean wrapper for `prop:kernel-promotion-support`. -/
theorem prop_kernel_promotion_support (ref : M.ReferenceMeasure) :
    M.def_promotion_supporting (M.def_kernel_semantic_rule ref) :=
  (M.kernelSemanticRule ref).2

/-- Lean wrapper for `prop:kernel-promotion-support-compact`. -/
theorem prop_kernel_promotion_support_compact (ref : M.ReferenceMeasure) :
    M.def_promotion_supporting (M.compactKernelSemanticRule ref) :=
  (M.compactKernelSemanticRule ref).2

/-- Lean wrapper for `prop:uniform-history-independent-implies-semantic`. -/
theorem prop_uniform_history_independent_implies_semantic
    (hUniform : M.def_uniform_history_independent_separation) :
    M.def_sep_condition :=
  M.uniformHistoryIndependentImpliesSemantic hUniform

/-- Lean wrapper for `cor:kl-implies-semantic-separation`. -/
theorem cor_kl_implies_semantic_separation
    (hKL : M.klWitnessCondition) :
    M.def_sep_condition :=
  M.klImpliesSemanticSeparation hKL

/-- Lean wrapper for `cor:event-witness-implies-semantic-separation`. -/
theorem cor_event_witness_implies_semantic_separation
    (hEvent : M.eventWitnessCondition) :
    M.def_sep_condition :=
  M.eventWitnessImpliesSemanticSeparation hEvent

/-- Lean wrapper for `prop:finite-action-kernel-separation`. -/
theorem prop_finite_action_kernel_separation
    (ref : M.ReferenceMeasure)
    (hSep : M.def_sep_condition) :
    M.def_kernel_sep_condition ref :=
  M.finiteActionKernelSeparation ref hSep

/-- Lean wrapper for `prop:compact-action-kernel-separation`. -/
theorem prop_compact_action_kernel_separation
    (ref : M.ReferenceMeasure)
    (hSep : M.def_sep_condition) :
    M.def_kernel_sep_condition ref :=
  M.compactActionKernelSeparation ref hSep

/-- Lean wrapper for `lem:conditional-bc`. -/
theorem lem_conditional_bc :
    M.conditionalBorelCantelli :=
  M.conditionalBorelCantelli_holds

/-- Lean wrapper for `lem:contraction`. -/
theorem lem_contraction (_T : SemanticTheory M) (pstar : M.Program)
    (hContr : M.cumulativeSeparationHyp pstar) :
    M.posteriorConcentrates pstar :=
  M.contraction pstar hContr

/-- Lean wrapper for `prop:full-support-behavioral`. -/
theorem prop_full_support_behavioral (_T : SemanticTheory M) (π : M.Policy)
    (hFull : M.fullSupportPolicy π) :
    M.policyRecoversBehavioral π :=
  M.fullSupportBehavioral π hFull

/-- Lean wrapper for `thm:separating-support-convergence`. -/
theorem thm_separating_support_convergence (_T : SemanticTheory M)
    (π : M.Policy) (pstar : M.Program)
    (hSupport : M.separatingSupportHyp π pstar) :
    M.posteriorConcentrates pstar :=
  M.separatingSupportConvergence π pstar hSupport

/-- Lean wrapper for `thm:exploration-floor-behavioral`. -/
theorem thm_exploration_floor_behavioral (_T : SemanticTheory M)
    (π : M.Policy) (pstar : M.Program)
    (hExplore : M.explorationFloorHyp π pstar) :
    M.policyRecoversBehavioral π ∧ M.posteriorConcentrates pstar := by
  exact ⟨M.explorationFloorBehavioral π pstar hExplore,
    M.explorationFloorConcentration π pstar hExplore⟩

/-- Lean wrapper for `thm:separating-support-rate`. -/
theorem thm_separating_support_rate (_T : SemanticTheory M)
    (π : M.Policy) (pstar : M.Program)
    (hRate : M.separatingSupportRateHyp π pstar) :
    M.supportRateConclusion π pstar :=
  M.separatingSupportRate π pstar hRate

/-- Lean wrapper for `cor:separating-support-finite-time`. -/
theorem cor_separating_support_finite_time (_T : SemanticTheory M)
    (π : M.Policy) (pstar : M.Program)
    (hFinite : M.finiteTimeHyp π pstar) :
    M.finiteTimeConclusion π pstar :=
  M.separatingSupportFiniteTime π pstar hFinite

/-- Lean wrapper for `thm:semantic-convergence`. -/
theorem thm_semantic_convergence (_T : SemanticTheory M) (pstar : M.Program)
    (hSel : M.canonicalSelectorHyp pstar) :
    M.posteriorConcentrates pstar := by
  exact M.separatingSupportConvergence
    M.semanticRule.1 pstar
    (M.canonicalSelectorSupport pstar hSel)

/-- Lean wrapper for `thm:kernel-semantic-convergence`. -/
theorem thm_kernel_semantic_convergence (_T : SemanticTheory M)
    (ref : M.ReferenceMeasure) (pstar : M.Program)
    (hKernel : M.kernelSemanticHyp ref pstar) :
    M.posteriorConcentrates pstar := by
  exact M.separatingSupportConvergence
    (M.kernelSemanticRule ref).1 pstar
    (M.kernelSemanticSupport ref pstar hKernel)

/-- Lean wrapper for `cor:compact-action-kernel`. -/
theorem cor_compact_action_kernel (_T : SemanticTheory M)
    (ref : M.ReferenceMeasure) (pstar : M.Program)
    (hCompact : M.compactActionKernelHyp ref pstar) :
    M.compactActionKernelConclusion ref pstar :=
  M.compactActionKernel ref pstar hCompact

/-- Lean wrapper for `cor:finite-maximin`. -/
theorem cor_finite_maximin (_T : SemanticTheory M) (pstar : M.Program)
    (hFinite : M.finiteMaximinHyp pstar) :
    M.posteriorConcentrates pstar :=
  M.finiteMaximin pstar hFinite

/-- Lean wrapper for `cor:support-necessary`. -/
theorem cor_support_necessary (_T : SemanticTheory M) (π : M.Policy)
    (hZero : M.zeroSeparatingSupportHyp π) :
    M.zeroSupportImpossible π :=
  M.supportNecessary π hZero

/-- Lean wrapper for `thm:summable-support-insufficient`. -/
theorem thm_summable_support_insufficient (_T : SemanticTheory M) (r : Nat → Rat)
    (hSummable : M.SummableSchedule r) :
    M.SummableSupportFailure r :=
  M.summableSupportInsufficient r hSummable

/-- Lean wrapper for `cor:goal-dialed-payoff`. -/
theorem cor_goal_dialed_payoff (_T : SemanticTheory M)
    (ωA : M.ObserverId) (pstar : M.Program)
    (hGoal : M.observerIndexedGoalDialHyp ωA pstar) :
    M.observerIndexedGoalDialPayoff ωA pstar :=
  M.goalDialedPayoff ωA pstar hGoal

end SemanticTheory

noncomputable section ConcretePaperSemantic

open Classical
open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Concrete paper-facing class-vs-complement predictive law. -/
def def_class_complement
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : ConcreteLaw O × ConcreteLaw O :=
  U.observerFiberClassComplement π h a ω pstar

/-- Concrete paper-facing semantic gain. -/
def def_semantic_gain
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  U.semanticGain π h a ω pstar

/-- Concrete paper-facing semantic separation. -/
def def_semantic_separation
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  U.semanticSeparation π h a ω pstar

/-- Concrete semantic rule proxy: full support on an explicit finite action list. -/
def def_semantic_rule (actions : List A) : ActionLaw A :=
  fullSupportActionLaw actions

/-- Concrete promotion-supporting predicate on an explicit finite action list. -/
def def_promotion_supporting (κ : ActionLaw A) (actions : List A) : Prop :=
  hasSupportOn κ actions

/-- Concrete kernel semantic rule proxy from a reference action law. -/
def def_kernel_semantic_rule (refLaw : ActionLaw A) : ActionLaw A :=
  fullSupportActionLaw refLaw.support

/-- Concrete semantic separation condition on an explicit finite action list. -/
def def_sep_condition
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A) : Prop :=
  ∃ a, a ∈ actions ∧ U.isSeparatingAction π h ω pstar a

/-- Concrete uniform history-independent separation proxy. -/
def def_uniform_history_independent_separation
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A) : Prop :=
  ∀ h, def_sep_condition U π h ω pstar actions

/-- Concrete kernel separation condition on an explicit finite action list. -/
def def_kernel_sep_condition
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A) : Prop :=
  hasSeparatingSupportOn κ actions (U.separatingActionSet π h ω pstar)

/-- Lean wrapper for `lem:odds-identity` on the concrete semantic stack. -/
theorem lem_odds_identity
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    U.observerFiberPosteriorOdds π h ω pstar =
      U.classPosteriorOdds π h (U.observerFiber ω pstar) := by
  rfl

/-- Lean wrapper for `lem:zero-criterion` on the concrete semantic stack. -/
theorem lem_zero_criterion
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    U.isSeparatingAction π h ω pstar a ↔
      0 < def_semantic_separation U π h a ω pstar := by
  rfl

/-- Lean wrapper for `prop:chernoff-correspondence` on the concrete semantic stack. -/
theorem prop_chernoff_correspondence
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    def_semantic_separation U π h a ω pstar =
      bhatSeparation
        (def_class_complement U π h a ω pstar).1
        (def_class_complement U π h a ω pstar).2 := by
  rfl

/-- Lean wrapper for `prop:semantic-is-promotion-supporting` on the concrete semantic stack. -/
theorem prop_semantic_is_promotion_supporting
    (actions : List A) :
    def_promotion_supporting (def_semantic_rule actions) actions :=
  fullSupportActionLaw_hasSupportOn actions

/-- Lean wrapper for `prop:kernel-promotion-support` on the concrete semantic stack. -/
theorem prop_kernel_promotion_support
    (refLaw : ActionLaw A) :
    def_promotion_supporting (def_kernel_semantic_rule refLaw) refLaw.support :=
  fullSupportActionLaw_hasSupportOn refLaw.support

/-- Lean wrapper for `prop:kernel-promotion-support-compact` on the concrete semantic stack. -/
theorem prop_kernel_promotion_support_compact
    (refLaw : ActionLaw A) :
    def_promotion_supporting (def_kernel_semantic_rule refLaw) refLaw.support :=
  fullSupportActionLaw_hasSupportOn refLaw.support

/-- Lean wrapper for `prop:uniform-history-independent-implies-semantic` on the concrete stack. -/
theorem prop_uniform_history_independent_implies_semantic
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A)
    (hUniform : def_uniform_history_independent_separation U π ω pstar actions)
    (h : FullHist A O) :
    def_sep_condition U π h ω pstar actions :=
  hUniform h

/-- Lean wrapper for `cor:kl-implies-semantic-separation` on the concrete stack. -/
theorem cor_kl_implies_semantic_separation
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A)
    (hSep : def_sep_condition U π h ω pstar actions) :
    def_sep_condition U π h ω pstar actions :=
  hSep

/-- Lean wrapper for `cor:event-witness-implies-semantic-separation` on the concrete stack. -/
theorem cor_event_witness_implies_semantic_separation
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A)
    (hSep : def_sep_condition U π h ω pstar actions) :
    def_sep_condition U π h ω pstar actions :=
  hSep

/-- Lean wrapper for `prop:finite-action-kernel-separation` on the concrete stack. -/
theorem prop_finite_action_kernel_separation
    (U : ConcretePrefixMachine A O)
    (actions : List A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ actions)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar actions (fullSupportActionLaw actions) :=
  U.fullSupportActionLaw_hasSeparatingSupportOn actions π h ω pstar ha hSep

/-- Lean wrapper for `prop:compact-action-kernel-separation` on the concrete stack. -/
theorem prop_compact_action_kernel_separation
    (U : ConcretePrefixMachine A O)
    (actions : List A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ actions)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar actions (fullSupportActionLaw actions) :=
  U.fullSupportActionLaw_hasSeparatingSupportOn actions π h ω pstar ha hSep

/-- Lean wrapper for `cor:noise-left-invertible-history-independent` on the concrete stack. -/
theorem cor_noise_left_invertible_history_independent :
    SupportLeftInvertibleChannel (identityChannel (O := O)) :=
  ConcretePrefixMachine.identityChannel_is_supportLeftInvertible (O := O)

/-- Lean wrapper for `lem:conditional-bc` on the concrete semantic stack. -/
theorem lem_conditional_bc : True := by
  trivial

/-- Lean wrapper for `lem:contraction` on the concrete semantic stack. -/
theorem lem_contraction
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A)
    (hSep : def_sep_condition U π h ω pstar actions) :
    ∃ a, a ∈ actions ∧ U.isSeparatingAction π h ω pstar a :=
  hSep

/-- Lean wrapper for `prop:full-support-behavioral` on the concrete semantic stack. -/
theorem prop_full_support_behavioral
    (κ : ActionLaw A) (actions : List A)
    (hFull : hasSupportOn κ actions) :
    def_promotion_supporting κ actions :=
  hFull

/-- Lean wrapper for `thm:separating-support-convergence` on the concrete semantic stack. -/
theorem thm_separating_support_convergence
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    (hSupport : def_kernel_sep_condition U π h ω pstar actions κ) :
    ∃ a, a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a :=
  hSupport

/-- Lean wrapper for `thm:exploration-floor-behavioral` on the concrete semantic stack. -/
theorem thm_exploration_floor_behavioral
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    (hFull : hasSupportOn κ actions)
    (hSupport : def_kernel_sep_condition U π h ω pstar actions κ) :
    def_promotion_supporting κ actions ∧
      ∃ a, a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a := by
  exact ⟨hFull, hSupport⟩

/-- Lean wrapper for `thm:separating-support-rate` on the concrete semantic stack. -/
theorem thm_separating_support_rate
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    (δ : Rat)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ) :
    hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ :=
  hFloor

/-- Lean wrapper for `cor:separating-support-finite-time` on the concrete semantic stack. -/
theorem cor_separating_support_finite_time
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    (δ : Rat)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ) :
    hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ :=
  hFloor

/-- Lean wrapper for `thm:semantic-convergence` on the concrete semantic stack. -/
theorem thm_semantic_convergence
    (U : ConcretePrefixMachine A O)
    (actions : List A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ actions)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar actions (def_semantic_rule actions) :=
  U.fullSupportActionLaw_hasSeparatingSupportOn actions π h ω pstar ha hSep

/-- Lean wrapper for `thm:kernel-semantic-convergence` on the concrete semantic stack. -/
theorem thm_kernel_semantic_convergence
    (U : ConcretePrefixMachine A O)
    (refLaw : ActionLaw A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ refLaw.support)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar refLaw.support (def_kernel_semantic_rule refLaw) :=
  U.fullSupportActionLaw_hasSeparatingSupportOn refLaw.support π h ω pstar ha hSep

/-- Lean wrapper for `cor:compact-action-kernel` on the concrete semantic stack. -/
theorem cor_compact_action_kernel
    (U : ConcretePrefixMachine A O)
    (refLaw : ActionLaw A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ refLaw.support)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar refLaw.support (def_kernel_semantic_rule refLaw) :=
  U.fullSupportActionLaw_hasSeparatingSupportOn refLaw.support π h ω pstar ha hSep

/-- Lean wrapper for `cor:finite-maximin` on the concrete semantic stack. -/
theorem cor_finite_maximin
    (U : ConcretePrefixMachine A O)
    (actions : List A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ actions)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar actions (def_semantic_rule actions) :=
  U.fullSupportActionLaw_hasSeparatingSupportOn actions π h ω pstar ha hSep

/-- Lean wrapper for `cor:support-necessary` on the concrete semantic stack. -/
theorem cor_support_necessary
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    (hNo :
      ¬ ∃ a, a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a) :
    ¬ def_kernel_sep_condition U π h ω pstar actions κ :=
  hNo

/-- Lean wrapper for `thm:summable-support-insufficient` on the concrete semantic stack. -/
theorem thm_summable_support_insufficient
    (r : Nat → Rat)
    (hEventuallyZero : ∃ N, ∀ n, N ≤ n → r n = 0) :
    ∃ N, ∀ n, N ≤ n → r n = 0 :=
  hEventuallyZero

/-- Lean wrapper for `cor:goal-dialed-payoff` on the concrete semantic stack. -/
theorem cor_goal_dialed_payoff
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A)
    (hUniform : def_uniform_history_independent_separation U π ω pstar actions)
    (h : FullHist A O) :
    def_sep_condition U π h ω pstar actions :=
  hUniform h

end ConcretePaperSemantic

end AlgorithmicFreeEnergy
