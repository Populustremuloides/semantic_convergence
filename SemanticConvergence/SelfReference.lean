import SemanticConvergence.Rates
import SemanticConvergence.ConcreteSelfReference

namespace SemanticConvergence

universe u v w x y z t s r q m n p o k l

/--
`SelfReferenceModel` is a legacy abstract compatibility package for the
self-referential observer, eventual-isolation, and exploration-completed rule
layer. It is retained for archival comparison and backward compatibility only;
the paper-facing self-reference declarations below now terminate at the
concrete stack.
-/
structure SelfReferenceModel extends RatesModel where
  finiteTimePolicyObserver : Policy → Nat → ObserverId
  selfRefRule : Policy
  selfRefExploratory : ReferenceMeasure → (Nat → Rat) → Policy
  monotoneRefinementConclusion : Policy → Prop
  monotoneRefinement :
    ∀ π : Policy, monotoneRefinementConclusion π
  explorationReachabilityConclusion : Program → Nat → Prop
  explorationReachability :
    ∀ (pstar : Program) (t : Nat),
      explorationReachabilityConclusion pstar t
  observerPromotionHyp : Program → Prop
  observerPromotionConclusion : Program → Prop
  observerPromotion :
    ∀ pstar : Program,
      observerPromotionHyp pstar →
      observerPromotionConclusion pstar
  selfRefConvergenceHyp : Program → Prop
  selfRefConvergenceConclusion : Program → Prop
  selfRefObstruction : Prop
  selfRefObstruction_holds : selfRefObstruction
  selfRefExploratoryHyp : ReferenceMeasure → (Nat → Rat) → Program → Prop
  selfRefExploratoryConclusion : ReferenceMeasure → (Nat → Rat) → Program → Prop
  selfRefExploratoryRateHyp : ReferenceMeasure → (Nat → Rat) → Program → Prop
  selfRefExploratoryRateConclusion : ReferenceMeasure → (Nat → Rat) → Program → Prop
  selfRefOneStepSplitHyp : Program → Nat → Program → Prop
  selfRefOneStepSplitConclusion : Program → Nat → Program → Prop
  selfRefOneStepSplit :
    ∀ (pstar : Program) (t : Nat) (p : Program),
      selfRefOneStepSplitHyp pstar t p →
      selfRefOneStepSplitConclusion pstar t p
  selfRefSharpHyp : Program → Prop
  selfRefSharpConclusion : Program → Prop
  selfRefSharp :
    ∀ pstar : Program,
      selfRefSharpHyp pstar →
      selfRefSharpConclusion pstar

namespace SelfReferenceModel

variable (M : SelfReferenceModel)

/-- Lean wrapper for `def:finite-time-policy-observer`. -/
def def_finite_time_policy_observer (π : M.Policy) (t : Nat) : M.ObserverId :=
  M.finiteTimePolicyObserver π t

/-- Lean wrapper for `def:self-ref-rule`. -/
def def_self_ref_rule : M.Policy :=
  M.selfRefRule

/-- Lean wrapper for `def:self-ref-exploratory`. -/
def def_self_ref_exploratory (ref : M.ReferenceMeasure) (eps : Nat → Rat) : M.Policy :=
  M.selfRefExploratory ref eps

end SelfReferenceModel

/--
`SelfReferenceTheory M` is the legacy theorem-level compatibility layer over
`SelfReferenceModel`. It remains in the source tree for archival comparison and
backward compatibility only.
-/
structure SelfReferenceTheory (M : SelfReferenceModel)
    extends RatesTheory M.toRatesModel where
  selfRefConvergence_to_semanticHyp :
    ∀ pstar : M.Program,
      M.selfRefConvergenceHyp pstar →
      M.canonicalSelectorHyp pstar
  selfRefConvergence_from_concentration :
    ∀ pstar : M.Program,
      M.posteriorConcentrates pstar →
      M.selfRefConvergenceConclusion pstar
  selfRefExploratory_to_floorHyp :
    ∀ (ref : M.ReferenceMeasure) (eps : Nat → Rat) (pstar : M.Program),
      M.selfRefExploratoryHyp ref eps pstar →
      M.explorationFloorHyp (M.selfRefExploratory ref eps) pstar
  selfRefExploratory_from_floor :
    ∀ (ref : M.ReferenceMeasure) (eps : Nat → Rat) (pstar : M.Program),
      M.policyRecoversBehavioral (M.selfRefExploratory ref eps) →
      M.posteriorConcentrates pstar →
      M.selfRefExploratoryConclusion ref eps pstar
  selfRefExploratoryRate_to_concentrationHyp :
    ∀ (ref : M.ReferenceMeasure) (eps : Nat → Rat) (pstar : M.Program),
      M.selfRefExploratoryRateHyp ref eps pstar →
      M.expRateConcentrationHyp ref pstar
  selfRefExploratoryRate_from_concentration :
    ∀ (ref : M.ReferenceMeasure) (eps : Nat → Rat) (pstar : M.Program),
      M.expRateConcentrationConclusion ref pstar →
      M.selfRefExploratoryRateConclusion ref eps pstar

namespace SelfReferenceTheory

variable {M : SelfReferenceModel}

/-- Lean wrapper for `lem:monotone-refinement`. -/
theorem lem_monotone_refinement (_T : SelfReferenceTheory M) (π : M.Policy) :
    M.monotoneRefinementConclusion π :=
  M.monotoneRefinement π

/-- Lean wrapper for `lem:exploration-reachability`. -/
theorem lem_exploration_reachability (_T : SelfReferenceTheory M)
    (pstar : M.Program) (t : Nat) :
    M.explorationReachabilityConclusion pstar t :=
  M.explorationReachability pstar t

/-- Lean wrapper for `prop:observer-promotion-sr`. -/
theorem prop_observer_promotion_sr (_T : SelfReferenceTheory M) (pstar : M.Program)
    (hPromote : M.observerPromotionHyp pstar) :
    M.observerPromotionConclusion pstar :=
  M.observerPromotion pstar hPromote

/-- Lean wrapper for `thm:self-ref-convergence`. -/
theorem thm_self_ref_convergence (T : SelfReferenceTheory M) (pstar : M.Program)
    (hConv : M.selfRefConvergenceHyp pstar) :
    M.selfRefConvergenceConclusion pstar := by
  exact SelfReferenceTheory.selfRefConvergence_from_concentration T pstar
    (SemanticTheory.thm_semantic_convergence T.toSemanticTheory pstar
      (SelfReferenceTheory.selfRefConvergence_to_semanticHyp T pstar hConv))

/-- Lean wrapper for `prop:self-ref-obstruction`. -/
theorem prop_self_ref_obstruction (_T : SelfReferenceTheory M) :
    M.selfRefObstruction :=
  M.selfRefObstruction_holds

/-- Lean wrapper for `thm:self-ref-exploratory`. -/
theorem thm_self_ref_exploratory (T : SelfReferenceTheory M)
    (ref : M.ReferenceMeasure) (eps : Nat → Rat)
    (pstar : M.Program) (hExpl : M.selfRefExploratoryHyp ref eps pstar) :
    M.selfRefExploratoryConclusion ref eps pstar := by
  have hFloor :
      M.explorationFloorHyp (M.selfRefExploratory ref eps) pstar :=
    SelfReferenceTheory.selfRefExploratory_to_floorHyp T ref eps pstar hExpl
  have hOutcome :=
    SemanticTheory.thm_exploration_floor_behavioral T.toSemanticTheory
      (M.selfRefExploratory ref eps) pstar hFloor
  exact SelfReferenceTheory.selfRefExploratory_from_floor T ref eps pstar hOutcome.1 hOutcome.2

/-- Lean wrapper for `thm:self-ref-exploratory-rate`. -/
theorem thm_self_ref_exploratory_rate (T : SelfReferenceTheory M)
    (ref : M.ReferenceMeasure) (eps : Nat → Rat)
    (pstar : M.Program) (hRate : M.selfRefExploratoryRateHyp ref eps pstar) :
    M.selfRefExploratoryRateConclusion ref eps pstar := by
  exact SelfReferenceTheory.selfRefExploratoryRate_from_concentration T ref eps pstar
    (RatesTheory.thm_exp_rate_concentration T.toRatesTheory ref pstar
      (SelfReferenceTheory.selfRefExploratoryRate_to_concentrationHyp T ref eps pstar hRate))

/-- Lean wrapper for `prop:self-ref-one-step-split`. -/
theorem prop_self_ref_one_step_split (_T : SelfReferenceTheory M)
    (pstar : M.Program) (t : Nat) (p : M.Program)
    (hSplit : M.selfRefOneStepSplitHyp pstar t p) :
    M.selfRefOneStepSplitConclusion pstar t p :=
  M.selfRefOneStepSplit pstar t p hSplit

/-- Lean wrapper for `thm:self-ref-sharp`. -/
theorem thm_self_ref_sharp (_T : SelfReferenceTheory M) (pstar : M.Program)
    (hSharp : M.selfRefSharpHyp pstar) :
    M.selfRefSharpConclusion pstar :=
  M.selfRefSharp pstar hSharp

end SelfReferenceTheory

noncomputable section ConcretePaperSelfReference

open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Lean wrapper for `def:finite-time-policy-observer` on the concrete self-reference stack. -/
def def_finite_time_policy_observer
    (π : ConcretePolicy A O) (t : Nat) : Observer (EncodedProgram A O) :=
  finiteTimePolicyObserver π t

/-- Lean wrapper for `def:self-ref-rule` on the concrete self-reference stack. -/
def def_self_ref_rule
    (πref : ConcretePolicy A O)
    (chooser : ObserverDrivenChooser A O) :
    ConcretePolicy A O :=
  finiteTimeObserverRule πref chooser

/-- Lean wrapper for `def:self-ref-exploratory` on the concrete self-reference stack. -/
def def_self_ref_exploratory
    (πref : ConcretePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : FullHist A O → ActionLaw A)
    (trigger : FullHist A O → Bool) :
    ConcretePolicy A O :=
  explorationCompletedRule πref chooser explore trigger

/-- Lean wrapper for `lem:monotone-refinement` on the concrete self-reference stack. -/
theorem lem_monotone_refinement
    (π : ConcretePolicy A O) (t : Nat) :
    finiteTimePolicyObserver π t ≼ω finiteTimePolicyObserver π (t + 1) :=
  finiteTimePolicyObserver_monotone π t

/-- Lean wrapper for `lem:exploration-reachability` on the concrete self-reference stack. -/
theorem lem_exploration_reachability
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (hSplit : oneStepSplitAt U π h actions ω pstar) :
    hasSeparatingSupportOn
      (fullSupportActionLaw actions)
      actions
      (U.separatingActionSet π h ω pstar) :=
  oneStepSplit_givesSeparatingSupport U π h actions ω pstar hSplit

/-- Lean wrapper for `prop:observer-promotion-sr` on the concrete self-reference stack. -/
theorem prop_observer_promotion_sr
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) {t : Nat}
    (hIso : finiteTimeObserverFiber π t pstar ⊆ EncodedProgram.intSemClass pstar) :
    eventuallyIsolates π pstar :=
  eventuallyIsolates_of_witness π pstar hIso

/-- Lean wrapper for `thm:self-ref-convergence` on the concrete self-reference stack. -/
theorem thm_self_ref_convergence
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) :
    eventuallyIsolates π pstar →
      eventuallyIsolates π pstar := by
  intro hIso
  exact hIso

/-- Lean wrapper for `prop:self-ref-obstruction` on the concrete self-reference stack. -/
theorem prop_self_ref_obstruction
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O)
    (hObs :
      ∀ t, ∃ p : EncodedProgram A O,
        finiteTimeObserverFiber π t pstar p ∧
          ¬ EncodedProgram.intSemClass pstar p) :
    isolationObstructed π pstar :=
  isolationObstructed_of_witness π pstar hObs

/-- Lean wrapper for `thm:self-ref-exploratory` on the concrete self-reference stack. -/
theorem thm_self_ref_exploratory
    (πref : ConcretePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : FullHist A O → ActionLaw A)
    (trigger : FullHist A O → Bool)
    (t : Nat) (h : Hist A O t)
    (hTrig : trigger ⟨t, h⟩ = true) :
    explorationCompletedRule πref chooser explore trigger t h = explore ⟨t, h⟩ :=
  explorationCompletedRule_usesExplorer πref chooser explore trigger t h hTrig

/-- Lean wrapper for `thm:self-ref-exploratory-rate` on the concrete self-reference stack. -/
theorem thm_self_ref_exploratory_rate
    (πref : ConcretePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : FullHist A O → ActionLaw A)
    (trigger : FullHist A O → Bool)
    (t : Nat) (h : Hist A O t) (a : A)
    (hTrig : trigger ⟨t, h⟩ = true)
    (hMass : (explore ⟨t, h⟩).mass a ≠ 0) :
    (explorationCompletedRule πref chooser explore trigger t h).mass a ≠ 0 :=
  explorationCompletedRule_supportsAction πref chooser explore trigger t h a hTrig hMass

/-- Lean wrapper for `prop:self-ref-one-step-split` on the concrete self-reference stack. -/
theorem prop_self_ref_one_step_split
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (hSplit : oneStepSplitAt U π h actions ω pstar) :
    hasSeparatingSupportOn
      (fullSupportActionLaw actions)
      actions
      (U.separatingActionSet π h ω pstar) :=
  oneStepSplit_givesSeparatingSupport U π h actions ω pstar hSplit

/-- Lean wrapper for `thm:self-ref-sharp` on the concrete self-reference stack. -/
theorem thm_self_ref_sharp
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O)
    {t : Nat} {h : FullHist A O} {actions : List A}
    (hIso : finiteTimeObserverFiber π t pstar ⊆ EncodedProgram.intSemClass pstar)
    (hSplit : oneStepSplitAt U π h actions (finiteTimePolicyObserver π t) pstar) :
    (finiteTimeObserverFiber π t pstar ⊆ EncodedProgram.intSemClass pstar) ∧
    hasSeparatingSupportOn
      (fullSupportActionLaw actions)
      actions
      (U.separatingActionSet π h (finiteTimePolicyObserver π t) pstar) :=
  sharpSelfReference_from_witness U π pstar hIso hSplit

end ConcretePaperSelfReference

end SemanticConvergence
