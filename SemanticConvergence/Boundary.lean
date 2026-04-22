import SemanticConvergence.Semantic
import SemanticConvergence.ConcreteBoundary

namespace SemanticConvergence

universe u v w x y z t s r q m n p o k l

/--
`BoundaryModel` is a legacy abstract compatibility package for the
expected-free-energy boundary, near-miss, and observer-promotion-failure layer.
It is retained for archival comparison and backward compatibility only; the
paper-facing boundary declarations below now terminate at the concrete stack.
-/
structure BoundaryModel extends SemanticModel where
  expectedFreeEnergy : Action → History → Rat
  afePrinciple : Policy
  riskMinusInformationGain : Action → History → Prop
  riskMinusInformationGain_holds :
    ∀ (a : Action) (h : History), riskMinusInformationGain a h
  riskIgSpecializationHyp : Prop
  riskIgSpecialization_holds : riskIgSpecializationHyp
  efeSpecialization : Prop
  infoDecomposition : Program → History → Prop
  infoDecomposition_holds :
    ∀ (pstar : Program) (h : History), infoDecomposition pstar h
  boundaryIdentityBeliefPart : Program → Prop
  boundaryIdentityActionPart : Program → Prop
  boundaryIdentityConclusion : Program → Prop
  afeNearMissConclusion : Prop
  afeNearMiss_holds : afeNearMissConclusion
  observerPromotionFailureConclusion : Prop
  observerPromotionFailure_holds : observerPromotionFailureConclusion
  observerPromotionUniversalConclusion : Prop
  promotionContrastConclusion : Prop
  efeSpecialization_from_riskIg :
    (∀ (a : Action) (h : History), riskMinusInformationGain a h) →
    riskIgSpecializationHyp →
    efeSpecialization
  boundaryIdentity_from_parts :
    ∀ pstar : Program,
      boundaryIdentityBeliefPart pstar →
      boundaryIdentityActionPart pstar →
      boundaryIdentityConclusion pstar
  observerPromotionUniversal_from_failure :
    observerPromotionFailureConclusion →
    observerPromotionUniversalConclusion
  promotionContrast_from_components :
    afeNearMissConclusion →
    observerPromotionFailureConclusion →
    (∀ pstar : Program, canonicalSelectorHyp pstar → posteriorConcentrates pstar) →
    promotionContrastConclusion

namespace BoundaryModel

variable (M : BoundaryModel)

/-- Lean wrapper for `def:efe`. -/
def def_efe (a : M.Action) (h : M.History) : Rat :=
  M.expectedFreeEnergy a h

/-- Lean wrapper for `def:afe-principle`. -/
def def_afe_principle : M.Policy :=
  M.afePrinciple

end BoundaryModel

/--
`BoundaryTheory M` is the legacy theorem-level compatibility layer over
`BoundaryModel`. It remains in the source tree for archival comparison and
backward compatibility only.
-/
structure BoundaryTheory (M : BoundaryModel) extends SemanticTheory M.toSemanticModel where
  boundaryIdentityBelief_field :
    ∀ pstar : M.Program, M.boundaryIdentityBeliefPart pstar
  boundaryIdentityAction_field :
    ∀ pstar : M.Program, M.boundaryIdentityActionPart pstar

namespace BoundaryTheory

variable {M : BoundaryModel}

/-- Lean wrapper for `prop:boundary-identity`. -/
theorem prop_boundary_identity (T : BoundaryTheory M) (pstar : M.Program) :
    M.boundaryIdentityConclusion pstar := by
  exact M.boundaryIdentity_from_parts pstar
    (BoundaryTheory.boundaryIdentityBelief_field T pstar)
    (BoundaryTheory.boundaryIdentityAction_field T pstar)

/-- Lean wrapper for `lem:risk-ig`. -/
theorem lem_risk_ig (_T : BoundaryTheory M) (a : M.Action) (h : M.History) :
    M.riskMinusInformationGain a h :=
  M.riskMinusInformationGain_holds a h

/-- Lean wrapper for `cor:efe-specialization`. -/
theorem cor_efe_specialization (T : BoundaryTheory M) :
    M.efeSpecialization := by
  exact M.efeSpecialization_from_riskIg
    (fun a h => BoundaryTheory.lem_risk_ig T a h)
    M.riskIgSpecialization_holds

/-- Lean wrapper for `lem:info-decomp`. -/
theorem lem_info_decomp (_T : BoundaryTheory M) (pstar : M.Program) (h : M.History) :
    M.infoDecomposition pstar h :=
  M.infoDecomposition_holds pstar h

/-- Lean wrapper for `thm:afe-near-miss`. -/
theorem thm_afe_near_miss (_T : BoundaryTheory M) :
    M.afeNearMissConclusion :=
  M.afeNearMiss_holds

/-- Lean wrapper for `thm:observer-promotion-failure`. -/
theorem thm_observer_promotion_failure (_T : BoundaryTheory M) :
    M.observerPromotionFailureConclusion :=
  M.observerPromotionFailure_holds

/-- Lean wrapper for `cor:observer-promotion-universal`. -/
theorem cor_observer_promotion_universal (T : BoundaryTheory M) :
    M.observerPromotionUniversalConclusion := by
  exact M.observerPromotionUniversal_from_failure
    (BoundaryTheory.thm_observer_promotion_failure T)

/-- Lean wrapper for `cor:promotion-contrast`. -/
theorem cor_promotion_contrast (T : BoundaryTheory M) :
    M.promotionContrastConclusion := by
  exact M.promotionContrast_from_components
    (BoundaryTheory.thm_afe_near_miss T)
    (BoundaryTheory.thm_observer_promotion_failure T)
    (fun pstar hSel => SemanticTheory.thm_semantic_convergence T.toSemanticTheory pstar hSel)

end BoundaryTheory

noncomputable section ConcretePaperBoundary

open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Lean wrapper for `prop:boundary-identity` on the concrete boundary stack. -/
theorem prop_boundary_identity
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.expectedFreeEnergyRat π h a ω p =
      U.expectedFreeEnergyRat π h a ω q :=
  U.expectedFreeEnergyRat_eq_of_sameView π h a ω hView

/-- Lean wrapper for `def:efe` on the concrete boundary stack. -/
def def_efe (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat :=
  U.expectedFreeEnergyRat π h a ω pstar

/-- Lean wrapper for `lem:risk-ig` on the concrete boundary stack. -/
theorem lem_risk_ig
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    def_efe U π h a ω pstar =
      U.boundaryRiskTerm π h a ω pstar -
        U.boundaryInformationGainTerm π h a ω pstar :=
  U.expectedFreeEnergyRat_eq_risk_minus_informationGain π h a ω pstar

/-- Lean wrapper for `cor:efe-specialization` on the concrete boundary stack. -/
theorem cor_efe_specialization
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    def_efe U π h a ω pstar =
      U.boundaryRiskTerm π h a ω pstar -
        U.boundaryInformationGainTerm π h a ω pstar :=
  U.riskMinusInformationGain_of_rfl π h a ω pstar

/-- Lean wrapper for `def:afe-principle` on the concrete boundary stack. -/
def def_afe_principle (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : ActionLaw A :=
  U.afePrincipleLaw π h actions hActions ω pstar

/-- Lean wrapper for `lem:info-decomp` on the concrete boundary stack. -/
theorem lem_info_decomp
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    U.infoDecomposition π h a ω pstar =
      (U.observerFiberPosteriorOdds π h ω pstar,
        U.boundaryInformationGainTerm π h a ω pstar) := by
  rfl

/-- Lean wrapper for `thm:afe-near-miss` on the concrete boundary stack. -/
theorem thm_afe_near_miss
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ωB ωA : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (hMiss : U.afeNearMissAt π h actions ωB ωA pstar) :
    U.afeNearMissAt π h actions ωB ωA pstar :=
  U.afeNearMiss_of_witness π h actions ωB ωA pstar hMiss

/-- Lean wrapper for `thm:observer-promotion-failure` on the concrete boundary stack. -/
theorem thm_observer_promotion_failure
    {ωB ωA : Observer (EncodedProgram A O)}
    (hFail : ConcretePrefixMachine.failsObserverPromotion ωB ωA) :
    ConcretePrefixMachine.failsObserverPromotion ωB ωA :=
  ConcretePrefixMachine.observerPromotionFailure_of_witness hFail

/-- Lean wrapper for `cor:observer-promotion-universal` on the concrete boundary stack. -/
theorem cor_observer_promotion_universal
    {ωB ωA : Observer (EncodedProgram A O)}
    (hFail : ConcretePrefixMachine.failsObserverPromotion ωB ωA) :
    ConcretePrefixMachine.failsObserverPromotion ωB ωA :=
  thm_observer_promotion_failure hFail

/-- Lean wrapper for `cor:promotion-contrast` on the concrete boundary stack. -/
theorem cor_promotion_contrast
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ωB ωA : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (hMiss : U.afeNearMissAt π h actions ωB ωA pstar)
    (hFail : ConcretePrefixMachine.failsObserverPromotion ωB ωA) :
    U.promotionContrast π h actions ωB ωA pstar :=
  U.promotionContrast_of_witness π h actions ωB ωA pstar hMiss hFail

end ConcretePaperBoundary

end SemanticConvergence
