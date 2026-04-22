import AlgorithmicFreeEnergy.ConcreteSelfReference

namespace AlgorithmicFreeEnergy

universe u v

open Classical

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/--
A concrete risk-like term on an observer fiber, measured by one minus the rational
overlap affinity of the class/complement predictive laws.
-/
def boundaryRiskTerm (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat :=
  let pair := U.observerFiberClassComplement π h a ω pstar
  1 - overlapAffinity pair.1 pair.2

/--
A concrete information-gain-like term obtained by weighting the risk term by the
observer-fiber posterior mass.
-/
def boundaryInformationGainTerm (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat :=
  U.observerFiberPosteriorMass π h ω pstar *
    U.boundaryRiskTerm π h a ω pstar

/-- Concrete expected free energy at a history-action pair on an observer fiber. -/
def expectedFreeEnergyRat (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat :=
  U.boundaryRiskTerm π h a ω pstar -
    U.boundaryInformationGainTerm π h a ω pstar

/--
Concrete information decomposition recorded as posterior odds together with the local
information-gain term.
-/
def infoDecomposition (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat × Rat :=
  (U.observerFiberPosteriorOdds π h ω pstar,
   U.boundaryInformationGainTerm π h a ω pstar)

/-- Finite-list concrete AFE minimizer. -/
noncomputable def afeArgmin (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : A :=
  argminOnList actions (fun a => U.expectedFreeEnergyRat π h a ω pstar) hActions

/-- Deterministic concrete AFE action law concentrated on the finite-list minimizer. -/
def afePrincipleLaw (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : ActionLaw A :=
  fullSupportActionLaw [U.afeArgmin π h actions hActions ω pstar]

/--
Witness form of the AFE near-miss phenomenon: a low-EFE action can fail to be
semantically separating even though a separating action exists on the same finite list.
-/
def afeNearMissAt (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ωB ωA : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Prop :=
  ∃ aBad aGood, aBad ∈ actions ∧ aGood ∈ actions ∧
    U.expectedFreeEnergyRat π h aBad ωB pstar ≤
      U.expectedFreeEnergyRat π h aGood ωB pstar ∧
    ¬ U.isSeparatingAction π h ωA pstar aBad ∧
    U.isSeparatingAction π h ωA pstar aGood

/-- Witness form of observer-promotion failure between two concrete observers. -/
def failsObserverPromotion
    (ωB ωA : Observer (EncodedProgram A O)) : Prop :=
  ∃ p q : EncodedProgram A O, ωB.view p = ωB.view q ∧ ωA.view p ≠ ωA.view q

/-- Concrete promotion contrast: a near miss together with observer-promotion failure. -/
def promotionContrast (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ωB ωA : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Prop :=
  U.afeNearMissAt π h actions ωB ωA pstar ∧ failsObserverPromotion ωB ωA

theorem expectedFreeEnergyRat_eq_risk_minus_informationGain
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    U.expectedFreeEnergyRat π h a ω pstar =
      U.boundaryRiskTerm π h a ω pstar -
        U.boundaryInformationGainTerm π h a ω pstar := by
  rfl

theorem boundaryRiskTerm_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.boundaryRiskTerm π h a ω p =
      U.boundaryRiskTerm π h a ω q := by
  have hPair := U.observerFiberComplementLaw_eq_of_sameView π h a ω hView
  simp [boundaryRiskTerm, hPair]

theorem boundaryInformationGainTerm_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.boundaryInformationGainTerm π h a ω p =
      U.boundaryInformationGainTerm π h a ω q := by
  have hMass := U.observerFiberPosteriorMass_eq_of_sameView π h ω hView
  have hRisk := U.boundaryRiskTerm_eq_of_sameView π h a ω hView
  simp [boundaryInformationGainTerm, hMass, hRisk]

theorem expectedFreeEnergyRat_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.expectedFreeEnergyRat π h a ω p =
      U.expectedFreeEnergyRat π h a ω q := by
  have hRisk := U.boundaryRiskTerm_eq_of_sameView π h a ω hView
  have hInfo := U.boundaryInformationGainTerm_eq_of_sameView π h a ω hView
  simp [expectedFreeEnergyRat, hRisk, hInfo]

theorem infoDecomposition_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.infoDecomposition π h a ω p =
      U.infoDecomposition π h a ω q := by
  have hOdds := U.observerFiberPosteriorOdds_eq_of_sameView π h ω hView
  have hInfo := U.boundaryInformationGainTerm_eq_of_sameView π h a ω hView
  simp [infoDecomposition, hOdds, hInfo]

theorem afeArgmin_spec
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    MinimizesOnList actions
      (fun a => U.expectedFreeEnergyRat π h a ω pstar)
      (U.afeArgmin π h actions hActions ω pstar) :=
  argminOnList_spec actions (fun a => U.expectedFreeEnergyRat π h a ω pstar) hActions

theorem afePrincipleLaw_supportsArgmin
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    (U.afePrincipleLaw π h actions hActions ω pstar).mass
      (U.afeArgmin π h actions hActions ω pstar) ≠ 0 := by
  simp [afePrincipleLaw, fullSupportActionLaw]

theorem riskMinusInformationGain_of_rfl
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    U.expectedFreeEnergyRat π h a ω pstar =
      U.boundaryRiskTerm π h a ω pstar -
        U.boundaryInformationGainTerm π h a ω pstar :=
  U.expectedFreeEnergyRat_eq_risk_minus_informationGain π h a ω pstar

theorem observerPromotionFailure_of_witness
    {ωB ωA : Observer (EncodedProgram A O)}
    (hFail : failsObserverPromotion ωB ωA) :
    failsObserverPromotion ωB ωA :=
  hFail

theorem afeNearMiss_of_witness
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ωB ωA : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (hMiss : U.afeNearMissAt π h actions ωB ωA pstar) :
    U.afeNearMissAt π h actions ωB ωA pstar :=
  hMiss

theorem promotionContrast_of_witness
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ωB ωA : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (hMiss : U.afeNearMissAt π h actions ωB ωA pstar)
    (hFail : failsObserverPromotion ωB ωA) :
    U.promotionContrast π h actions ωB ωA pstar :=
  ⟨hMiss, hFail⟩

end ConcretePrefixMachine

end

end AlgorithmicFreeEnergy
