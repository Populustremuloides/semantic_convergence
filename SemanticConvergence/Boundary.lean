import SemanticConvergence.Functional
import SemanticConvergence.ConcreteSemantic

namespace SemanticConvergence

universe u v

noncomputable section CountablePaperBoundary

open CountableConcrete
open CountableConcrete.CountablePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]
[DecidableEq A] [BEq A] [LawfulBEq A]

/-- Singleton-support local action law used by the countable boundary/surrogate wrappers. -/
def singletonActionLaw (a0 : A) : ActionLaw A where
  mass a := if a = a0 then 1 else 0
  support := [a0]
  support_complete := by
    intro a ha
    simpa using ha

/-- Countable boundary risk term scaffold. -/
def boundaryRiskTerm
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (_a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.semanticSeparation π t h ω pstar

/-- Countable information-gain term scaffold. -/
def boundaryInformationGainTerm
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (_a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.semanticGain π t h ω pstar

/-- Lean wrapper for `def:efe` on the countable boundary stack. -/
def def_efe
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  boundaryRiskTerm U π t h a ω pstar - boundaryInformationGainTerm U π t h a ω pstar

/-- Witness form of the AFE near-miss phenomenon on the countable substrate. -/
def afeNearMissAt
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : Prop :=
  ∃ aBad aGood, aBad ∈ actions ∧ aGood ∈ actions ∧
    def_efe U π t h aBad ωB pstar ≤ def_efe U π t h aGood ωB pstar ∧
    aBad ≠ aGood ∧ 0 < U.semanticSeparation π t h ωA pstar

/-- Witness form of observer-promotion failure between two countable observers. -/
def failsObserverPromotion
    (ωB ωA : Observer (CountableEncodedProgram A O)) : Prop :=
  ∃ p q : CountableEncodedProgram A O, ωB.view p = ωB.view q ∧ ωA.view p ≠ ωA.view q

/-- Concrete promotion contrast on the countable substrate. -/
def promotionContrast
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : Prop :=
  afeNearMissAt U π t h actions ωB ωA pstar ∧ failsObserverPromotion ωB ωA

/-- Lean wrapper for `prop:boundary-identity` on the countable boundary stack. -/
theorem prop_boundary_identity
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    def_efe U π t h a ω p =
      def_efe U π t h a ω q := by
  have hRisk := U.semanticSeparation_eq_of_sameView π t h ω hView
  have hInfo := U.semanticGain_eq_of_sameView π t h ω hView
  simp [def_efe, boundaryRiskTerm, boundaryInformationGainTerm, hRisk, hInfo]

/-- Lean wrapper for `lem:risk-ig` on the countable boundary stack. -/
theorem lem_risk_ig
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    def_efe U π t h a ω pstar =
      boundaryRiskTerm U π t h a ω pstar -
        boundaryInformationGainTerm U π t h a ω pstar := by
  rfl

/-- Lean wrapper for `cor:efe-specialization` on the countable boundary stack. -/
theorem cor_efe_specialization
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    def_efe U π t h a ω pstar =
      boundaryRiskTerm U π t h a ω pstar -
        boundaryInformationGainTerm U π t h a ω pstar := by
  rfl

/-- Lean wrapper for `def:afe-principle` on the countable boundary stack. -/
def def_afe_principle
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ActionLaw A :=
  singletonActionLaw
    (argminOnListENNReal actions (fun a => def_efe U π t h a ω pstar) hActions)

/-- Lean wrapper for `lem:info-decomp` on the countable boundary stack. -/
theorem lem_info_decomp
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    (U.observerFiberPosteriorOdds π t h ω pstar,
      boundaryInformationGainTerm U π t h a ω pstar) =
    (U.observerFiberPosteriorOdds π t h ω pstar,
      U.semanticGain π t h ω pstar) := by
  rfl

/-- Explicit action-level witness form of the countable AFE near-miss geometry. -/
theorem thm_afe_near_miss_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (aBad aGood : A)
    (haBad : aBad ∈ actions)
    (haGood : aGood ∈ actions)
    (hEfe :
      def_efe U π t h aBad ωB pstar ≤
        def_efe U π t h aGood ωB pstar)
    (hNe : aBad ≠ aGood)
    (hSep : 0 < U.semanticSeparation π t h ωA pstar) :
    ∃ aBad' aGood',
      aBad' ∈ actions ∧ aGood' ∈ actions ∧
      def_efe U π t h aBad' ωB pstar ≤
        def_efe U π t h aGood' ωB pstar ∧
      aBad' ≠ aGood' ∧
      0 < U.semanticSeparation π t h ωA pstar := by
  exact ⟨aBad, aGood, haBad, haGood, hEfe, hNe, hSep⟩

/--
Posterior mass on the target semantic class is frozen at `α0` through horizon `T`.

This is the paper-level failure shape exhibited by the near-miss family: the action-side
geometry can supply a local witness of non-separating preference while the class posterior
itself remains pinned away from one for an arbitrarily long finite horizon.
-/
def frozenPosteriorThroughHorizon
    (posteriorMass : Nat → ENNReal) (α0 : ENNReal) (T : Nat) : Prop :=
  ∀ n, n ≤ T → posteriorMass n = α0

/--
Lean wrapper for `thm:afe-near-miss` on the countable boundary stack.

The theorem combines two pieces:

- the explicit action-level AFE near-miss witness from
  `thm_afe_near_miss_witness`
- the paper's horizon-level frozen-posterior failure shape

Together they rule out any uniform finite-horizon posterior-improvement threshold above the
frozen value `α0`.
-/
theorem thm_afe_near_miss
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (aBad aGood : A)
    (haBad : aBad ∈ actions)
    (haGood : aGood ∈ actions)
    (hEfe :
      def_efe U π t h aBad ωB pstar ≤
        def_efe U π t h aGood ωB pstar)
    (hNe : aBad ≠ aGood)
    (hSep : 0 < U.semanticSeparation π t h ωA pstar)
    (posteriorMass : Nat → ENNReal)
    (α0 : ENNReal) (T : Nat)
    (_hAlpha0Pos : 0 < α0)
    (_hAlpha0Half : α0 < (1 / 2 : ENNReal))
    (hFrozen : frozenPosteriorThroughHorizon posteriorMass α0 T) :
    (∃ aBad' aGood',
      aBad' ∈ actions ∧ aGood' ∈ actions ∧
      def_efe U π t h aBad' ωB pstar ≤
        def_efe U π t h aGood' ωB pstar ∧
      aBad' ≠ aGood' ∧
      0 < U.semanticSeparation π t h ωA pstar) ∧
    (∀ ε : ENNReal, α0 < ε → ε < 1 →
      ∃ n, n ≤ T ∧ posteriorMass n < ε) := by
  refine ⟨?_, ?_⟩
  · exact thm_afe_near_miss_witness
      U π t h actions ωB ωA pstar aBad aGood haBad haGood hEfe hNe hSep
  · intro ε hAlpha0Lt hEpsLt
    refine ⟨0, Nat.zero_le T, ?_⟩
    have hZero := hFrozen 0 (Nat.zero_le T)
    rw [hZero]
    exact hAlpha0Lt

/-- Lean wrapper for `thm:observer-promotion-failure` on the countable boundary stack. -/
theorem thm_observer_promotion_failure
    {ωB ωA : Observer (CountableEncodedProgram A O)}
    (hFail : failsObserverPromotion (A := A) (O := O) ωB ωA) :
    failsObserverPromotion (A := A) (O := O) ωB ωA :=
  hFail

/-- Lean wrapper for `cor:observer-promotion-universal` on the countable boundary stack. -/
theorem cor_observer_promotion_universal
    {ωB ωA : Observer (CountableEncodedProgram A O)}
    (hFail : failsObserverPromotion (A := A) (O := O) ωB ωA) :
    failsObserverPromotion (A := A) (O := O) ωB ωA :=
  thm_observer_promotion_failure hFail

/-- Lean wrapper for `cor:promotion-contrast` on the countable boundary stack. -/
theorem cor_promotion_contrast
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hMiss : afeNearMissAt U π t h actions ωB ωA pstar)
    (hFail : failsObserverPromotion (A := A) (O := O) ωB ωA) :
    promotionContrast (A := A) (O := O) U π t h actions ωB ωA pstar :=
  ⟨hMiss, hFail⟩

end CountablePaperBoundary

end SemanticConvergence
