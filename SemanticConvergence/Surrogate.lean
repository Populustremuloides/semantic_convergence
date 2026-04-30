import SemanticConvergence.Boundary
import SemanticConvergence.Semantic
import SemanticConvergence.ConcreteSurrogate
import SemanticConvergence.Rates

namespace SemanticConvergence

universe u v

noncomputable section CountablePaperSurrogate

open CountableConcrete
open CountableConcrete.CountablePrefixMachine
open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]
[DecidableEq A] [BEq A] [LawfulBEq A]

/-- Countable surrogate information score inherited from the boundary layer. -/
def surrogateInformationScore
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  boundaryInformationGainTerm U π t h a ω pstar

/-- Countable regularization penalty against a reference local action law. -/
def surrogateRegularization
    (refLaw : ActionLaw A) (a : A) : ENNReal :=
  ratToENNReal (Rat.abs (1 - refLaw.mass a))

/-- Countable amortized-surrogate energy. -/
def surrogateEnergy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) : ENNReal :=
  def_efe U π t h a ω pstar + reg * surrogateRegularization refLaw a

/-- Finite-list countable surrogate minimizer. -/
noncomputable def surrogateArgmin
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) : A :=
  argminOnListENNReal actions
    (fun a => surrogateEnergy U π t h a ω pstar refLaw reg)
    hActions

/-- Countable local action law induced by the surrogate minimizer. -/
def surrogateChosenLaw
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) : ActionLaw A :=
  singletonActionLaw (surrogateArgmin U π t h actions hActions ω pstar refLaw reg)

/-- Lean wrapper for `prop:amortized-surrogate-minimizer` on the countable stack. -/
theorem prop_amortized_surrogate_minimizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) :
    MinimizesOnListENNReal actions
      (fun a => surrogateEnergy U π t h a ω pstar refLaw reg)
      (surrogateArgmin U π t h actions hActions ω pstar refLaw reg) :=
  argminOnListENNReal_spec actions
    (fun a => surrogateEnergy U π t h a ω pstar refLaw reg)
    hActions

/--
Countable finite-list counterpart of deployment assumption `(A3)`.

Because the present countable semantic scaffold carries the class-vs.-complement score at
the history level rather than as an action-indexed predicate, the assumption says that the
same positive semantic-separation floor is inherited along the entire learned high-score
set.
-/
def countableSurrogateAssumptionA3
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (highScoreActions : List A) : Prop :=
  ∀ a, a ∈ highScoreActions → 0 < U.semanticSeparation π t h ω pstar

/-- Helper theorem retaining the old singleton-selector existence result. -/
theorem helper_amortized_surrogate_selector_existence_of_positiveSeparation
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal)
    (hSep : 0 < U.semanticSeparation π t h ω pstar) :
    ∃ a, a ∈ [surrogateArgmin U π t h actions hActions ω pstar refLaw reg] ∧
      (surrogateChosenLaw U π t h actions hActions ω pstar refLaw reg).mass a ≠ 0 ∧
      0 < U.semanticSeparation π t h ω pstar := by
  refine ⟨surrogateArgmin U π t h actions hActions ω pstar refLaw reg, by simp, ?_, hSep⟩
  simp [surrogateChosenLaw, singletonActionLaw]

/-- Helper corollary retaining the old singleton-selector support fact. -/
theorem helper_amortized_surrogate_selector_support
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) :
    (surrogateChosenLaw U π t h actions hActions ω pstar refLaw reg).mass
      (surrogateArgmin U π t h actions hActions ω pstar refLaw reg) ≠ 0 := by
  simp [surrogateChosenLaw, singletonActionLaw]

/--
Countable deployment-side surrogate support theorem.

This is the countable wrapper matching the repaired concrete theorem surface: assumptions
`(A1)`--`(A3)` are exposed directly, the implemented law is the same finite-list
deployment law `surrogateImplementedLaw`, and the conclusion gives both the paper's
`δ_impl` lower bound and an explicit supported high-score action.
-/
theorem thm_amortized_surrogate_selector_existence
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoFloor rhoStar lambdaFloor bonusFloor : Rat)
    (hRhoFloorPos : 0 < rhoFloor)
    (hLambdaFloorPos : 0 < lambdaFloor)
    (hBonusFloorPos : 0 < bonusFloor)
    (hA1 : surrogateAssumptionA1 rhoFloor rhoStar)
    (hA2 : surrogateAssumptionA2 refLaw highScoreActions lambdaFloor)
    (hA3 : countableSurrogateAssumptionA3 U π t h ω pstar highScoreActions) :
    surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor ≤
        listWeightedSum highScoreActions
          (fun a => (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a) ∧
      ∃ a, a ∈ highScoreActions ∧
        (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a ≠ 0 ∧
        0 < U.semanticSeparation π t h ω pstar := by
  have hRhoStarNonneg : 0 ≤ rhoStar := le_trans (le_of_lt hRhoFloorPos) hA1
  have hScaledRho :
      rhoFloor * lambdaFloor ≤ rhoStar * lambdaFloor := by
    exact mul_le_mul_of_nonneg_right hA1 (le_of_lt hLambdaFloorPos)
  have hScaledMass :
      rhoStar * lambdaFloor ≤ rhoStar * listWeightedSum highScoreActions refLaw.mass := by
    exact mul_le_mul_of_nonneg_left hA2 hRhoStarNonneg
  have hCombined :
      rhoFloor * lambdaFloor ≤ rhoStar * listWeightedSum highScoreActions refLaw.mass := by
    exact le_trans hScaledRho hScaledMass
  have hBonusScaled :
      bonusFloor * (rhoFloor * lambdaFloor) ≤
        bonusFloor * (rhoStar * listWeightedSum highScoreActions refLaw.mass) := by
    exact mul_le_mul_of_nonneg_left hCombined (le_of_lt hBonusFloorPos)
  have hFloorWeight :
      surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor ≤
        listWeightedSum highScoreActions
          (fun a => (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a) := by
    rw [surrogateImplementedLaw_weight_on_highScore highScoreActions refLaw rhoStar bonusFloor]
    unfold surrogateDeltaImpl
    simpa [mul_assoc, mul_left_comm, mul_comm] using hBonusScaled
  have hRefMassPos : 0 < listWeightedSum highScoreActions refLaw.mass := by
    exact lt_of_lt_of_le hLambdaFloorPos hA2
  have hRefMassNe :
      listWeightedSum highScoreActions refLaw.mass ≠ 0 := ne_of_gt hRefMassPos
  rcases listWeightedSum_ne_zero_exists
      (xs := highScoreActions) (f := refLaw.mass) hRefMassNe with
    ⟨a, ha, hRefMassA⟩
  have hRhoStarPos : 0 < rhoStar := lt_of_lt_of_le hRhoFloorPos hA1
  have hMassEq :
      (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a =
        rhoStar * bonusFloor * refLaw.mass a :=
    surrogateImplementedLaw_mass_of_mem ha
  have hImplMass :
      (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a ≠ 0 := by
    rw [hMassEq]
    exact mul_ne_zero
      (mul_ne_zero (ne_of_gt hRhoStarPos) (ne_of_gt hBonusFloorPos))
      hRefMassA
  exact ⟨hFloorWeight, ⟨a, ha, hImplMass, hA3 a ha⟩⟩

/--
Countable support corollary for the deployment-side surrogate wrapper.

This is intentionally weaker than the full concrete theorem: it records the abstract
countable fact that assumptions `(A1)`--`(A3)` already force some supported high-score
action under the implemented law.
-/
theorem cor_amortized_surrogate_selector_support
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoFloor rhoStar lambdaFloor bonusFloor : Rat)
    (hRhoFloorPos : 0 < rhoFloor)
    (hLambdaFloorPos : 0 < lambdaFloor)
    (hBonusFloorPos : 0 < bonusFloor)
    (hA1 : surrogateAssumptionA1 rhoFloor rhoStar)
    (hA2 : surrogateAssumptionA2 refLaw highScoreActions lambdaFloor)
    (hA3 : countableSurrogateAssumptionA3 U π t h ω pstar highScoreActions) :
    ∃ a, a ∈ highScoreActions ∧
      (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a ≠ 0 := by
  rcases (thm_amortized_surrogate_selector_existence
      U π t h ω pstar highScoreActions refLaw
      rhoFloor rhoStar lambdaFloor bonusFloor
      hRhoFloorPos hLambdaFloorPos hBonusFloorPos hA1 hA2 hA3).2 with
    ⟨a, ha, hMass, _⟩
  exact ⟨a, ha, hMass⟩

end CountablePaperSurrogate

noncomputable section ConcretePaperSurrogate

open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/--
Concrete deployed-policy mass assigned to genuinely separating actions under the implemented
surrogate law.

This packages the finite-list separating-support weight without exposing the local
decidability scaffolding of `separatingActionSet` in the paper-facing theorem signatures.
-/
def surrogateImplementedSeparatingMass
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoStar bonusFloor : Rat) : Rat := by
  classical
  exact separatingSupportWeight
    (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
    highScoreActions
    (U.separatingActionSet π h ω pstar)

/--
Lean wrapper for `thm:amortized-surrogate` on the concrete deployment-side stack.

This theorem exposes the paper's load-bearing deployment assumptions `(A1)`--`(A3)` as
finite-list hypotheses and derives the separating-support floor `δ_impl` needed by the
Section 6 recovery theorems.
-/
theorem thm_amortized_surrogate
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoFloor rhoStar lambdaFloor bonusFloor : Rat)
    (hRhoFloorPos : 0 < rhoFloor)
    (hLambdaFloorPos : 0 < lambdaFloor)
    (hBonusFloorPos : 0 < bonusFloor)
    (hA1 : surrogateAssumptionA1 rhoFloor rhoStar)
    (hA2 : surrogateAssumptionA2 refLaw highScoreActions lambdaFloor)
    (hA3 : surrogateAssumptionA3 U π h ω pstar highScoreActions) :
    surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor ≤
        surrogateImplementedSeparatingMass
          U π h ω pstar highScoreActions refLaw rhoStar bonusFloor ∧
    hasSeparatingSupportOn
      (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
      highScoreActions
      (U.separatingActionSet π h ω pstar) := by
  classical
  have hFloorWeight :
      surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor ≤
        surrogateImplementedSeparatingMass
          U π h ω pstar highScoreActions refLaw rhoStar bonusFloor := by
    simpa [surrogateImplementedSeparatingMass, hasSeparatingSupportFloor, separatingSupportWeight] using
      U.surrogateImplementedLaw_hasSeparatingSupportFloor
        π h ω pstar highScoreActions refLaw
        rhoFloor rhoStar lambdaFloor bonusFloor
        hRhoFloorPos hLambdaFloorPos hBonusFloorPos hA1 hA2 hA3
  have hSupport :=
    U.surrogateImplementedLaw_hasSeparatingSupportOn
      π h ω pstar highScoreActions refLaw
      rhoFloor rhoStar lambdaFloor bonusFloor
      hRhoFloorPos hLambdaFloorPos hBonusFloorPos hA1 hA2 hA3
  exact ⟨hFloorWeight, hSupport⟩

/--
Lean wrapper for `cor:amortized-surrogate-finite-time` on the concrete deployment-side
stack.

This is the current finite-time consequence available in the Lean tree: once the
deployment-side assumptions `(A1)`--`(A3)` supply the separating-support floor `δ_impl`,
the deterministic residual-odds finite-time theorem applies immediately.
-/
theorem cor_amortized_surrogate_finite_time
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoFloor rhoStar lambdaFloor bonusFloor : Rat)
    (hRhoFloorPos : 0 < rhoFloor)
    (hLambdaFloorPos : 0 < lambdaFloor)
    (hBonusFloorPos : 0 < bonusFloor)
    (hA1 : surrogateAssumptionA1 rhoFloor rhoStar)
    (hA2 : surrogateAssumptionA2 refLaw highScoreActions lambdaFloor)
    (hA3 : surrogateAssumptionA3 U π h ω pstar highScoreActions)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hDecayPos :
      ∀ ⦃a : A⦄,
        a ∈ highScoreActions →
          (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a ≠ 0 →
            U.isSeparatingAction π h ω pstar a →
              ∃ o,
                0 < (U.observerFiberClassComplement π h a ω pstar).1.mass o ∧
                (U.observerFiberClassComplement π h a ω pstar).2.mass o = 0)
    {N : Nat} {ε : Rat}
    (hε :
      posteriorRateFactorFromFloor N *
        U.residualObserverFiberPosteriorOdds π h ω pstar ≤ ε) :
    oneStepResidualPosteriorConcentrates
        U π h ω pstar highScoreActions
        (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
        (surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor) ∧
      ∀ x : Nat → Rat,
        posteriorDecayRecurrence
            (surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor)
            (U.residualObserverFiberPosteriorOdds π h ω pstar) x →
          x N ≤ ε := by
  have hDeltaPos : 0 < surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor := by
    unfold surrogateDeltaImpl
    have hMul : 0 < rhoFloor * lambdaFloor := mul_pos hRhoFloorPos hLambdaFloorPos
    exact mul_pos hMul hBonusFloorPos
  have hFloorWeight :=
    (thm_amortized_surrogate
      U π h ω pstar highScoreActions refLaw
      rhoFloor rhoStar lambdaFloor bonusFloor
      hRhoFloorPos hLambdaFloorPos hBonusFloorPos
      hA1 hA2 hA3).1
  classical
  have hFloor : hasSeparatingSupportFloor
      (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
      highScoreActions
      (U.separatingActionSet π h ω pstar)
      (surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor) := by
    simpa [surrogateImplementedSeparatingMass, hasSeparatingSupportFloor, separatingSupportWeight] using
      hFloorWeight
  have hDecayPos' :
      ∀ ⦃a : A⦄,
        a ∈ highScoreActions →
          (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a ≠ 0 →
            U.isSeparatingAction π h ω pstar a →
              ∃ o,
                0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ∧
                (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0 := by
    simpa [ConcretePrefixMachine.observerFiberClassComplement] using hDecayPos
  exact cor_separating_support_finite_time_deterministic
    U π h ω pstar highScoreActions
    (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
    hDeltaPos hOdds0 hFloor hDecayPos' hε

/--
Combined H10-facing finite-time surrogate certificate.

The amortized assumptions `(A1)`--`(A3)` still prove the deployment-side
separating-support floor. The finite-horizon residual and posterior-share
bounds are discharged by the explicit zero-out package, not by the asymptotic
H10 main theorem.
-/
theorem cor_amortized_surrogate_finite_time_zeroOutPackage
    [Encodable A] [Encodable O]
    [DecidableEq O] [BEq O] [LawfulBEq O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoFloor rhoStar lambdaFloor bonusFloor : Rat)
    (hRhoFloorPos : 0 < rhoFloor)
    (hLambdaFloorPos : 0 < lambdaFloor)
    (hBonusFloorPos : 0 < bonusFloor)
    (hA1 : surrogateAssumptionA1 rhoFloor rhoStar)
    (hA2 : surrogateAssumptionA2 refLaw highScoreActions lambdaFloor)
    (hA3 :
      surrogateAssumptionA3 U π h ω (U.toEncodedProgram pstar) highScoreActions)
    (δ : Rat) (T : Nat)
    (h𝒵 : ZeroOutRatePackage U π hπ hSem penv pstar ω T) :
    (surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor ≤
        surrogateImplementedSeparatingMass
          U π h ω (U.toEncodedProgram pstar) highScoreActions refLaw rhoStar bonusFloor ∧
      hasSeparatingSupportOn
        (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
        highScoreActions
        (U.separatingActionSet π h ω (U.toEncodedProgram pstar))) ∧
      (∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
          (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
        ∀ N, N ≤ T →
          (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) N ξ ≤
            CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N *
              (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
                (toCountablePolicy π hπ) (U.liftObserver ω)
                (U.toCountableEncodedProgram hSem pstar)) ∧
      (∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
          (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
        ∀ N, N ≤ T →
          (1 + CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N *
            (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar))⁻¹ ≤
            (U.toCountablePrefixMachine hSem).observerFiberPosteriorShareProcess
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) N ξ) := by
  have hSurrogate :=
    thm_amortized_surrogate
      U π h ω (U.toEncodedProgram pstar) highScoreActions refLaw
      rhoFloor rhoStar lambdaFloor bonusFloor
      hRhoFloorPos hLambdaFloorPos hBonusFloorPos hA1 hA2 hA3
  have hRate :=
    zeroOutRatePackage_residualRate
      U π hπ hSem penv pstar ω δ T h𝒵
  have hShare :=
    zeroOutRatePackage_posteriorShareFiniteTime
      U π hπ hSem penv pstar ω δ T h𝒵
  exact ⟨hSurrogate, hRate, hShare⟩

end ConcretePaperSurrogate

end SemanticConvergence
