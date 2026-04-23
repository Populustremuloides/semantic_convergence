import SemanticConvergence.Boundary
import SemanticConvergence.Semantic
import SemanticConvergence.ConcreteSurrogate

namespace SemanticConvergence

universe u v

noncomputable section CountablePaperSurrogate

open CountableConcrete
open CountableConcrete.CountablePrefixMachine

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

/-- Helper theorem retaining the old singleton-selector existence result. -/
theorem thm_amortized_surrogate_selector_existence
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
theorem cor_amortized_surrogate_selector_support
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) :
    (surrogateChosenLaw U π t h actions hActions ω pstar refLaw reg).mass
      (surrogateArgmin U π t h actions hActions ω pstar refLaw reg) ≠ 0 := by
  simp [surrogateChosenLaw, singletonActionLaw]

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

end ConcretePaperSurrogate

end SemanticConvergence
