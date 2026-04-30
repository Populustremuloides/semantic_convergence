import SemanticConvergence.ConcretePosteriorDecay

namespace SemanticConvergence

universe u v

open Classical

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Nonnegativity of the smoothed class/complement residual likelihood ratio. -/
theorem softClassResidualLikelihoodRatio_nonneg
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (hOut0 : 0 ≤ (U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o)
    (hInPos : 0 < (U.softPredictiveLawInClass π h a C refLaw ε).mass o) :
    0 ≤
      (((U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o /
        (U.softPredictiveLawInClass π h a C refLaw ε).mass o : Rat) : Real) := by
  rw [Rat.cast_div]
  have hOut0Real :
      0 ≤ ((U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o : Real) := by
    exact_mod_cast hOut0
  have hIn0Real :
      0 ≤ ((U.softPredictiveLawInClass π h a C refLaw ε).mass o : Real) := by
    exact_mod_cast (le_of_lt hInPos)
  exact div_nonneg hOut0Real hIn0Real

/-- Observer-fiber specialization of residual likelihood-ratio nonnegativity. -/
theorem softObserverFiberResidualLikelihoodRatio_nonneg
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (hOut0 :
      0 ≤
        (U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o)
    (hInPos :
      0 <
        (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) :
    0 ≤
      (((U.softPredictiveLawOutsideClass
          π h a (U.observerFiber ω pstar) refLaw ε).mass o /
        (U.softPredictiveLawInClass
          π h a (U.observerFiber ω pstar) refLaw ε).mass o : Rat) : Real) := by
  exact
    U.softClassResidualLikelihoodRatio_nonneg
      π h a (U.observerFiber ω pstar) refLaw ε o hOut0 hInPos

/--
Real square-root form of the smoothed Bayes residual-odds update.

This is the local Hellinger algebra that the Section 6 martingale spine needs: after a
nondegenerate one-step Bayes update, the square root of the next residual odds is the
square root of the current residual odds times the square root of the residual likelihood
ratio. The remaining hypotheses are intentionally explicit because `ConcreteLaw` stores
finite mass functions without a global probability-law nonnegativity invariant.
-/
theorem sqrt_softOneStepClassResidualOdds_eq_sqrt_mul_sqrt_likelihoodRatio
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (hOdds0 : 0 ≤ U.residualClassPosteriorOdds π h C)
    (hInPos : 0 < (U.softPredictiveLawInClass π h a C refLaw ε).mass o) :
    Real.sqrt (U.softOneStepClassResidualOdds π h a C refLaw ε o : Real) =
      Real.sqrt (U.residualClassPosteriorOdds π h C : Real) *
        Real.sqrt
          (((U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o /
            (U.softPredictiveLawInClass π h a C refLaw ε).mass o : Rat) : Real) := by
  have hIn :
      (U.softPredictiveLawInClass π h a C refLaw ε).mass o ≠ 0 :=
    ne_of_gt hInPos
  have hOdds0Real :
      0 ≤ (U.residualClassPosteriorOdds π h C : Real) := by
    exact_mod_cast hOdds0
  by_cases hClass : U.posteriorClassMass π h C = 0
  · have hResidualZero :
        U.residualClassPosteriorOdds π h C = 0 := by
      simp [residualClassPosteriorOdds, hClass]
    have hSoftZero :
        U.softOneStepClassResidualOdds π h a C refLaw ε o = 0 := by
      simp [softOneStepClassResidualOdds, softOneStepClassObservationMass, hClass]
    simp [hResidualZero, hSoftZero]
  · have hUpdate :=
      U.softOneStepClassResidualOdds_eq_mul_likelihoodRatio
        π h a C refLaw ε o hClass hIn
    rw [hUpdate]
    rw [Rat.cast_mul]
    exact Real.sqrt_mul hOdds0Real _

/--
Observer-fiber specialization of the Hellinger square-root Bayes update.
-/
theorem sqrt_softOneStepObserverFiberResidualOdds_eq_sqrt_mul_sqrt_likelihoodRatio
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hInPos :
      0 <
        (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) :
    Real.sqrt (U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o : Real) =
      Real.sqrt (U.residualObserverFiberPosteriorOdds π h ω pstar : Real) *
        Real.sqrt
          (((U.softPredictiveLawOutsideClass
              π h a (U.observerFiber ω pstar) refLaw ε).mass o /
            (U.softPredictiveLawInClass
              π h a (U.observerFiber ω pstar) refLaw ε).mass o : Rat) : Real) := by
  simpa [residualObserverFiberPosteriorOdds, softOneStepObserverFiberResidualOdds] using
    U.sqrt_softOneStepClassResidualOdds_eq_sqrt_mul_sqrt_likelihoodRatio
      π h a (U.observerFiber ω pstar) refLaw ε o hOdds0 hInPos

/--
Square-root form of a one-step residual-odds decay bound.

This is the deterministic inequality companion to the Hellinger identity above: once a
soft one-step residual update is bounded by `posteriorDecayFactor δ` times the current
residual odds, the same bound holds after taking square roots.
-/
theorem sqrt_softOneStepObserverFiberResidualOdds_le_sqrt_decayFactor_mul_sqrt_residual
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (δ : Rat)
    (hBound :
      U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o ≤
        posteriorDecayFactor δ * U.residualObserverFiberPosteriorOdds π h ω pstar) :
    Real.sqrt (U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o : Real) ≤
      Real.sqrt (posteriorDecayFactor δ : Real) *
        Real.sqrt (U.residualObserverFiberPosteriorOdds π h ω pstar : Real) := by
  have hBoundReal :
      (U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o : Real) ≤
        ((posteriorDecayFactor δ *
          U.residualObserverFiberPosteriorOdds π h ω pstar : Rat) : Real) := by
    exact_mod_cast hBound
  have hFactor0Real : 0 ≤ (posteriorDecayFactor δ : Real) := by
    exact_mod_cast posteriorDecayFactor_nonneg δ
  calc
    Real.sqrt (U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o : Real) ≤
        Real.sqrt
          ((posteriorDecayFactor δ *
            U.residualObserverFiberPosteriorOdds π h ω pstar : Rat) : Real) := by
          exact Real.sqrt_le_sqrt hBoundReal
    _ = Real.sqrt
          ((posteriorDecayFactor δ : Real) *
            (U.residualObserverFiberPosteriorOdds π h ω pstar : Real)) := by
          norm_num
    _ = Real.sqrt (posteriorDecayFactor δ : Real) *
        Real.sqrt (U.residualObserverFiberPosteriorOdds π h ω pstar : Real) := by
          exact Real.sqrt_mul hFactor0Real _

end ConcretePrefixMachine

end

end SemanticConvergence
