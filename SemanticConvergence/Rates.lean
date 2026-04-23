import SemanticConvergence.Semantic
import SemanticConvergence.ConcreteRates

namespace SemanticConvergence

universe u v

noncomputable section ConcretePaperRates

open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Lean wrapper for `lem:one-step-drift` on the concrete rate stack. -/
theorem lem_one_step_drift
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A)
    {δ : Rat} (hδ : 0 < δ)
    {δDrift δGain : Float}
    (hDrift : δDrift ≤ U.oneStepLogOddsDrift π h h' ω pstar)
    (hGain : U.hasExpectedGainLowerBound π h ω pstar κ δGain)
    (hOdds0 : 0 ≤ U.observerFiberPosteriorOdds π h ω pstar) :
    U.hasConcentrationCertificate π h h' ω pstar κ δDrift δGain := by
  refine ⟨δ, hδ, hDrift, hGain, hOdds0, ?_⟩
  intro x hx0 hStep N
  exact ConcretePrefixMachine.posteriorRateBound_of_positiveDecay
    (δ := δ) hδ hOdds0 hx0 hStep N

/-- Lean wrapper for `prop:exp-rate` on the concrete rate stack. -/
theorem prop_exp_rate
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {δ : Rat} (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar) :
    ∀ x : Nat → Rat,
      x 0 = U.residualObserverFiberPosteriorOdds π h ω pstar →
      (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
      ∀ N, x N ≤ posteriorRateFactorFromFloor N *
        U.residualObserverFiberPosteriorOdds π h ω pstar := by
  intro x hx0 hStep N
  have hBound :=
    ConcretePrefixMachine.posteriorRateBound_of_positiveDecay
      (δ := δ) hδ hOdds0 hx0 hStep N
  simpa using hBound

/-- Lean wrapper for `lem:one-step-drift-kernel` on the concrete rate stack. -/
theorem lem_one_step_drift_kernel
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (κ : ActionLaw A)
    {p q : EncodedProgram A O}
    {δDrift δGain : Float}
    (hView : ω.view p = ω.view q) :
    U.hasConcentrationCertificate π h h' ω p κ δDrift δGain →
      U.hasConcentrationCertificate π h h' ω q κ δDrift δGain := by
  intro hCert
  rcases hCert with ⟨δ, hδ, hDrift, hGain, hOdds0, hRate⟩
  have hDriftEq := U.oneStepLogOddsDrift_eq_of_sameView π h h' ω hView
  have hGainEq := U.expectedSemanticGain_eq_of_sameView π h ω κ hView
  have hOddsEq := U.observerFiberPosteriorOdds_eq_of_sameView π h ω hView
  refine ⟨δ, hδ, ?_, ?_, ?_, ?_⟩
  · simpa [hDriftEq] using hDrift
  · simpa [ConcretePrefixMachine.hasExpectedGainLowerBound, hGainEq] using hGain
  · simpa [hOddsEq] using hOdds0
  · intro x hx0 hStep N
    have hx0' : x 0 = U.observerFiberPosteriorOdds π h ω p := by
      simpa [hOddsEq] using hx0
    have hBound := hRate x hx0' hStep N
    simpa [hOddsEq] using hBound

/-- Lean wrapper for `prop:kernel-exp-rate` on the concrete rate stack. -/
theorem prop_kernel_exp_rate
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    {δ : Rat}
    (hView : ω.view p = ω.view q) :
    (∀ x : Nat → Rat,
      x 0 = U.residualObserverFiberPosteriorOdds π h ω p →
      (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
      ∀ N, x N ≤ posteriorRateFactorFromFloor N *
        U.residualObserverFiberPosteriorOdds π h ω p) →
    ∀ x : Nat → Rat,
      x 0 = U.residualObserverFiberPosteriorOdds π h ω q →
      (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
      ∀ N, x N ≤ posteriorRateFactorFromFloor N *
        U.residualObserverFiberPosteriorOdds π h ω q := by
  intro hRate x hx0 hStep N
  have hOddsEq := U.residualObserverFiberPosteriorOdds_eq_of_sameView π h ω hView
  have hx0' : x 0 = U.residualObserverFiberPosteriorOdds π h ω p := by
    simpa [hOddsEq] using hx0
  have hBound := hRate x hx0' hStep N
  simpa [hOddsEq] using hBound

/-- Lean wrapper for `thm:exp-rate-concentration` on the concrete rate stack. -/
theorem thm_exp_rate_concentration
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    {δ : Rat} (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω p)
    (hView : ω.view p = ω.view q) :
    ∀ x : Nat → Rat,
      x 0 = U.residualObserverFiberPosteriorOdds π h ω q →
      (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
      ∀ N, x N ≤ posteriorRateFactorFromFloor N *
        U.residualObserverFiberPosteriorOdds π h ω q := by
  have hRate :=
    prop_exp_rate U π h ω p hδ hOdds0
  exact prop_kernel_exp_rate U π h ω hView hRate

end ConcretePaperRates

end SemanticConvergence
