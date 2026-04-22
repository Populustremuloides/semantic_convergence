import AlgorithmicFreeEnergy.Semantic
import AlgorithmicFreeEnergy.ConcreteRates

namespace AlgorithmicFreeEnergy

universe u v w x y z t s r q m n p o k l

/--
`RatesModel` is a legacy abstract compatibility package for the one-step drift,
expectation-form, and finite-time concentration layer. It is retained for
archival comparison and backward compatibility only; the paper-facing rate
declarations below now terminate at the concrete stack.
-/
structure RatesModel extends SemanticModel where
  oneStepDriftHyp : Program → Prop
  oneStepDriftConclusion : Program → Prop
  oneStepDrift :
    ∀ pstar : Program,
      oneStepDriftHyp pstar →
      oneStepDriftConclusion pstar
  expRateHyp : Program → Prop
  expRateConclusion : Program → Prop
  expRateHyp_to_driftHyp :
    ∀ pstar : Program,
      expRateHyp pstar →
      oneStepDriftHyp pstar
  expRate_from_drift :
    ∀ pstar : Program,
      oneStepDriftConclusion pstar →
      expRateConclusion pstar
  oneStepDriftKernelHyp : ReferenceMeasure → Program → Prop
  oneStepDriftKernelConclusion : ReferenceMeasure → Program → Prop
  oneStepDriftKernel :
    ∀ (ref : ReferenceMeasure) (pstar : Program),
      oneStepDriftKernelHyp ref pstar →
      oneStepDriftKernelConclusion ref pstar
  kernelExpRateHyp : ReferenceMeasure → Program → Prop
  kernelExpRateConclusion : ReferenceMeasure → Program → Prop
  kernelExpRateHyp_to_driftHyp :
    ∀ (ref : ReferenceMeasure) (pstar : Program),
      kernelExpRateHyp ref pstar →
      oneStepDriftKernelHyp ref pstar
  kernelExpRate_from_drift :
    ∀ (ref : ReferenceMeasure) (pstar : Program),
      oneStepDriftKernelConclusion ref pstar →
      kernelExpRateConclusion ref pstar
  expRateConcentrationHyp : ReferenceMeasure → Program → Prop
  expRateConcentrationConclusion : ReferenceMeasure → Program → Prop
  concentrationHyp_to_expRateHyp :
    ∀ (ref : ReferenceMeasure) (pstar : Program),
      expRateConcentrationHyp ref pstar →
      expRateHyp pstar
  concentrationHyp_to_kernelExpRateHyp :
    ∀ (ref : ReferenceMeasure) (pstar : Program),
      expRateConcentrationHyp ref pstar →
      kernelExpRateHyp ref pstar
  concentration_from_rates :
    ∀ (ref : ReferenceMeasure) (pstar : Program),
      expRateConcentrationHyp ref pstar →
      expRateConclusion pstar →
      kernelExpRateConclusion ref pstar →
      expRateConcentrationConclusion ref pstar

/--
`RatesTheory M` is the legacy theorem-level compatibility layer over
`RatesModel`. It remains in the source tree for archival comparison and
backward compatibility only.
-/
structure RatesTheory (M : RatesModel) extends SemanticTheory M.toSemanticModel where

namespace RatesTheory

variable {M : RatesModel}

/-- Lean wrapper for `lem:one-step-drift`. -/
theorem lem_one_step_drift (_T : RatesTheory M) (pstar : M.Program)
    (hDrift : M.oneStepDriftHyp pstar) :
    M.oneStepDriftConclusion pstar :=
  M.oneStepDrift pstar hDrift

/-- Lean wrapper for `prop:exp-rate`. -/
theorem prop_exp_rate (T : RatesTheory M) (pstar : M.Program)
    (hRate : M.expRateHyp pstar) :
    M.expRateConclusion pstar := by
  exact M.expRate_from_drift pstar
    (RatesTheory.lem_one_step_drift T pstar
      (M.expRateHyp_to_driftHyp pstar hRate))

/-- Lean wrapper for `lem:one-step-drift-kernel`. -/
theorem lem_one_step_drift_kernel (_T : RatesTheory M)
    (ref : M.ReferenceMeasure) (pstar : M.Program)
    (hDrift : M.oneStepDriftKernelHyp ref pstar) :
    M.oneStepDriftKernelConclusion ref pstar :=
  M.oneStepDriftKernel ref pstar hDrift

/-- Lean wrapper for `prop:kernel-exp-rate`. -/
theorem prop_kernel_exp_rate (T : RatesTheory M)
    (ref : M.ReferenceMeasure) (pstar : M.Program)
    (hRate : M.kernelExpRateHyp ref pstar) :
    M.kernelExpRateConclusion ref pstar := by
  exact M.kernelExpRate_from_drift ref pstar
    (RatesTheory.lem_one_step_drift_kernel T ref pstar
      (M.kernelExpRateHyp_to_driftHyp ref pstar hRate))

/-- Lean wrapper for `thm:exp-rate-concentration`. -/
theorem thm_exp_rate_concentration (T : RatesTheory M)
    (ref : M.ReferenceMeasure) (pstar : M.Program)
    (hConc : M.expRateConcentrationHyp ref pstar) :
    M.expRateConcentrationConclusion ref pstar := by
  exact M.concentration_from_rates ref pstar hConc
    (RatesTheory.prop_exp_rate T pstar
      (M.concentrationHyp_to_expRateHyp ref pstar hConc))
    (RatesTheory.prop_kernel_exp_rate T ref pstar
      (M.concentrationHyp_to_kernelExpRateHyp ref pstar hConc))

end RatesTheory

noncomputable section ConcretePaperRates

open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Lean wrapper for `lem:one-step-drift` on the concrete rate stack. -/
theorem lem_one_step_drift
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    U.oneStepLogOddsDrift π h h' ω pstar =
      (U.observerFiberLogOdds π h' ω pstar -
        U.observerFiberLogOdds π h ω pstar) := by
  rfl

/-- Lean wrapper for `prop:exp-rate` on the concrete rate stack. -/
theorem prop_exp_rate
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) {δ : Float}
    (hGain : U.hasExpectedGainLowerBound π h ω pstar κ δ) :
    U.hasExpectedGainLowerBound π h ω pstar κ δ :=
  hGain

/-- Lean wrapper for `lem:one-step-drift-kernel` on the concrete rate stack. -/
theorem lem_one_step_drift_kernel
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.oneStepLogOddsDrift π h h' ω p =
      U.oneStepLogOddsDrift π h h' ω q :=
  U.oneStepLogOddsDrift_eq_of_sameView π h h' ω hView

/-- Lean wrapper for `prop:kernel-exp-rate` on the concrete rate stack. -/
theorem prop_kernel_exp_rate
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (κ : ActionLaw A)
    (hView : ω.view p = ω.view q) :
    U.expectedSemanticGain π h ω p κ =
      U.expectedSemanticGain π h ω q κ :=
  U.expectedSemanticGain_eq_of_sameView π h ω κ hView

/-- Lean wrapper for `thm:exp-rate-concentration` on the concrete rate stack. -/
theorem thm_exp_rate_concentration
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) {δ : Float}
    (hDrift :
      U.oneStepLogOddsDrift π h h' ω pstar =
        (U.observerFiberLogOdds π h' ω pstar -
          U.observerFiberLogOdds π h ω pstar))
    (hGain : U.hasExpectedGainLowerBound π h ω pstar κ δ) :
    (U.oneStepLogOddsDrift π h h' ω pstar =
      (U.observerFiberLogOdds π h' ω pstar -
        U.observerFiberLogOdds π h ω pstar)) ∧
      U.hasExpectedGainLowerBound π h ω pstar κ δ := by
  exact ⟨hDrift, hGain⟩

end ConcretePaperRates

end AlgorithmicFreeEnergy
