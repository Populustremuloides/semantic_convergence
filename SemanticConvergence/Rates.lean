import SemanticConvergence.Semantic
import SemanticConvergence.ConcreteRates

namespace SemanticConvergence

universe u v

noncomputable section ConcretePaperRates

open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Lean wrapper for `lem:one-step-drift` on the concrete rate stack. -/
theorem lem_one_step_drift_deterministic
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
theorem prop_exp_rate_deterministic
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
theorem lem_one_step_drift_kernel_deterministic
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
theorem prop_kernel_exp_rate_deterministic
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
theorem thm_exp_rate_concentration_deterministic
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
    prop_exp_rate_deterministic U π h ω p hδ hOdds0
  exact prop_kernel_exp_rate_deterministic U π h ω hView hRate

end ConcretePaperRates

noncomputable section CountablePaperRates

open CountableConcrete
open CountableConcrete.CountablePrefixMachine
open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

/-- Internal witness-transport helper for `lem:one-step-drift`. -/
theorem lem_one_step_drift_of_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ n, n < T →
        U.residualObserverFiberProcess π ω pstar (n + 1) ξ ≤
          posteriorDecayFactorENNReal δ * U.residualObserverFiberProcess π ω pstar n ξ := by
  have hSupportwise :
      U.HasSupportwiseResidualRecurrence π penv ω pstar δ T :=
    U.hasSupportwiseResidualRecurrence_of_witness π penv ω pstar δ T hWitness
  exact U.ae_residualObserverFiberRecurrence_of_supportwise π penv ω pstar δ T
    hSupportwise

/-- Bridged first-principles wrapper for `lem:one-step-drift`. -/
theorem lem_one_step_drift
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar)) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ n, n < T →
        (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar) (n + 1) ξ ≤
          posteriorDecayFactorENNReal δ *
            (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) n ξ := by
  let Uc := U.toCountablePrefixMachine hSem
  let πc := toCountablePolicy π hπ
  let penvc := U.toCountableProgram hSem penv
  let ωc := U.liftObserver ω
  let pstarc := U.toCountableEncodedProgram hSem pstar
  have hWitness : Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pstarc δ T := by
    simpa [Uc, πc, penvc, ωc, pstarc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv pstar ω δ T hStep
  have hDrift :
      ∀ᵐ ξ ∂(Uc.trajectoryLaw πc penvc T).toMeasure,
        ∀ n, n < T →
          Uc.residualObserverFiberProcess πc ωc pstarc (n + 1) ξ ≤
            posteriorDecayFactorENNReal δ * Uc.residualObserverFiberProcess πc ωc pstarc n ξ :=
    lem_one_step_drift_of_witness Uc πc penvc ωc pstarc δ T hWitness
  simpa [Uc, πc, penvc, ωc, pstarc] using hDrift

/-- Internal witness-transport helper for `prop:exp-rate`. -/
theorem prop_exp_rate_of_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ N, N ≤ T →
        U.residualObserverFiberProcess π ω pstar N ξ ≤
          posteriorDecayFactorENNReal δ ^ N *
            U.initialResidualObserverFiberOdds π ω pstar := by
  have hSupportwise :
      U.HasSupportwiseResidualRecurrence π penv ω pstar δ T :=
    U.hasSupportwiseResidualRecurrence_of_witness π penv ω pstar δ T hWitness
  exact U.ae_residualObserverFiberRateBound_of_supportwise π penv ω pstar δ T
    hSupportwise

/-- Lean wrapper for `lem:one-step-drift-kernel` on the countable probabilistic rate stack. -/
theorem lem_one_step_drift_kernel
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (δ : Rat) (T : Nat)
    (hView : ω.view p = ω.view q) :
    U.HasSupportwiseResidualContractionWitness π penv ω p δ T →
      U.HasSupportwiseResidualContractionWitness π penv ω q δ T := by
  intro hWitness
  exact U.hasSupportwiseResidualContractionWitness_of_sameView π penv ω δ T hView hWitness

/-- Bridged first-principles wrapper for `prop:exp-rate`. -/
theorem prop_exp_rate
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar)) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ N, N ≤ T →
        (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar) N ξ ≤
          posteriorDecayFactorENNReal δ ^ N *
            (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) := by
  let Uc := U.toCountablePrefixMachine hSem
  let πc := toCountablePolicy π hπ
  let penvc := U.toCountableProgram hSem penv
  let ωc := U.liftObserver ω
  let pstarc := U.toCountableEncodedProgram hSem pstar
  have hWitness : Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pstarc δ T := by
    simpa [Uc, πc, penvc, ωc, pstarc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv pstar ω δ T hStep
  have hRate :
      ∀ᵐ ξ ∂(Uc.trajectoryLaw πc penvc T).toMeasure,
        ∀ N, N ≤ T →
          Uc.residualObserverFiberProcess πc ωc pstarc N ξ ≤
            posteriorDecayFactorENNReal δ ^ N * Uc.initialResidualObserverFiberOdds πc ωc pstarc :=
    prop_exp_rate_of_witness Uc πc penvc ωc pstarc δ T hWitness
  simpa [Uc, πc, penvc, ωc, pstarc] using hRate

/-- Internal witness-transport helper for `prop:kernel-exp-rate`. -/
theorem prop_kernel_exp_rate_of_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (δ : Rat) (T : Nat)
    (hView : ω.view p = ω.view q)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω p δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ N, N ≤ T →
        U.residualObserverFiberProcess π ω q N ξ ≤
          posteriorDecayFactorENNReal δ ^ N *
            U.initialResidualObserverFiberOdds π ω q := by
  have hWitness' := lem_one_step_drift_kernel U π penv ω δ T hView hWitness
  exact prop_exp_rate_of_witness U π penv ω q δ T hWitness'

/-- Bridged first-principles wrapper for `prop:kernel-exp-rate`. -/
theorem prop_kernel_exp_rate
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv : U.Program)
    (ω : Observer (EncodedProgram A O))
    {p q : U.Program}
    (δ : Rat) (T : Nat)
    (hView : ω.view (U.toEncodedProgram p) = ω.view (U.toEncodedProgram q))
    (hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram p) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram p)) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ N, N ≤ T →
        (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem q) N ξ ≤
          posteriorDecayFactorENNReal δ ^ N *
            (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem q) := by
  let Uc := U.toCountablePrefixMachine hSem
  let πc := toCountablePolicy π hπ
  let penvc := U.toCountableProgram hSem penv
  let ωc := U.liftObserver ω
  let pc := U.toCountableEncodedProgram hSem p
  let qc := U.toCountableEncodedProgram hSem q
  have hWitness :
      Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pc δ T := by
    simpa [Uc, πc, penvc, ωc, pc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv p ω δ T hStep
  have hViewCountable : ωc.view pc = ωc.view qc := by
    exact (U.liftObserver_sameView_toCountableEncodedProgram_iff ω hSem p q).2 hView
  have hWitness' := lem_one_step_drift_kernel Uc πc penvc ωc δ T hViewCountable hWitness
  simpa [Uc, πc, penvc, ωc, qc] using
    prop_exp_rate_of_witness Uc πc penvc ωc qc δ T hWitness'

/-- Internal witness-transport helper for `thm:exp-rate-concentration`. -/
theorem thm_exp_rate_concentration_of_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (δ : Rat) (T : Nat)
    (hView : ω.view p = ω.view q)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω p δ T)
    (hInitTop : U.initialResidualObserverFiberOdds π ω p ≠ ⊤) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ N, N ≤ T →
        (1 + posteriorDecayFactorENNReal δ ^ N *
          U.initialResidualObserverFiberOdds π ω q)⁻¹ ≤
          U.observerFiberPosteriorShareProcess π ω q N ξ := by
  have hWitness' := lem_one_step_drift_kernel U π penv ω δ T hView hWitness
  have hInitEq := U.initialResidualObserverFiberOdds_eq_of_sameView π ω hView
  have hInitTop' : U.initialResidualObserverFiberOdds π ω q ≠ ⊤ := by
    simpa [hInitEq] using hInitTop
  exact cor_separating_support_finite_time_of_witness U π penv ω q δ T hWitness' hInitTop'

/-- Bridged first-principles wrapper for `thm:exp-rate-concentration`. -/
theorem thm_exp_rate_concentration
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv : U.Program)
    (ω : Observer (EncodedProgram A O))
    {p q : U.Program}
    (δ : Rat) (T : Nat)
    (hView : ω.view (U.toEncodedProgram p) = ω.view (U.toEncodedProgram q))
    (hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram p) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram p))
    (hInitTop :
      (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
          (toCountablePolicy π hπ) (U.liftObserver ω)
          (U.toCountableEncodedProgram hSem p) ≠ ⊤) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ N, N ≤ T →
        (1 + posteriorDecayFactorENNReal δ ^ N *
          (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem q))⁻¹ ≤
          (U.toCountablePrefixMachine hSem).observerFiberPosteriorShareProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem q) N ξ := by
  let Uc := U.toCountablePrefixMachine hSem
  let πc := toCountablePolicy π hπ
  let penvc := U.toCountableProgram hSem penv
  let ωc := U.liftObserver ω
  let pc := U.toCountableEncodedProgram hSem p
  let qc := U.toCountableEncodedProgram hSem q
  have hWitness :
      Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pc δ T := by
    simpa [Uc, πc, penvc, ωc, pc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv p ω δ T hStep
  have hViewCountable : ωc.view pc = ωc.view qc := by
    exact (U.liftObserver_sameView_toCountableEncodedProgram_iff ω hSem p q).2 hView
  have hWitness' := lem_one_step_drift_kernel Uc πc penvc ωc δ T hViewCountable hWitness
  have hInitEq := Uc.initialResidualObserverFiberOdds_eq_of_sameView πc ωc hViewCountable
  have hInitTop' :
      Uc.initialResidualObserverFiberOdds πc ωc qc ≠ ⊤ := by
    intro hTop
    exact hInitTop (hInitEq.trans hTop)
  simpa [Uc, πc, penvc, ωc, qc] using
    cor_separating_support_finite_time_of_witness Uc πc penvc ωc qc δ T hWitness' hInitTop'

end CountablePaperRates

end SemanticConvergence
