import SemanticConvergence.Rates
import SemanticConvergence.ConcreteNoise

namespace SemanticConvergence

universe u v w

noncomputable section ConcretePaperNoise

open ConcretePrefixMachine

variable {A : Type u} {O : Type v} {O' : Type w}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
variable [DecidableEq O'] [BEq O'] [LawfulBEq O']

/-- Lean wrapper for `def:decodable-channel` on the concrete noise stack. -/
def def_decodable_channel (K : ObsChannel O O') : Prop :=
  DecodableChannel K

/-- Lean wrapper for `def:left-invertible-channel` on the concrete noise stack. -/
def def_left_invertible_channel (K : ObsChannel O O') : Prop :=
  SupportLeftInvertibleChannel K

/-- Lean wrapper for `prop:noise-immunity` on the concrete noise stack. -/
theorem prop_noise_immunity
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (K : ObsChannel O O')
    (hView : ω.view p = ω.view q) :
    U.noisySemanticSeparation π h a ω p K =
      U.noisySemanticSeparation π h a ω q K := by
  have hPair :=
    U.noisyObserverFiberClassComplement_eq_of_sameView π h a ω K hView
  simpa [ConcretePrefixMachine.noisySemanticSeparation] using
    congrArg (fun pair => bhatSeparation pair.1 pair.2) hPair

/-- Lean wrapper for `prop:noise-left-invertible` on the concrete noise stack. -/
theorem prop_noise_left_invertible
    (K : ObsChannel O O')
    (hInv : def_left_invertible_channel K) :
    ∃ decode : O' → O, DecodableWith K decode := by
  rcases hInv with ⟨decode, hdecode⟩
  exact ⟨decode, hdecode⟩

/-- Lean wrapper for `prop:noise-decoding` on the concrete noise stack. -/
theorem prop_noise_decoding
    (K : ObsChannel O O')
    (hDec : def_decodable_channel K) :
    SupportLeftInvertibleChannel K := by
  rcases hDec with ⟨decode, hdecode⟩
  exact ⟨decode, hdecode⟩

/-- Lean wrapper for `cor:noise-transfer` on the concrete noise stack. -/
theorem cor_noise_transfer_deterministic
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (K : ObsChannel O O')
    {δ : Rat} (hδ : 0 < δ)
    (hDec : def_decodable_channel K)
    (hView : ω.view p = ω.view q)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω p) :
    def_left_invertible_channel K ∧
      U.noisySemanticSeparation π h a ω p K =
        U.noisySemanticSeparation π h a ω q K ∧
      (∀ x : Nat → Rat,
        x 0 = U.residualObserverFiberPosteriorOdds π h ω q →
        (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
        ∀ N, x N ≤ posteriorRateFactorFromFloor N *
          U.residualObserverFiberPosteriorOdds π h ω q) := by
  refine ⟨prop_noise_decoding K hDec, ?_, ?_⟩
  · exact prop_noise_immunity U π h a ω K hView
  · exact thm_exp_rate_concentration_deterministic U π h ω hδ hOdds0 hView

end ConcretePaperNoise

noncomputable section CountablePaperNoise

open CountableConcrete
open CountableConcrete.CountablePrefixMachine
open ConcretePrefixMachine

variable {A : Type u} {O : Type v} {O' : Type w}
variable [Encodable A] [Encodable O]
variable [DecidableEq O'] [BEq O'] [LawfulBEq O']

/-- Internal witness-transport helper for `cor:noise-transfer`. -/
theorem cor_noise_transfer_of_witness
    (K : ObsChannel O O')
    (hDec : def_decodable_channel K)
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (δ : Rat) (T : Nat)
    (hView : ω.view p = ω.view q)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω p δ T)
    (hInitTop : U.initialResidualObserverFiberOdds π ω p ≠ ⊤) :
    def_left_invertible_channel K ∧
      ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
        ∀ N, N ≤ T →
          (1 + posteriorDecayFactorENNReal δ ^ N *
            U.initialResidualObserverFiberOdds π ω q)⁻¹ ≤
            U.observerFiberPosteriorShareProcess π ω q N ξ := by
  rcases hDec with ⟨decode, hdecode⟩
  refine ⟨⟨decode, hdecode⟩, ?_⟩
  exact thm_exp_rate_concentration_of_witness U π penv ω δ T hView hWitness hInitTop

/-- Bridged first-principles wrapper for `cor:noise-transfer`. -/
theorem cor_noise_transfer
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (K : ObsChannel O O')
    (hDec : def_decodable_channel K)
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
    def_left_invertible_channel K ∧
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
  rcases hDec with ⟨decode, hdecode⟩
  refine ⟨⟨decode, hdecode⟩, ?_⟩
  exact thm_exp_rate_concentration
    U hCodes π hπ hπN hSem hSemN penv ω δ T hView hStep hInitTop

end CountablePaperNoise

end SemanticConvergence
