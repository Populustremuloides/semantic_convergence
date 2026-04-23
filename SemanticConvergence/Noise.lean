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
theorem cor_noise_transfer
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
  · exact thm_exp_rate_concentration U π h ω hδ hOdds0 hView

end ConcretePaperNoise

end SemanticConvergence
