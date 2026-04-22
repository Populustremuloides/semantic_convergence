import AlgorithmicFreeEnergy.Semantic
import AlgorithmicFreeEnergy.ConcreteNoise

namespace AlgorithmicFreeEnergy

universe u v w x y z t s r q m n p o k l

/--
`NoiseModel` is a legacy abstract compatibility package for the
corrupted-observation and noise-transfer layer. It is retained for archival
comparison and backward compatibility only; the paper-facing noise declarations
below now terminate at the concrete stack.
-/
structure NoiseModel extends SemanticModel where
  CorruptedObservation : Type
  CorruptedHistory : Type
  Channel : Type
  decodableChannel : Channel → Prop
  leftInvertibleChannel : Channel → Prop
  corruptedObserverLaw : Channel → ObsClass → Action → CorruptedHistory → LawObs
  corruptedSeparation : Channel → ObsClass → Action → CorruptedHistory → Rat
  noiseImmunityConclusion : Channel → ObsClass → Action → History → Prop
  noiseImmunity :
    ∀ (K : Channel) (c : ObsClass) (a : Action) (h : History),
      noiseImmunityConclusion K c a h
  noiseLeftInvertibleConclusion : Channel → Rat → Prop
  noiseLeftInvertible :
    ∀ (K : Channel) (η : Rat),
      leftInvertibleChannel K →
      noiseLeftInvertibleConclusion K η
  noiseDecodingConclusion : Channel → Prop
  noiseDecoding :
    ∀ K : Channel,
      decodableChannel K →
      noiseDecodingConclusion K
  noiseTransferHyp : Channel → Program → Prop
  noiseTransferConclusion : Channel → Program → Prop
  noiseTransfer_to_semanticHyp :
    ∀ (K : Channel) (pstar : Program),
      noiseTransferHyp K pstar →
      canonicalSelectorHyp pstar
  noiseTransfer_from_concentration :
    ∀ (K : Channel) (pstar : Program),
      posteriorConcentrates pstar →
      noiseTransferConclusion K pstar
  noiseLeftInvertibleHistoryIndependentHyp : Channel → Program → Prop
  noiseLeftInvertibleHistoryIndependentConclusion : Channel → Program → Prop
  noiseLeftInvertibleHistoryIndependent_to_semanticHyp :
    ∀ (K : Channel) (pstar : Program),
      noiseLeftInvertibleHistoryIndependentHyp K pstar →
      canonicalSelectorHyp pstar
  noiseLeftInvertibleHistoryIndependent_from_concentration :
    ∀ (K : Channel) (pstar : Program),
      posteriorConcentrates pstar →
      noiseLeftInvertibleHistoryIndependentConclusion K pstar

namespace NoiseModel

variable (M : NoiseModel)

/-- Lean wrapper for `def:decodable-channel`. -/
def def_decodable_channel (K : M.Channel) : Prop :=
  M.decodableChannel K

/-- Lean wrapper for `def:left-invertible-channel`. -/
def def_left_invertible_channel (K : M.Channel) : Prop :=
  M.leftInvertibleChannel K

end NoiseModel

/--
`NoiseTheory M` is the legacy theorem-level compatibility layer over
`NoiseModel`. It remains in the source tree for archival comparison and
backward compatibility only.
-/
structure NoiseTheory (M : NoiseModel) extends SemanticTheory M.toSemanticModel where

namespace NoiseTheory

variable {M : NoiseModel}

/-- Lean wrapper for `prop:noise-immunity`. -/
theorem prop_noise_immunity (_T : NoiseTheory M)
    (K : M.Channel) (c : M.ObsClass) (a : M.Action) (h : M.History) :
    M.noiseImmunityConclusion K c a h :=
  M.noiseImmunity K c a h

/-- Lean wrapper for `prop:noise-left-invertible`. -/
theorem prop_noise_left_invertible (_T : NoiseTheory M)
    (K : M.Channel) (η : Rat)
    (hInv : M.def_left_invertible_channel K) :
    M.noiseLeftInvertibleConclusion K η :=
  M.noiseLeftInvertible K η hInv

/-- Lean wrapper for `prop:noise-decoding`. -/
theorem prop_noise_decoding (_T : NoiseTheory M) (K : M.Channel)
    (hDec : M.def_decodable_channel K) :
    M.noiseDecodingConclusion K :=
  M.noiseDecoding K hDec

/-- Lean wrapper for `cor:noise-transfer`. -/
theorem cor_noise_transfer (T : NoiseTheory M)
    (K : M.Channel) (pstar : M.Program)
    (hTransfer : M.noiseTransferHyp K pstar) :
    M.noiseTransferConclusion K pstar := by
  exact M.noiseTransfer_from_concentration K pstar
    (SemanticTheory.thm_semantic_convergence T.toSemanticTheory pstar
      (M.noiseTransfer_to_semanticHyp K pstar hTransfer))

/-- Lean wrapper for `cor:noise-left-invertible-history-independent`. -/
theorem cor_noise_left_invertible_history_independent (T : NoiseTheory M)
    (K : M.Channel) (pstar : M.Program)
    (hTransfer : M.noiseLeftInvertibleHistoryIndependentHyp K pstar) :
    M.noiseLeftInvertibleHistoryIndependentConclusion K pstar := by
  exact M.noiseLeftInvertibleHistoryIndependent_from_concentration K pstar
    (SemanticTheory.thm_semantic_convergence T.toSemanticTheory pstar
      (M.noiseLeftInvertibleHistoryIndependent_to_semanticHyp K pstar hTransfer))

end NoiseTheory

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
      U.noisySemanticSeparation π h a ω q K :=
  U.noisySemanticSeparation_eq_of_sameView π h a ω K hView

/-- Lean wrapper for `prop:noise-left-invertible` on the concrete noise stack. -/
theorem prop_noise_left_invertible
    (K : ObsChannel O O')
    (hInv : def_left_invertible_channel K) :
    SupportLeftInvertibleChannel K :=
  hInv

/-- Lean wrapper for `prop:noise-decoding` on the concrete noise stack. -/
theorem prop_noise_decoding
    (K : ObsChannel O O')
    (hDec : def_decodable_channel K) :
    SupportLeftInvertibleChannel K :=
  decodable_implies_supportLeftInvertible hDec

/-- Lean wrapper for `cor:noise-transfer` on the concrete noise stack. -/
theorem cor_noise_transfer :
    def_decodable_channel (identityChannel (O := O)) :=
  ConcretePrefixMachine.identityChannel_is_decodable (O := O)

end ConcretePaperNoise

end AlgorithmicFreeEnergy
