import SemanticConvergence.ConcreteRates

namespace SemanticConvergence

universe u v w

open Classical

noncomputable section

/-- Concrete discrete observation channel from `O` into `O'`. -/
abbrev ObsChannel (O : Type u) (O' : Type v) := O → ConcreteLaw O'

section Channels

variable {O : Type u} {O' : Type v}
variable [DecidableEq O'] [BEq O'] [LawfulBEq O']

/-- Push a concrete observation law through a concrete channel. -/
def channelImage (K : ObsChannel O O') (μ : ConcreteLaw O) : ConcreteLaw O' :=
  mixLaw μ K

/-- Pointwise extension of a channel to a pair of laws. -/
def channelImagePair (K : ObsChannel O O')
    (pair : ConcreteLaw O × ConcreteLaw O) : ConcreteLaw O' × ConcreteLaw O' :=
  (channelImage K pair.1, channelImage K pair.2)

/-- Deterministic channel induced by a plain observation map. -/
def deterministicChannel (f : O → O') : ObsChannel O O' :=
  fun o => ConcreteLaw.pure (f o)

/-- Identity observation channel. -/
def identityChannel [DecidableEq O] [BEq O] [LawfulBEq O] : ObsChannel O O :=
  deterministicChannel id

/--
Concrete decodability: every positive-mass emitted symbol decodes back to the source
observation.
-/
def DecodableWith (K : ObsChannel O O') (decode : O' → O) : Prop :=
  ∀ o o', (K o).mass o' ≠ 0 → decode o' = o

/-- A concrete observation channel is decodable when some decoder witnesses it. -/
def DecodableChannel (K : ObsChannel O O') : Prop :=
  ∃ decode : O' → O, DecodableWith K decode

/--
Concrete support-left-invertibility: after applying a decoder, every positive-mass output
already identifies the unique source observation that emitted it.
-/
def SupportLeftInvertibleChannel (K : ObsChannel O O') : Prop :=
  ∃ decode : O' → O, DecodableWith K decode

theorem identityChannel_decodable
    [DecidableEq O] [BEq O] [LawfulBEq O] :
    DecodableChannel (identityChannel (O := O)) := by
  refine ⟨id, ?_⟩
  intro o o' hmass
  by_cases hEq : o' = o
  · exact hEq
  · have : (ConcreteLaw.pure o).mass o' = 0 := by
      simp [ConcreteLaw.pure, hEq]
    exact False.elim (hmass this)

set_option linter.unusedSectionVars false in
theorem decodable_implies_supportLeftInvertible
    {K : ObsChannel O O'}
    (hDec : DecodableChannel K) :
    SupportLeftInvertibleChannel K :=
  hDec

end Channels

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v} {O' : Type w}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
variable [DecidableEq O'] [BEq O'] [LawfulBEq O']

/-- Noisy observer-fiber class-vs-complement predictive pair under a channel. -/
def noisyObserverFiberClassComplement (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (K : ObsChannel O O') : ConcreteLaw O' × ConcreteLaw O' :=
  channelImagePair K (U.observerFiberClassComplement π h a ω pstar)

/-- Noisy semantic separation induced by a concrete observation channel. -/
def noisySemanticSeparation (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (K : ObsChannel O O') : Float :=
  let pair := U.noisyObserverFiberClassComplement π h a ω pstar K
  bhatSeparation pair.1 pair.2

theorem noisyObserverFiberClassComplement_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (K : ObsChannel O O')
    (hView : ω.view p = ω.view q) :
    U.noisyObserverFiberClassComplement π h a ω p K =
      U.noisyObserverFiberClassComplement π h a ω q K := by
  have hPair := U.observerFiberComplementLaw_eq_of_sameView π h a ω hView
  simpa [noisyObserverFiberClassComplement, channelImagePair] using
    congrArg (channelImagePair K) hPair

theorem noisySemanticSeparation_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (K : ObsChannel O O')
    (hView : ω.view p = ω.view q) :
    U.noisySemanticSeparation π h a ω p K =
      U.noisySemanticSeparation π h a ω q K := by
  have hPair := U.noisyObserverFiberClassComplement_eq_of_sameView π h a ω K hView
  simpa [noisySemanticSeparation] using
    congrArg (fun pair => bhatSeparation pair.1 pair.2) hPair

theorem identityChannel_is_decodable :
    DecodableChannel (identityChannel (O := O)) :=
  identityChannel_decodable

theorem identityChannel_is_supportLeftInvertible :
    SupportLeftInvertibleChannel (identityChannel (O := O)) :=
  decodable_implies_supportLeftInvertible identityChannel_is_decodable

end ConcretePrefixMachine

end

end SemanticConvergence
