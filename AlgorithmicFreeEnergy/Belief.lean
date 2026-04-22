import AlgorithmicFreeEnergy.Functional
import AlgorithmicFreeEnergy.ConcreteBelief

namespace AlgorithmicFreeEnergy

universe u v w x y z t s r q m n p o k l

/--
`BeliefModel` is a legacy abstract compatibility package for the universal-prior
and Bayes/Gibbs belief layer. It is retained for archival comparison and
backward compatibility only; the paper-facing belief declarations below now
terminate at the concrete stack.
-/
structure BeliefModel extends FunctionalModel where
  PrefixMachine : Type k
  InteractionPrefix : Type l
  AltPrior : Type
  universalPrior : Program → Rat
  machineMixture : PrefixMachine → InteractionPrefix → Rat
  semanticComplexity : PrefixMachine → ObsClass → Nat
  altPriorClassMass : AltPrior → ObsClass → Rat
  altPosteriorMass : AltPrior → History → ObsClass → Rat
  algorithmicFreeEnergy : ProgramDist → History → Score
  variationalIdentity : History → ProgramDist → Prop
  variationalIdentity_holds :
    ∀ (h : History) (q : ProgramDist), variationalIdentity h q
  klNecessityHyp : Prop
  klNecessityConclusion : Prop
  predictiveMerges : Program → Prop
  priorNecessityHyp : AltPrior → ObsClass → Prop
  priorNecessityConclusion : AltPrior → History → ObsClass → Prop
  priorInvariance :
    ∀ U V : PrefixMachine,
      ∃ cUV cVU : Rat,
        0 < cUV ∧ 0 < cVU ∧
        ∀ pref : InteractionPrefix,
          cUV * machineMixture V pref ≤ machineMixture U pref ∧
          cVU * machineMixture U pref ≤ machineMixture V pref
  priorNecessity :
    ∀ (alt : AltPrior) (c : ObsClass) (h : History),
      priorNecessityHyp alt c →
      priorNecessityConclusion alt h c
  afeMinimizes :
    ∀ h : History,
      minimizesProgramDist
        (fun q => algorithmicFreeEnergy q h)
        (bayesGibbsPosterior h)
  afeUnique :
    ∀ (h : History) (q : ProgramDist),
      minimizesProgramDist
        (fun q' => algorithmicFreeEnergy q' h)
        q →
      q = bayesGibbsPosterior h
  klNecessity :
    klNecessityHyp → klNecessityConclusion
  merging :
    ∀ pstar : Program, predictiveMerges pstar

namespace BeliefModel

variable (M : BeliefModel)

/-- Lean wrapper for `def:universal-prior`. -/
def def_universal_prior : M.Program → Rat :=
  M.universalPrior

/-- Lean wrapper for `def:afe`. -/
def def_afe (q : M.ProgramDist) (h : M.History) : M.Score :=
  M.algorithmicFreeEnergy q h

/-- Lean wrapper for `lem:prior-invariance`. -/
theorem lem_prior_invariance (U V : M.PrefixMachine) :
    ∃ cUV cVU : Rat,
      0 < cUV ∧ 0 < cVU ∧
      ∀ pref : M.InteractionPrefix,
        cUV * M.machineMixture V pref ≤ M.machineMixture U pref ∧
        cVU * M.machineMixture U pref ≤ M.machineMixture V pref :=
  M.priorInvariance U V

/-- Lean wrapper for `lem:prior-necessity`. -/
theorem lem_prior_necessity
    (alt : M.AltPrior) (c : M.ObsClass) (h : M.History)
    (hNec : M.priorNecessityHyp alt c) :
    M.priorNecessityConclusion alt h c :=
  M.priorNecessity alt c h hNec

/-- Lean wrapper for `lem:variational`. -/
theorem lem_variational (h : M.History) :
    (∀ q : M.ProgramDist, M.variationalIdentity h q) ∧
    UniqueMinimizer M.minimizesProgramDist
      (fun q => M.def_afe q h)
      (M.bayesGibbsPosterior h) :=
by
  constructor
  · intro q
    exact M.variationalIdentity_holds h q
  · exact uniqueMinimizer_of_minimizes_unique
      (M.afeMinimizes h)
      (M.afeUnique h)

/-- Lean wrapper for `lem:kl-necessity`. -/
theorem lem_kl_necessity (hKL : M.klNecessityHyp) :
    M.klNecessityConclusion :=
  M.klNecessity hKL

/-- Lean wrapper for `lem:merging`. -/
theorem lem_merging (pstar : M.Program) :
    M.predictiveMerges pstar :=
  M.merging pstar

end BeliefModel

noncomputable section ConcretePaperBelief

open Classical
open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Concrete paper-facing universal prior wrapper. -/
def def_universal_prior (U : ConcretePrefixMachine A O) : U.Program → Rat :=
  U.universalPrior

/-- Concrete posterior-mass agreement on the finite machine domain. -/
def samePosteriorMasses
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (q : ConcreteLaw U.Program) : Prop :=
  ∀ p, p ∈ U.allPrograms → q.mass p = (U.posteriorLaw π h).mass p

/-- Concrete paper-facing AFE proxy: zero exactly on posterior-mass agreement. -/
def def_afe
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (q : ConcreteLaw U.Program) : Rat :=
  if samePosteriorMasses U π h q then 0 else 1

theorem posteriorLaw_samePosteriorMasses
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) :
    samePosteriorMasses U π h (U.posteriorLaw π h) := by
  intro p hp
  rfl

/-- Lean wrapper for `lem:prior-invariance` on the concrete prefix-machine stack. -/
theorem lem_prior_invariance
    {U V : ConcretePrefixMachine A O}
    (E : PrefixExtension U V) (p : V.Program) :
    codeWeight (E.translateCode p.1) =
      Rat.divInt 1 (pow2 (E.header.length + p.1.length)) := by
  simpa using E.translatedPrior_formula p

/-- Lean wrapper for `lem:prior-necessity` on the concrete prefix-machine stack. -/
theorem lem_prior_necessity
    (U : ConcretePrefixMachine A O)
    (C : PredSet U.Program) [DecidablePred C] :
    U.classPriorMass C =
      listWeightedSum U.codes (fun c =>
        if hc : c ∈ U.codes then
          if C ⟨c, hc⟩ then codeWeight c else 0
        else
          0) := by
  rfl

/-- Lean wrapper for `lem:variational` on the concrete posterior stack. -/
theorem lem_variational
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) :
    def_afe U π h (U.posteriorLaw π h) = 0 ∧
    ∀ q : ConcreteLaw U.Program,
      def_afe U π h q = 0 ↔ samePosteriorMasses U π h q := by
  constructor
  · simp [def_afe, posteriorLaw_samePosteriorMasses]
  · intro q
    by_cases hq : samePosteriorMasses U π h q
    · simp [def_afe, hq]
    · simp [def_afe, hq]

/-- Lean wrapper for `lem:kl-necessity` on the concrete posterior stack. -/
theorem lem_kl_necessity
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (q : ConcreteLaw U.Program)
    (hZero : def_afe U π h q = 0) :
    samePosteriorMasses U π h q := by
  by_cases hq : samePosteriorMasses U π h q
  · exact hq
  · simp [def_afe, hq] at hZero

/-- Lean wrapper for `lem:merging` on the concrete posterior stack. -/
theorem lem_merging
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberPosteriorMass π h ω p =
      U.observerFiberPosteriorMass π h ω q := by
  simpa using U.observerFiberPosteriorMass_eq_of_sameView π h ω hView

end ConcretePaperBelief

end AlgorithmicFreeEnergy
