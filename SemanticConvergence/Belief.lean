import SemanticConvergence.Functional
import SemanticConvergence.ConcreteBelief

namespace SemanticConvergence

universe u v

noncomputable section CountablePaperBelief

open Classical
open CountableConcrete
open CountableConcrete.CountablePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

/-- Countable paper-facing universal prior wrapper. -/
def def_universal_prior (U : CountablePrefixMachine A O) : U.Program → ENNReal :=
  U.universalWeight

/-- Countable class-prior weight scaffold. -/
def classPriorWeight
    (U : CountablePrefixMachine A O)
    (C : PredSet U.Program) : ENNReal :=
  ∑' p : U.Program, if C p then U.universalWeight p else 0

/-- Lean wrapper for `lem:prior-invariance` on the countable prefix-machine stack. -/
theorem lem_prior_invariance
    (U : CountablePrefixMachine A O)
    (p : U.Program) :
    def_universal_prior U p = codeWeightENNReal (U.programCode p) := by
  rfl

/-- Lean wrapper for `lem:prior-necessity` on the countable prefix-machine stack. -/
theorem lem_prior_necessity
    (U : CountablePrefixMachine A O)
    (C : PredSet U.Program) :
    classPriorWeight U C =
      ∑' p : U.Program, if C p then U.universalWeight p else 0 := by
  rfl

/-- Lean wrapper for `lem:variational` on the countable posterior stack. -/
theorem lem_variational
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) :
    def_afe U π t h (fun p => U.posteriorWeight π t h p) = 0 ∧
    ∀ q : U.Program → ENNReal,
      def_afe U π t h q = 0 ↔ samePosteriorWeights U π t h q := by
  constructor
  · exact (def_afe_eq_zero_iff_samePosteriorWeights U π t h
      (fun p => U.posteriorWeight π t h p)).2
        (posteriorWeight_samePosteriorWeights U π t h)
  · intro q
    exact def_afe_eq_zero_iff_samePosteriorWeights U π t h q

/-- Lean wrapper for `lem:kl-necessity` on the countable posterior stack. -/
theorem lem_kl_necessity
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hZero : def_afe U π t h q = 0) :
    samePosteriorWeights U π t h q := by
  have hTerms :
      ∀ p : U.Program,
        posteriorWeightKLDivergenceTerm (q p) (U.posteriorWeight π t h p) = 0 := by
    exact ENNReal.tsum_eq_zero.mp (by simpa [def_afe] using hZero)
  intro p
  exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (posteriorWeight_ne_top U π t h p)).mp (hTerms p)

/-- Lean wrapper for `lem:merging` on the countable posterior stack. -/
theorem lem_merging
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberPosteriorWeight π t h ω p =
      U.observerFiberPosteriorWeight π t h ω q := by
  simpa using U.observerFiberPosteriorWeight_eq_of_sameView π t h ω hView

end CountablePaperBelief

end SemanticConvergence
