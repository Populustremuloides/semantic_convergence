import SemanticConvergence.Boundary

namespace SemanticConvergence

universe u v

noncomputable section CountablePaperSurrogate

open CountableConcrete
open CountableConcrete.CountablePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]
[DecidableEq A] [BEq A] [LawfulBEq A]

/-- Countable surrogate information score inherited from the boundary layer. -/
def surrogateInformationScore
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  boundaryInformationGainTerm U π t h a ω pstar

/-- Countable regularization penalty against a reference local action law. -/
def surrogateRegularization
    (refLaw : ActionLaw A) (a : A) : ENNReal :=
  ratToENNReal (Rat.abs (1 - refLaw.mass a))

/-- Countable amortized-surrogate energy. -/
def surrogateEnergy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) : ENNReal :=
  def_efe U π t h a ω pstar + reg * surrogateRegularization refLaw a

/-- Finite-list countable surrogate minimizer. -/
noncomputable def surrogateArgmin
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) : A :=
  argminOnListENNReal actions
    (fun a => surrogateEnergy U π t h a ω pstar refLaw reg)
    hActions

/-- Countable local action law induced by the surrogate minimizer. -/
def surrogateChosenLaw
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) : ActionLaw A :=
  singletonActionLaw (surrogateArgmin U π t h actions hActions ω pstar refLaw reg)

/-- Lean wrapper for `prop:amortized-surrogate-minimizer` on the countable stack. -/
theorem prop_amortized_surrogate_minimizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) :
    MinimizesOnListENNReal actions
      (fun a => surrogateEnergy U π t h a ω pstar refLaw reg)
      (surrogateArgmin U π t h actions hActions ω pstar refLaw reg) :=
  argminOnListENNReal_spec actions
    (fun a => surrogateEnergy U π t h a ω pstar refLaw reg)
    hActions

/-- Lean wrapper for `thm:amortized-surrogate` on the countable stack. -/
theorem thm_amortized_surrogate
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal)
    (hSep : 0 < U.semanticSeparation π t h ω pstar) :
    ∃ a, a ∈ [surrogateArgmin U π t h actions hActions ω pstar refLaw reg] ∧
      (surrogateChosenLaw U π t h actions hActions ω pstar refLaw reg).mass a ≠ 0 ∧
      0 < U.semanticSeparation π t h ω pstar := by
  refine ⟨surrogateArgmin U π t h actions hActions ω pstar refLaw reg, by simp, ?_, hSep⟩
  simp [surrogateChosenLaw, singletonActionLaw]

/-- Lean wrapper for `cor:amortized-surrogate-finite-time` on the countable stack. -/
theorem cor_amortized_surrogate_finite_time
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (refLaw : ActionLaw A) (reg : ENNReal) :
    (surrogateChosenLaw U π t h actions hActions ω pstar refLaw reg).mass
      (surrogateArgmin U π t h actions hActions ω pstar refLaw reg) ≠ 0 := by
  simp [surrogateChosenLaw, singletonActionLaw]

end CountablePaperSurrogate

end SemanticConvergence
