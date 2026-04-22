import AlgorithmicFreeEnergy.ConcreteBoundary

namespace AlgorithmicFreeEnergy

universe u v

open Classical

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Concrete surrogate information score inherited from the boundary layer. -/
def surrogateInformationScore (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat :=
  U.boundaryInformationGainTerm π h a ω pstar

/-- Simple rational regularization penalty against a reference local action law. -/
def surrogateRegularization
    (refLaw : ActionLaw A) (a : A) : Rat :=
  Rat.abs (1 - refLaw.mass a)

/--
Concrete amortized-surrogate energy: expected free energy plus a rational regularization
term against a reference local action law.
-/
def surrogateEnergy (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) : Rat :=
  U.expectedFreeEnergyRat π h a ω pstar +
    reg * surrogateRegularization refLaw a

/-- Finite-list concrete surrogate minimizer. -/
noncomputable def surrogateArgmin (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) : A :=
  argminOnList actions
    (fun a => U.surrogateEnergy π h a ω pstar refLaw reg)
    hActions

/--
Concrete local action law induced by the surrogate minimizer, represented as a
deterministic singleton-support law on the chosen finite-list minimizer.
-/
def surrogateChosenLaw (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) : ActionLaw A :=
  fullSupportActionLaw [U.surrogateArgmin π h actions hActions ω pstar refLaw reg]

theorem surrogateEnergy_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (refLaw : ActionLaw A) (reg : Rat)
    (hView : ω.view p = ω.view q) :
    U.surrogateEnergy π h a ω p refLaw reg =
      U.surrogateEnergy π h a ω q refLaw reg := by
  have hEfe := U.expectedFreeEnergyRat_eq_of_sameView π h a ω hView
  simp [surrogateEnergy, hEfe]

theorem surrogateArgmin_spec
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) :
    MinimizesOnList actions
      (fun a => U.surrogateEnergy π h a ω pstar refLaw reg)
      (U.surrogateArgmin π h actions hActions ω pstar refLaw reg) :=
  argminOnList_spec actions
    (fun a => U.surrogateEnergy π h a ω pstar refLaw reg)
    hActions

theorem surrogateChosenLaw_supportsArgmin
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) :
    (U.surrogateChosenLaw π h actions hActions ω pstar refLaw reg).mass
      (U.surrogateArgmin π h actions hActions ω pstar refLaw reg) ≠ 0 := by
  simp [surrogateChosenLaw, fullSupportActionLaw]

theorem surrogateChosenLaw_hasSeparatingSupport_of_argmin
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat)
    (hSep :
      U.isSeparatingAction π h ω pstar
        (U.surrogateArgmin π h actions hActions ω pstar refLaw reg)) :
    hasSeparatingSupportOn
      (U.surrogateChosenLaw π h actions hActions ω pstar refLaw reg)
      [U.surrogateArgmin π h actions hActions ω pstar refLaw reg]
      (U.separatingActionSet π h ω pstar) := by
  refine ⟨U.surrogateArgmin π h actions hActions ω pstar refLaw reg, by simp, ?_, hSep⟩
  exact U.surrogateChosenLaw_supportsArgmin π h actions hActions ω pstar refLaw reg

/--
Witness-driven finite-list surrogate theorem: if the concrete surrogate minimizer is
itself semantically separating, then the induced singleton-support action law already has
separating support.
-/
theorem amortizedSurrogate_from_witness
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat)
    (hSep :
      U.isSeparatingAction π h ω pstar
        (U.surrogateArgmin π h actions hActions ω pstar refLaw reg)) :
    hasSeparatingSupportOn
      (U.surrogateChosenLaw π h actions hActions ω pstar refLaw reg)
      [U.surrogateArgmin π h actions hActions ω pstar refLaw reg]
      (U.separatingActionSet π h ω pstar) :=
  U.surrogateChosenLaw_hasSeparatingSupport_of_argmin
    π h actions hActions ω pstar refLaw reg hSep

end ConcretePrefixMachine

end

end AlgorithmicFreeEnergy
