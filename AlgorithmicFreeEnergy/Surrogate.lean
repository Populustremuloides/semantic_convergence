import AlgorithmicFreeEnergy.Rates
import AlgorithmicFreeEnergy.ConcreteSurrogate

namespace AlgorithmicFreeEnergy

universe u v w x y z t s r q m n p o k l

/--
`SurrogateModel` is a legacy abstract compatibility package for the
amortized-surrogate implementation layer. It is retained for archival
comparison and backward compatibility only; the paper-facing surrogate
declarations below now terminate at the concrete stack.
-/
structure SurrogateModel extends RatesModel where
  LatentClass : Type
  ImplKernel : Type
  surrogatePolicy : Policy
  surrogateRateRef : ReferenceMeasure
  amortizedSurrogateMinimizerHyp : History → Prop
  amortizedSurrogateMinimizerConclusion : History → Prop
  amortizedSurrogateMinimizer :
    ∀ h : History,
      amortizedSurrogateMinimizerHyp h →
      amortizedSurrogateMinimizerConclusion h
  amortizedSurrogateHyp : Program → Prop
  amortizedSurrogateConclusion : Program → Prop
  amortizedSurrogateFiniteTimeHyp : Program → Prop
  amortizedSurrogateFiniteTimeConclusion : Program → Prop

/--
`SurrogateTheory M` is the legacy theorem-level compatibility layer over
`SurrogateModel`. It remains in the source tree for archival comparison and
backward compatibility only.
-/
structure SurrogateTheory (M : SurrogateModel) extends RatesTheory M.toRatesModel where
  amortizedSurrogate_to_support :
    ∀ pstar : M.Program,
      M.amortizedSurrogateHyp pstar →
      M.separatingSupportHyp M.surrogatePolicy pstar
  amortizedSurrogate_from_concentration :
    ∀ pstar : M.Program,
      M.posteriorConcentrates pstar →
      M.amortizedSurrogateConclusion pstar
  amortizedSurrogateFiniteTime_to_concentration :
    ∀ pstar : M.Program,
      M.amortizedSurrogateFiniteTimeHyp pstar →
      M.expRateConcentrationHyp M.surrogateRateRef pstar
  amortizedSurrogateFiniteTime_from_concentration :
    ∀ pstar : M.Program,
      M.expRateConcentrationConclusion M.surrogateRateRef pstar →
      M.amortizedSurrogateFiniteTimeConclusion pstar

namespace SurrogateTheory

variable {M : SurrogateModel}

/-- Lean wrapper for `prop:amortized-surrogate-minimizer`. -/
theorem prop_amortized_surrogate_minimizer (_T : SurrogateTheory M) (h : M.History)
    (hMin : M.amortizedSurrogateMinimizerHyp h) :
    M.amortizedSurrogateMinimizerConclusion h :=
  M.amortizedSurrogateMinimizer h hMin

/-- Lean wrapper for `thm:amortized-surrogate`. -/
theorem thm_amortized_surrogate (T : SurrogateTheory M) (pstar : M.Program)
    (hSur : M.amortizedSurrogateHyp pstar) :
    M.amortizedSurrogateConclusion pstar := by
  exact SurrogateTheory.amortizedSurrogate_from_concentration T pstar
    (SemanticTheory.thm_separating_support_convergence T.toSemanticTheory
      M.surrogatePolicy pstar
      (SurrogateTheory.amortizedSurrogate_to_support T pstar hSur))

/-- Lean wrapper for `cor:amortized-surrogate-finite-time`. -/
theorem cor_amortized_surrogate_finite_time (T : SurrogateTheory M) (pstar : M.Program)
    (hFin : M.amortizedSurrogateFiniteTimeHyp pstar) :
    M.amortizedSurrogateFiniteTimeConclusion pstar := by
  exact SurrogateTheory.amortizedSurrogateFiniteTime_from_concentration T pstar
    (RatesTheory.thm_exp_rate_concentration T.toRatesTheory
      M.surrogateRateRef pstar
      (SurrogateTheory.amortizedSurrogateFiniteTime_to_concentration T pstar hFin))

end SurrogateTheory

noncomputable section ConcretePaperSurrogate

open ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Lean wrapper for `prop:amortized-surrogate-minimizer` on the concrete stack. -/
theorem prop_amortized_surrogate_minimizer
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) :
    MinimizesOnList actions
      (fun a => U.surrogateEnergy π h a ω pstar refLaw reg)
      (U.surrogateArgmin π h actions hActions ω pstar refLaw reg) :=
  U.surrogateArgmin_spec π h actions hActions ω pstar refLaw reg

/-- Lean wrapper for `thm:amortized-surrogate` on the concrete stack. -/
theorem thm_amortized_surrogate
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
  U.amortizedSurrogate_from_witness π h actions hActions ω pstar refLaw reg hSep

/-- Lean wrapper for `cor:amortized-surrogate-finite-time` on the concrete stack. -/
theorem cor_amortized_surrogate_finite_time
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) :
    (U.surrogateChosenLaw π h actions hActions ω pstar refLaw reg).mass
      (U.surrogateArgmin π h actions hActions ω pstar refLaw reg) ≠ 0 :=
  U.surrogateChosenLaw_supportsArgmin π h actions hActions ω pstar refLaw reg

end ConcretePaperSurrogate

end AlgorithmicFreeEnergy
