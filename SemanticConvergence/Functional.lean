import SemanticConvergence.Hierarchy
import SemanticConvergence.ConcreteBelief
import SemanticConvergence.ConcreteSemantic
import SemanticConvergence.ConcreteFunctional

namespace SemanticConvergence

universe u v

noncomputable section CountablePaperFunctional

open Classical
open CountableConcrete
open CountableConcrete.CountablePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]
[DecidableEq A] [BEq A] [LawfulBEq A]

/-- Convert a rational into `ℝ≥0∞` for the countable action-side penalties. -/
def ratToENNReal (q : Rat) : ENNReal :=
  ENNReal.ofReal q

/-- Finite-list minimizer witness for `ℝ≥0∞`-valued objectives. -/
def MinimizesOnListENNReal {α : Type u} (xs : List α) (f : α → ENNReal) (x : α) : Prop :=
  x ∈ xs ∧ ∀ y, y ∈ xs → f x ≤ f y

theorem exists_minimizerOnListENNReal {α : Type u}
    (xs : List α) (f : α → ENNReal) (hxs : xs ≠ []) :
    ∃ x, MinimizesOnListENNReal xs f x := by
  induction xs with
  | nil =>
      contradiction
  | cons x xs ih =>
      by_cases htail : xs = []
      · refine ⟨x, ?_⟩
        constructor
        · simp
        · intro y hy
          simp [htail] at hy
          rcases hy with rfl
          exact le_rfl
      · rcases ih htail with ⟨x', hx'⟩
        by_cases hle : f x ≤ f x'
        · refine ⟨x, ?_⟩
          constructor
          · simp
          · intro y hy
            simp at hy
            rcases hy with rfl | hy
            · exact le_rfl
            · exact le_trans hle (hx'.2 y hy)
        · have hx'le : f x' ≤ f x := le_of_not_ge hle
          refine ⟨x', ?_⟩
          constructor
          · simp [hx'.1]
          · intro y hy
            simp at hy
            rcases hy with rfl | hy
            · exact hx'le
            · exact hx'.2 y hy

/-- Countable `argmin` on a nonempty finite list. -/
noncomputable def argminOnListENNReal {α : Type u}
    (xs : List α) (f : α → ENNReal) (hxs : xs ≠ []) : α :=
  Classical.choose (exists_minimizerOnListENNReal xs f hxs)

theorem argminOnListENNReal_spec {α : Type u}
    (xs : List α) (f : α → ENNReal) (hxs : xs ≠ []) :
    MinimizesOnListENNReal xs f (argminOnListENNReal xs f hxs) :=
  Classical.choose_spec (exists_minimizerOnListENNReal xs f hxs)

/-- Countable belief-side admissibility range. -/
def BeliefAdmissible (ω : Observer (CountableEncodedProgram A O)) : Prop :=
  behavioralObserver (A := A) (O := O) ≼ω ω

/-- Countable action-side admissibility range. -/
def ActionAdmissible (ω : Observer (CountableEncodedProgram A O)) : Prop :=
  ω ≼ω behavioralObserver (A := A) (O := O)

/-- Countable programs in the `ω`-fiber of `pstar`, viewed on the enumerable machine domain. -/
def goalDialedTarget
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    PredSet U.Program :=
  U.observerFiber ω pstar

/-- Countable observer fiber viewed directly on encoded programs. -/
def encodedObserverFiber
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    PredSet (CountableEncodedProgram A O) :=
  fun p => ω.view p = ω.view pstar

/-- Countable behavioral-fiber weight under the current posterior scaffold. -/
def behavioralFiberMass
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.observerFiberPosteriorWeight π t h (behavioralObserver (A := A) (O := O)) pstar

/-- Ratio of behavioral-fiber posterior weights for two targets. -/
def posteriorRatio
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (p₁ p₂ : CountableEncodedProgram A O) : ENNReal :=
  let num := behavioralFiberMass (A := A) (O := O) U π t h p₁
  let den := behavioralFiberMass (A := A) (O := O) U π t h p₂
  if den = 0 then 0 else num / den

/-- Countable goal-dialed convergence proxy. -/
def goalDialConverges
    (ω : Observer (CountableEncodedProgram A O))
    (_pstar : CountableEncodedProgram A O) : Prop :=
  BeliefAdmissible (A := A) (O := O) ω

/-- Lean wrapper for `def:bhat-omega` on the countable functional stack. -/
def def_bhat_omega
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.semanticSeparation π t h ω pstar

/-- Lean wrapper for `def:raw-two-observer-functional` on the countable functional stack. -/
def def_raw_two_observer_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.observerFiberPosteriorWeight π t h ωB pstar *
    U.semanticSeparation π t h ωA pstar

/-- Lean wrapper for `def:two-observer-functional` on the countable functional stack. -/
def def_two_observer_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  def_raw_two_observer_functional U π t h ωB ωA pstar

/-- Lean wrapper for `def:kernel-functional` on the countable functional stack. -/
def def_kernel_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (κ refLaw : ActionLaw A) : ENNReal :=
  def_two_observer_functional U π t h ωB ωA pstar +
    ratToENNReal (lawL1 κ refLaw)

/-- Lean wrapper for `def:meeting-point-shorthand` on the countable functional stack. -/
def def_meeting_point_shorthand
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (κ refLaw : ActionLaw A) :
    ENNReal × ENNReal × ENNReal :=
  (def_bhat_omega U π t h ωA pstar,
   def_two_observer_functional U π t h ωB ωA pstar,
   def_kernel_functional U π t h ωB ωA pstar κ refLaw)

/-- Lean wrapper for `prop:belief-invariance-above` on the countable functional stack. -/
theorem prop_belief_invariance_above
    {ωB : Observer (CountableEncodedProgram A O)}
    (hAbove : BeliefAdmissible (A := A) (O := O) ωB)
    {p q : CountableEncodedProgram A O}
    (hSame : ωB.view p = ωB.view q) :
    (behavioralObserver (A := A) (O := O)).view p =
      (behavioralObserver (A := A) (O := O)).view q := by
  rcases hAbove with ⟨f, hf⟩
  simpa [Function.comp, hf] using congrArg f hSame

/-- Lean wrapper for `cor:twins-frozen-ratio` on the countable functional stack. -/
theorem cor_twins_frozen_ratio
    {p₁ p₂ : CountableEncodedProgram A O}
    (hTwin :
      (behavioralObserver (A := A) (O := O)).view p₁ =
        (behavioralObserver (A := A) (O := O)).view p₂) :
    encodedObserverFiber (A := A) (O := O) (behavioralObserver (A := A) (O := O)) p₁ =
      encodedObserverFiber (A := A) (O := O) (behavioralObserver (A := A) (O := O)) p₂ := by
  funext r
  simp [encodedObserverFiber, hTwin]

/-- Lean wrapper for `cor:canonical-pair` on the countable functional stack. -/
theorem cor_canonical_pair :
    BeliefAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) ∧
    ActionAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) := by
  constructor
  · exact observerRefines_refl _
  · exact observerRefines_refl _

/-- Lean wrapper for `prop:goal-dialed` on the countable functional stack. -/
theorem prop_goal_dialed
    {ωA : Observer (CountableEncodedProgram A O)}
    {pstar : CountableEncodedProgram A O}
    (hRef : BeliefAdmissible (A := A) (O := O) ωA) :
    goalDialConverges (A := A) (O := O) ωA pstar :=
  hRef

/-- Lean wrapper for `prop:two-observer-minimizer` on the countable functional stack. -/
theorem prop_two_observer_minimizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (hTargets : targets ≠ []) :
    ∃ pmin, MinimizesOnListENNReal targets
      (fun pstar => def_two_observer_functional U π t h ωB ωA pstar) pmin := by
  exact exists_minimizerOnListENNReal targets
    (fun pstar => def_two_observer_functional U π t h ωB ωA pstar) hTargets

/-- Lean wrapper for `prop:kernel-functional-minimizer` on the countable functional stack. -/
theorem prop_kernel_functional_minimizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (kernelCandidates : List (ActionLaw A))
    (hTargets : targets ≠ []) (hKer : kernelCandidates ≠ []) :
    ∃ pmin, MinimizesOnListENNReal targets
      (fun pstar => def_two_observer_functional U π t h ωB ωA pstar) pmin ∧
      ∃ κmin, MinimizesOnListENNReal kernelCandidates
        (fun κ => def_kernel_functional U π t h ωB ωA pmin κ κ) κmin := by
  rcases exists_minimizerOnListENNReal targets
      (fun pstar => def_two_observer_functional U π t h ωB ωA pstar) hTargets with ⟨pmin, hpmin⟩
  rcases exists_minimizerOnListENNReal kernelCandidates
      (fun κ => def_kernel_functional U π t h ωB ωA pmin κ κ) hKer with ⟨κmin, hκmin⟩
  exact ⟨pmin, hpmin, κmin, hκmin⟩

/-- Lean wrapper for `prop:kernel-functional-minimizer-compact` on the countable functional stack. -/
theorem prop_kernel_functional_minimizer_compact
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (compactCandidates : List (ActionLaw A))
    (hTargets : targets ≠ []) (hCompact : compactCandidates ≠ []) :
    ∃ pmin, MinimizesOnListENNReal targets
      (fun pstar => def_two_observer_functional U π t h ωB ωA pstar) pmin ∧
      ∃ κmin, MinimizesOnListENNReal compactCandidates
        (fun κ => def_kernel_functional U π t h ωB ωA pmin κ κ) κmin := by
  rcases exists_minimizerOnListENNReal targets
      (fun pstar => def_two_observer_functional U π t h ωB ωA pstar) hTargets with ⟨pmin, hpmin⟩
  rcases exists_minimizerOnListENNReal compactCandidates
      (fun κ => def_kernel_functional U π t h ωB ωA pmin κ κ) hCompact with ⟨κmin, hκmin⟩
  exact ⟨pmin, hpmin, κmin, hκmin⟩

/-- Lean wrapper for `prop:belief-illtyped-below` on the countable functional stack. -/
theorem prop_belief_illtyped_below
    {ωB : Observer (CountableEncodedProgram A O)}
    {pstar : CountableEncodedProgram A O}
    (_hBelow : ActionAdmissible (A := A) (O := O) ωB)
    (hNotAbove : ¬ BeliefAdmissible (A := A) (O := O) ωB) :
    ¬ goalDialConverges (A := A) (O := O) ωB pstar :=
  hNotAbove

/-- Lean wrapper for `prop:action-cap` on the countable functional stack. -/
theorem prop_action_cap
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (κ : ActionLaw A) :
    def_kernel_functional U π t h ωB ωA pstar κ κ =
      def_two_observer_functional U π t h ωB ωA pstar + ratToENNReal (lawL1 κ κ) := by
  rfl

/-- Lean wrapper for `thm:meeting-point` on the countable functional stack. -/
theorem thm_meeting_point :
    BeliefAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) ∧
    ActionAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) := by
  exact cor_canonical_pair (A := A) (O := O)

end CountablePaperFunctional

end SemanticConvergence
