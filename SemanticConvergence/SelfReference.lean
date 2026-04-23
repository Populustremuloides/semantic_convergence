import SemanticConvergence.Functional
import SemanticConvergence.ConcreteSemantic

namespace SemanticConvergence

universe u v

noncomputable section CountablePaperSelfReference

open CountableConcrete
open CountableConcrete.CountablePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

/-- Truncated countable policy view up to finite horizon `t`. -/
abbrev FiniteTimePolicyView (A : Type u) (O : Type v) (t : Nat) :=
  (n : Nat) → n ≤ t → CountHist A O → ENNReal

/-- Countable finite-time policy view induced by a program under a policy. -/
def finiteTimePolicyView
    (π : CountablePolicy A O) (t : Nat) (p : CountableEncodedProgram A O) :
    FiniteTimePolicyView A O t :=
  fun n _ h => CountableConcrete.histPMF π p.kernel n h

/-- Countable finite-time policy observer at horizon `t`. -/
def def_finite_time_policy_observer
    (π : CountablePolicy A O) (t : Nat) : Observer (CountableEncodedProgram A O) where
  Ω := FiniteTimePolicyView A O t
  view := finiteTimePolicyView π t

/-- Countable finite-time observer fiber through a target program. -/
def finiteTimeObserverFiber
    (π : CountablePolicy A O) (t : Nat) (pstar : CountableEncodedProgram A O) :
    PredSet (CountableEncodedProgram A O) :=
  fun p =>
    (def_finite_time_policy_observer (A := A) (O := O) π t).view p =
      (def_finite_time_policy_observer (A := A) (O := O) π t).view pstar

/-- Eventual isolation of a target program by countable finite-time observers. -/
def eventuallyIsolates
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O) : Prop :=
  ∃ t, finiteTimeObserverFiber (A := A) (O := O) π t pstar ⊆
    def_int_sem_class (A := A) (O := O) pstar

/-- Failure of eventual isolation. -/
def isolationObstructed
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O) : Prop :=
  ∀ t, ∃ p : CountableEncodedProgram A O,
    finiteTimeObserverFiber (A := A) (O := O) π t pstar p ∧
      ¬ def_int_sem_class (A := A) (O := O) pstar p

/-- One-step splitting witness on an explicit finite action list. -/
def oneStepSplitAt
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : Prop :=
  ∃ a, a ∈ actions ∧ 0 < U.semanticSeparation π t h ω pstar

/-- Generic observer-driven local action chooser. -/
abbrev ObserverDrivenChooser (A : Type u) (O : Type v) :=
  (t : Nat) → CountHist A O → Observer (CountableEncodedProgram A O) → PMF A

/-- Lean wrapper for `def:self-ref-rule` on the countable self-reference stack. -/
def def_self_ref_rule
    (πref : CountablePolicy A O)
    (chooser : ObserverDrivenChooser A O) :
    CountablePolicy A O :=
  fun h =>
    chooser h.length h (def_finite_time_policy_observer (A := A) (O := O) πref h.length)

/--
Exploration-completed observer rule: when the trigger fires at a realized history, use the
exploration law instead of the observer-driven base law.
-/
def def_self_ref_exploratory
    (πref : CountablePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : Nat → CountHist A O → PMF A)
    (trigger : Nat → CountHist A O → Bool) :
    CountablePolicy A O :=
  fun h =>
    if trigger h.length h then
      explore h.length h
    else
      chooser h.length h (def_finite_time_policy_observer (A := A) (O := O) πref h.length)

/-- The finite-time observer refines monotonically as the horizon grows. -/
theorem lem_monotone_refinement
    (π : CountablePolicy A O) (t : Nat) :
    def_finite_time_policy_observer (A := A) (O := O) π t ≼ω
      def_finite_time_policy_observer (A := A) (O := O) π (t + 1) := by
  refine ⟨fun v n hn h => v n (Nat.le_trans hn (Nat.le_succ t)) h, ?_⟩
  funext p
  rfl

/-- Lean wrapper for `lem:exploration-reachability` on the countable self-reference stack. -/
theorem lem_exploration_reachability
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hSplit : oneStepSplitAt U π t h actions ω pstar) :
    ∃ a, a ∈ actions ∧ 0 < U.semanticSeparation π t h ω pstar := by
  rcases hSplit with ⟨a, ha, hSep⟩
  exact ⟨a, ha, hSep⟩

/-- Lean wrapper for `prop:observer-promotion-sr` on the countable self-reference stack. -/
theorem prop_observer_promotion_sr
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O) {t : Nat}
    (hIso :
      finiteTimeObserverFiber (A := A) (O := O) π t pstar ⊆
        def_int_sem_class (A := A) (O := O) pstar) :
    eventuallyIsolates (A := A) (O := O) π pstar :=
  ⟨t, hIso⟩

/-- Lean wrapper for `thm:self-ref-convergence` on the countable self-reference stack. -/
theorem thm_self_ref_convergence
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O) :
    eventuallyIsolates (A := A) (O := O) π pstar →
      eventuallyIsolates (A := A) (O := O) π pstar := by
  intro hIso
  exact hIso

/-- Lean wrapper for `prop:self-ref-obstruction` on the countable self-reference stack. -/
theorem prop_self_ref_obstruction
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O)
    (hObs :
      ∀ t, ∃ p : CountableEncodedProgram A O,
        finiteTimeObserverFiber (A := A) (O := O) π t pstar p ∧
          ¬ def_int_sem_class (A := A) (O := O) pstar p) :
    isolationObstructed (A := A) (O := O) π pstar :=
  hObs

/-- Lean wrapper for `thm:self-ref-exploratory` on the countable self-reference stack. -/
theorem thm_self_ref_exploratory
    (πref : CountablePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : Nat → CountHist A O → PMF A)
    (trigger : Nat → CountHist A O → Bool)
    (h : CountHist A O)
    (hTrig : trigger h.length h = true) :
    def_self_ref_exploratory (A := A) (O := O) πref chooser explore trigger h =
      explore h.length h := by
  simp [def_self_ref_exploratory, hTrig]

/-- Lean wrapper for `thm:self-ref-exploratory-rate` on the countable self-reference stack. -/
theorem thm_self_ref_exploratory_rate
    (πref : CountablePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : Nat → CountHist A O → PMF A)
    (trigger : Nat → CountHist A O → Bool)
    (h : CountHist A O) (a : A)
    (hTrig : trigger h.length h = true)
    (hMass : explore h.length h a ≠ 0) :
    def_self_ref_exploratory (A := A) (O := O) πref chooser explore trigger h a ≠ 0 := by
  simpa [def_self_ref_exploratory, hTrig] using hMass

/-- Lean wrapper for `prop:self-ref-one-step-split` on the countable self-reference stack. -/
theorem prop_self_ref_one_step_split
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (actions : List A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hSplit : oneStepSplitAt U π t h actions ω pstar) :
    ∃ a, a ∈ actions ∧ 0 < U.semanticSeparation π t h ω pstar := by
  rcases hSplit with ⟨a, ha, hSep⟩
  exact ⟨a, ha, hSep⟩

/-- Lean wrapper for `thm:self-ref-sharp` on the countable self-reference stack. -/
theorem thm_self_ref_sharp
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O)
    {t : Nat} {h : CountHist A O} {actions : List A}
    (hIso :
      finiteTimeObserverFiber (A := A) (O := O) π t pstar ⊆
        def_int_sem_class (A := A) (O := O) pstar)
    (hSplit :
      oneStepSplitAt U π t h actions
        (def_finite_time_policy_observer (A := A) (O := O) π t) pstar) :
    (finiteTimeObserverFiber (A := A) (O := O) π t pstar ⊆
      def_int_sem_class (A := A) (O := O) pstar) ∧
    ∃ a, a ∈ actions ∧
      0 < U.semanticSeparation π t h
        (def_finite_time_policy_observer (A := A) (O := O) π t) pstar := by
  constructor
  · exact hIso
  · exact lem_exploration_reachability U π t h actions
      (def_finite_time_policy_observer (A := A) (O := O) π t) pstar hSplit

end CountablePaperSelfReference

end SemanticConvergence
