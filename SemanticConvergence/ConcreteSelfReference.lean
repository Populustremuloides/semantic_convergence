import SemanticConvergence.ConcreteRates

namespace SemanticConvergence

universe u v

open Classical

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Truncated policy view up to finite horizon `t`. -/
abbrev FiniteTimePolicyView (A : Type u) (O : Type v) (t : Nat) :=
  (n : Nat) → n ≤ t → Hist A O n → Rat

/-- Concrete finite-time policy view induced by a program under a policy. -/
def finiteTimePolicyView
    (π : ConcretePolicy A O) (t : Nat) (p : EncodedProgram A O) :
    FiniteTimePolicyView A O t :=
  fun n _ h => (histLaw π p.kernel n).mass h

/-- Concrete finite-time policy observer at horizon `t`. -/
def finiteTimePolicyObserver
    (π : ConcretePolicy A O) (t : Nat) : Observer (EncodedProgram A O) where
  Ω := FiniteTimePolicyView A O t
  view := finiteTimePolicyView π t

/-- Concrete finite-time observer fiber through a target program. -/
def finiteTimeObserverFiber
    (π : ConcretePolicy A O) (t : Nat) (pstar : EncodedProgram A O) :
    PredSet (EncodedProgram A O) :=
  fun p => (finiteTimePolicyObserver π t).view p = (finiteTimePolicyObserver π t).view pstar

/-- Eventual isolation of a target program by finite-time observers. -/
def eventuallyIsolates
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) : Prop :=
  ∃ t, finiteTimeObserverFiber π t pstar ⊆ EncodedProgram.intSemClass pstar

/-- Failure of eventual isolation. -/
def isolationObstructed
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) : Prop :=
  ∀ t, ∃ p : EncodedProgram A O,
    finiteTimeObserverFiber π t pstar p ∧ ¬ EncodedProgram.intSemClass pstar p

/-- One-step splitting witness on an explicit finite action list. -/
def oneStepSplitAt
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Prop :=
  ∃ a, a ∈ actions ∧ U.isSeparatingAction π h ω pstar a

/-- Generic observer-driven local action chooser. -/
abbrev ObserverDrivenChooser (A : Type u) (O : Type v) :=
  (h : FullHist A O) → Observer (EncodedProgram A O) → ActionLaw A

/-- Observer-driven rule using the finite-time observer of a reference policy. -/
def finiteTimeObserverRule
    (πref : ConcretePolicy A O) (chooser : ObserverDrivenChooser A O) :
    ConcretePolicy A O :=
  fun t h => chooser ⟨t, h⟩ (finiteTimePolicyObserver πref t)

/--
Exploration-completed observer rule: when the trigger fires at a realized history, use the
exploration law instead of the observer-driven base law.
-/
def explorationCompletedRule
    (πref : ConcretePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : FullHist A O → ActionLaw A)
    (trigger : FullHist A O → Bool) :
    ConcretePolicy A O :=
  fun t h =>
    let H : FullHist A O := ⟨t, h⟩
    if trigger H then explore H else chooser H (finiteTimePolicyObserver πref t)

/-- The finite-time observer refines to the full policy observer. -/
theorem finiteTimePolicyObserver_refines_policyObserver
    (π : ConcretePolicy A O) (t : Nat) :
    finiteTimePolicyObserver π t ≼ω EncodedProgram.policyObserver π := by
  refine ⟨fun v n _ h => v n h, ?_⟩
  funext p
  rfl

/-- As the horizon grows, finite-time observers refine monotonically. -/
theorem finiteTimePolicyObserver_monotone
    (π : ConcretePolicy A O) (t : Nat) :
    finiteTimePolicyObserver π t ≼ω finiteTimePolicyObserver π (t + 1) := by
  refine ⟨fun v n hn h => v n (Nat.le_trans hn (Nat.le_succ t)) h, ?_⟩
  funext p
  rfl

/-- Finite-time observer fibers shrink monotonically with the horizon. -/
theorem finiteTimeObserverFiber_antitone
    (π : ConcretePolicy A O) (t : Nat) (pstar : EncodedProgram A O) :
    finiteTimeObserverFiber π (t + 1) pstar ⊆ finiteTimeObserverFiber π t pstar := by
  intro p hp
  funext n
  funext hn
  funext h
  exact congrArg
    (fun v => v n (Nat.le_trans hn (Nat.le_succ t)) h)
    hp

/-- Eventual isolation witnessed at a concrete finite time. -/
theorem eventuallyIsolates_of_witness
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) {t : Nat}
    (hIso : finiteTimeObserverFiber π t pstar ⊆ EncodedProgram.intSemClass pstar) :
    eventuallyIsolates π pstar :=
  ⟨t, hIso⟩

/-- Obstruction of eventual isolation witnessed by concrete counterexamples at every time. -/
theorem isolationObstructed_of_witness
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O)
    (hObs :
      ∀ t, ∃ p : EncodedProgram A O,
        finiteTimeObserverFiber π t pstar p ∧ ¬ EncodedProgram.intSemClass pstar p) :
    isolationObstructed π pstar :=
  hObs

/-- Same-view targets induce the same finite-time observer fiber. -/
theorem finiteTimeObserverFiber_eq_of_sameView
    (π : ConcretePolicy A O) (t : Nat)
    {p q : EncodedProgram A O}
    (hView : (finiteTimePolicyObserver π t).view p = (finiteTimePolicyObserver π t).view q) :
    finiteTimeObserverFiber π t p = finiteTimeObserverFiber π t q := by
  funext r
  simp [finiteTimeObserverFiber, hView]

/-- A witnessed split gives a separating-support witness for the supplied full-support explorer. -/
theorem oneStepSplit_givesSeparatingSupport
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (hSplit : oneStepSplitAt U π h actions ω pstar) :
    hasSeparatingSupportOn
      (fullSupportActionLaw actions)
      actions
      (U.separatingActionSet π h ω pstar) := by
  rcases hSplit with ⟨a, ha, hSep⟩
  exact U.fullSupportActionLaw_hasSeparatingSupportOn actions π h ω pstar ha hSep

/-- When the exploration trigger fires, the exploration-completed rule uses the explorer law. -/
theorem explorationCompletedRule_usesExplorer
    (πref : ConcretePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : FullHist A O → ActionLaw A)
    (trigger : FullHist A O → Bool)
    (t : Nat) (h : Hist A O t)
    (hTrig : trigger ⟨t, h⟩ = true) :
    explorationCompletedRule πref chooser explore trigger t h = explore ⟨t, h⟩ := by
  simp [explorationCompletedRule, hTrig]

/-- Under an active trigger, explorer support transfers directly to the completed rule. -/
theorem explorationCompletedRule_supportsAction
    (πref : ConcretePolicy A O)
    (chooser : ObserverDrivenChooser A O)
    (explore : FullHist A O → ActionLaw A)
    (trigger : FullHist A O → Bool)
    (t : Nat) (h : Hist A O t) (a : A)
    (hTrig : trigger ⟨t, h⟩ = true)
    (hMass : (explore ⟨t, h⟩).mass a ≠ 0) :
    (explorationCompletedRule πref chooser explore trigger t h).mass a ≠ 0 := by
  simpa [explorationCompletedRule, hTrig] using hMass

/--
Witness-driven sharpened self-reference statement: if eventual isolation holds and a split
action is available under the semantic core, then the corresponding finite-time observer
fiber is already semantically isolating and separating-supporting.
-/
theorem sharpSelfReference_from_witness
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O)
    {t : Nat} {h : FullHist A O} {actions : List A}
    (hIso : finiteTimeObserverFiber π t pstar ⊆ EncodedProgram.intSemClass pstar)
    (hSplit : oneStepSplitAt U π h actions (finiteTimePolicyObserver π t) pstar) :
    (finiteTimeObserverFiber π t pstar ⊆ EncodedProgram.intSemClass pstar) ∧
    hasSeparatingSupportOn
      (fullSupportActionLaw actions)
      actions
      (U.separatingActionSet π h (finiteTimePolicyObserver π t) pstar) := by
  constructor
  · exact hIso
  · exact oneStepSplit_givesSeparatingSupport
      U π h actions (finiteTimePolicyObserver π t) pstar hSplit

end ConcretePrefixMachine

end

end SemanticConvergence
