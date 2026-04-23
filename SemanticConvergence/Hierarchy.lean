import SemanticConvergence.Foundations
import SemanticConvergence.ConcretePrior

namespace SemanticConvergence

universe u v w

noncomputable section CountablePaperHierarchy

open CountableConcrete
open CountableConcrete.CountablePrefixMachine

variable {A : Type u} {O : Type v} {T : Type w}
variable [Encodable A] [Encodable O]

/-- The countable policy-view codomain: horizon-indexed PMF masses on countable histories. -/
abbrev PolicyView (A : Type u) (O : Type v) := (t : Nat) → CountHist A O → ENNReal

/-- The countable history-view codomain at a fixed history. -/
abbrev HistoryView := ENNReal

/-- The countable policy-level path view induced by a program under a policy. -/
def pathView
    (π : CountablePolicy A O) (p : CountableEncodedProgram A O) : PolicyView A O :=
  fun t h => CountableConcrete.histPMF π p.kernel t h

/-- The countable history observer at a fixed policy/history pair. -/
def historyView
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (p : CountableEncodedProgram A O) : HistoryView :=
  pathView π p t h

/--
Countable interventional semantic equivalence: two programs are semantically identical when
they induce the same path view under every countable policy.
-/
def semanticEq : Setoid (CountableEncodedProgram A O) where
  r p q := ∀ π : CountablePolicy A O, pathView π p = pathView π q
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p π
      rfl
    · intro p q hpq π
      exact (hpq π).symm
    · intro p q r hpq hqr π
      exact (hpq π).trans (hqr π)

/-- Countable semantic quotient used by the paper-facing hierarchy wrappers. -/
abbrev SemanticQuotient (A : Type u) (O : Type v) [Encodable A] [Encodable O] :=
  Quotient (semanticEq (A := A) (O := O))

/-- Programs compatible with the currently realized countable history under the given policy. -/
def def_history_compat
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O)
    (t : Nat) (h : CountHist A O) :
    PredSet (CountableEncodedProgram A O) :=
  fun p => historyView π t h p = historyView π t h pstar

/-- Programs compatible with the entire countable policy-conditioned path view. -/
def def_policy_pred
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O) :
    PredSet (CountableEncodedProgram A O) :=
  fun p => pathView π p = pathView π pstar

/-- The concrete interventional semantic class of a countable encoded program. -/
def def_int_sem_class
    (pstar : CountableEncodedProgram A O) :
    PredSet (CountableEncodedProgram A O) :=
  fun p => (semanticEq (A := A) (O := O)).r p pstar

/-- The syntactic observer remembers the full countable encoded program. -/
def syntacticObserver : Observer (CountableEncodedProgram A O) where
  Ω := CountableEncodedProgram A O
  view := id

/-- The semantic observer is the quotient observer of countable semantic equivalence. -/
def behavioralObserver :
    Observer (CountableEncodedProgram A O) :=
  quotientObserver (semanticEq (A := A) (O := O))

/-- The countable policy observer under a fixed policy. -/
def policyObserver
    (π : CountablePolicy A O) : Observer (CountableEncodedProgram A O) where
  Ω := PolicyView A O
  view := pathView π

/-- The countable history observer at a fixed policy/history pair. -/
def historyObserver
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) :
    Observer (CountableEncodedProgram A O) where
  Ω := HistoryView
  view := historyView π t h

/-- Lean wrapper for `def:history-recoverable` on the countable hierarchy stack. -/
def def_history_recoverable (τ : CountableEncodedProgram A O → T) : Prop :=
  ∃ π : CountablePolicy A O, ∃ decoder : PolicyView A O → T,
    ∀ p : CountableEncodedProgram A O, decoder (pathView π p) = τ p

theorem intSemClass_self (pstar : CountableEncodedProgram A O) :
    def_int_sem_class (A := A) (O := O) pstar pstar := by
  intro π
  rfl

theorem intSemClass_subset_policyPred
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O) :
    def_int_sem_class (A := A) (O := O) pstar ⊆
      def_policy_pred (A := A) (O := O) π pstar := by
  intro p hp
  exact hp π

theorem policyPred_subset_historyCompat
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O)
    (t : Nat) (h : CountHist A O) :
    def_policy_pred (A := A) (O := O) π pstar ⊆
      def_history_compat (A := A) (O := O) π pstar t h := by
  intro p hp
  exact congrArg (fun f => f t h) hp

/-- Concrete witness package used by the paper-facing hierarchy gap theorems. -/
structure HierarchyWitnesses
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O)
    (t : Nat) (h : CountHist A O) where
  fitGapWitness :
    ∃ p : CountableEncodedProgram A O,
      def_history_compat (A := A) (O := O) π pstar t h p ∧
        ¬ def_policy_pred (A := A) (O := O) π pstar p
  policyGapWitness :
    ∃ p : CountableEncodedProgram A O,
      def_policy_pred (A := A) (O := O) π pstar p ∧
        ¬ def_int_sem_class (A := A) (O := O) pstar p
  syntacticGapWitness :
    ∃ p' : CountableEncodedProgram A O,
      p' ≠ pstar ∧ def_int_sem_class (A := A) (O := O) pstar p'

/-- Lean wrapper for `lem:nesting` on the countable hierarchy stack. -/
theorem lem_nesting
    (π : CountablePolicy A O) (pstar : CountableEncodedProgram A O)
    (t : Nat) (h : CountHist A O) :
    predSingleton pstar ⊆ def_int_sem_class (A := A) (O := O) pstar ∧
    def_int_sem_class (A := A) (O := O) pstar ⊆
      def_policy_pred (A := A) (O := O) π pstar ∧
    def_policy_pred (A := A) (O := O) π pstar ⊆
      def_history_compat (A := A) (O := O) π pstar t h ∧
    def_history_compat (A := A) (O := O) π pstar t h ⊆ predUniv := by
  constructor
  · intro p hp
    cases hp
    exact intSemClass_self (A := A) (O := O) pstar
  constructor
  · exact intSemClass_subset_policyPred (A := A) (O := O) π pstar
  constructor
  · exact policyPred_subset_historyCompat (A := A) (O := O) π pstar t h
  · intro p hp
    trivial

/-- Lean wrapper for `prop:refinement-chain` on the countable hierarchy stack. -/
theorem prop_refinement_chain
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) :
    historyObserver (A := A) (O := O) π t h ≼ω policyObserver (A := A) (O := O) π ∧
    policyObserver (A := A) (O := O) π ≼ω behavioralObserver (A := A) (O := O) ∧
    behavioralObserver (A := A) (O := O) ≼ω syntacticObserver (A := A) (O := O) := by
  constructor
  · refine ⟨fun f => f t h, ?_⟩
    funext p
    rfl
  constructor
  · refine ⟨Quotient.lift (fun p => pathView π p) ?_, ?_⟩
    · intro p q hpq
      exact hpq π
    · funext p
      rfl
  · refine ⟨Quotient.mk (semanticEq (A := A) (O := O)), ?_⟩
    rfl

/-- Lean wrapper for `lem:observable-quotient` on the countable hierarchy stack. -/
theorem lem_observable_quotient
    {p q : CountableEncodedProgram A O} :
    (behavioralObserver (A := A) (O := O)).view p =
      (behavioralObserver (A := A) (O := O)).view q ↔
    (semanticEq (A := A) (O := O)).r p q :=
  quotientObserver_eq_iff (semanticEq (A := A) (O := O)) p q

theorem history_recoverable_constantOnSemanticClasses
    (τ : CountableEncodedProgram A O → T)
    (hτ : def_history_recoverable (A := A) (O := O) τ) :
    constantOnSetoid (semanticEq (A := A) (O := O)) τ := by
  rcases hτ with ⟨π, decoder, hdec⟩
  intro p q hpq
  calc
    τ p = decoder (pathView π p) := by simpa using (hdec p).symm
    _ = decoder (pathView π q) := by rw [hpq π]
    _ = τ q := by simpa using (hdec q)

/-- Lean wrapper for `thm:factor-through-quotient` on the countable hierarchy stack. -/
theorem thm_factor_through_quotient
    (τ : CountableEncodedProgram A O → T)
    (hτ : def_history_recoverable (A := A) (O := O) τ) :
    ∃ τbar : SemanticQuotient A O → T,
      τ = τbar ∘ Quotient.mk (semanticEq (A := A) (O := O)) := by
  exact (constantOnSetoid_iff_exists_quotientLift
    (semanticEq (A := A) (O := O)) τ).mp
      (history_recoverable_constantOnSemanticClasses (A := A) (O := O) τ hτ)

/-- Lean wrapper for `lem:fit-gap` on the countable hierarchy stack. -/
theorem lem_fit_gap
    {π : CountablePolicy A O} {pstar : CountableEncodedProgram A O}
    {t : Nat} {h : CountHist A O}
    (W : HierarchyWitnesses (A := A) (O := O) π pstar t h) :
    ∃ p : CountableEncodedProgram A O,
      def_history_compat (A := A) (O := O) π pstar t h p ∧
        ¬ def_policy_pred (A := A) (O := O) π pstar p :=
  W.fitGapWitness

/-- Lean wrapper for `thm:policy-gap` on the countable hierarchy stack. -/
theorem thm_policy_gap
    {π : CountablePolicy A O} {pstar : CountableEncodedProgram A O}
    {t : Nat} {h : CountHist A O}
    (W : HierarchyWitnesses (A := A) (O := O) π pstar t h) :
    ∃ p : CountableEncodedProgram A O,
      def_policy_pred (A := A) (O := O) π pstar p ∧
        ¬ def_int_sem_class (A := A) (O := O) pstar p :=
  W.policyGapWitness

/-- Lean wrapper for `lem:syntactic-gap` on the countable hierarchy stack. -/
theorem lem_syntactic_gap
    {π : CountablePolicy A O} {pstar : CountableEncodedProgram A O}
    {t : Nat} {h : CountHist A O}
    (W : HierarchyWitnesses (A := A) (O := O) π pstar t h) :
    predSingleton pstar ⊂ def_int_sem_class (A := A) (O := O) pstar := by
  refine ⟨?_, ?_⟩
  · intro p hp
    cases hp
    exact intSemClass_self (A := A) (O := O) pstar
  · rcases W.syntacticGapWitness with ⟨p', hp'ne, hp'sem⟩
    refine ⟨p', hp'sem, ?_⟩
    intro hpSingleton
    exact hp'ne hpSingleton

/-- Lean wrapper for `thm:strict-hierarchy` on the countable hierarchy stack. -/
theorem thm_strict_hierarchy
    {π : CountablePolicy A O} {pstar : CountableEncodedProgram A O}
    {t : Nat} {h : CountHist A O}
    (W : HierarchyWitnesses (A := A) (O := O) π pstar t h) :
    predSingleton pstar ⊂ def_int_sem_class (A := A) (O := O) pstar ∧
    def_int_sem_class (A := A) (O := O) pstar ⊂
      def_policy_pred (A := A) (O := O) π pstar ∧
    def_policy_pred (A := A) (O := O) π pstar ⊂
      def_history_compat (A := A) (O := O) π pstar t h := by
  constructor
  · exact lem_syntactic_gap (A := A) (O := O) W
  constructor
  · refine ⟨(lem_nesting (A := A) (O := O) π pstar t h).2.1, ?_⟩
    rcases W.policyGapWitness with ⟨p, hpPred, hpNotSem⟩
    exact ⟨p, hpPred, hpNotSem⟩
  · refine ⟨(lem_nesting (A := A) (O := O) π pstar t h).2.2.1, ?_⟩
    rcases W.fitGapWitness with ⟨p, hpHist, hpNotPred⟩
    exact ⟨p, hpHist, hpNotPred⟩

end CountablePaperHierarchy

end SemanticConvergence
