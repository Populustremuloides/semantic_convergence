import AlgorithmicFreeEnergy.Foundations
import AlgorithmicFreeEnergy.ConcreteHierarchy

namespace AlgorithmicFreeEnergy

universe u v w x y z t s r

/--
`HierarchyModel` is a legacy abstract compatibility package for the hierarchy section.
It is retained for archival comparison and backward compatibility only; the
paper-facing hierarchy declarations below now terminate at the concrete stack.
-/
structure HierarchyModel where
  Program : Type u
  Action : Type v
  Observation : Type w
  Policy : Type x
  History : Type y
  PathObs : Type z
  HistObs : Type t
  SemanticEq : Setoid Program
  pathView : Policy → Program → PathObs
  histView : History → Program → HistObs
  semToPath : Policy → Quotient SemanticEq → PathObs
  pathToHist : Policy → History → PathObs → HistObs
  semToPath_spec : ∀ π : Policy, pathView π = semToPath π ∘ Quotient.mk SemanticEq
  pathToHist_spec : ∀ π : Policy, ∀ h : History, histView h = pathToHist π h ∘ pathView π
  reachable : Program → Policy → History → Prop
  actionSupported : Policy → History → Action → Prop
  actionSuppressed : Policy → History → Action → Prop
  nondegenerate : Program → History → Action → Prop
  hasSemanticTwin : Program → Prop
  ConvergesInProb : {T : Type s} → Policy → (Nat → History → T) → Program → T → Prop
  convergence_unique :
    ∀ {T : Type s} {π : Policy} {est : Nat → History → T}
      {p p' : Program} {tp tq : T},
      pathView π p = pathView π p' →
      ConvergesInProb π est p tp →
      ConvergesInProb π est p' tq →
      tp = tq
  fit_gap_witness :
    ∀ {pstar : Program} {π : Policy} {h : History} {a : Action},
      reachable pstar π h →
      actionSupported π h a →
      nondegenerate pstar h a →
      ∃ p : Program,
        histView h p = histView h pstar ∧
        pathView π p ≠ pathView π pstar
  policy_gap_witness :
    ∀ {pstar : Program} {π : Policy} {h : History} {b : Action},
      reachable pstar π h →
      actionSuppressed π h b →
      nondegenerate pstar h b →
      ∃ p : Program,
        pathView π p = pathView π pstar ∧
        ¬ SemanticEq.r p pstar
  syntactic_gap_witness :
    ∀ {pstar : Program},
      hasSemanticTwin pstar →
      ∃ p' : Program, p' ≠ pstar ∧ SemanticEq.r p' pstar

namespace HierarchyModel

variable (M : HierarchyModel)

/-- Lean wrapper for `def:history-compat`. -/
def def_history_compat (pstar : M.Program) (h : M.History) : PredSet M.Program :=
  fun p => M.histView h p = M.histView h pstar

/-- Lean wrapper for `def:policy-pred`. -/
def def_policy_pred (pstar : M.Program) (π : M.Policy) : PredSet M.Program :=
  fun p => M.pathView π p = M.pathView π pstar

/-- Lean wrapper for `def:int-sem-class`. -/
def def_int_sem_class (pstar : M.Program) : PredSet M.Program :=
  fun p => M.SemanticEq.r p pstar

/-- The quotient type of semantic classes. -/
abbrev SemanticQuotient := Quotient M.SemanticEq

/-- Lean wrapper for `def:observer`. -/
abbrev def_observer := Observer M.Program

/-- The semantic/behavioral observer induced by the quotient map. -/
def behavioralObserver : Observer M.Program :=
  quotientObserver M.SemanticEq

/-- The syntactic observer is the identity-on-programs observer. -/
def syntacticObserver : Observer M.Program where
  Ω := M.Program
  view := id

/-- The policy observer attached to a fixed policy. -/
def policyObserver (π : M.Policy) : Observer M.Program where
  Ω := M.PathObs
  view := M.pathView π

/-- The realized-history observer attached to a fixed history. -/
def historyObserver (h : M.History) : Observer M.Program where
  Ω := M.HistObs
  view := M.histView h

/-- Lean wrapper for `def:history-recoverable`. -/
def def_history_recoverable {T : Type s} (τ : M.Program → T) : Prop :=
  ∃ π : M.Policy, ∃ est : Nat → M.History → T, ∀ p : M.Program, M.ConvergesInProb π est p (τ p)

theorem def_int_sem_class_self (pstar : M.Program) : M.def_int_sem_class pstar pstar := by
  exact M.SemanticEq.refl pstar

theorem def_int_sem_class_subset_policy_pred (pstar : M.Program) (π : M.Policy) :
    M.def_int_sem_class pstar ⊆ M.def_policy_pred pstar π := by
  intro p hp
  change M.pathView π p = M.pathView π pstar
  have hq : (Quotient.mk M.SemanticEq p : Quotient M.SemanticEq) =
      Quotient.mk M.SemanticEq pstar := Quotient.sound hp
  calc
    M.pathView π p = M.semToPath π (Quotient.mk M.SemanticEq p) := by
      simpa [Function.comp] using congrArg (fun f => f p) (M.semToPath_spec π)
    _ = M.semToPath π (Quotient.mk M.SemanticEq pstar) := by simp [hq]
    _ = M.pathView π pstar := by
      simpa [Function.comp] using congrArg (fun f => f pstar) (M.semToPath_spec π).symm

theorem def_policy_pred_subset_history_compat (pstar : M.Program) (π : M.Policy) (h : M.History) :
    M.def_policy_pred pstar π ⊆ M.def_history_compat pstar h := by
  intro p hp
  change M.histView h p = M.histView h pstar
  calc
    M.histView h p = M.pathToHist π h (M.pathView π p) := by
      simpa [Function.comp] using congrArg (fun f => f p) (M.pathToHist_spec π h)
    _ = M.pathToHist π h (M.pathView π pstar) := by
      simpa [def_policy_pred] using congrArg (M.pathToHist π h) hp
    _ = M.histView h pstar := by
      simpa [Function.comp] using congrArg (fun f => f pstar) (M.pathToHist_spec π h).symm

/-- Lean wrapper for `lem:nesting`. -/
theorem lem_nesting (pstar : M.Program) (π : M.Policy) (h : M.History) :
    predSingleton pstar ⊆ M.def_int_sem_class pstar ∧
    M.def_int_sem_class pstar ⊆ M.def_policy_pred pstar π ∧
    M.def_policy_pred pstar π ⊆ M.def_history_compat pstar h ∧
    M.def_history_compat pstar h ⊆ predUniv := by
  constructor
  · intro p hp
    cases hp
    exact M.SemanticEq.refl pstar
  constructor
  · exact M.def_int_sem_class_subset_policy_pred pstar π
  constructor
  · exact M.def_policy_pred_subset_history_compat pstar π h
  · intro p hp
    trivial

/--
Lean wrapper for `prop:refinement-chain`.
The order matches the manuscript: history observer, then policy observer,
then behavioral observer, then syntactic observer.
-/
theorem prop_refinement_chain (π : M.Policy) (h : M.History) :
    M.historyObserver h ≼ω M.policyObserver π ∧
    M.policyObserver π ≼ω M.behavioralObserver ∧
    M.behavioralObserver ≼ω M.syntacticObserver := by
  constructor
  · refine ⟨M.pathToHist π h, ?_⟩
    exact M.pathToHist_spec π h
  constructor
  · refine ⟨M.semToPath π, ?_⟩
    exact M.semToPath_spec π
  · refine ⟨Quotient.mk M.SemanticEq, ?_⟩
    rfl

/-- Lean wrapper for `lem:observable-quotient`. -/
theorem lem_observable_quotient {p p' : M.Program} (hpq : M.SemanticEq.r p p') :
    ∀ π : M.Policy, M.pathView π p = M.pathView π p' := by
  intro π
  exact (M.def_int_sem_class_subset_policy_pred p' π) hpq

/-- Internal constancy lemma used by `thm:factor-through-quotient`. -/
theorem history_recoverable_constant_on_semantic_classes {T : Type s} (τ : M.Program → T)
    (hτ : M.def_history_recoverable τ) :
    constantOnSetoid M.SemanticEq τ := by
  rcases hτ with ⟨π, est, hconv⟩
  intro p q hpq
  have hview : M.pathView π p = M.pathView π q := M.lem_observable_quotient hpq π
  exact M.convergence_unique hview (hconv p) (hconv q)

/-- Lean wrapper for `thm:factor-through-quotient`. -/
theorem thm_factor_through_quotient {T : Type s} (τ : M.Program → T)
    (hτ : M.def_history_recoverable τ) :
    (∀ {p q : M.Program}, M.SemanticEq.r p q → τ p = τ q) ∧
    ∃ τbar : M.SemanticQuotient → T,
      τ = τbar ∘ Quotient.mk M.SemanticEq ∧
      ∀ τbar' : M.SemanticQuotient → T,
        τ = τbar' ∘ Quotient.mk M.SemanticEq → τbar' = τbar := by
  have hconst : constantOnSetoid M.SemanticEq τ := M.history_recoverable_constant_on_semantic_classes τ hτ
  rcases (constantOnSetoid_iff_exists_quotientLift M.SemanticEq τ).mp hconst with ⟨τbar, hτbar⟩
  refine ⟨?_, τbar, hτbar, ?_⟩
  · intro p q hpq
    exact hconst hpq
  · intro τbar' hτbar'
    have hcomp : τbar' ∘ Quotient.mk M.SemanticEq = τbar ∘ Quotient.mk M.SemanticEq := by
      calc
        τbar' ∘ Quotient.mk M.SemanticEq = τ := hτbar'.symm
        _ = τbar ∘ Quotient.mk M.SemanticEq := hτbar
    exact quotientLift_unique M.SemanticEq hcomp

/-- Lean wrapper for `lem:fit-gap`. -/
theorem lem_fit_gap (_hObs : ∃ x y : M.Observation, x ≠ y) {pstar : M.Program} {π : M.Policy}
    {h : M.History} {a : M.Action}
    (hReach : M.reachable pstar π h)
    (hSupport : M.actionSupported π h a)
    (hNondeg : M.nondegenerate pstar h a) :
    ∃ p : M.Program, M.def_history_compat pstar h p ∧ ¬ M.def_policy_pred pstar π p := by
  rcases M.fit_gap_witness hReach hSupport hNondeg with ⟨p, hhist, hpath⟩
  refine ⟨p, hhist, ?_⟩
  intro hpred
  exact hpath hpred

/-- Lean wrapper for `thm:policy-gap`. -/
theorem thm_policy_gap (_hAct : ∃ a₁ a₂ : M.Action, a₁ ≠ a₂) {pstar : M.Program} {π : M.Policy}
    {h : M.History} {b : M.Action}
    (hReach : M.reachable pstar π h)
    (hSuppressed : M.actionSuppressed π h b)
    (hNondeg : M.nondegenerate pstar h b) :
    ∃ p' : M.Program, M.def_policy_pred pstar π p' ∧ ¬ M.def_int_sem_class pstar p' := by
  rcases M.policy_gap_witness hReach hSuppressed hNondeg with ⟨p', hpath, hnotsem⟩
  refine ⟨p', hpath, ?_⟩
  intro hsem
  exact hnotsem hsem

/-- Lean wrapper for `lem:syntactic-gap`. -/
theorem lem_syntactic_gap {pstar : M.Program} (hTwin : M.hasSemanticTwin pstar) :
    predSingleton pstar ⊂ M.def_int_sem_class pstar := by
  refine ⟨?_, ?_⟩
  · intro p hp
    cases hp
    exact M.SemanticEq.refl pstar
  · rcases M.syntactic_gap_witness hTwin with ⟨p', hp'ne, hp'sem⟩
    refine ⟨p', hp'sem, ?_⟩
    intro hpSingleton
    exact hp'ne hpSingleton

/-- Lean wrapper for `thm:strict-hierarchy`. -/
theorem thm_strict_hierarchy (_hObs : ∃ x y : M.Observation, x ≠ y)
    (_hAct : ∃ a₁ a₂ : M.Action, a₁ ≠ a₂)
    {pstar : M.Program} {π : M.Policy}
    {h₀ h : M.History} {b a : M.Action}
    (hTwin : M.hasSemanticTwin pstar)
    (hReach₀ : M.reachable pstar π h₀)
    (hSuppressed : M.actionSuppressed π h₀ b)
    (hNondeg₀ : M.nondegenerate pstar h₀ b)
    (hReach : M.reachable pstar π h)
    (hSupport : M.actionSupported π h a)
    (hNondeg : M.nondegenerate pstar h a) :
    predSingleton pstar ⊂ M.def_int_sem_class pstar ∧
    M.def_int_sem_class pstar ⊂ M.def_policy_pred pstar π ∧
    M.def_policy_pred pstar π ⊂ M.def_history_compat pstar h := by
  constructor
  · exact M.lem_syntactic_gap hTwin
  constructor
  · refine ⟨(M.lem_nesting pstar π h).2.1, ?_⟩
    rcases M.thm_policy_gap _hAct hReach₀ hSuppressed hNondeg₀ with ⟨p', hp'pred, hp'notsem⟩
    refine ⟨p', hp'pred, ?_⟩
    intro hp'class
    exact hp'notsem hp'class
  · refine ⟨(M.lem_nesting pstar π h).2.2.1, ?_⟩
    rcases M.lem_fit_gap _hObs hReach hSupport hNondeg with ⟨p, hp'hist, hp'notpred⟩
    refine ⟨p, hp'hist, ?_⟩
    intro hp'pred
    exact hp'notpred hp'pred

end HierarchyModel

noncomputable section ConcretePaperHierarchy

open EncodedProgram

variable {A : Type u} {O : Type v} {T : Type w}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Concrete semantic quotient used by the paper-facing hierarchy wrappers. -/
abbrev SemanticQuotient :=
  EncodedProgram.SemanticQuotient (A := A) (O := O)

/-- Paper-facing concrete behavioral observer. -/
abbrev behavioralObserver :
    Observer (EncodedProgram A O) :=
  EncodedProgram.behavioralObserver (A := A) (O := O)

/-- Paper-facing concrete syntactic observer. -/
abbrev syntacticObserver :
    Observer (EncodedProgram A O) :=
  EncodedProgram.syntacticObserver (A := A) (O := O)

/-- Paper-facing concrete policy observer. -/
abbrev policyObserver (π : ConcretePolicy A O) :
    Observer (EncodedProgram A O) :=
  EncodedProgram.policyObserver (A := A) (O := O) π

/-- Paper-facing concrete history observer. -/
abbrev historyObserver (π : ConcretePolicy A O) (h : FullHist A O) :
    Observer (EncodedProgram A O) :=
  EncodedProgram.historyObserver (A := A) (O := O) π h

/-- Lean wrapper for `def:history-compat` on the concrete hierarchy stack. -/
def def_history_compat
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) (h : FullHist A O) :
    PredSet (EncodedProgram A O) :=
  EncodedProgram.historyCompat π pstar h

/-- Lean wrapper for `def:policy-pred` on the concrete hierarchy stack. -/
def def_policy_pred
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) :
    PredSet (EncodedProgram A O) :=
  EncodedProgram.policyPred π pstar

/-- Lean wrapper for `def:int-sem-class` on the concrete hierarchy stack. -/
def def_int_sem_class
    (pstar : EncodedProgram A O) :
    PredSet (EncodedProgram A O) :=
  EncodedProgram.intSemClass pstar

/-- Lean wrapper for `def:history-recoverable` on the concrete hierarchy stack. -/
def def_history_recoverable (τ : EncodedProgram A O → T) : Prop :=
  EncodedProgram.exactPolicyRecoverable τ

/-- Concrete witness package used by the paper-facing hierarchy gap theorems. -/
abbrev HierarchyWitnesses
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) (h : FullHist A O) :=
  EncodedProgram.HierarchyWitnesses (A := A) (O := O) π pstar h

/-- Lean wrapper for `lem:nesting` on the concrete hierarchy stack. -/
theorem lem_nesting
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) (h : FullHist A O) :
    predSingleton pstar ⊆ def_int_sem_class pstar ∧
    def_int_sem_class pstar ⊆ def_policy_pred π pstar ∧
    def_policy_pred π pstar ⊆ def_history_compat π pstar h ∧
    def_history_compat π pstar h ⊆ predUniv := by
  simpa [def_int_sem_class, def_policy_pred, def_history_compat] using
    (EncodedProgram.nesting (A := A) (O := O) π pstar h)

/-- Lean wrapper for `prop:refinement-chain` on the concrete hierarchy stack. -/
theorem prop_refinement_chain
    (π : ConcretePolicy A O) (h : FullHist A O) :
    historyObserver (A := A) (O := O) π h ≼ω policyObserver (A := A) (O := O) π ∧
    policyObserver (A := A) (O := O) π ≼ω behavioralObserver (A := A) (O := O) ∧
    behavioralObserver (A := A) (O := O) ≼ω syntacticObserver (A := A) (O := O) := by
  simpa [historyObserver, policyObserver, behavioralObserver, syntacticObserver] using
    (EncodedProgram.refinement_chain (A := A) (O := O) π h)

/-- Lean wrapper for `lem:observable-quotient` on the concrete hierarchy stack. -/
theorem lem_observable_quotient
    {p q : EncodedProgram A O} :
    (behavioralObserver (A := A) (O := O)).view p =
      (behavioralObserver (A := A) (O := O)).view q ↔
    (EncodedProgram.semanticEq (A := A) (O := O)).r p q := by
  simpa [behavioralObserver] using
    (EncodedProgram.observable_quotient (A := A) (O := O) (p := p) (q := q))

/-- Lean wrapper for `thm:factor-through-quotient` on the concrete hierarchy stack. -/
theorem thm_factor_through_quotient
    (τ : EncodedProgram A O → T)
    (hτ : def_history_recoverable τ) :
    ∃ τbar : SemanticQuotient (A := A) (O := O) → T,
      τ = τbar ∘ Quotient.mk (EncodedProgram.semanticEq (A := A) (O := O)) := by
  simpa [def_history_recoverable, SemanticQuotient] using
    (EncodedProgram.factor_through_semantic_quotient
      (A := A) (O := O) (T := T) τ hτ)

/-- Lean wrapper for `lem:fit-gap` on the concrete hierarchy stack. -/
theorem lem_fit_gap
    {π : ConcretePolicy A O} {pstar : EncodedProgram A O} {h : FullHist A O}
    (W : HierarchyWitnesses (A := A) (O := O) π pstar h) :
    ∃ p : EncodedProgram A O,
      def_history_compat π pstar h p ∧ ¬ def_policy_pred π pstar p := by
  simpa [HierarchyWitnesses, def_history_compat, def_policy_pred] using
    (EncodedProgram.fit_gap (A := A) (O := O) (π := π) (pstar := pstar) (h := h) W)

/-- Lean wrapper for `thm:policy-gap` on the concrete hierarchy stack. -/
theorem thm_policy_gap
    {π : ConcretePolicy A O} {pstar : EncodedProgram A O} {h : FullHist A O}
    (W : HierarchyWitnesses (A := A) (O := O) π pstar h) :
    ∃ p : EncodedProgram A O,
      def_policy_pred π pstar p ∧ ¬ def_int_sem_class pstar p := by
  simpa [HierarchyWitnesses, def_policy_pred, def_int_sem_class] using
    (EncodedProgram.policy_gap (A := A) (O := O) (π := π) (pstar := pstar) (h := h) W)

/-- Lean wrapper for `lem:syntactic-gap` on the concrete hierarchy stack. -/
theorem lem_syntactic_gap
    {π : ConcretePolicy A O} {pstar : EncodedProgram A O} {h : FullHist A O}
    (W : HierarchyWitnesses (A := A) (O := O) π pstar h) :
    predSingleton pstar ⊂ def_int_sem_class pstar := by
  simpa [HierarchyWitnesses, def_int_sem_class] using
    (EncodedProgram.syntactic_gap (A := A) (O := O) (π := π) (pstar := pstar) (h := h) W)

/-- Lean wrapper for `thm:strict-hierarchy` on the concrete hierarchy stack. -/
theorem thm_strict_hierarchy
    {π : ConcretePolicy A O} {pstar : EncodedProgram A O} {h : FullHist A O}
    (W : HierarchyWitnesses (A := A) (O := O) π pstar h) :
    predSingleton pstar ⊂ def_int_sem_class pstar ∧
    def_int_sem_class pstar ⊂ def_policy_pred π pstar ∧
    def_policy_pred π pstar ⊂ def_history_compat π pstar h := by
  simpa [HierarchyWitnesses, def_int_sem_class, def_policy_pred, def_history_compat] using
    (EncodedProgram.strict_hierarchy (A := A) (O := O) (π := π) (pstar := pstar) (h := h) W)

end ConcretePaperHierarchy

end AlgorithmicFreeEnergy
