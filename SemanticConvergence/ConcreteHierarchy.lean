import SemanticConvergence.ConcretePrior

namespace SemanticConvergence

universe u v w

noncomputable section

/-- Concrete program syntax: an explicit code together with a concrete environment kernel. -/
structure EncodedProgram (A : Type u) (O : Type v) where
  code : BitCode
  kernel : ConcreteProgram A O

namespace EncodedProgram

variable {A : Type u} {O : Type v}

/-- The concrete policy-view codomain: all finite-horizon history masses under the policy. -/
abbrev PolicyView (A : Type u) (O : Type v) := (t : Nat) → Hist A O t → Rat

/-- The concrete history-view codomain at a fixed history: the mass of that history. -/
abbrev HistoryView := Rat

/-- The policy-level concrete path view induced by a program under a policy. -/
def pathView
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (p : EncodedProgram A O) : PolicyView A O :=
  fun t h => (histLaw π p.kernel t).mass h

/-- The concrete history observer at a fixed policy/history pair. -/
def historyView
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) (p : EncodedProgram A O) : HistoryView :=
  pathView π p h.1 h.2

/--
Concrete interventional semantic equivalence: two programs are semantically identical when
they induce the same policy-view under every policy.
-/
def semanticEq
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O] :
    Setoid (EncodedProgram A O) where
  r p q := ∀ π : ConcretePolicy A O, pathView π p = pathView π q
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p π
      rfl
    · intro p q hpq π
      exact (hpq π).symm
    · intro p q r hpq hqr π
      exact (hpq π).trans (hqr π)

/-- Programs compatible with the currently realized history under the given policy. -/
def historyCompat
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) (h : FullHist A O) :
    PredSet (EncodedProgram A O) :=
  fun p => historyView π h p = historyView π h pstar

/-- Programs compatible with the entire policy-conditioned path view. -/
def policyPred
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) :
    PredSet (EncodedProgram A O) :=
  fun p => pathView π p = pathView π pstar

/-- The concrete interventional semantic class of a program. -/
def intSemClass
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (pstar : EncodedProgram A O) :
    PredSet (EncodedProgram A O) :=
  fun p => (semanticEq (A := A) (O := O)).r p pstar

/-- The concrete semantic quotient type. -/
abbrev SemanticQuotient
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O] :=
  Quotient (semanticEq (A := A) (O := O))

/-- The syntactic observer remembers the full encoded program. -/
def syntacticObserver : Observer (EncodedProgram A O) where
  Ω := EncodedProgram A O
  view := id

/-- The semantic observer is the quotient observer of concrete semantic equivalence. -/
def behavioralObserver
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O] :
    Observer (EncodedProgram A O) :=
  quotientObserver (semanticEq (A := A) (O := O))

/-- The concrete policy observer under a fixed policy. -/
def policyObserver
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) : Observer (EncodedProgram A O) where
  Ω := PolicyView A O
  view := pathView π

/-- The concrete history observer at a fixed policy/history pair. -/
def historyObserver
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) : Observer (EncodedProgram A O) where
  Ω := HistoryView
  view := historyView π h

theorem intSemClass_self
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (pstar : EncodedProgram A O) :
    intSemClass pstar pstar := by
  intro π
  rfl

theorem intSemClass_subset_policyPred
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) :
    intSemClass pstar ⊆ policyPred π pstar := by
  intro p hp
  exact hp π

theorem policyPred_subset_historyCompat
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) (h : FullHist A O) :
    policyPred π pstar ⊆ historyCompat π pstar h := by
  intro p hp
  exact congrArg (fun f => f h.1 h.2) hp

/-- Concrete nesting chain for the hierarchy observers. -/
theorem nesting
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) (h : FullHist A O) :
    predSingleton pstar ⊆ intSemClass pstar ∧
    intSemClass pstar ⊆ policyPred π pstar ∧
    policyPred π pstar ⊆ historyCompat π pstar h ∧
    historyCompat π pstar h ⊆ predUniv := by
  constructor
  · intro p hp
    cases hp
    exact intSemClass_self pstar
  constructor
  · exact intSemClass_subset_policyPred π pstar
  constructor
  · exact policyPred_subset_historyCompat π pstar h
  · intro p hp
    trivial

/-- Concrete refinement chain: history -> policy -> semantic -> syntactic. -/
theorem refinement_chain
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) :
    historyObserver (A := A) (O := O) π h ≼ω policyObserver (A := A) (O := O) π ∧
    policyObserver (A := A) (O := O) π ≼ω behavioralObserver (A := A) (O := O) ∧
    behavioralObserver (A := A) (O := O) ≼ω syntacticObserver (A := A) (O := O) := by
  constructor
  · refine ⟨fun f => f h.1 h.2, ?_⟩
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

/-- Concrete observable quotient statement. -/
theorem observable_quotient
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    {p q : EncodedProgram A O} :
    (behavioralObserver (A := A) (O := O)).view p =
      (behavioralObserver (A := A) (O := O)).view q ↔
    (semanticEq (A := A) (O := O)).r p q :=
  quotientObserver_eq_iff (semanticEq (A := A) (O := O)) p q

/--
Exact recoverability from a concrete policy observer. This is the policy-view analogue of
history recoverability, phrased without asymptotics.
-/
def exactPolicyRecoverable
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    {T : Type w} (τ : EncodedProgram A O → T) : Prop :=
  ∃ π : ConcretePolicy A O, ∃ decoder : PolicyView A O → T,
    ∀ p : EncodedProgram A O, decoder (pathView π p) = τ p

theorem exactPolicyRecoverable_constantOnSemanticClasses
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    {T : Type w} (τ : EncodedProgram A O → T)
    (hτ : exactPolicyRecoverable τ) :
    constantOnSetoid (semanticEq (A := A) (O := O)) τ := by
  rcases hτ with ⟨π, decoder, hdec⟩
  intro p q hpq
  calc
    τ p = decoder (pathView π p) := by simpa using (hdec p).symm
    _ = decoder (pathView π q) := by rw [hpq π]
    _ = τ q := by simpa using (hdec q)

/-- Concrete quotient factorization for exactly policy-recoverable targets. -/
theorem factor_through_semantic_quotient
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    {T : Type w} (τ : EncodedProgram A O → T)
    (hτ : exactPolicyRecoverable τ) :
    ∃ τbar : SemanticQuotient (A := A) (O := O) → T,
      τ = τbar ∘ Quotient.mk (semanticEq (A := A) (O := O)) := by
  exact (constantOnSetoid_iff_exists_quotientLift
    (semanticEq (A := A) (O := O)) τ).mp
      (exactPolicyRecoverable_constantOnSemanticClasses τ hτ)

/-- Explicit witness package for the concrete strict hierarchy. -/
structure HierarchyWitnesses
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (pstar : EncodedProgram A O) (h : FullHist A O) where
  fitGapWitness :
    ∃ p : EncodedProgram A O,
      historyCompat π pstar h p ∧ ¬ policyPred π pstar p
  policyGapWitness :
    ∃ p : EncodedProgram A O,
      policyPred π pstar p ∧ ¬ intSemClass pstar p
  syntacticGapWitness :
    ∃ p' : EncodedProgram A O, p' ≠ pstar ∧ intSemClass pstar p'

theorem fit_gap
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    {π : ConcretePolicy A O} {pstar : EncodedProgram A O} {h : FullHist A O}
    (W : HierarchyWitnesses π pstar h) :
    ∃ p : EncodedProgram A O, historyCompat π pstar h p ∧ ¬ policyPred π pstar p :=
  W.fitGapWitness

theorem policy_gap
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    {π : ConcretePolicy A O} {pstar : EncodedProgram A O} {h : FullHist A O}
    (W : HierarchyWitnesses π pstar h) :
    ∃ p : EncodedProgram A O, policyPred π pstar p ∧ ¬ intSemClass pstar p :=
  W.policyGapWitness

theorem syntactic_gap
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    {π : ConcretePolicy A O} {pstar : EncodedProgram A O} {h : FullHist A O}
    (W : HierarchyWitnesses π pstar h) :
    predSingleton pstar ⊂ intSemClass pstar := by
  refine ⟨?_, ?_⟩
  · intro p hp
    cases hp
    exact intSemClass_self pstar
  · rcases W.syntacticGapWitness with ⟨p', hp'ne, hp'sem⟩
    refine ⟨p', hp'sem, ?_⟩
    intro hpSingleton
    exact hp'ne hpSingleton

theorem strict_hierarchy
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    {π : ConcretePolicy A O} {pstar : EncodedProgram A O} {h : FullHist A O}
    (W : HierarchyWitnesses π pstar h) :
    predSingleton pstar ⊂ intSemClass pstar ∧
    intSemClass pstar ⊂ policyPred π pstar ∧
    policyPred π pstar ⊂ historyCompat π pstar h := by
  constructor
  · exact syntactic_gap W
  constructor
  · refine ⟨(nesting π pstar h).2.1, ?_⟩
    rcases W.policyGapWitness with ⟨p, hpPred, hpNotSem⟩
    exact ⟨p, hpPred, hpNotSem⟩
  · refine ⟨(nesting π pstar h).2.2.1, ?_⟩
    rcases W.fitGapWitness with ⟨p, hpHist, hpNotPred⟩
    exact ⟨p, hpHist, hpNotPred⟩

end EncodedProgram

end

end SemanticConvergence
