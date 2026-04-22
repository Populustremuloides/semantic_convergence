namespace SemanticConvergence

universe u v w

/--
`def_observer` is the Lean counterpart of `def:observer` from the manuscript.
It packages a codomain together with the view map from programs into that codomain.
-/
structure def_observer (P : Type u) where
  Ω : Type v
  view : P → Ω

abbrev Observer := def_observer

/-- Finite action-observation event at one interaction step. -/
abbrev HistEvent (A : Type u) (O : Type v) := A × O

/-- Predicate-style sets used throughout the abstract paper model. -/
abbrev PredSet (α : Type u) := α → Prop

/-- Subset relation on predicate-style sets. -/
def PredSubset {α : Type u} (s t : PredSet α) : Prop := ∀ ⦃a : α⦄, s a → t a

infix:50 " ⊆ " => PredSubset

/-- Strict subset relation on predicate-style sets. -/
def PredSSubset {α : Type u} (s t : PredSet α) : Prop :=
  s ⊆ t ∧ ∃ a : α, t a ∧ ¬ s a

infix:50 " ⊂ " => PredSSubset

/-- Singleton predicate-set. -/
def predSingleton {α : Type u} (a : α) : PredSet α := fun x => x = a

/-- Universal predicate-set. -/
def predUniv {α : Type u} : PredSet α := fun _ => True

/-- Length-`t` interaction histories, modeled as functions on `Fin t`. -/
abbrev Hist (A : Type u) (O : Type v) (t : Nat) := Fin t → HistEvent A O

/-- Disjoint union of all finite interaction histories. -/
abbrev FullHist (A : Type u) (O : Type v) := Σ t : Nat, Hist A O t

/-- Programs are observationally equivalent at observer `ω` when `ω` gives the same view. -/
def observerEquiv {P : Type u} (ω : Observer P) : Setoid P where
  r p q := ω.view p = ω.view q
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      rfl
    · intro p q hpq
      exact hpq.symm
    · intro p q r hpq hqr
      exact hpq.trans hqr

/--
Observer refinement: `ω₁ ≤ ω₂` iff the view of `ω₂` factors through the view of `ω₁`.
This is the exact structural relation used repeatedly in the paper.
-/
def observerRefines {P : Type u} (ω₁ ω₂ : Observer P) : Prop :=
  ∃ f : ω₂.Ω → ω₁.Ω, ω₁.view = f ∘ ω₂.view

infix:50 " ≼ω " => observerRefines

theorem observerRefines_refl {P : Type u} (ω : Observer P) : ω ≼ω ω := by
  refine ⟨id, ?_⟩
  funext p
  rfl

theorem observerRefines_trans {P : Type u} {ω₁ ω₂ ω₃ : Observer P}
    (h₁₂ : ω₁ ≼ω ω₂) (h₂₃ : ω₂ ≼ω ω₃) : ω₁ ≼ω ω₃ := by
  rcases h₁₂ with ⟨f₂₁, hf₂₁⟩
  rcases h₂₃ with ⟨f₃₂, hf₃₂⟩
  refine ⟨f₂₁ ∘ f₃₂, ?_⟩
  funext p
  simp [Function.comp, hf₂₁, hf₃₂]

/-- The canonical quotient observer attached to a setoid. -/
def quotientObserver {P : Type u} (s : Setoid P) : Observer P where
  Ω := Quotient s
  view := Quotient.mk s

/--
`τ` is constant on `s`-classes exactly when it factors through the quotient.
This is the Lean counterpart of the quotient-lift mechanism used in
`thm:factor-through-quotient`.
-/
def constantOnSetoid {P : Type u} {T : Type v} (s : Setoid P) (τ : P → T) : Prop :=
  ∀ ⦃p q : P⦄, s.r p q → τ p = τ q

theorem constantOnSetoid_iff_exists_quotientLift {P : Type u} {T : Type v}
    (s : Setoid P) (τ : P → T) :
    constantOnSetoid s τ ↔ ∃ τbar : Quotient s → T, τ = τbar ∘ Quotient.mk s := by
  constructor
  · intro hτ
    refine ⟨Quotient.lift τ (by intro p q hpq; exact hτ hpq), ?_⟩
    funext p
    rfl
  · intro hτ
    rcases hτ with ⟨τbar, hτbar⟩
    intro p q hpq
    have hq : (Quotient.mk s p : Quotient s) = Quotient.mk s q := Quotient.sound hpq
    have hp : τ p = τbar (Quotient.mk s p) := by
      simpa [Function.comp] using congrArg (fun f => f p) hτbar
    have hq' : τ q = τbar (Quotient.mk s q) := by
      simpa [Function.comp] using congrArg (fun f => f q) hτbar
    calc
      τ p = τbar (Quotient.mk s p) := hp
      _ = τbar (Quotient.mk s q) := by simp [hq]
      _ = τ q := hq'.symm

theorem quotientLift_unique {P : Type u} {T : Type v} (s : Setoid P)
    {τbar₁ τbar₂ : Quotient s → T}
    (h : τbar₁ ∘ Quotient.mk s = τbar₂ ∘ Quotient.mk s) :
    τbar₁ = τbar₂ := by
  funext q
  refine Quotient.inductionOn q ?_
  intro p
  exact congrArg (fun f => f p) h

/--
The quotient observer identifies precisely the classes of the underlying setoid.
This is the core structural content behind `lem:observable-quotient`.
-/
theorem quotientObserver_eq_iff {P : Type u} (s : Setoid P) (p q : P) :
    (quotientObserver s).view p = (quotientObserver s).view q ↔ s.r p q := by
  constructor
  · intro hpq
    exact Quotient.exact hpq
  · intro hpq
    exact Quotient.sound hpq

end SemanticConvergence
