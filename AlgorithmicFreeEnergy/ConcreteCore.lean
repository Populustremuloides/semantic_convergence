import AlgorithmicFreeEnergy.Foundations

namespace AlgorithmicFreeEnergy

universe u v

open Classical

noncomputable section

/-- Finite-support sum of rational weights over a list. -/
def listWeightedSum {α : Type u} (xs : List α) (f : α → Rat) : Rat :=
  xs.foldr (fun x acc => f x + acc) 0

theorem listWeightedSum_nil {α : Type u} (f : α → Rat) :
    listWeightedSum [] f = 0 := rfl

theorem listWeightedSum_cons {α : Type u} (x : α) (xs : List α) (f : α → Rat) :
    listWeightedSum (x :: xs) f = f x + listWeightedSum xs f := rfl

/--
If a finite-support sum is nonzero, some summand is already nonzero.
This is the basic bookkeeping lemma used by the concrete support proofs below.
-/
theorem listWeightedSum_ne_zero_exists {α : Type u} {xs : List α} {f : α → Rat}
    (hsum : listWeightedSum xs f ≠ 0) :
    ∃ x, x ∈ xs ∧ f x ≠ 0 := by
  induction xs with
  | nil =>
      simp [listWeightedSum] at hsum
  | cons x xs ih =>
      by_cases hx : f x = 0
      · have htail : listWeightedSum xs f ≠ 0 := by
          intro hzero
          apply hsum
          have htail' : List.foldr (fun x acc => f x + acc) 0 xs = 0 := hzero
          have hcons : 0 + List.foldr (fun x acc => f x + acc) 0 xs = 0 := by
            rw [htail']
            native_decide
          simpa [listWeightedSum, hx] using hcons
        rcases ih htail with ⟨y, hy, hy_ne⟩
        exact ⟨y, by simp [hy], hy_ne⟩
      · exact ⟨x, by simp, hx⟩

/--
Concrete finitely supported law on a discrete type. The support list only needs to
contain every nonzero-mass outcome; later phases can strengthen this to positivity and
normalization lemmas as needed.
-/
structure ConcreteLaw (α : Type u) where
  mass : α → Rat
  support : List α
  support_complete : ∀ a, mass a ≠ 0 → a ∈ support

namespace ConcreteLaw

variable {α : Type u} {β : Type v}

/-- Dirac law at a single point. -/
def pure [DecidableEq α] [BEq α] [LawfulBEq α] (a : α) : ConcreteLaw α where
  mass b := if b = a then 1 else 0
  support := [a]
  support_complete := by
    intro b hb
    by_cases h : b = a
    · simp [h]
    · simp [h] at hb

/-- Pushforward of a concrete law along a map. -/
def map [DecidableEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
    (f : α → β) (μ : ConcreteLaw α) : ConcreteLaw β where
  mass b := listWeightedSum μ.support (fun a => if f a = b then μ.mass a else 0)
  support := (μ.support.map f).eraseDups
  support_complete := by
    intro b hb
    rcases listWeightedSum_ne_zero_exists (xs := μ.support)
        (f := fun a => if f a = b then μ.mass a else 0) hb with ⟨a, ha, hneq⟩
    have hab : f a = b := by
      by_cases hEq : f a = b
      · exact hEq
      · simp [hEq] at hneq
    exact (List.mem_eraseDups).2 <| (List.mem_map).2 ⟨a, ha, hab⟩

/--
Kleisli bind for finitely supported concrete laws. The support is the finite union of
the branch supports over the source support.
-/
def bind [DecidableEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
    (μ : ConcreteLaw α) (κ : α → ConcreteLaw β) : ConcreteLaw β where
  mass b := listWeightedSum μ.support (fun a => μ.mass a * (κ a).mass b)
  support := (μ.support.flatMap fun a => (κ a).support).eraseDups
  support_complete := by
    intro b hb
    rcases listWeightedSum_ne_zero_exists (xs := μ.support)
        (f := fun a => μ.mass a * (κ a).mass b) hb with ⟨a, ha, hneq⟩
    have hk : (κ a).mass b ≠ 0 := by
      intro hz
      apply hneq
      simp [hz]
    have hmem : b ∈ (κ a).support := (κ a).support_complete b hk
    exact (List.mem_eraseDups).2 <| (List.mem_flatMap).2 ⟨a, ha, hmem⟩

/-- Pointwise equality of the mass functions underlying two concrete laws. -/
def PointwiseEq (μ ν : ConcreteLaw α) : Prop := ∀ a, μ.mass a = ν.mass a

theorem pointwiseEq_refl (μ : ConcreteLaw α) : PointwiseEq μ μ := by
  intro a
  rfl

theorem pointwiseEq_symm {μ ν : ConcreteLaw α} :
    PointwiseEq μ ν → PointwiseEq ν μ := by
  intro h a
  exact (h a).symm

theorem pointwiseEq_trans {μ ν ξ : ConcreteLaw α} :
    PointwiseEq μ ν → PointwiseEq ν ξ → PointwiseEq μ ξ := by
  intro h₁ h₂ a
  exact (h₁ a).trans (h₂ a)

end ConcreteLaw

section Histories

variable {A : Type u} {O : Type v}

/-- Empty interaction history. -/
def emptyHist : Hist A O 0 := by
  intro i
  exact Fin.elim0 i

/-- Append one action-observation event to the end of a finite history. -/
def snoc {t : Nat} (h : Hist A O t) (e : HistEvent A O) : Hist A O (t + 1) := by
  intro i
  by_cases hi : i.val < t
  · exact h ⟨i.val, hi⟩
  · exact e

theorem snoc_last {t : Nat} (h : Hist A O t) (e : HistEvent A O) :
    snoc h e ⟨t, Nat.lt_succ_self t⟩ = e := by
  simp [snoc]

/-- Promote a length-indexed history into the disjoint-union history space. -/
def asFullHist {t : Nat} (h : Hist A O t) : FullHist A O :=
  ⟨t, h⟩

end Histories

section Kernels

variable (A : Type u) (O : Type v)

abbrev ConcretePolicy := (t : Nat) → Hist A O t → ConcreteLaw A
abbrev ConcreteKernel := (t : Nat) → Hist A O t → A → ConcreteLaw O
abbrev ConcreteProgram := ConcreteKernel A O

end Kernels

section HistInstances

variable {A : Type u} {O : Type v} [DecidableEq A] [DecidableEq O]

instance instDecidableEqHist (t : Nat) : DecidableEq (Hist A O t) :=
  by
    classical
    infer_instance

instance instBEqHist (t : Nat) : BEq (Hist A O t) where
  beq h₁ h₂ := if h₁ = h₂ then true else false

instance instReflBEqHist (t : Nat) : ReflBEq (Hist A O t) where
  rfl := by
    intro h
    change (if h = h then true else false) = true
    simp

instance instLawfulBEqHist (t : Nat) : LawfulBEq (Hist A O t) where
  eq_of_beq := by
    intro h₁ h₂ hEq
    change (if h₁ = h₂ then true else false) = true at hEq
    by_cases h : h₁ = h₂
    · exact h
    · simp [h] at hEq

instance instDecidableEqFullHist : DecidableEq (FullHist A O) :=
  by
    classical
    infer_instance

instance instBEqFullHist : BEq (FullHist A O) where
  beq h₁ h₂ := if h₁ = h₂ then true else false

instance instReflBEqFullHist : ReflBEq (FullHist A O) where
  rfl := by
    intro h
    change (if h = h then true else false) = true
    simp

instance instLawfulBEqFullHist : LawfulBEq (FullHist A O) where
  eq_of_beq := by
    intro h₁ h₂ hEq
    change (if h₁ = h₂ then true else false) = true at hEq
    by_cases h : h₁ = h₂
    · exact h
    · simp [h] at hEq

end HistInstances

section PathLaws

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/--
Concrete finite-horizon path law induced by a concrete policy and one-step observation
kernel.
-/
def histLaw (π : ConcretePolicy A O) (κ : ConcreteKernel A O) : (t : Nat) → ConcreteLaw (Hist A O t)
  | 0 => ConcreteLaw.pure (emptyHist : Hist A O 0)
  | t + 1 =>
      ConcreteLaw.bind (histLaw π κ t) (fun h =>
        ConcreteLaw.bind (π t h) (fun a =>
          ConcreteLaw.map (fun o => snoc h (a, o)) (κ t h a)))

/-- The same finite-horizon law, viewed in the disjoint-union history space. -/
def fullHistLaw (π : ConcretePolicy A O) (κ : ConcreteKernel A O) (t : Nat) :
    ConcreteLaw (FullHist A O) :=
  ConcreteLaw.map asFullHist (histLaw π κ t)

/-- A finite history is reachable exactly when it has nonzero mass under the induced law. -/
def reachableHist (π : ConcretePolicy A O) (κ : ConcreteKernel A O) {t : Nat}
    (h : Hist A O t) : Prop :=
  (histLaw π κ t).mass h ≠ 0

/-- A full history is reachable exactly when it has nonzero mass under the lifted law. -/
def reachableFullHist (π : ConcretePolicy A O) (κ : ConcreteKernel A O) (t : Nat)
    (h : FullHist A O) : Prop :=
  (fullHistLaw π κ t).mass h ≠ 0

/-- A policy supports an action at a history when the action has nonzero one-step mass. -/
def actionSupported (π : ConcretePolicy A O) {t : Nat} (h : Hist A O t) (a : A) : Prop :=
  (π t h).mass a ≠ 0

/-- Reachable history-action pairs under the concrete interaction semantics. -/
def reachablePair (π : ConcretePolicy A O) (κ : ConcreteKernel A O) {t : Nat}
    (h : Hist A O t) (a : A) : Prop :=
  reachableHist π κ h ∧ actionSupported π h a

omit [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O] in
theorem reachableHist_mem_support (π : ConcretePolicy A O) (κ : ConcreteKernel A O)
    {t : Nat} {h : Hist A O t} (hReach : reachableHist π κ h) :
    h ∈ (histLaw π κ t).support :=
  (histLaw π κ t).support_complete h hReach

omit [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O] in
theorem reachableFullHist_mem_support (π : ConcretePolicy A O) (κ : ConcreteKernel A O)
    {t : Nat} {h : FullHist A O} (hReach : reachableFullHist π κ t h) :
    h ∈ (fullHistLaw π κ t).support :=
  (fullHistLaw π κ t).support_complete h hReach

/-- Reachable-pair predicate associated to a concrete policy/kernel pair. -/
abbrev ReachablePairPred (A : Type u) (O : Type v) :=
  ∀ {t : Nat}, Hist A O t → A → Prop

/--
Agreement of concrete kernels on a fixed family of reachable history-action pairs.
This is the concrete first-principles version of the manuscript's reachable-pair
equality convention.
-/
def kernelEqOnReachablePairs (R : ReachablePairPred A O)
    (κ₁ κ₂ : ConcreteKernel A O) : Prop :=
  ∀ {t : Nat} (h : Hist A O t) (a : A) (o : O),
    R h a →
    (κ₁ t h a).mass o = (κ₂ t h a).mass o

/-- The concrete reachable-pair predicate induced by a policy/kernel pair. -/
def reachablePairPredicate (π : ConcretePolicy A O) (κ : ConcreteKernel A O) :
    ReachablePairPred A O :=
  fun h a => reachablePair π κ h a

omit [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O] in
theorem kernelEqOnReachablePairs_refl (R : ReachablePairPred A O)
    (κ : ConcreteKernel A O) :
    kernelEqOnReachablePairs R κ κ := by
  intro t h a o hR
  rfl

omit [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O] in
theorem kernelEqOnReachablePairs_symm (R : ReachablePairPred A O)
    {κ₁ κ₂ : ConcreteKernel A O} :
    kernelEqOnReachablePairs R κ₁ κ₂ →
    kernelEqOnReachablePairs R κ₂ κ₁ := by
  intro hEq t h a o hR
  exact (hEq h a o hR).symm

omit [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O] in
theorem kernelEqOnReachablePairs_trans (R : ReachablePairPred A O)
    {κ₁ κ₂ κ₃ : ConcreteKernel A O} :
    kernelEqOnReachablePairs R κ₁ κ₂ →
    kernelEqOnReachablePairs R κ₂ κ₃ →
    kernelEqOnReachablePairs R κ₁ κ₃ := by
  intro h₁₂ h₂₃ t h a o hR
  exact (h₁₂ h a o hR).trans (h₂₃ h a o hR)

/-- Setoid of concrete programs modulo agreement on a fixed reachable-pair predicate. -/
def reachableKernelSetoid (R : ReachablePairPred A O) : Setoid (ConcreteProgram A O) where
  r := kernelEqOnReachablePairs R
  iseqv := by
    refine ⟨kernelEqOnReachablePairs_refl R, ?_, ?_⟩
    · intro κ₁ κ₂
      exact kernelEqOnReachablePairs_symm R
    · intro κ₁ κ₂ κ₃
      exact kernelEqOnReachablePairs_trans R

end PathLaws
end

end AlgorithmicFreeEnergy
