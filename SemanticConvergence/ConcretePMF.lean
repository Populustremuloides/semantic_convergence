import SemanticConvergence.ConcreteCore

namespace SemanticConvergence

universe u

open Classical
open scoped BigOperators

noncomputable section

namespace ConcreteLaw

variable {α : Type u} [DecidableEq α]

/-- `ENNReal` mass function associated to a finite-support rational law. -/
def toENNRealMass (μ : ConcreteLaw α) (a : α) : ENNReal :=
  ENNReal.ofReal (μ.mass a : ℝ)

/--
The finite-support law can be transported to a PMF: masses are nonnegative and sum to one over
the deduplicated support.
-/
def HasPMFMass (μ : ConcreteLaw α) : Prop :=
  (∀ a, 0 ≤ μ.mass a) ∧ ((μ.support.toFinset.sum fun a => μ.toENNRealMass a) = 1)

theorem mass_eq_zero_of_not_mem_support (μ : ConcreteLaw α) {a : α}
    (ha : a ∉ μ.support.toFinset) :
    μ.mass a = 0 := by
  by_contra hne
  exact ha <| by simpa using μ.support_complete a hne

theorem toENNRealMass_eq_zero_of_not_mem_support (μ : ConcreteLaw α) {a : α}
    (ha : a ∉ μ.support.toFinset) :
    μ.toENNRealMass a = 0 := by
  simp [toENNRealMass, μ.mass_eq_zero_of_not_mem_support ha]

/-- Transport a finite-support rational law to a PMF once its probability constraints are given. -/
def toPMF (μ : ConcreteLaw α) (hμ : μ.HasPMFMass) : PMF α :=
  PMF.ofFinset (μ.toENNRealMass) μ.support.toFinset hμ.2
    (fun _ ha => μ.toENNRealMass_eq_zero_of_not_mem_support ha)

@[simp]
theorem toPMF_apply (μ : ConcreteLaw α) (hμ : μ.HasPMFMass) (a : α) :
    μ.toPMF hμ a = μ.toENNRealMass a :=
  rfl

theorem mem_support_toPMF_iff (μ : ConcreteLaw α) (hμ : μ.HasPMFMass) (a : α) :
    a ∈ (μ.toPMF hμ).support ↔ μ.mass a ≠ 0 := by
  constructor
  · intro ha
    have hpmf : μ.toPMF hμ a ≠ 0 := (PMF.mem_support_iff _ _).1 ha
    have hnonneg := hμ.1 a
    by_contra hmass
    apply hpmf
    simp [ConcreteLaw.toPMF, ConcreteLaw.toENNRealMass, hmass]
  · intro hmass
    have hnonneg := hμ.1 a
    have hmassENN : μ.toENNRealMass a ≠ 0 := by
      intro hzero
      apply hmass
      have hnonneg_real : (0 : ℝ) ≤ μ.mass a := by
        exact_mod_cast hnonneg
      have hle_real : (μ.mass a : ℝ) ≤ 0 := by
        simpa [ConcreteLaw.toENNRealMass] using (ENNReal.ofReal_eq_zero.mp hzero)
      have hzero_real : (μ.mass a : ℝ) = 0 := le_antisymm hle_real hnonneg_real
      exact_mod_cast hzero_real
    exact (PMF.mem_support_iff _ _).2 <| by
      simpa [ConcreteLaw.toPMF] using hmassENN

end ConcreteLaw

end

end SemanticConvergence
