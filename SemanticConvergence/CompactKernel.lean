import Mathlib

/-!
# Compact kernel primitives

This module is the measure-theoretic substrate for the compact-action kernel
overhaul.  It deliberately stops before the paper-facing minimizer theorem: the
goal here is to expose the product reference measure, bounded measurable score,
extended KL term, Gibbs weight, partition function, and normalized Gibbs measure
with first-principles normalization lemmas.
-/

namespace SemanticConvergence

noncomputable section

open Classical MeasureTheory Set
open InformationTheory
open scoped ENNReal

namespace CompactKernel

universe u v

/-- A Borel probability law has full topological support when every nonempty
open set has nonzero mass. -/
def HasFullSupport {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  ∀ ⦃s : Set X⦄, IsOpen s → s.Nonempty → μ s ≠ 0

theorem HasFullSupport.measure_ne_zero_of_isOpen
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} (hμ : HasFullSupport μ)
    {s : Set X} (hs_open : IsOpen s) (hs_nonempty : s.Nonempty) :
    μ s ≠ 0 :=
  hμ hs_open hs_nonempty

theorem HasFullSupport.ball_ne_zero
    {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X} (hμ : HasFullSupport μ)
    (x : X) {ε : ℝ} (hε : 0 < ε) :
    μ (Metric.ball x ε) ≠ 0 := by
  exact hμ Metric.isOpen_ball ⟨x, Metric.mem_ball_self hε⟩

/-- Uniform radius-`r` lower mass used by the compact-action support theorem. -/
def ballMassFloor
    {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) : ℝ≥0∞ :=
  ⨅ x : X, μ (Metric.ball x r)

theorem ballMassFloor_le_ball
    {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (x : X) :
    ballMassFloor μ r ≤ μ (Metric.ball x r) :=
  iInf_le (fun x : X => μ (Metric.ball x r)) x

theorem exists_positive_le_ball_mass_floor
    {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X] [CompactSpace X]
    [Nonempty X] {μ : Measure X} (hμ : HasFullSupport μ)
    {r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ≥0∞, ρ ≠ 0 ∧ ∀ x : X, ρ ≤ μ (Metric.ball x r) := by
  have hr2 : 0 < r / 2 := by linarith
  have hcover : (univ : Set X) ⊆ ⋃ x : X, Metric.ball x (r / 2) := by
    intro x hx
    exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self hr2⟩
  obtain ⟨t, htcover⟩ :=
    (isCompact_univ (X := X)).elim_finite_subcover
      (fun x : X => Metric.ball x (r / 2))
      (fun _ => Metric.isOpen_ball)
      hcover
  have ht_nonempty : t.Nonempty := by
    have hxcover := htcover (mem_univ (Classical.arbitrary X))
    simp only [mem_iUnion] at hxcover
    rcases hxcover with ⟨i, hi⟩
    exact ⟨i, hi.1⟩
  obtain ⟨i0, hi0, hmin⟩ :=
    Finset.exists_min_image t
      (fun i : X => μ (Metric.ball i (r / 2))) ht_nonempty
  refine ⟨μ (Metric.ball i0 (r / 2)), hμ.ball_ne_zero i0 hr2, ?_⟩
  intro x
  have hxcover := htcover (mem_univ x)
  simp only [mem_iUnion] at hxcover
  rcases hxcover with ⟨i, hi⟩
  have hxi : dist x i < r / 2 := by
    simpa [Metric.mem_ball] using hi.2
  have hsubset : Metric.ball i (r / 2) ⊆ Metric.ball x r := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    calc
      dist y x ≤ dist y i + dist i x := dist_triangle y i x
      _ = dist y i + dist x i := by rw [dist_comm i x]
      _ < r / 2 + r / 2 := add_lt_add hy hxi
      _ = r := by ring
  exact (hmin i hi.1).trans (measure_mono hsubset)

theorem ballMassFloor_ne_zero_of_fullSupport
    {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X] [CompactSpace X]
    [Nonempty X] {μ : Measure X} (hμ : HasFullSupport μ)
    {r : ℝ} (hr : 0 < r) :
    ballMassFloor μ r ≠ 0 := by
  obtain ⟨ρ, hρ_ne_zero, hρ_le⟩ :=
    exists_positive_le_ball_mass_floor (X := X) hμ hr
  have hρ_floor : ρ ≤ ballMassFloor μ r := by
    exact le_iInf hρ_le
  intro hfloor
  exact hρ_ne_zero (le_antisymm (by simpa [hfloor] using hρ_floor) bot_le)

/--
A bounded measurable kernel score on a class/action product.

The manuscript's compact kernel only needs boundedness; nonnegativity is not
baked in.  The interval witnesses give the later Gibbs normalization proof a
uniform finite upper bound and a uniform strictly positive lower Gibbs weight.
-/
structure BoundedKernelScore
    (C : Type u) (X : Type v) [MeasurableSpace C] [MeasurableSpace X] where
  toFun : C → X → ℝ
  measurable : Measurable fun z : C × X => toFun z.1 z.2
  lower : ℝ
  upper : ℝ
  lower_le : ∀ c x, lower ≤ toFun c x
  le_upper : ∀ c x, toFun c x ≤ upper

instance
    {C : Type u} {X : Type v} [MeasurableSpace C] [MeasurableSpace X] :
    CoeFun (BoundedKernelScore C X) (fun _ => C → X → ℝ) where
  coe B := B.toFun

namespace BoundedKernelScore

variable {C : Type u} {X : Type v} [MeasurableSpace C] [MeasurableSpace X]

/-- Product-coordinate view of a kernel score. -/
def prodFun (B : BoundedKernelScore C X) : C × X → ℝ :=
  fun z => B z.1 z.2

@[simp]
theorem prodFun_apply (B : BoundedKernelScore C X) (z : C × X) :
    B.prodFun z = B z.1 z.2 :=
  rfl

theorem measurable_prodFun (B : BoundedKernelScore C X) :
    Measurable B.prodFun :=
  B.measurable

theorem lower_le_prodFun (B : BoundedKernelScore C X) (z : C × X) :
    B.lower ≤ B.prodFun z :=
  B.lower_le z.1 z.2

theorem prodFun_le_upper (B : BoundedKernelScore C X) (z : C × X) :
    B.prodFun z ≤ B.upper :=
  B.le_upper z.1 z.2

/-- A concrete absolute bound induced by the interval witnesses. -/
def absBound (B : BoundedKernelScore C X) : ℝ :=
  max |B.lower| |B.upper|

theorem absBound_nonneg (B : BoundedKernelScore C X) :
    0 ≤ B.absBound := by
  exact le_trans (abs_nonneg B.lower) (le_max_left _ _)

theorem norm_prodFun_le_absBound (B : BoundedKernelScore C X) (z : C × X) :
    ‖B.prodFun z‖ ≤ B.absBound := by
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hlow_abs : -B.absBound ≤ B.lower := by
      have h₁ : -|B.lower| ≤ B.lower := neg_abs_le B.lower
      have h₂ : |B.lower| ≤ B.absBound := le_max_left _ _
      linarith
    exact hlow_abs.trans (B.lower_le_prodFun z)
  · have hupper_abs : B.upper ≤ B.absBound := by
      have h₁ : B.upper ≤ |B.upper| := le_abs_self B.upper
      have h₂ : |B.upper| ≤ B.absBound := le_max_right _ _
      linarith
    exact (B.prodFun_le_upper z).trans hupper_abs

theorem integrable_prodFun
    (B : BoundedKernelScore C X) (μ : Measure (C × X))
    [IsFiniteMeasure μ] :
    Integrable B.prodFun μ := by
  refine Integrable.of_bound B.measurable_prodFun.aestronglyMeasurable B.absBound ?_
  exact ae_of_all μ fun z => B.norm_prodFun_le_absBound z

end BoundedKernelScore

variable {C : Type u} {X : Type v} [MeasurableSpace C] [MeasurableSpace X]

/-- Product reference law `wbar ⊗ λ` for class and action references. -/
def referenceMeasure (classRef : Measure C) (actionRef : Measure X) :
    Measure (C × X) :=
  classRef.prod actionRef

theorem referenceMeasure_eq_prod
    (classRef : Measure C) (actionRef : Measure X) :
    referenceMeasure classRef actionRef = classRef.prod actionRef :=
  rfl

instance referenceMeasure.instIsProbabilityMeasure
    (classRef : Measure C) (actionRef : Measure X)
    [IsProbabilityMeasure classRef] [IsProbabilityMeasure actionRef] :
    IsProbabilityMeasure (referenceMeasure classRef actionRef) := by
  dsimp [referenceMeasure]
  infer_instance

@[simp]
theorem referenceMeasure_univ
    (classRef : Measure C) (actionRef : Measure X)
    [IsProbabilityMeasure classRef] [IsProbabilityMeasure actionRef] :
    referenceMeasure classRef actionRef univ = 1 := by
  exact measure_univ

/-- Extended KL of a kernel law against the product reference. -/
def kernelKL (κ ref : Measure (C × X)) : ℝ≥0∞ :=
  klDiv κ ref

theorem kernelKL_eq_top_of_not_ac
    {κ ref : Measure (C × X)} (hκ : ¬ κ ≪ ref) :
    kernelKL κ ref = ∞ := by
  simpa [kernelKL] using klDiv_of_not_ac hκ

theorem kernelKL_ne_top_iff
    {κ ref : Measure (C × X)} :
    kernelKL κ ref ≠ ∞ ↔ κ ≪ ref ∧ Integrable (llr κ ref) κ := by
  simpa [kernelKL] using (klDiv_ne_top_iff : klDiv κ ref ≠ ∞ ↔ κ ≪ ref ∧
    Integrable (llr κ ref) κ)

theorem kernelKL_eq_zero_iff_eq
    (κ ν : Measure (C × X)) [IsFiniteMeasure κ] [IsFiniteMeasure ν] :
    kernelKL κ ν = 0 ↔ κ = ν := by
  simpa [kernelKL] using
    (klDiv_eq_zero_iff (μ := κ) (ν := ν))

theorem kernelKL_toReal_nonneg
    (κ ν : Measure (C × X)) :
    0 ≤ (kernelKL κ ν).toReal :=
  ENNReal.toReal_nonneg

theorem kernelKL_toReal_eq_zero_iff_eq_of_ne_top
    (κ ν : Measure (C × X)) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (hfinite : kernelKL κ ν ≠ ∞) :
    (kernelKL κ ν).toReal = 0 ↔ κ = ν := by
  constructor
  · intro hzero
    have hKLzero : kernelKL κ ν = 0 := by
      rw [← ENNReal.ofReal_toReal hfinite, hzero, ENNReal.ofReal_zero]
    exact (kernelKL_eq_zero_iff_eq κ ν).mp hKLzero
  · intro hκν
    have hKLzero : kernelKL κ ν = 0 :=
      (kernelKL_eq_zero_iff_eq κ ν).mpr hκν
    rw [hKLzero, ENNReal.toReal_zero]

/-- Real expected score of a kernel law. Boundedness of `B` supplies integrability. -/
def scoreIntegral (κ : Measure (C × X)) (B : BoundedKernelScore C X) : ℝ :=
  ∫ z, B.prodFun z ∂κ

theorem scoreIntegral_integrable
    (κ : Measure (C × X)) [IsFiniteMeasure κ]
    (B : BoundedKernelScore C X) :
    Integrable B.prodFun κ :=
  B.integrable_prodFun κ

theorem scoreIntegral_lower_bound
    (κ : Measure (C × X)) [IsProbabilityMeasure κ]
    (B : BoundedKernelScore C X) :
    B.lower ≤ scoreIntegral κ B := by
  have hconst : Integrable (fun _ : C × X => B.lower) κ := integrable_const _
  have hscore : Integrable B.prodFun κ := B.integrable_prodFun κ
  have hle :
      (∫ z : C × X, B.lower ∂κ) ≤ ∫ z, B.prodFun z ∂κ := by
    exact integral_mono hconst hscore fun z => B.lower_le_prodFun z
  simpa [scoreIntegral] using hle

theorem scoreIntegral_upper_bound
    (κ : Measure (C × X)) [IsProbabilityMeasure κ]
    (B : BoundedKernelScore C X) :
    scoreIntegral κ B ≤ B.upper := by
  have hscore : Integrable B.prodFun κ := B.integrable_prodFun κ
  have hconst : Integrable (fun _ : C × X => B.upper) κ := integrable_const _
  have hle :
      (∫ z, B.prodFun z ∂κ) ≤ ∫ _ : C × X, B.upper ∂κ := by
    exact integral_mono hscore hconst fun z => B.prodFun_le_upper z
  simpa [scoreIntegral] using hle

/-- Finite-value real view of the kernel objective, used only under finite-KL hypotheses. -/
def kernelObjectiveReal
    (β γ : ℝ) (B : BoundedKernelScore C X)
    (κ ref : Measure (C × X)) : ℝ :=
  -β * scoreIntegral κ B + γ * (kernelKL κ ref).toReal

/--
Extended-valued kernel objective from the manuscript:
`-β * Eκ[B] + γ * KL(κ || ref)`.

The KL contribution remains extended-valued, so non-dominated kernel laws are
not silently projected into a finite chart.
-/
def kernelObjectiveEReal
    (β γ : ℝ) (B : BoundedKernelScore C X)
    (κ ref : Measure (C × X)) : EReal :=
  (-(β * scoreIntegral κ B) : ℝ) + (γ : EReal) * (kernelKL κ ref : EReal)

theorem kernelObjectiveEReal_eq_top_of_not_ac
    {β γ : ℝ} (hγ : 0 < γ) (B : BoundedKernelScore C X)
    {κ ref : Measure (C × X)} (hκref : ¬ κ ≪ ref) :
    kernelObjectiveEReal β γ B κ ref = ⊤ := by
  unfold kernelObjectiveEReal
  rw [kernelKL_eq_top_of_not_ac hκref, EReal.coe_ennreal_top,
    EReal.mul_top_of_pos (EReal.coe_pos.mpr hγ),
    EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]

/-- The real exponent used in the compact Gibbs density. -/
def scaledScore (β γ : ℝ) (B : BoundedKernelScore C X) :
    C × X → ℝ :=
  fun z => (β / γ) * B.prodFun z

theorem scaledScore_apply
    (β γ : ℝ) (B : BoundedKernelScore C X) (z : C × X) :
    scaledScore β γ B z = (β / γ) * B.prodFun z :=
  rfl

theorem scaledScore_measurable
    (β γ : ℝ) (B : BoundedKernelScore C X) :
    Measurable (scaledScore β γ B) :=
  B.measurable_prodFun.const_mul (β / γ)

theorem scaledScore_integrable
    (κ : Measure (C × X)) [IsFiniteMeasure κ]
    (β γ : ℝ) (B : BoundedKernelScore C X) :
    Integrable (scaledScore β γ B) κ := by
  refine Integrable.of_bound
    (scaledScore_measurable β γ B).aestronglyMeasurable
    (|β / γ| * B.absBound) ?_
  refine ae_of_all κ fun z => ?_
  calc
    ‖scaledScore β γ B z‖ = ‖β / γ‖ * ‖B.prodFun z‖ := by
      rw [scaledScore_apply, norm_mul]
    _ = |β / γ| * ‖B.prodFun z‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ |β / γ| * B.absBound :=
      mul_le_mul_of_nonneg_left (B.norm_prodFun_le_absBound z) (abs_nonneg _)

theorem integral_scaledScore
    (κ : Measure (C × X)) [IsFiniteMeasure κ]
    (β γ : ℝ) (B : BoundedKernelScore C X) :
    ∫ z, scaledScore β γ B z ∂κ = (β / γ) * scoreIntegral κ B := by
  simp [scaledScore, scoreIntegral, integral_const_mul]

theorem exp_scaledScore_integrable
    (κ : Measure (C × X)) [IsFiniteMeasure κ]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    Integrable (fun z => Real.exp (scaledScore β γ B z)) κ := by
  refine Integrable.of_bound
    ((Real.measurable_exp.comp (scaledScore_measurable β γ B)).aestronglyMeasurable)
    (Real.exp ((β / γ) * B.upper)) ?_
  refine ae_of_all κ fun z => ?_
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (B.prodFun_le_upper z)
      (div_nonneg hβ hγ.le))

/-- The unnormalized Gibbs weight `exp((β/γ) * B(c,a))`. -/
def gibbsWeight (β γ : ℝ) (B : BoundedKernelScore C X) :
    C × X → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (Real.exp (scaledScore β γ B z))

theorem gibbsWeight_measurable
    (β γ : ℝ) (B : BoundedKernelScore C X) :
    Measurable (gibbsWeight β γ B) := by
  unfold gibbsWeight
  exact (Real.measurable_exp.comp (scaledScore_measurable β γ B)).ennreal_ofReal

theorem gibbsWeight_ne_zero
    (β γ : ℝ) (B : BoundedKernelScore C X) (z : C × X) :
    gibbsWeight β γ B z ≠ 0 := by
  unfold gibbsWeight
  exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)

theorem gibbsWeight_ne_top
    (β γ : ℝ) (B : BoundedKernelScore C X) (z : C × X) :
    gibbsWeight β γ B z ≠ ∞ := by
  unfold gibbsWeight
  exact ENNReal.ofReal_ne_top

theorem gibbsWeight_lower_bound
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) (z : C × X) :
    ENNReal.ofReal (Real.exp ((β / γ) * B.lower)) ≤
      gibbsWeight β γ B z := by
  unfold gibbsWeight
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (B.lower_le_prodFun z)
      (div_nonneg hβ hγ.le))

theorem gibbsWeight_upper_bound
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) (z : C × X) :
    gibbsWeight β γ B z ≤
      ENNReal.ofReal (Real.exp ((β / γ) * B.upper)) := by
  unfold gibbsWeight
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (B.prodFun_le_upper z)
      (div_nonneg hβ hγ.le))

/-- Partition function of the compact kernel Gibbs density. -/
def partition (ref : Measure (C × X)) (β γ : ℝ)
    (B : BoundedKernelScore C X) : ℝ≥0∞ :=
  ∫⁻ z, gibbsWeight β γ B z ∂ref

theorem partition_lower_bound
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    ENNReal.ofReal (Real.exp ((β / γ) * B.lower)) ≤
      partition ref β γ B := by
  have hmono :
      (∫⁻ _ : C × X, ENNReal.ofReal (Real.exp ((β / γ) * B.lower)) ∂ref) ≤
        partition ref β γ B := by
    exact lintegral_mono fun z => gibbsWeight_lower_bound hβ hγ B z
  simpa [partition, lintegral_const, measure_univ, one_mul] using hmono

theorem partition_upper_bound
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    partition ref β γ B ≤
      ENNReal.ofReal (Real.exp ((β / γ) * B.upper)) := by
  have hmono :
      partition ref β γ B ≤
        ∫⁻ _ : C × X, ENNReal.ofReal (Real.exp ((β / γ) * B.upper)) ∂ref := by
    exact lintegral_mono fun z => gibbsWeight_upper_bound hβ hγ B z
  simpa [partition, lintegral_const, measure_univ, one_mul] using hmono

theorem partition_ne_zero
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    partition ref β γ B ≠ 0 := by
  intro hzero
  have hpos_real : (0 : ℝ) < Real.exp ((β / γ) * B.lower) := Real.exp_pos _
  have hpos_enn :
      (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp ((β / γ) * B.lower)) := by
    exact ENNReal.ofReal_pos.mpr hpos_real
  have hle := partition_lower_bound ref hβ hγ B
  rw [hzero] at hle
  exact not_lt_of_ge hle hpos_enn

theorem partition_ne_top
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    partition ref β γ B ≠ ∞ := by
  have hle := partition_upper_bound ref hβ hγ B
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

theorem partition_eq_ofReal_integral_exp
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    partition ref β γ B =
      ENNReal.ofReal (∫ z, Real.exp (scaledScore β γ B z) ∂ref) := by
  rw [partition]
  change (∫⁻ z, ENNReal.ofReal (Real.exp (scaledScore β γ B z)) ∂ref) =
    ENNReal.ofReal (∫ z, Real.exp (scaledScore β γ B z) ∂ref)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (exp_scaledScore_integrable ref hβ hγ B)
    (ae_of_all ref fun z => (Real.exp_pos (scaledScore β γ B z)).le)]

theorem partition_toReal_eq_integral_exp
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    (partition ref β γ B).toReal =
      ∫ z, Real.exp (scaledScore β γ B z) ∂ref := by
  rw [partition_eq_ofReal_integral_exp ref hβ hγ B]
  exact ENNReal.toReal_ofReal
    (integral_nonneg fun z => (Real.exp_pos (scaledScore β γ B z)).le)

theorem integral_exp_scaledScore_pos
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    0 < ∫ z, Real.exp (scaledScore β γ B z) ∂ref :=
  integral_exp_pos (exp_scaledScore_integrable ref hβ hγ B)

/-- Normalized Gibbs density with respect to the product reference. -/
def gibbsDensity (ref : Measure (C × X)) (β γ : ℝ)
    (B : BoundedKernelScore C X) : C × X → ℝ≥0∞ :=
  fun z => gibbsWeight β γ B z * (partition ref β γ B)⁻¹

theorem gibbsDensity_measurable
    (ref : Measure (C × X)) (β γ : ℝ)
    (B : BoundedKernelScore C X) :
    Measurable (gibbsDensity ref β γ B) := by
  unfold gibbsDensity
  exact (gibbsWeight_measurable β γ B).mul measurable_const

/-- The normalized Gibbs law induced by the bounded score and reference law. -/
def gibbsMeasure (ref : Measure (C × X)) (β γ : ℝ)
    (B : BoundedKernelScore C X) : Measure (C × X) :=
  ref.withDensity (gibbsDensity ref β γ B)

theorem gibbsMeasure_absolutelyContinuous
    (ref : Measure (C × X)) (β γ : ℝ)
    (B : BoundedKernelScore C X) :
    gibbsMeasure ref β γ B ≪ ref := by
  exact withDensity_absolutelyContinuous ref (gibbsDensity ref β γ B)

theorem gibbsMeasure_univ
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    gibbsMeasure ref β γ B univ = 1 := by
  have hmeas : Measurable (gibbsWeight β γ B) :=
    gibbsWeight_measurable β γ B
  calc
    gibbsMeasure ref β γ B univ
        = ∫⁻ z, gibbsDensity ref β γ B z ∂ref := by
          simp [gibbsMeasure, withDensity_apply]
    _ = ∫⁻ z, gibbsWeight β γ B z * (partition ref β γ B)⁻¹ ∂ref := by
          rfl
    _ = partition ref β γ B * (partition ref β γ B)⁻¹ := by
          rw [lintegral_mul_const _ hmeas]
          rfl
    _ = 1 := ENNReal.mul_inv_cancel
          (partition_ne_zero ref hβ hγ B)
          (partition_ne_top ref hβ hγ B)

theorem gibbsMeasure_isProbabilityMeasure
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    IsProbabilityMeasure (gibbsMeasure ref β γ B) :=
  ⟨gibbsMeasure_univ ref hβ hγ B⟩

theorem partition_upper_bound_unit_interval
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hB_le_one : ∀ z : C × X, B.prodFun z ≤ 1) :
    partition ref β γ B ≤ ENNReal.ofReal (Real.exp (β / γ)) := by
  have hmono :
      partition ref β γ B ≤
        ∫⁻ _ : C × X, ENNReal.ofReal (Real.exp (β / γ)) ∂ref := by
    unfold partition
    refine lintegral_mono fun z => ?_
    unfold gibbsWeight scaledScore
    refine ENNReal.ofReal_le_ofReal ?_
    exact Real.exp_le_exp.mpr
      (by
        have hscale_nonneg : 0 ≤ β / γ := div_nonneg hβ hγ.le
        exact mul_le_of_le_one_right hscale_nonneg (hB_le_one z))
  simpa [lintegral_const, measure_univ, one_mul] using hmono

theorem one_le_gibbsWeight_of_nonnegative
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hB_nonneg : ∀ z : C × X, 0 ≤ B.prodFun z)
    (z : C × X) :
    1 ≤ gibbsWeight β γ B z := by
  unfold gibbsWeight scaledScore
  have hReal :
      (1 : ℝ) ≤ Real.exp (β / γ * B.prodFun z) := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (β / γ * B.prodFun z) := by
        refine Real.exp_le_exp.mpr ?_
        have hscale_nonneg : 0 ≤ β / γ := div_nonneg hβ hγ.le
        exact mul_nonneg hscale_nonneg (hB_nonneg z)
  simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hReal

theorem gibbsDensity_unit_interval_floor
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hB_nonneg : ∀ z : C × X, 0 ≤ B.prodFun z)
    (hB_le_one : ∀ z : C × X, B.prodFun z ≤ 1)
    (z : C × X) :
    ENNReal.ofReal (Real.exp (-(β / γ))) ≤ gibbsDensity ref β γ B z := by
  have hExpPos : 0 < Real.exp (β / γ) := Real.exp_pos _
  have hInv :
      ENNReal.ofReal (Real.exp (-(β / γ))) ≤ (partition ref β γ B)⁻¹ := by
    rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos hExpPos, ENNReal.inv_le_inv]
    exact partition_upper_bound_unit_interval ref hβ hγ B hB_le_one
  have hWeight : 1 ≤ gibbsWeight β γ B z :=
    one_le_gibbsWeight_of_nonnegative hβ hγ B hB_nonneg z
  calc
    ENNReal.ofReal (Real.exp (-(β / γ)))
        ≤ 1 * (partition ref β γ B)⁻¹ := by simpa using hInv
    _ ≤ gibbsWeight β γ B z * (partition ref β γ B)⁻¹ :=
        mul_le_mul_left hWeight _
    _ = gibbsDensity ref β γ B z := rfl

theorem gibbsMeasure_reference_mass_floor
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hB_nonneg : ∀ z : C × X, 0 ≤ B.prodFun z)
    (hB_le_one : ∀ z : C × X, B.prodFun z ≤ 1)
    {s : Set (C × X)} (hs : MeasurableSet s) :
    ENNReal.ofReal (Real.exp (-(β / γ))) * ref s ≤
      gibbsMeasure ref β γ B s := by
  calc
    ENNReal.ofReal (Real.exp (-(β / γ))) * ref s
        = ∫⁻ _ : C × X in s, ENNReal.ofReal (Real.exp (-(β / γ))) ∂ref := by
          simp [lintegral_const]
    _ ≤ ∫⁻ z : C × X in s, gibbsDensity ref β γ B z ∂ref := by
          exact lintegral_mono fun z =>
            gibbsDensity_unit_interval_floor ref hβ hγ B hB_nonneg hB_le_one z
    _ = gibbsMeasure ref β γ B s := by
          rw [gibbsMeasure, withDensity_apply _ hs]

theorem gibbsMeasure_product_mass_floor
    (classRef : Measure C) (actionRef : Measure X)
    [IsProbabilityMeasure classRef] [IsProbabilityMeasure actionRef]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hB_nonneg : ∀ z : C × X, 0 ≤ B.prodFun z)
    (hB_le_one : ∀ z : C × X, B.prodFun z ≤ 1)
    {classSet : Set C} {actionSet : Set X}
    (hclass : MeasurableSet classSet) (haction : MeasurableSet actionSet) :
    ENNReal.ofReal (Real.exp (-(β / γ))) *
        (classRef classSet * actionRef actionSet) ≤
      gibbsMeasure (referenceMeasure classRef actionRef) β γ B
        (classSet ×ˢ actionSet) := by
  have hFloor :=
    gibbsMeasure_reference_mass_floor
      (referenceMeasure classRef actionRef) hβ hγ B hB_nonneg hB_le_one
      (hclass.prod haction)
  simpa [referenceMeasure, Measure.prod_prod] using hFloor

theorem gibbsMeasure_eq_tilted
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    gibbsMeasure ref β γ B = ref.tilted (scaledScore β γ B) := by
  rw [gibbsMeasure, Measure.tilted]
  refine withDensity_congr_ae ?_
  refine ae_of_all ref fun z => ?_
  have hIntPos := integral_exp_scaledScore_pos ref hβ hγ B
  rw [gibbsDensity, gibbsWeight, partition_eq_ofReal_integral_exp ref hβ hγ B]
  symm
  change ENNReal.ofReal
      (Real.exp (scaledScore β γ B z) /
        ∫ x, Real.exp (scaledScore β γ B x) ∂ref) =
    ENNReal.ofReal (Real.exp (scaledScore β γ B z)) *
      (ENNReal.ofReal (∫ x, Real.exp (scaledScore β γ B x) ∂ref))⁻¹
  rw [ENNReal.ofReal_div_of_pos hIntPos, div_eq_mul_inv]

theorem reference_absolutelyContinuous_gibbsMeasure
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    ref ≪ gibbsMeasure ref β γ B := by
  rw [gibbsMeasure_eq_tilted ref hβ hγ B]
  exact absolutelyContinuous_tilted (exp_scaledScore_integrable ref hβ hγ B)

theorem not_absolutelyContinuous_gibbsMeasure_of_not_absolutelyContinuous_reference
    (ref : Measure (C × X)) {κ : Measure (C × X)}
    {β γ : ℝ} (B : BoundedKernelScore C X)
    (hκref : ¬ κ ≪ ref) :
    ¬ κ ≪ gibbsMeasure ref β γ B := by
  intro hκgibbs
  exact hκref (hκgibbs.trans (gibbsMeasure_absolutelyContinuous ref β γ B))

theorem kernelKL_gibbs_eq_top_of_not_ac_reference
    (ref : Measure (C × X)) {κ : Measure (C × X)}
    {β γ : ℝ} (B : BoundedKernelScore C X)
    (hκref : ¬ κ ≪ ref) :
    kernelKL κ (gibbsMeasure ref β γ B) = ∞ :=
  kernelKL_eq_top_of_not_ac
    (not_absolutelyContinuous_gibbsMeasure_of_not_absolutelyContinuous_reference
      ref B hκref)

theorem llr_gibbs_integrable_of_reference
    (κ ref : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hκref : κ ≪ ref)
    (hllr : Integrable (llr κ ref) κ) :
    Integrable (llr κ (gibbsMeasure ref β γ B)) κ := by
  rw [gibbsMeasure_eq_tilted ref hβ hγ B]
  exact integrable_llr_tilted_right
    (μ := κ) (ν := ref) (f := scaledScore β γ B)
    hκref
    (scaledScore_integrable κ β γ B)
    hllr
    (exp_scaledScore_integrable ref hβ hγ B)

theorem kernelKL_gibbs_ne_top_of_reference
    (κ ref : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hκref : κ ≪ ref)
    (hllr : Integrable (llr κ ref) κ) :
    kernelKL κ (gibbsMeasure ref β γ B) ≠ ∞ := by
  rw [kernelKL_ne_top_iff]
  exact ⟨hκref.trans (reference_absolutelyContinuous_gibbsMeasure ref hβ hγ B),
    llr_gibbs_integrable_of_reference κ ref hβ hγ B hκref hllr⟩

theorem gibbs_llr_reference_integrable
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    Integrable (llr (gibbsMeasure ref β γ B) ref)
      (gibbsMeasure ref β γ B) := by
  let f : C × X → ℝ := scaledScore β γ B
  have hf_exp : Integrable (fun z => Real.exp (f z)) ref :=
    exp_scaledScore_integrable ref hβ hγ B
  have hf : Integrable f (ref.tilted f) := by
    letI : IsProbabilityMeasure (ref.tilted f) :=
      isProbabilityMeasure_tilted hf_exp
    exact scaledScore_integrable (ref.tilted f) β γ B
  have hbase_llr : Integrable (llr ref ref) ref := by
    rw [integrable_congr (llr_self ref)]
    exact integrable_zero _ _ ref
  have hEqRef :
      llr (ref.tilted f) ref =ᵐ[ref]
        fun z => f z - Real.log (∫ y, Real.exp (f y) ∂ref) := by
    have htilt :
        llr (ref.tilted f) ref =ᵐ[ref]
          fun z => f z - Real.log (∫ y, Real.exp (f y) ∂ref) + llr ref ref z :=
      llr_tilted_left
        (μ := ref) (ν := ref) (f := f)
        (Measure.AbsolutelyContinuous.rfl)
        hf_exp
        (scaledScore_measurable β γ B).aemeasurable
    have hself : llr ref ref =ᵐ[ref] 0 := llr_self ref
    filter_upwards [htilt, hself] with z hz hzero
    rw [hz, hzero]
    simp
  have hEqTilted :
      llr (ref.tilted f) ref =ᵐ[ref.tilted f]
        fun z => f z - Real.log (∫ y, Real.exp (f y) ∂ref) :=
    (tilted_absolutelyContinuous ref f).ae_le hEqRef
  rw [gibbsMeasure_eq_tilted ref hβ hγ B]
  rw [integrable_congr hEqTilted]
  exact hf.sub (integrable_const _)

theorem gibbs_kernelKL_reference_ne_top
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    kernelKL (gibbsMeasure ref β γ B) ref ≠ ∞ := by
  rw [kernelKL_ne_top_iff]
  exact ⟨gibbsMeasure_absolutelyContinuous ref β γ B,
    gibbs_llr_reference_integrable ref hβ hγ B⟩

theorem kernelKL_toReal_eq_integral_llr_of_probability
    (κ ν : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ν]
    (hκν : κ ≪ ν) :
    (kernelKL κ ν).toReal = ∫ z, llr κ ν z ∂κ := by
  have hMass : κ univ = ν univ := by simp
  simpa [kernelKL] using
    (toReal_klDiv_of_measure_eq (μ := κ) (ν := ν) hκν hMass)

/--
Finite-KL Gibbs decomposition for the compact kernel:
`KL(κ || κ_G) = KL(κ || ref) - (β/γ) Eκ[B] + log Z`.
-/
theorem kernelKL_gibbs_toReal_decomposition
    (κ ref : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hκref : κ ≪ ref)
    (hllr : Integrable (llr κ ref) κ) :
    (kernelKL κ (gibbsMeasure ref β γ B)).toReal =
      (kernelKL κ ref).toReal - (β / γ) * scoreIntegral κ B +
        Real.log (partition ref β γ B).toReal := by
  letI : IsProbabilityMeasure (gibbsMeasure ref β γ B) :=
    gibbsMeasure_isProbabilityMeasure ref hβ hγ B
  have hκgibbs : κ ≪ gibbsMeasure ref β γ B :=
    hκref.trans (reference_absolutelyContinuous_gibbsMeasure ref hβ hγ B)
  have hTilted :
      ∫ z, llr κ (ref.tilted (scaledScore β γ B)) z ∂κ =
        ∫ z, llr κ ref z ∂κ -
          ∫ z, scaledScore β γ B z ∂κ +
            Real.log (∫ z, Real.exp (scaledScore β γ B z) ∂ref) :=
    integral_llr_tilted_right
      (μ := κ) (ν := ref) (f := scaledScore β γ B)
      hκref
      (scaledScore_integrable κ β γ B)
      (exp_scaledScore_integrable ref hβ hγ B)
      hllr
  calc
    (kernelKL κ (gibbsMeasure ref β γ B)).toReal
        = ∫ z, llr κ (gibbsMeasure ref β γ B) z ∂κ :=
          kernelKL_toReal_eq_integral_llr_of_probability κ
            (gibbsMeasure ref β γ B) hκgibbs
    _ = ∫ z, llr κ (ref.tilted (scaledScore β γ B)) z ∂κ := by
          rw [gibbsMeasure_eq_tilted ref hβ hγ B]
    _ = ∫ z, llr κ ref z ∂κ -
          ∫ z, scaledScore β γ B z ∂κ +
            Real.log (∫ z, Real.exp (scaledScore β γ B z) ∂ref) :=
          hTilted
    _ = (kernelKL κ ref).toReal - (β / γ) * scoreIntegral κ B +
          Real.log (partition ref β γ B).toReal := by
          rw [kernelKL_toReal_eq_integral_llr_of_probability κ ref hκref,
            integral_scaledScore κ β γ B,
            partition_toReal_eq_integral_exp ref hβ hγ B]

/--
Finite-KL variational identity for the compact kernel objective:
`-β Eκ[B] + γ KL(κ||ref) = -γ log Z + γ KL(κ||κ_G)`.
-/
theorem kernelObjectiveReal_decomposition
    (κ ref : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hκref : κ ≪ ref)
    (hllr : Integrable (llr κ ref) κ) :
    kernelObjectiveReal β γ B κ ref =
      -γ * Real.log (partition ref β γ B).toReal +
        γ * (kernelKL κ (gibbsMeasure ref β γ B)).toReal := by
  have hKL :=
    kernelKL_gibbs_toReal_decomposition κ ref hβ hγ B hκref hllr
  unfold kernelObjectiveReal
  rw [hKL]
  field_simp [hγ.ne']
  ring

theorem kernelObjectiveReal_gibbs_value
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    kernelObjectiveReal β γ B (gibbsMeasure ref β γ B) ref =
      -γ * Real.log (partition ref β γ B).toReal := by
  letI : IsProbabilityMeasure (gibbsMeasure ref β γ B) :=
    gibbsMeasure_isProbabilityMeasure ref hβ hγ B
  have hDecomp :=
    kernelObjectiveReal_decomposition
      (gibbsMeasure ref β γ B) ref hβ hγ B
      (gibbsMeasure_absolutelyContinuous ref β γ B)
      (gibbs_llr_reference_integrable ref hβ hγ B)
  simpa [kernelKL, klDiv_self] using hDecomp

theorem kernelObjectiveReal_gibbs_gap
    (κ ref : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hκref : κ ≪ ref)
    (hllr : Integrable (llr κ ref) κ) :
    kernelObjectiveReal β γ B κ ref -
        kernelObjectiveReal β γ B (gibbsMeasure ref β γ B) ref =
      γ * (kernelKL κ (gibbsMeasure ref β γ B)).toReal := by
  rw [kernelObjectiveReal_decomposition κ ref hβ hγ B hκref hllr,
    kernelObjectiveReal_gibbs_value ref hβ hγ B]
  ring

theorem kernelObjectiveReal_gibbs_le
    (κ ref : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hκref : κ ≪ ref)
    (hllr : Integrable (llr κ ref) κ) :
    kernelObjectiveReal β γ B (gibbsMeasure ref β γ B) ref ≤
      kernelObjectiveReal β γ B κ ref := by
  have hgap := kernelObjectiveReal_gibbs_gap κ ref hβ hγ B hκref hllr
  have hnonneg :
      0 ≤ γ * (kernelKL κ (gibbsMeasure ref β γ B)).toReal :=
    mul_nonneg hγ.le (kernelKL_toReal_nonneg κ (gibbsMeasure ref β γ B))
  linarith

theorem kernelObjectiveReal_eq_gibbs_iff
    (κ ref : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X)
    (hκref : κ ≪ ref)
    (hllr : Integrable (llr κ ref) κ) :
    kernelObjectiveReal β γ B κ ref =
        kernelObjectiveReal β γ B (gibbsMeasure ref β γ B) ref ↔
      κ = gibbsMeasure ref β γ B := by
  letI : IsProbabilityMeasure (gibbsMeasure ref β γ B) :=
    gibbsMeasure_isProbabilityMeasure ref hβ hγ B
  constructor
  · intro hobj
    have hgap := kernelObjectiveReal_gibbs_gap κ ref hβ hγ B hκref hllr
    have hzero_real :
        (kernelKL κ (gibbsMeasure ref β γ B)).toReal = 0 := by
      have hmul_zero :
          γ * (kernelKL κ (gibbsMeasure ref β γ B)).toReal = 0 := by
        linarith
      exact (mul_eq_zero.mp hmul_zero).resolve_left hγ.ne'
    exact
      (kernelKL_toReal_eq_zero_iff_eq_of_ne_top κ
        (gibbsMeasure ref β γ B)
        (kernelKL_gibbs_ne_top_of_reference κ ref hβ hγ B hκref hllr)).mp
        hzero_real
  · intro hκ
    rw [hκ]

theorem kernelObjectiveReal_gibbs_unique_minimizer
    (ref : Measure (C × X)) [IsProbabilityMeasure ref]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : BoundedKernelScore C X) :
    (∀ (κ : Measure (C × X)) [IsProbabilityMeasure κ],
        κ ≪ ref → Integrable (llr κ ref) κ →
          kernelObjectiveReal β γ B (gibbsMeasure ref β γ B) ref ≤
            kernelObjectiveReal β γ B κ ref) ∧
      (∀ (κ : Measure (C × X)) [IsProbabilityMeasure κ],
        κ ≪ ref → Integrable (llr κ ref) κ →
          (kernelObjectiveReal β γ B κ ref =
              kernelObjectiveReal β γ B (gibbsMeasure ref β γ B) ref ↔
            κ = gibbsMeasure ref β γ B)) := by
  exact ⟨fun κ _ hκref hllr =>
      kernelObjectiveReal_gibbs_le κ ref hβ hγ B hκref hllr,
    fun κ _ hκref hllr =>
      kernelObjectiveReal_eq_gibbs_iff κ ref hβ hγ B hκref hllr⟩

/-- The exact compact-kernel data package used by later paper-facing phases. -/
structure Setup
    (C : Type u) (X : Type v)
    [MeasurableSpace C] [TopologicalSpace X] [MeasurableSpace X] where
  classRef : Measure C
  actionRef : Measure X
  class_isProbability : IsProbabilityMeasure classRef
  action_isProbability : IsProbabilityMeasure actionRef
  action_fullSupport : HasFullSupport actionRef

namespace Setup

variable {C : Type u} {X : Type v} [MeasurableSpace C] [MeasurableSpace X]

/-- Product reference measure attached to a compact-kernel setup. -/
def reference [TopologicalSpace X] (S : Setup C X) : Measure (C × X) :=
  referenceMeasure S.classRef S.actionRef

theorem reference_eq_referenceMeasure
    [TopologicalSpace X] (S : Setup C X) :
    S.reference = referenceMeasure S.classRef S.actionRef :=
  rfl

theorem reference_isProbability
    [TopologicalSpace X]
    (S : Setup C X) :
    IsProbabilityMeasure S.reference := by
  letI : IsProbabilityMeasure S.classRef := S.class_isProbability
  letI : IsProbabilityMeasure S.actionRef := S.action_isProbability
  dsimp [reference]
  infer_instance

theorem reference_univ
    [TopologicalSpace X]
    (S : Setup C X) :
    S.reference univ = 1 := by
  letI : IsProbabilityMeasure S.reference := S.reference_isProbability
  exact measure_univ

theorem action_ball_ne_zero
    [PseudoMetricSpace X] (S : Setup C X)
    (x : X) {ε : ℝ} (hε : 0 < ε) :
    S.actionRef (Metric.ball x ε) ≠ 0 :=
  S.action_fullSupport.ball_ne_zero x hε

end Setup

end CompactKernel

end

end SemanticConvergence
