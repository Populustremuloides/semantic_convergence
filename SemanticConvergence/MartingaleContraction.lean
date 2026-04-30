import Mathlib
import Mathlib.Probability.Martingale.Convergence

namespace SemanticConvergence

universe u

noncomputable section

open Filter MeasureTheory
open scoped Topology MeasureTheory NNReal ENNReal

/--
Analytic spine of the paper's martingale contraction lemma.

If the residual odds `Rₙ` are nonnegative, the exponential envelope
`Mₙ = exp(Sₙ) * sqrt(Rₙ)` converges to a finite real value, and cumulative
separation `Sₙ` diverges, then the residual odds converge to zero. This is the
deterministic pointwise part of the martingale proof after the nonnegative
martingale convergence theorem has supplied convergence of `Mₙ`.
-/
theorem residualOdds_tendsto_zero_of_exponential_martingale_spine
    {R M S : Nat → ℝ}
    (hR_nonneg : ∀ n, 0 ≤ R n)
    {m : ℝ}
    (hM : Tendsto M atTop (nhds m))
    (hS : Tendsto S atTop atTop)
    (hIdentity : ∀ n, Real.sqrt (R n) = M n * Real.exp (-(S n))) :
    Tendsto R atTop (nhds 0) := by
  have hNegS : Tendsto (fun n => -S n) atTop atBot := by
    exact (Filter.tendsto_neg_atBot_iff).2 hS
  have hExp : Tendsto (fun n => Real.exp (-(S n))) atTop (nhds 0) := by
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hNegS
  have hSqrt : Tendsto (fun n => Real.sqrt (R n)) atTop (nhds 0) := by
    have hProd := hM.mul hExp
    simpa [hIdentity] using hProd
  have hSq :
      Tendsto (fun n => (Real.sqrt (R n)) ^ 2) atTop (nhds (0 ^ 2 : ℝ)) :=
    hSqrt.pow 2
  have hSqrtSq : (fun n => (Real.sqrt (R n)) ^ 2) = R := by
    funext n
    exact Real.sq_sqrt (hR_nonneg n)
  simpa [hSqrtSq] using hSq

/-- Residual odds converging to zero imply the corresponding posterior share tends to one. -/
theorem posteriorShare_tendsto_one_of_residualOdds_tendsto_zero
    {R : Nat → ℝ}
    (hR : Tendsto R atTop (nhds 0)) :
    Tendsto (fun n => (1 + R n)⁻¹) atTop (nhds 1) := by
  have hAdd : Tendsto (fun n => (1 : ℝ) + R n) atTop (nhds (1 + 0 : ℝ)) :=
    hR.const_add 1
  have hInv := hAdd.inv₀ (by norm_num : (1 + 0 : ℝ) ≠ 0)
  simpa using hInv

/--
Posterior-share form of the martingale contraction spine: if
`sqrt(Rₙ) = Mₙ exp(-Sₙ)`, `Mₙ` converges, and `Sₙ → ∞`, then
`1 / (1 + Rₙ) → 1`.
-/
theorem posteriorShare_tendsto_one_of_exponential_martingale_spine
    {R M S : Nat → ℝ}
    (hR_nonneg : ∀ n, 0 ≤ R n)
    {m : ℝ}
    (hM : Tendsto M atTop (nhds m))
    (hS : Tendsto S atTop atTop)
    (hIdentity : ∀ n, Real.sqrt (R n) = M n * Real.exp (-(S n))) :
    Tendsto (fun n => (1 + R n)⁻¹) atTop (nhds 1) :=
  posteriorShare_tendsto_one_of_residualOdds_tendsto_zero
    (residualOdds_tendsto_zero_of_exponential_martingale_spine
      hR_nonneg hM hS hIdentity)

/--
Almost-sure form of the deterministic martingale spine.

This packages the pointwise argument under `∀ᵐ`: once the envelope convergence,
cumulative-separation divergence, and exponential identity hold almost surely, the
posterior-share transform tends to one almost surely.
-/
theorem ae_posteriorShare_tendsto_one_of_exponential_martingale_spine
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {R M S : Nat → Ω → ℝ}
    (hR_nonneg : ∀ᵐ ξ ∂μ, ∀ n, 0 ≤ R n ξ)
    (hM : ∀ᵐ ξ ∂μ, ∃ m : ℝ, Tendsto (fun n => M n ξ) atTop (nhds m))
    (hS : ∀ᵐ ξ ∂μ, Tendsto (fun n => S n ξ) atTop atTop)
    (hIdentity : ∀ᵐ ξ ∂μ,
      ∀ n, Real.sqrt (R n ξ) = M n ξ * Real.exp (-(S n ξ))) :
    ∀ᵐ ξ ∂μ, Tendsto (fun n => (1 + R n ξ)⁻¹) atTop (nhds 1) := by
  filter_upwards [hR_nonneg, hM, hS, hIdentity] with ξ hR hMξ hSξ hId
  rcases hMξ with ⟨m, hMξ⟩
  exact posteriorShare_tendsto_one_of_exponential_martingale_spine
    (R := fun n => R n ξ) (M := fun n => M n ξ) (S := fun n => S n ξ)
    hR (m := m) hMξ hSξ hId

/--
Martingale-convergence form of the contraction spine.

Mathlib supplies almost-sure convergence of an L¹-bounded submartingale. Since every
martingale is a submartingale, an L¹-bounded exponential envelope `M` converges almost
surely; the deterministic exponential-spine theorem then turns divergence of `S` into
posterior-share convergence.
-/
theorem ae_posteriorShare_tendsto_one_of_martingale_exponential_spine
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat mΩ}
    {R M S : Nat → Ω → ℝ} {C : ℝ≥0}
    (hR_nonneg : ∀ᵐ ξ ∂μ, ∀ n, 0 ≤ R n ξ)
    (hM_martingale : Martingale M ℱ μ)
    (hM_bdd : ∀ n, eLpNorm (M n) 1 μ ≤ (C : ℝ≥0∞))
    (hS : ∀ᵐ ξ ∂μ, Tendsto (fun n => S n ξ) atTop atTop)
    (hIdentity : ∀ᵐ ξ ∂μ,
      ∀ n, Real.sqrt (R n ξ) = M n ξ * Real.exp (-(S n ξ))) :
    ∀ᵐ ξ ∂μ, Tendsto (fun n => (1 + R n ξ)⁻¹) atTop (nhds 1) := by
  have hMconv :
      ∀ᵐ ξ ∂μ, Tendsto (fun n => M n ξ) atTop (nhds (ℱ.limitProcess M μ ξ)) :=
    hM_martingale.submartingale.ae_tendsto_limitProcess hM_bdd
  exact ae_posteriorShare_tendsto_one_of_exponential_martingale_spine
    hR_nonneg
    (hM := by
      filter_upwards [hMconv] with ξ hξ
      exact ⟨ℱ.limitProcess M μ ξ, hξ⟩)
    hS hIdentity

/--
Named package for the soft Hellinger/Bhattacharyya convergence route.

This is the manuscript's Section 6 contraction spine as a Lean interface: residual odds
are nonnegative, the exponential envelope is an L¹-bounded martingale, cumulative
separation diverges, and the square-root Bayes update identity identifies residual odds
with the envelope times `exp(-Sₙ)`.
-/
structure HellingerConvergenceSpine
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration Nat mΩ)
    (R M S : Nat → Ω → ℝ) (C : ℝ≥0) : Prop where
  residual_nonneg : ∀ᵐ ξ ∂μ, ∀ n, 0 ≤ R n ξ
  envelope_martingale : Martingale M ℱ μ
  envelope_l1_bounded : ∀ n, eLpNorm (M n) 1 μ ≤ (C : ℝ≥0∞)
  cumulative_separation_diverges : ∀ᵐ ξ ∂μ, Tendsto (fun n => S n ξ) atTop atTop
  sqrt_residual_identity :
    ∀ᵐ ξ ∂μ, ∀ n, Real.sqrt (R n ξ) = M n ξ * Real.exp (-(S n ξ))

/-- Cumulative realized separation process `Sₙ = ∑_{i<n} Bᵢ`. -/
def cumulativeSeparationProcess
    {Ω : Type u} (B : Nat → Ω → ℝ) : Nat → Ω → ℝ :=
  fun n ξ => ∑ i ∈ Finset.range n, B i ξ

/--
A uniform one-step separation floor gives a linear lower bound on the cumulative
separation process.
-/
theorem cumulativeSeparationProcess_ge_linear_of_step_lower_bound
    {Ω : Type u} (B : Nat → Ω → ℝ) {κ : ℝ} (n : Nat) (ξ : Ω)
    (hStep : ∀ i, i < n → κ ≤ B i ξ) :
    κ * (n : ℝ) ≤ cumulativeSeparationProcess B n ξ := by
  unfold cumulativeSeparationProcess
  have hsum :
      (∑ i ∈ Finset.range n, κ) ≤
        ∑ i ∈ Finset.range n, B i ξ := by
    exact Finset.sum_le_sum
      (fun i hi => hStep i (Finset.mem_range.mp hi))
  calc
    κ * (n : ℝ) = ∑ i ∈ Finset.range n, κ := by
      simp [Finset.card_range, mul_comm]
    _ ≤ ∑ i ∈ Finset.range n, B i ξ := hsum

/--
If every one-step separation along a path is bounded below by a positive
constant, the cumulative separation on that path diverges.
-/
theorem cumulativeSeparationProcess_tendsto_atTop_of_uniform_step_lower_bound
    {Ω : Type u} (B : Nat → Ω → ℝ) {κ : ℝ} (hκ : 0 < κ) (ξ : Ω)
    (hStep : ∀ i, κ ≤ B i ξ) :
    Tendsto (fun n => cumulativeSeparationProcess B n ξ) atTop atTop := by
  have hlinear :
      ∀ n : Nat, κ * (n : ℝ) ≤ cumulativeSeparationProcess B n ξ := by
    intro n
    exact cumulativeSeparationProcess_ge_linear_of_step_lower_bound
      B n ξ (fun i _hi => hStep i)
  have hNat : Tendsto (fun n : Nat => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hκTop : Tendsto (fun n : Nat => κ * (n : ℝ)) atTop atTop :=
    hNat.const_mul_atTop' hκ
  exact tendsto_atTop_mono hlinear hκTop

/--
Almost-sure divergence of cumulative separation from an almost-sure uniform
positive one-step separation floor.
-/
theorem ae_cumulativeSeparationProcess_tendsto_atTop_of_uniform_step_lower_bound
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (B : Nat → Ω → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hStep : ∀ᵐ ξ ∂μ, ∀ i, κ ≤ B i ξ) :
    ∀ᵐ ξ ∂μ, Tendsto (fun n => cumulativeSeparationProcess B n ξ) atTop atTop := by
  filter_upwards [hStep] with ξ hξ
  exact cumulativeSeparationProcess_tendsto_atTop_of_uniform_step_lower_bound
    B hκ ξ hξ

/-- Exponential Hellinger envelope `Mₙ = exp(Sₙ) * sqrt(Rₙ)`. -/
def hellingerEnvelopeProcess
    {Ω : Type u} (R S : Nat → Ω → ℝ) : Nat → Ω → ℝ :=
  fun n ξ => Real.exp (S n ξ) * Real.sqrt (R n ξ)

/-- The envelope definition gives the square-root identity used by the spine. -/
theorem hellingerEnvelopeProcess_mul_exp_neg
    {Ω : Type u} (R S : Nat → Ω → ℝ) (n : Nat) (ξ : Ω) :
    Real.sqrt (R n ξ) =
      hellingerEnvelopeProcess R S n ξ * Real.exp (-(S n ξ)) := by
  unfold hellingerEnvelopeProcess
  calc
    Real.sqrt (R n ξ) = Real.sqrt (R n ξ) * 1 := by ring
    _ =
        Real.sqrt (R n ξ) *
          (Real.exp (S n ξ) * Real.exp (-(S n ξ))) := by
          simp [← Real.exp_add]
    _ =
        Real.exp (S n ξ) * Real.sqrt (R n ξ) *
          Real.exp (-(S n ξ)) := by
          ring

/--
Constructor target for the paper's soft Hellinger route.

Once future phases prove residual nonnegativity, martingality, L¹-boundedness,
and divergence for the realized processes, this theorem assembles them into the
`HellingerConvergenceSpine`. The square-root identity is definitional from
`hellingerEnvelopeProcess`.
-/
theorem HellingerConvergenceSpine.of_processes
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat mΩ}
    {R B : Nat → Ω → ℝ} {C : ℝ≥0}
    (hR_nonneg : ∀ᵐ ξ ∂μ, ∀ n, 0 ≤ R n ξ)
    (hM_martingale :
      Martingale
        (hellingerEnvelopeProcess R (cumulativeSeparationProcess B)) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm
          (hellingerEnvelopeProcess R (cumulativeSeparationProcess B) n) 1 μ ≤
            (C : ℝ≥0∞))
    (hS_diverges :
      ∀ᵐ ξ ∂μ,
        Tendsto (fun n => cumulativeSeparationProcess B n ξ) atTop atTop) :
    HellingerConvergenceSpine μ ℱ R
      (hellingerEnvelopeProcess R (cumulativeSeparationProcess B))
      (cumulativeSeparationProcess B) C where
  residual_nonneg := hR_nonneg
  envelope_martingale := hM_martingale
  envelope_l1_bounded := hM_bdd
  cumulative_separation_diverges := hS_diverges
  sqrt_residual_identity := by
    exact Filter.Eventually.of_forall
      (fun ξ n =>
        hellingerEnvelopeProcess_mul_exp_neg
          R (cumulativeSeparationProcess B) n ξ)

/--
The named Hellinger convergence spine proves posterior-share convergence.

This is the paper-facing soft route: no exact zero-out observation is needed. The load
bearing hypotheses are the martingale envelope and the Hellinger square-root identity.
-/
theorem HellingerConvergenceSpine.posteriorShare_tendsto_one
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat mΩ}
    {R M S : Nat → Ω → ℝ} {C : ℝ≥0}
    (h : HellingerConvergenceSpine μ ℱ R M S C) :
    ∀ᵐ ξ ∂μ, Tendsto (fun n => (1 + R n ξ)⁻¹) atTop (nhds 1) :=
  ae_posteriorShare_tendsto_one_of_martingale_exponential_spine
    h.residual_nonneg h.envelope_martingale h.envelope_l1_bounded
    h.cumulative_separation_diverges h.sqrt_residual_identity

end

end SemanticConvergence
