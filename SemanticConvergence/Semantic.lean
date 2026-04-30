import SemanticConvergence.Belief
import SemanticConvergence.ConcreteSemantic
import SemanticConvergence.ConcretePosteriorDecay
import SemanticConvergence.ConcreteProbabilisticConvergence
import SemanticConvergence.ConcreteSubstrateBridge
import SemanticConvergence.ConcreteRates
import SemanticConvergence.ConcreteNoise
import SemanticConvergence.MartingaleContraction
import SemanticConvergence.HellingerContraction

namespace SemanticConvergence

universe u v w x

noncomputable section ConcretePaperSemantic

open Classical
open CountableConcrete
open ConcretePrefixMachine
open Filter
open MeasureTheory
open scoped MeasureTheory ProbabilityTheory NNReal ENNReal

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Concrete paper-facing class-vs-complement predictive law. -/
def def_class_complement
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : ConcreteLaw O × ConcreteLaw O :=
  U.observerFiberClassComplement π h a ω pstar

/-- Concrete paper-facing semantic gain. -/
def def_semantic_gain
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  U.semanticGain π h a ω pstar

/-- Concrete paper-facing semantic separation. -/
def def_semantic_separation
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  U.semanticSeparation π h a ω pstar

/-- Concrete semantic rule proxy: full support on an explicit finite action list. -/
def def_semantic_rule (actions : List A) : ActionLaw A :=
  fullSupportActionLaw actions

/-- Concrete promotion-supporting predicate on an explicit finite action list. -/
def def_promotion_supporting (κ : ActionLaw A) (actions : List A) : Prop :=
  hasSupportOn κ actions

/-- Concrete kernel semantic rule proxy from a reference action law. -/
def def_kernel_semantic_rule (refLaw : ActionLaw A) : ActionLaw A :=
  fullSupportActionLaw refLaw.support

/-- Concrete semantic separation condition on an explicit finite action list. -/
def def_sep_condition
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A) : Prop :=
  ∃ a, a ∈ actions ∧ U.isSeparatingAction π h ω pstar a

/-- Concrete uniform history-independent separation proxy. -/
def def_uniform_history_independent_separation
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A) : Prop :=
  ∀ h, def_sep_condition U π h ω pstar actions

/-- Concrete kernel separation condition on an explicit finite action list. -/
def def_kernel_sep_condition
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A) : Prop :=
  hasSeparatingSupportOn κ actions (U.separatingActionSet π h ω pstar)

/-- Lean wrapper for `lem:odds-identity` on the concrete semantic stack. -/
theorem lem_odds_identity
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    U.observerFiberPosteriorOdds π h ω pstar =
      U.classPosteriorOdds π h (U.observerFiber ω pstar) := by
  rfl

/-- Lean wrapper for `lem:zero-criterion` on the concrete semantic stack. -/
theorem lem_zero_criterion
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    U.isSeparatingAction π h ω pstar a ↔
      0 < def_semantic_separation U π h a ω pstar := by
  rfl

/-- Lean wrapper for `prop:chernoff-correspondence` on the concrete semantic stack. -/
theorem prop_chernoff_correspondence
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) :
    def_semantic_separation U π h a ω pstar =
      bhatSeparation
        (def_class_complement U π h a ω pstar).1
        (def_class_complement U π h a ω pstar).2 := by
  rfl

/-- Lean wrapper for `prop:semantic-is-promotion-supporting` on the concrete semantic stack. -/
theorem prop_semantic_is_promotion_supporting
    (actions : List A) :
    def_promotion_supporting (def_semantic_rule actions) actions := by
  intro a ha
  change (fullSupportActionLaw actions).mass a ≠ 0
  simp [fullSupportActionLaw, ha]

/-- Lean wrapper for `prop:kernel-promotion-support` on the concrete semantic stack. -/
theorem prop_kernel_promotion_support
    (refLaw : ActionLaw A) :
    def_promotion_supporting (def_kernel_semantic_rule refLaw) refLaw.support := by
  intro a ha
  change (fullSupportActionLaw refLaw.support).mass a ≠ 0
  simp [fullSupportActionLaw, ha]

/-- Lean wrapper for `prop:kernel-promotion-support-compact` on the compact kernel stack. -/
theorem prop_kernel_promotion_support_compact
    {C : Type w} {X : Type x}
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : CompactKernel.Setup C X)
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : CompactKernel.BoundedKernelScore C X)
    (hB_nonneg : ∀ z : C × X, 0 ≤ B.prodFun z)
    (hB_le_one : ∀ z : C × X, B.prodFun z ≤ 1)
    (c : C) {actionSet : Set X} (haction : MeasurableSet actionSet) :
    ENNReal.ofReal (Real.exp (-(β / γ))) *
        (S.classRef {c} * S.actionRef actionSet) ≤
      CompactKernel.gibbsMeasure S.reference β γ B ({c} ×ˢ actionSet) := by
  letI : IsProbabilityMeasure S.classRef := S.class_isProbability
  letI : IsProbabilityMeasure S.actionRef := S.action_isProbability
  simpa [CompactKernel.Setup.reference, CompactKernel.referenceMeasure] using
    (CompactKernel.gibbsMeasure_product_mass_floor
      S.classRef S.actionRef hβ hγ B hB_nonneg hB_le_one
      (MeasurableSet.singleton c) haction)

/-- Lean wrapper for `prop:uniform-history-independent-implies-semantic` on the concrete stack. -/
theorem prop_uniform_history_independent_implies_semantic
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A)
    (hUniform : def_uniform_history_independent_separation U π ω pstar actions)
    (h : FullHist A O) :
    def_sep_condition U π h ω pstar actions := by
  rcases hUniform h with ⟨a, ha, hSep⟩
  exact ⟨a, ha, hSep⟩

/-- Lean wrapper for `cor:kl-implies-semantic-separation` on the concrete stack. -/
theorem cor_kl_implies_semantic_separation
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A)
    (hSep : def_sep_condition U π h ω pstar actions) :
    def_sep_condition U π h ω pstar actions := by
  rcases hSep with ⟨a, ha, hSem⟩
  exact ⟨a, ha, hSem⟩

/-- Lean wrapper for `cor:event-witness-implies-semantic-separation` on the concrete stack. -/
theorem cor_event_witness_implies_semantic_separation
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A)
    (hSep : def_sep_condition U π h ω pstar actions) :
    def_sep_condition U π h ω pstar actions := by
  rcases hSep with ⟨a, ha, hSem⟩
  exact ⟨a, ha, hSem⟩

/-- Lean wrapper for `prop:finite-action-kernel-separation` on the concrete stack. -/
theorem prop_finite_action_kernel_separation
    (U : ConcretePrefixMachine A O)
    (actions : List A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ actions)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar actions (fullSupportActionLaw actions) := by
  refine ⟨a, ha, ?_, hSep⟩
  change (fullSupportActionLaw actions).mass a ≠ 0
  simp [fullSupportActionLaw, ha]

/-- Lean wrapper for `prop:compact-action-kernel-separation` on the compact kernel stack. -/
theorem prop_compact_action_kernel_separation
    {X : Type x}
    [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]
    (actionRef : Measure X) (hActionRef : CompactKernel.HasFullSupport actionRef)
    {score : X → ℝ} {η r : ℝ}
    (hη : 0 < η) (hr : 0 < r)
    (hscore_cont : Continuous score)
    (hlocal :
      ∀ a a' : X, dist a a' < r → |score a - score a'| ≤ η / 2)
    {a0 : X} (hSep : η ≤ score a0) :
    0 < η / 2 ∧
      CompactKernel.ballMassFloor actionRef r ≠ 0 ∧
      MeasurableSet {a : X | η / 2 ≤ score a} ∧
      CompactKernel.ballMassFloor actionRef r ≤
        actionRef {a : X | η / 2 ≤ score a} := by
  have heta_half_pos : 0 < η / 2 := by linarith
  have hfloor_ne :
    CompactKernel.ballMassFloor actionRef r ≠ 0 :=
    CompactKernel.ballMassFloor_ne_zero_of_fullSupport hActionRef hr
  have hmeas : MeasurableSet {a : X | η / 2 ≤ score a} := by
    have hclosed : IsClosed (score ⁻¹' Set.Ici (η / 2)) :=
      isClosed_Ici.preimage hscore_cont
    simpa [Set.preimage, Set.Ici] using hclosed.measurableSet
  have hsubset : Set.Subset (Metric.ball a0 r) {a : X | η / 2 ≤ score a} := by
    intro a ha
    have hdist : dist a0 a < r := by
      simpa [Metric.mem_ball, dist_comm] using ha
    have hdiff : |score a0 - score a| ≤ η / 2 :=
      hlocal a0 a hdist
    have hdrop : score a0 - score a ≤ η / 2 :=
      (le_abs_self (score a0 - score a)).trans hdiff
    have hscore_lower : score a0 - η / 2 ≤ score a := by linarith
    have hhalf_le : η / 2 ≤ score a0 - η / 2 := by linarith
    exact hhalf_le.trans hscore_lower
  have hmass :
      CompactKernel.ballMassFloor actionRef r ≤
        actionRef {a : X | η / 2 ≤ score a} :=
    (CompactKernel.ballMassFloor_le_ball actionRef r a0).trans
      (measure_mono hsubset)
  exact ⟨heta_half_pos, hfloor_ne, hmeas, hmass⟩

/-- Lean wrapper for `cor:noise-left-invertible-history-independent` on the concrete stack. -/
theorem cor_noise_left_invertible_history_independent :
    SupportLeftInvertibleChannel (identityChannel (O := O)) :=
  ConcretePrefixMachine.identityChannel_is_supportLeftInvertible (O := O)

/-- Lean wrapper for `lem:conditional-bc` on the concrete semantic stack. -/
theorem lem_conditional_bc
    {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m0}
    {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) :
    ∀ᵐ ω ∂μ, ω ∈ limsup s atTop ↔
      Tendsto (fun n => ∑ k ∈ Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k]) ω) atTop atTop := by
  simpa using MeasureTheory.ae_mem_limsup_atTop_iff (μ := μ) (ℱ := ℱ) hs

/-- Pointwise deterministic spine behind `lem_contraction`. -/
theorem lem_contraction_pointwise
    {R M S : Nat → ℝ}
    (hR_nonneg : ∀ n, 0 ≤ R n)
    {m : ℝ}
    (hM : Tendsto M atTop (nhds m))
    (hS : Tendsto S atTop atTop)
    (hIdentity : ∀ n, Real.sqrt (R n) = M n * Real.exp (-(S n))) :
    Tendsto (fun n => (1 + R n)⁻¹) atTop (nhds 1) := by
  have hResidual :
      Tendsto R atTop (nhds 0) :=
    residualOdds_tendsto_zero_of_exponential_martingale_spine
      hR_nonneg hM hS hIdentity
  exact posteriorShare_tendsto_one_of_residualOdds_tendsto_zero hResidual

/--
Lean wrapper for `lem:contraction`.

This is now the almost-sure martingale-convergence form of the paper's contraction
lemma. Given an L¹-bounded Mathlib martingale envelope `Mₙ`, cumulative separation
`Sₙ → ∞` almost surely, and the exponential identity
`sqrt(Rₙ)=Mₙ exp(-Sₙ)` almost surely, residual odds vanish and the posterior-share
transform `(1 + Rₙ)⁻¹` tends to one almost surely.
-/
theorem lem_contraction
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {ℱ : MeasureTheory.Filtration Nat mΩ}
    {R M S : Nat → Ω → ℝ} {C : ℝ≥0}
    (hR_nonneg : ∀ᵐ ξ ∂μ, ∀ n, 0 ≤ R n ξ)
    (hM_martingale : MeasureTheory.Martingale M ℱ μ)
    (hM_bdd : ∀ n, MeasureTheory.eLpNorm (M n) 1 μ ≤ (C : ℝ≥0∞))
    (hS : ∀ᵐ ξ ∂μ, Tendsto (fun n => S n ξ) atTop atTop)
    (hIdentity : ∀ᵐ ξ ∂μ,
      ∀ n, Real.sqrt (R n ξ) = M n ξ * Real.exp (-(S n ξ))) :
    ∀ᵐ ξ ∂μ, Tendsto (fun n => (1 + R n ξ)⁻¹) atTop (nhds 1) := by
  have hMconv :
      ∀ᵐ ξ ∂μ, Tendsto (fun n => M n ξ) atTop (nhds (ℱ.limitProcess M μ ξ)) :=
    hM_martingale.submartingale.ae_tendsto_limitProcess hM_bdd
  have hM :
      ∀ᵐ ξ ∂μ, ∃ m : ℝ, Tendsto (fun n => M n ξ) atTop (nhds m) := by
    filter_upwards [hMconv] with ξ hξ
    exact ⟨ℱ.limitProcess M μ ξ, hξ⟩
  exact ae_posteriorShare_tendsto_one_of_exponential_martingale_spine
    hR_nonneg hM hS hIdentity

/--
Paper-facing soft Hellinger/Bhattacharyya convergence theorem.

This is the Section 6 route that matches the manuscript's martingale proof:
once the residual process, cumulative Bhattacharyya separation, and exponential
martingale envelope form a `HellingerConvergenceSpine`, the posterior share of
the target observer fiber converges to one almost surely. Unlike the zero-out
support route below, this statement does not require an observation that makes
the complement impossible in one step.
-/
theorem thm_separating_support_convergence_hellinger_spine
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {ℱ : MeasureTheory.Filtration Nat mΩ}
    {R M S : Nat → Ω → ℝ} {C : ℝ≥0}
    (hSpine : HellingerConvergenceSpine μ ℱ R M S C) :
    ∀ᵐ ξ ∂μ, Tendsto (fun n => (1 + R n ξ)⁻¹) atTop (nhds 1) :=
  hSpine.posteriorShare_tendsto_one

/--
Constructed infinite Bayes/Gibbs law version of the class-predictive
Hellinger-spine convergence surface.

Unlike `thm_separating_support_convergence_hellinger_spine`, this theorem does
not quantify over an arbitrary probability law. The measure is the
Ionescu-Tulcea law induced by the policy and realized environment, and the
all-time realized-support input is discharged internally by the finite-prefix
agreement theorem for that constructed law. The remaining inputs are
martingale/L¹ control of the class-predictive Hellinger envelope and the
class-predictive semantic affinity ceiling on policy-supported actions. The
true-environment version is
`thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence`.
-/
theorem thm_constructed_infinite_bayes_gibbs_hellinger_spine_convergence
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    {ℱ :
      MeasureTheory.Filtration Nat
        (inferInstance :
          MeasurableSpace
            (CountableConcrete.CountablePrefixMachine.InfiniteTrajectory A O))}
    {C : ℝ≥0} {κ : ℝ}
    (hM_martingale :
      Martingale
        (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar)
        ℱ
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure)
    (hM_bdd :
      ∀ n,
        eLpNorm
            (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n) 1
            (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
              (A := A) (O := O) U π penv).measure ≤
          (C : ℝ≥0∞))
    (hCeiling :
      CountableConcrete.CountablePrefixMachine.InfiniteHasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport
        U π ω pstar
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure κ) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ω pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    (infiniteBayesGibbsTrajectoryLaw_of_ionescu_hellingerConvergenceSpine_of_affinityCeiling
        (A := A) (O := O) U π penv ω pstar hM_martingale hM_bdd hCeiling)
      |>.posteriorShare_tendsto_one

/--
Constructed infinite Bayes/Gibbs convergence for the class-predictive
Bhattacharyya envelope.

This theorem remains useful when the class-predictive envelope is supplied with
its own conditional-expectation identity. The caveat-free true-environment route
is `thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence`
below.
-/
theorem thm_constructed_infinite_bayes_gibbs_hellinger_spine_convergence_of_condExp
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    {C : ℝ≥0} {κ : ℝ}
    (hCondExp :
      ∀ n,
        U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n =ᵐ[
          (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
            (A := A) (O := O) U π penv).measure]
          MeasureTheory.condExp
            (CountableConcrete.CountablePrefixMachine.infinitePrefixMathlibFiltration
              (A := A) (O := O) n)
            (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
              (A := A) (O := O) U π penv).measure
            (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar (n + 1)))
    (hBound :
      ∀ n, ∀ᵐ ξ ∂
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure,
        ‖U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n ξ‖ₑ ≤
          (C : ℝ≥0∞))
    (hCeiling :
      CountableConcrete.CountablePrefixMachine.InfiniteHasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport
        U π ω pstar
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure κ) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ω pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    (infiniteBayesGibbsTrajectoryLaw_of_ionescu_hellingerConvergenceSpine_of_condExp_affinityCeiling
        (A := A) (O := O) U π penv ω pstar hCondExp hBound hCeiling)
      |>.posteriorShare_tendsto_one

/--
Constructed infinite Bayes/Gibbs convergence for the true-environment
Hellinger envelope from a raw Ionescu-coordinate martingale.

This is the public true-law route without `hCondExp`, without a pointwise
envelope bound, and without a public trajectory-level martingale assumption.
The raw martingale is lifted through the constructed Ionescu law and canonical
prefix filtration; all-time realized support is discharged by construction, and
the `L¹` envelope bound is derived from nonnegative martingality.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    {κ : ℝ}
    (hRaw :
      Martingale
        (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
          (A := A) (O := O)
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar))
        (MeasureTheory.Filtration.piLE
          (X := CountableConcrete.CountablePrefixMachine.ionescuTrajectoryState A O))
        (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
          (A := A) (O := O) π (U.programSemantics penv)))
    (hCeiling :
      CountableConcrete.CountablePrefixMachine.InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure κ) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ω pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  rcases
    infiniteBayesGibbsTrajectoryLaw_of_ionescu_trueLawHellingerConvergenceSpine_of_rawIonescuMartingale_affinityCeiling
      (A := A) (O := O) U π penv ω pstar hRaw hCeiling with
  ⟨_, hSpine⟩
  exact hSpine.posteriorShare_tendsto_one

/--
Constructed true-law convergence from the finite-prefix one-step kernel
identity for the Hellinger envelope.

This variant discharges the raw Ionescu martingale internally from the direct
`trajMeasure` composition-product theorem. The remaining local input is exactly
the finite-prefix Bayes/Hellinger kernel identity, not a public
conditional-expectation or trajectory-level martingale assumption.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_prefix_kernel_integral
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hPrefixStep :
      ∀ n
        (y : (i : Finset.Iic n) →
          CountableConcrete.CountablePrefixMachine.ionescuTrajectoryState A O i),
        CountableConcrete.CountablePrefixMachine.infinitePrefixFactor
            (A := A) (O := O) n
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar n)
            (CountableConcrete.CountablePrefixMachine.ionescuIicPrefix
              (A := A) (O := O) n y) =
          ∫ e,
            CountableConcrete.CountablePrefixMachine.infinitePrefixFactor
              (A := A) (O := O) (n + 1)
              (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
                π penv ω pstar (n + 1))
              (CountableConcrete.CountablePrefixMachine.ionescuIicPrefix
                (A := A) (O := O) (n + 1)
                (CountableConcrete.CountablePrefixMachine.ionescuIicSuccExtend
                  (A := A) (O := O) n y e))
            ∂(CountableConcrete.CountablePrefixMachine.ionescuStepKernel
              (A := A) (O := O) π (U.programSemantics penv) n y))
    (hCeiling :
      CountableConcrete.CountablePrefixMachine.InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure κ) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ω pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  have hRaw :
      Martingale
        (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
          (A := A) (O := O)
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar))
        (MeasureTheory.Filtration.piLE
          (X := CountableConcrete.CountablePrefixMachine.ionescuTrajectoryState A O))
        (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
          (A := A) (O := O) π (U.programSemantics penv)) :=
    CountableConcrete.CountablePrefixMachine.infiniteRealizedObserverFiberTrueLawHellinger_rawIonescuMartingale_of_prefix_kernel_integral
      (A := A) (O := O) U π penv ω pstar hIntegrable hPrefixStep
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence
      (A := A) (O := O) U π penv ω pstar hRaw hCeiling

/--
Constructed true-law convergence from compact local Bayes/Hellinger prefix
kernel obligations.

This is the paper-facing version after the envelope-shape repair: the public
surface no longer takes the raw all-prefix `hPrefixStep`. The finite-prefix
identity is derived internally from the true-law local Bayes/Hellinger identity,
the `ionescuStepKernel` action-observation averaging bridge, and the canonical
Hellinger-envelope shape lemmas.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_prefix_kernel_obligations
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ω pstar)
    (hCeiling :
      CountableConcrete.CountablePrefixMachine.InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure κ) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ω pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  have hRaw :
      Martingale
        (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
          (A := A) (O := O)
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar))
        (MeasureTheory.Filtration.piLE
          (X := CountableConcrete.CountablePrefixMachine.ionescuTrajectoryState A O))
        (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
          (A := A) (O := O) π (U.programSemantics penv)) :=
    CountableConcrete.CountablePrefixMachine.infiniteRealizedObserverFiberTrueLawHellinger_rawIonescuMartingale_of_prefix_kernel_obligations
      (A := A) (O := O) U π penv ω pstar hIntegrable hObligations
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence
      (A := A) (O := O) U π penv ω pstar hRaw hCeiling

/--
Constructed true-law convergence from the semantic action rule.

This is the semantic-to-Hellinger bridge: instead of taking the infinite
trajectory-level true-law affinity ceiling directly, the theorem takes the
finite-prefix action rule saying that every policy-supported action is
true-law Hellinger-safe. The infinite ceiling is then derived internally for
the constructed Bayes/Gibbs trajectory law.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_action_rule
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ω pstar)
    (hActionRule :
      U.TrueLawHellingerAffinityCeilingActionRule π penv ω pstar κ) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ω pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_prefix_kernel_obligations
      (A := A) (O := O) U π penv ω pstar hIntegrable hObligations
      (U.infiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport_of_actionRule
        π penv ω pstar hActionRule)

/--
A sparse finite-prefix reference law is true-law Hellinger-safe when every
action to which it assigns nonzero mass satisfies the local true-law Hellinger
ceiling required by the Section 6 spine.
-/
def KernelReferenceLawTrueLawHellingerSafeAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A) : Prop :=
  ∀ a : A,
    refLaw.mass a ≠ 0 →
      0 < U.observerFiberTrueLawHellingerAffinity π penv h.length h a ω pstar ∧
        U.observerFiberTrueLawHellingerAffinity π penv h.length h a ω pstar ≤
          Real.exp (-κ)

/--
True-law Hellinger semantic separation at one finite prefix/action.

This is the score-floor form of the paper's semantic requirement: the local
true-law Hellinger score is at least `κ`, with the positive-multiplier side
condition needed to avoid the guarded zero branch in the `-log` transform.
-/
def TrueLawHellingerSemanticSeparationAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (a : A) : Prop :=
  0 < U.observerFiberTrueLawHellingerAffinity π penv h.length h a ω pstar ∧
    κ ≤ U.observerFiberTrueLawHellingerScore π penv h.length h a ω pstar

/--
A sparse reference law is semantically separated when every action in its
support has a true-law Hellinger semantic score floor.
-/
def KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A) : Prop :=
  ∀ a : A,
    refLaw.mass a ≠ 0 →
      TrueLawHellingerSemanticSeparationAt U π penv ω pstar κ h a

/--
Canonical countable observer whose view is exactly the one-step predictive
kernel carried by an encoded program.

Fibers of this observer are predictive equivalence classes: two encoded
programs have the same view iff they assign the same next-observation law at
every finite history/action pair. This is the hard route-2 replacement for an
arbitrary semantic fiber when the convergence proof needs calibration from the
fiber definition itself.
-/
def countablePredictiveKernelObserver
    {A : Type u} {O : Type v} :
    Observer (CountableConcrete.CountableEncodedProgram A O) where
  Ω := CountableConcrete.CountableProgram A O
  view p := p.kernel

/--
An observer is predictively extensional when its labels determine the complete
one-step predictive kernel. Equivalently, the canonical predictive-kernel
observer factors through it.
-/
def CountableObserverPredictivelyExtensional
    {A : Type u} {O : Type v}
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O)) : Prop :=
  countablePredictiveKernelObserver (A := A) (O := O) ≼ω ω

theorem countablePredictiveKernelObserver_predictivelyExtensional
    {A : Type u} {O : Type v} :
    CountableObserverPredictivelyExtensional
      (A := A) (O := O)
      (countablePredictiveKernelObserver (A := A) (O := O)) :=
  observerRefines_refl _

/--
If an observer is predictively extensional, equality of observer views forces
equality of the encoded predictive kernels.
-/
theorem countablePredictiveKernelObserver_kernel_eq_of_extensional
    {A : Type u} {O : Type v}
    {ω : Observer (CountableConcrete.CountableEncodedProgram A O)}
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ω)
    {p q : CountableConcrete.CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    p.kernel = q.kernel := by
  rcases hExt with ⟨decode, hdecode⟩
  have hp : p.kernel = decode (ω.view p) := by
    simpa [countablePredictiveKernelObserver, Function.comp] using congrFun hdecode p
  have hq : q.kernel = decode (ω.view q) := by
    simpa [countablePredictiveKernelObserver, Function.comp] using congrFun hdecode q
  rw [hp, hView, ← hq]

/--
Local calibration condition needed to turn the paper's class-predictive
Bhattacharyya score into the true-law Hellinger score consumed by the martingale
spine: the actual environment's next-observation law agrees with the in-class
observer-fiber predictive law at this prefix/action.
-/
def TrueEnvironmentClassPredictiveCalibratedAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (a : A) : Prop :=
  (fun o : O => U.programSemantics penv h a o) =
    U.observerFiberPredictiveLawInClass π h.length h a ω pstar

/--
Paper-facing local semantic separation: the class/complement predictive
Bhattacharyya affinity is positive and its `-log` score is at least `κ`.
-/
def ClassPredictiveBhattacharyyaSemanticSeparationAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (a : A) : Prop :=
  0 < U.observerFiberPredictiveLawAffinity π h.length h a ω pstar ∧
    κ ≤ U.observerFiberBhattacharyyaScore π h.length h a ω pstar

/--
A sparse reference law is calibrated when every action in its support has the
true environment law equal to the in-class predictive law.
-/
def KernelReferenceLawClassPredictiveCalibratedAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A) : Prop :=
  ∀ a : A,
    refLaw.mass a ≠ 0 →
      TrueEnvironmentClassPredictiveCalibratedAt U π penv ω pstar h a

/--
Structural, first-principles sufficient condition for calibration: every
posterior-supported program in the observer fiber has the same local
next-observation law as the true environment.
-/
def PosteriorSupportedObserverFiberSemanticsCoherentAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (a : A) : Prop :=
  ∀ p : U.Program,
    U.observerFiber ω pstar p →
      U.posteriorWeight π h.length h p ≠ 0 →
        (fun o : O => U.programSemantics p h a o) =
          fun o : O => U.programSemantics penv h a o

/--
Reference-support version of posterior-supported observer-fiber semantic
coherence.
-/
def KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A) : Prop :=
  ∀ a : A,
    refLaw.mass a ≠ 0 →
      PosteriorSupportedObserverFiberSemanticsCoherentAt U π penv ω pstar h a

/--
Predictively extensional observers derive the posterior-supported semantic
coherence predicate from the fiber definition itself, provided the true
environment program is in the target observer fiber.
-/
theorem PosteriorSupportedObserverFiberSemanticsCoherentAt_of_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (a : A)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ω)
    (hTruthFiber : U.observerFiber ω pstar penv) :
    PosteriorSupportedObserverFiberSemanticsCoherentAt
      U π penv ω pstar h a := by
  intro p hp _hPost
  have hpView :
      ω.view (U.toEncodedProgram p) = ω.view pstar := by
    simpa [CountableConcrete.CountablePrefixMachine.observerFiber] using hp
  have hTruthView :
      ω.view (U.toEncodedProgram penv) = ω.view pstar := by
    simpa [CountableConcrete.CountablePrefixMachine.observerFiber] using hTruthFiber
  have hKernel :
      (U.toEncodedProgram p).kernel =
        (U.toEncodedProgram penv).kernel :=
    countablePredictiveKernelObserver_kernel_eq_of_extensional
      (A := A) (O := O) hExt
      (p := U.toEncodedProgram p) (q := U.toEncodedProgram penv)
      (by
        calc
          ω.view (U.toEncodedProgram p) = ω.view pstar := hpView
          _ = ω.view (U.toEncodedProgram penv) := hTruthView.symm)
  have hSem : U.programSemantics p = U.programSemantics penv := by
    simpa [CountableConcrete.CountablePrefixMachine.toEncodedProgram] using hKernel
  have hLaw : U.programSemantics p h a = U.programSemantics penv h a :=
    congrFun (congrFun hSem h) a
  funext o
  exact congrArg (fun μ : PMF O => μ o) hLaw

/--
Reference-support version of predictive-extensional coherence.
-/
theorem KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt_of_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ω)
    (hTruthFiber : U.observerFiber ω pstar penv) :
    KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt
      U π penv ω pstar h refLaw := by
  intro a _ha
  exact
    PosteriorSupportedObserverFiberSemanticsCoherentAt_of_predictivelyExtensional
      U π penv ω pstar h a hExt hTruthFiber

/--
The true program is in its own canonical predictive-kernel fiber.
-/
theorem observerFiber_predictiveKernelObserver_true
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (penv : U.Program) :
    U.observerFiber
      (countablePredictiveKernelObserver (A := A) (O := O))
      (U.toEncodedProgram penv) penv := by
  simp [CountableConcrete.CountablePrefixMachine.observerFiber,
    countablePredictiveKernelObserver]

/--
Canonical predictive-kernel fibers derive the semantic coherence predicate with
no separate coherence assumption.
-/
theorem KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt_predictiveKernelObserver
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A) :
    KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt
      U π penv
      (countablePredictiveKernelObserver (A := A) (O := O))
      (U.toEncodedProgram penv) h refLaw :=
  KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt_of_predictivelyExtensional
    U π penv
    (countablePredictiveKernelObserver (A := A) (O := O))
    (U.toEncodedProgram penv) h refLaw
    (countablePredictiveKernelObserver_predictivelyExtensional
      (A := A) (O := O))
    (observerFiber_predictiveKernelObserver_true U penv)

/--
A sparse reference law is class-predictive semantically separated when every
supported action satisfies the paper-facing Bhattacharyya score floor.
-/
def KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A) : Prop :=
  ∀ a : A,
    refLaw.mass a ≠ 0 →
      ClassPredictiveBhattacharyyaSemanticSeparationAt U π ω pstar κ h a

/--
Posterior-supported observer-fiber semantic coherence derives the local
calibration equality between the true environment law and the in-class
predictive law.
-/
theorem TrueEnvironmentClassPredictiveCalibratedAt_of_posteriorSupportedFiberSemantics
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (a : A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ ⊤)
    (hCoherent :
      PosteriorSupportedObserverFiberSemanticsCoherentAt
        U π penv ω pstar h a) :
    TrueEnvironmentClassPredictiveCalibratedAt U π penv ω pstar h a := by
  unfold TrueEnvironmentClassPredictiveCalibratedAt
  exact
    (U.observerFiberPredictiveLawInClass_eq_programSemantics_of_fiber_semantics
      π penv h.length h a ω pstar hMass0 hMassTop hCoherent).symm

/--
Reference-support version: semantic coherence of posterior-supported in-fiber
programs derives the calibration predicate used by the class-predictive bridge.
-/
theorem KernelReferenceLawClassPredictiveCalibratedAt_of_posteriorSupportedFiberSemantics
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ ⊤)
    (hCoherent :
      KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt
        U π penv ω pstar h refLaw) :
    KernelReferenceLawClassPredictiveCalibratedAt U π penv ω pstar h refLaw := by
  intro a hMass
  exact
    TrueEnvironmentClassPredictiveCalibratedAt_of_posteriorSupportedFiberSemantics
      U π penv ω pstar h a hMass0 hMassTop (hCoherent a hMass)

/--
Predictively extensional observers derive class-predictive calibration from the
fiber definition itself, once the true environment program is in the target
fiber and the in-class predictive denominator is well formed.
-/
theorem KernelReferenceLawClassPredictiveCalibratedAt_of_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ ⊤)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ω)
    (hTruthFiber : U.observerFiber ω pstar penv) :
    KernelReferenceLawClassPredictiveCalibratedAt U π penv ω pstar h refLaw :=
  KernelReferenceLawClassPredictiveCalibratedAt_of_posteriorSupportedFiberSemantics
    U π penv ω pstar h refLaw hMass0 hMassTop
    (KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt_of_predictivelyExtensional
      U π penv ω pstar h refLaw hExt hTruthFiber)

/--
Canonical predictive-kernel observer version of class-predictive calibration.
-/
theorem KernelReferenceLawClassPredictiveCalibratedAt_predictiveKernelObserver
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) ≠ ⊤) :
    KernelReferenceLawClassPredictiveCalibratedAt
      U π penv
      (countablePredictiveKernelObserver (A := A) (O := O))
      (U.toEncodedProgram penv) h refLaw :=
  KernelReferenceLawClassPredictiveCalibratedAt_of_predictivelyExtensional
    U π penv
    (countablePredictiveKernelObserver (A := A) (O := O))
    (U.toEncodedProgram penv) h refLaw hMass0 hMassTop
    (countablePredictiveKernelObserver_predictivelyExtensional
      (A := A) (O := O))
    (observerFiber_predictiveKernelObserver_true U penv)

/--
Calibration closes the semantic caveat locally: class-predictive
Bhattacharyya separation becomes true-law Hellinger semantic separation.
-/
theorem TrueLawHellingerSemanticSeparationAt_of_classPredictive_calibrated
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (a : A)
    (hCal :
      TrueEnvironmentClassPredictiveCalibratedAt U π penv ω pstar h a)
    (hSep :
      ClassPredictiveBhattacharyyaSemanticSeparationAt U π ω pstar κ h a) :
    TrueLawHellingerSemanticSeparationAt U π penv ω pstar κ h a := by
  rcases hSep with ⟨hAffPos, hScore⟩
  have hAffEq :
      U.observerFiberTrueLawHellingerAffinity π penv h.length h a ω pstar =
        U.observerFiberPredictiveLawAffinity π h.length h a ω pstar :=
    U.observerFiberTrueLawHellingerAffinity_eq_predictiveLawAffinity_of_calibrated
      π penv h.length h a ω pstar hCal
  have hScoreEq :
      U.observerFiberTrueLawHellingerScore π penv h.length h a ω pstar =
        U.observerFiberBhattacharyyaScore π h.length h a ω pstar :=
    U.observerFiberTrueLawHellingerScore_eq_bhattacharyyaScore_of_calibrated
      π penv h.length h a ω pstar hCal
  exact ⟨by simpa [hAffEq] using hAffPos, by simpa [hScoreEq] using hScore⟩

/--
Reference-support version of the calibrated semantic bridge.
-/
theorem KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_calibrated
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hCal :
      KernelReferenceLawClassPredictiveCalibratedAt U π penv ω pstar h refLaw)
    (hSep :
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U π ω pstar κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
      U π penv ω pstar κ h refLaw := by
  intro a hMass
  exact
    TrueLawHellingerSemanticSeparationAt_of_classPredictive_calibrated
      U π penv ω pstar κ h a (hCal a hMass) (hSep a hMass)

/--
Reference-support semantic bridge with calibration discharged from
posterior-supported observer-fiber semantic coherence.
-/
theorem KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_fiberSemantics
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ ⊤)
    (hCoherent :
      KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt
        U π penv ω pstar h refLaw)
    (hSep :
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U π ω pstar κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
      U π penv ω pstar κ h refLaw :=
  KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_calibrated
    U π penv ω pstar κ h refLaw
    (KernelReferenceLawClassPredictiveCalibratedAt_of_posteriorSupportedFiberSemantics
      U π penv ω pstar h refLaw hMass0 hMassTop hCoherent)
    hSep

/--
Reference-support semantic bridge with calibration discharged from predictive
extensionality of the observer fiber.
-/
theorem KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ ⊤)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ω)
    (hTruthFiber : U.observerFiber ω pstar penv)
    (hSep :
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U π ω pstar κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
      U π penv ω pstar κ h refLaw :=
  KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_calibrated
    U π penv ω pstar κ h refLaw
    (KernelReferenceLawClassPredictiveCalibratedAt_of_predictivelyExtensional
      U π penv ω pstar h refLaw hMass0 hMassTop hExt hTruthFiber)
    hSep

/--
Canonical predictive-kernel observer version of the class-predictive semantic
bridge.
-/
theorem KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_predictiveKernelObserver
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) ≠ ⊤)
    (hSep :
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U π
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
      U π penv
      (countablePredictiveKernelObserver (A := A) (O := O))
      (U.toEncodedProgram penv) κ h refLaw :=
  KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_predictivelyExtensional
    U π penv
    (countablePredictiveKernelObserver (A := A) (O := O))
    (U.toEncodedProgram penv) κ h refLaw hMass0 hMassTop
    (countablePredictiveKernelObserver_predictivelyExtensional
      (A := A) (O := O))
    (observerFiber_predictiveKernelObserver_true U penv)
    hSep

/--
Semantic separation implies safety: a true-law Hellinger score floor on a
reference-supported action gives the affinity ceiling required by the safe
Gibbs-support bridge.
-/
theorem KernelReferenceLawTrueLawHellingerSafeAt_of_semanticSeparation
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hSemantic :
      KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
        U π penv ω pstar κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSafeAt U π penv ω pstar κ h refLaw := by
  intro a hMass
  rcases hSemantic a hMass with ⟨hAffPos, hScore⟩
  exact ⟨hAffPos,
    U.observerFiberTrueLawHellingerAffinity_le_exp_neg_of_score_ge
      π penv h.length h a ω pstar hAffPos hScore⟩

/--
Paper-facing semantic separation plus calibration implies the safe-reference
condition consumed by Gibbs support inheritance.
-/
theorem KernelReferenceLawTrueLawHellingerSafeAt_of_classPredictive_calibrated
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hCal :
      KernelReferenceLawClassPredictiveCalibratedAt U π penv ω pstar h refLaw)
    (hSep :
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U π ω pstar κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSafeAt U π penv ω pstar κ h refLaw :=
  KernelReferenceLawTrueLawHellingerSafeAt_of_semanticSeparation
    U π penv ω pstar κ h refLaw
    (KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_calibrated
      U π penv ω pstar κ h refLaw hCal hSep)

/--
Paper-facing semantic separation plus posterior-supported fiber semantic
coherence implies the safe-reference condition, with calibration derived
internally.
-/
theorem KernelReferenceLawTrueLawHellingerSafeAt_of_classPredictive_fiberSemantics
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ ⊤)
    (hCoherent :
      KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt
        U π penv ω pstar h refLaw)
    (hSep :
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U π ω pstar κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSafeAt U π penv ω pstar κ h refLaw :=
  KernelReferenceLawTrueLawHellingerSafeAt_of_semanticSeparation
    U π penv ω pstar κ h refLaw
    (KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_fiberSemantics
      U π penv ω pstar κ h refLaw hMass0 hMassTop hCoherent hSep)

/--
Paper-facing semantic separation plus predictive extensionality implies the
safe-reference condition, with calibration derived from the observer fiber.
-/
theorem KernelReferenceLawTrueLawHellingerSafeAt_of_classPredictive_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h ω pstar ≠ ⊤)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ω)
    (hTruthFiber : U.observerFiber ω pstar penv)
    (hSep :
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U π ω pstar κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSafeAt U π penv ω pstar κ h refLaw :=
  KernelReferenceLawTrueLawHellingerSafeAt_of_semanticSeparation
    U π penv ω pstar κ h refLaw
    (KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_predictivelyExtensional
      U π penv ω pstar κ h refLaw hMass0 hMassTop hExt hTruthFiber hSep)

/--
Canonical predictive-kernel observer version of the safe-reference bridge.
-/
theorem KernelReferenceLawTrueLawHellingerSafeAt_of_classPredictive_predictiveKernelObserver
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (κ : ℝ)
    (h : CountableConcrete.CountHist A O)
    (refLaw : ActionLaw A)
    (hMass0 :
      U.observerFiberPosteriorWeight π h.length h
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) ≠ 0)
    (hMassTop :
      U.observerFiberPosteriorWeight π h.length h
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) ≠ ⊤)
    (hSep :
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U π
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) κ h refLaw) :
    KernelReferenceLawTrueLawHellingerSafeAt
      U π penv
      (countablePredictiveKernelObserver (A := A) (O := O))
      (U.toEncodedProgram penv) κ h refLaw :=
  KernelReferenceLawTrueLawHellingerSafeAt_of_classPredictive_predictivelyExtensional
    U π penv
    (countablePredictiveKernelObserver (A := A) (O := O))
    (U.toEncodedProgram penv) κ h refLaw hMass0 hMassTop
    (countablePredictiveKernelObserver_predictivelyExtensional
      (A := A) (O := O))
    (observerFiber_predictiveKernelObserver_true U penv)
    hSep

/--
Constrained/safe Gibbs action rule.

If the policy's action mass at every finite prefix is exactly the action
marginal of the sparse Gibbs kernel, and the reference law at that prefix is
supported only on true-law Hellinger-safe actions, then the policy satisfies
the public true-law Hellinger affinity-ceiling action rule.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefSafe :
      ∀ h,
        KernelReferenceLawTrueLawHellingerSafeAt
          U π penv ωH pstar κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv ωH pstar κ := by
  refine ⟨hκ, ?_⟩
  intro h a ha
  have hπa : π h a ≠ 0 := (PMF.mem_support_iff (π h) a).1 ha
  have hMarg :
      kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a ≠ 0 := by
    simpa [hPolicy h a] using hπa
  exact
    kernelGibbsActionMarginal_support_subset_refLaw_action_property
      U ωA β γ (BbarAt h) (refLawAt h)
      (fun a =>
        0 < U.observerFiberTrueLawHellingerAffinity π penv h.length h a ωH pstar ∧
          U.observerFiberTrueLawHellingerAffinity π penv h.length h a ωH pstar ≤
            Real.exp (-κ))
      (hRefSafe h) hMarg

/--
Constrained Gibbs action rule from semantic separation on the sparse reference
support. This is the semantic-facing variant of
`trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal`.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_semanticSeparation
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
          U π penv ωH pstar κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv ωH pstar κ :=
  trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal
    (A := A) (O := O) U π penv ωH ωA pstar β γ BbarAt refLawAt
    hκ hPolicy
    (fun h =>
      KernelReferenceLawTrueLawHellingerSafeAt_of_semanticSeparation
        U π penv ωH pstar κ h (refLawAt h) (hRefSemantic h))

/--
Constrained Gibbs action rule from the paper-facing class-predictive
Bhattacharyya score, provided the true environment is calibrated to the
in-class predictive law on the sparse reference support.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_classPredictive
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefCal :
      ∀ h,
        KernelReferenceLawClassPredictiveCalibratedAt
          U π penv ωH pstar h (refLawAt h))
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv ωH pstar κ :=
  trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_semanticSeparation
    (A := A) (O := O) U π penv ωH ωA pstar β γ BbarAt refLawAt
    hκ hPolicy
    (fun h =>
      KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_calibrated
        U π penv ωH pstar κ h (refLawAt h) (hRefCal h) (hRefSemantic h))

/--
Constrained Gibbs action rule from class-predictive separation, with
true-environment calibration discharged by predictive extensionality of the
semantic observer.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_classPredictive_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ ⊤)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ωH)
    (hTruthFiber : U.observerFiber ωH pstar penv)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv ωH pstar κ :=
  trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_classPredictive
    (A := A) (O := O) U π penv ωH ωA pstar β γ
    BbarAt refLawAt hκ hPolicy
    (fun h =>
      KernelReferenceLawClassPredictiveCalibratedAt_of_predictivelyExtensional
        U π penv ωH pstar h (refLawAt h)
        (hRefMass0 h) (hRefMassTop h) hExt hTruthFiber)
    hRefSemantic

/--
Canonical predictive-kernel observer version of the constrained Gibbs action
rule. The observer is exactly the program kernel, so predictive extensionality
and truth-in-fiber are internal facts rather than hypotheses.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_classPredictive_predictiveKernelObserver
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) ≠ ⊤)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv
      (countablePredictiveKernelObserver (A := A) (O := O))
      (U.toEncodedProgram penv) κ :=
  trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_classPredictive_predictivelyExtensional
    (A := A) (O := O) U π penv
    (countablePredictiveKernelObserver (A := A) (O := O)) ωA
    (U.toEncodedProgram penv) β γ BbarAt refLawAt hκ hPolicy
    hRefMass0 hRefMassTop
    (countablePredictiveKernelObserver_predictivelyExtensional
      (A := A) (O := O))
    (observerFiber_predictiveKernelObserver_true U penv)
    hRefSemantic

/--
Constrained/safe minimizer action rule.

This is the support-inheritance bridge at the variational level. If, at every
finite prefix, the class-action optimizer minimizes the exact kernel
functional, the policy is the optimizer's action marginal, and the sparse
reference law is supported on true-law Hellinger-safe actions, then the policy
satisfies the public Hellinger affinity-ceiling action rule. The proof derives
Gibbs support inheritance from `prop_kernel_functional_minimizer` rather than
taking Gibbs-policy equality as an assumption.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefSafe :
      ∀ h,
        KernelReferenceLawTrueLawHellingerSafeAt
          U π penv ωH pstar κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv ωH pstar κ := by
  refine ⟨hκ, ?_⟩
  intro h a ha
  have hπa : π h a ≠ 0 := (PMF.mem_support_iff (π h) a).1 ha
  have hMarg :
      kernelLawActionMarginal (kernelAt h) a ≠ 0 := by
    simpa [hPolicyMarginal h a] using hπa
  obtain ⟨_, _, hEqIff⟩ :=
    prop_kernel_functional_minimizer U π h.length h ωB ωA β γ
      (BbarAt h) (hBbar_nonneg h) (hBbar_le_one h)
      (qAt h) (hq h) (refLawAt h) (href h) (kernelAt h)
      (hKernel h) hβ hγ
  have hKernelEq :
      ∀ c : ωA.Ω, ∀ a : A,
        kernelAt h c a =
          kernelGibbsLaw U ωA β γ (BbarAt h) (refLawAt h) c a :=
    (hEqIff.mp (hMin h)).2
  exact
    kernelLawActionMarginal_support_subset_refLaw_action_property_of_eq_gibbs
      U ωA β γ (BbarAt h) (refLawAt h) (kernelAt h) hKernelEq
      (fun a =>
        0 < U.observerFiberTrueLawHellingerAffinity π penv h.length h a ωH pstar ∧
          U.observerFiberTrueLawHellingerAffinity π penv h.length h a ωH pstar ≤
            Real.exp (-κ))
      (hRefSafe h) hMarg

/--
Constrained/safe minimizer action rule from semantic separation on reference
support. This connects the semantic score-floor hypothesis to the safe
reference condition used by Gibbs support inheritance.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_semanticSeparation
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
          U π penv ωH pstar κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv ωH pstar κ :=
  trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers
    (A := A) (O := O) U π penv ωH ωB ωA pstar β γ
    BbarAt qAt kernelAt refLawAt hκ hBbar_nonneg hBbar_le_one
    hq href hKernel hβ hγ hMin hPolicyMarginal
    (fun h =>
      KernelReferenceLawTrueLawHellingerSafeAt_of_semanticSeparation
        U π penv ωH pstar κ h (refLawAt h) (hRefSemantic h))

/--
Constrained variational-minimizer action rule from the paper-facing
class-predictive Bhattacharyya score plus true-environment calibration.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_classPredictive
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefCal :
      ∀ h,
        KernelReferenceLawClassPredictiveCalibratedAt
          U π penv ωH pstar h (refLawAt h))
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv ωH pstar κ :=
  trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_semanticSeparation
    (A := A) (O := O) U π penv ωH ωB ωA pstar β γ
    BbarAt qAt kernelAt refLawAt hκ hBbar_nonneg hBbar_le_one
    hq href hKernel hβ hγ hMin hPolicyMarginal
    (fun h =>
      KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt_of_classPredictive_calibrated
        U π penv ωH pstar κ h (refLawAt h) (hRefCal h) (hRefSemantic h))

/--
Constrained variational-minimizer action rule from class-predictive separation,
with true-environment calibration discharged by predictive extensionality.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_classPredictive_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ ⊤)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ωH)
    (hTruthFiber : U.observerFiber ωH pstar penv)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv ωH pstar κ :=
  trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_classPredictive
    (A := A) (O := O) U π penv ωH ωB ωA pstar β γ
    BbarAt qAt kernelAt refLawAt hκ hBbar_nonneg hBbar_le_one
    hq href hKernel hβ hγ hMin hPolicyMarginal
    (fun h =>
      KernelReferenceLawClassPredictiveCalibratedAt_of_predictivelyExtensional
        U π penv ωH pstar h (refLawAt h)
        (hRefMass0 h) (hRefMassTop h) hExt hTruthFiber)
    hRefSemantic

/--
Canonical predictive-kernel observer version of the constrained
variational-minimizer action rule.
-/
theorem trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_classPredictive_predictiveKernelObserver
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) ≠ ⊤)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) κ h (refLawAt h)) :
    U.TrueLawHellingerAffinityCeilingActionRule π penv
      (countablePredictiveKernelObserver (A := A) (O := O))
      (U.toEncodedProgram penv) κ :=
  trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_classPredictive_predictivelyExtensional
    (A := A) (O := O) U π penv
    (countablePredictiveKernelObserver (A := A) (O := O)) ωB ωA
    (U.toEncodedProgram penv) β γ BbarAt qAt kernelAt refLawAt hκ
    hBbar_nonneg hBbar_le_one hq href hKernel hβ hγ hMin
    hPolicyMarginal hRefMass0 hRefMassTop
    (countablePredictiveKernelObserver_predictivelyExtensional
      (A := A) (O := O))
    (observerFiber_predictiveKernelObserver_true U penv)
    hRefSemantic

/--
Constructed true-law convergence for a constrained/safe Gibbs policy.

This combines the sparse-reference support inheritance of the exact Gibbs
kernel with the existing Hellinger-spine theorem: a policy equal to the Gibbs
action marginal of safe reference laws satisfies the action rule internally,
so the public theorem no longer needs a separate trajectory-level affinity
ceiling hypothesis.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefSafe :
      ∀ h,
        KernelReferenceLawTrueLawHellingerSafeAt
          U π penv ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_action_rule
      (A := A) (O := O) U π penv ωH pstar hIntegrable hObligations
      (trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal
        (A := A) (O := O) U π penv ωH ωA pstar β γ
        BbarAt refLawAt hκ hPolicy hRefSafe)

/--
Constructed true-law convergence for a constrained Gibbs policy from semantic
separation on the sparse reference support.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule_semanticSeparation
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
          U π penv ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_action_rule
      (A := A) (O := O) U π penv ωH pstar hIntegrable hObligations
      (trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_semanticSeparation
        (A := A) (O := O) U π penv ωH ωA pstar β γ
        BbarAt refLawAt hκ hPolicy hRefSemantic)

/--
Constructed true-law convergence for a constrained Gibbs policy from the
paper-facing class-predictive Bhattacharyya separation hypothesis, with the
necessary true-environment calibration exposed on the sparse reference support.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule_classPredictive
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefCal :
      ∀ h,
        KernelReferenceLawClassPredictiveCalibratedAt
          U π penv ωH pstar h (refLawAt h))
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_action_rule
      (A := A) (O := O) U π penv ωH pstar hIntegrable hObligations
      (trueLawHellingerAffinityCeilingActionRule_of_kernelGibbsActionMarginal_classPredictive
        (A := A) (O := O) U π penv ωH ωA pstar β γ
        BbarAt refLawAt hκ hPolicy hRefCal hRefSemantic)

/--
Constructed true-law convergence for a constrained Gibbs policy from the
paper-facing class-predictive Bhattacharyya separation hypothesis, with
calibration derived internally from posterior-supported observer-fiber semantic
coherence.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule_classPredictive_fiberSemantics
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ ⊤)
    (hRefCoherent :
      ∀ h,
        KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt
          U π penv ωH pstar h (refLawAt h))
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule_classPredictive
      (A := A) (O := O) U π penv ωH ωA pstar β γ
      BbarAt refLawAt hIntegrable hObligations hκ hPolicy
      (fun h =>
        KernelReferenceLawClassPredictiveCalibratedAt_of_posteriorSupportedFiberSemantics
          U π penv ωH pstar h (refLawAt h)
          (hRefMass0 h) (hRefMassTop h) (hRefCoherent h))
      hRefSemantic

/--
Constructed true-law convergence for a constrained Gibbs policy from the
paper-facing class-predictive Bhattacharyya separation hypothesis, with
calibration discharged by predictive extensionality of the semantic observer.

This is the route-2 public theorem: semantic coherence is no longer an input.
Instead, the observer must be predictive enough that an observer fiber determines
the program kernel, and the true environment must lie in the target fiber.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule_classPredictive_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ ⊤)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ωH)
    (hTruthFiber : U.observerFiber ωH pstar penv)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule_classPredictive
      (A := A) (O := O) U π penv ωH ωA pstar β γ
      BbarAt refLawAt hIntegrable hObligations hκ hPolicy
      (fun h =>
        KernelReferenceLawClassPredictiveCalibratedAt_of_predictivelyExtensional
          U π penv ωH pstar h (refLawAt h)
          (hRefMass0 h) (hRefMassTop h) hExt hTruthFiber)
      hRefSemantic

/--
Canonical predictive-kernel observer version of the constructed constrained
Gibbs convergence theorem.

The target semantic fiber is the true environment's predictive kernel. Thus the
route-2 semantic-identification premises are proved internally; only the usual
posterior denominator and martingale/kernel obligations remain.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule_classPredictive_predictiveKernelObserver
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv
              (countablePredictiveKernelObserver (A := A) (O := O))
              (U.toEncodedProgram penv)) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv))
    (hκ : 0 < κ)
    (hPolicy :
      ∀ h a,
        π h a =
          kernelGibbsActionMarginal U ωA β γ (BbarAt h) (refLawAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) ≠ ⊤)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule_classPredictive_predictivelyExtensional
      (A := A) (O := O) U π penv
      (countablePredictiveKernelObserver (A := A) (O := O)) ωA
      (U.toEncodedProgram penv) β γ BbarAt refLawAt hIntegrable hObligations
      hκ hPolicy hRefMass0 hRefMassTop
      (countablePredictiveKernelObserver_predictivelyExtensional
        (A := A) (O := O))
      (observerFiber_predictiveKernelObserver_true U penv)
      hRefSemantic

/--
Constructed true-law convergence from constrained/safe variational minimizers.

Compared with
`thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_gibbs_rule`,
this theorem does not assume policy equality with the Gibbs action marginal.
It derives that support fact from exact kernel-functional minimization plus the
assumption that the policy is the action marginal of the minimizing
class-action kernel.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefSafe :
      ∀ h,
        KernelReferenceLawTrueLawHellingerSafeAt
          U π penv ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_action_rule
      (A := A) (O := O) U π penv ωH pstar hIntegrable hObligations
      (trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers
        (A := A) (O := O) U π penv ωH ωB ωA pstar β γ
        BbarAt qAt kernelAt refLawAt hκ hBbar_nonneg hBbar_le_one
        hq href hKernel hβ hγ hMin hPolicyMarginal hRefSafe)

/--
Constructed true-law convergence from constrained variational minimizers and
semantic separation on sparse reference support.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_semanticSeparation
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawTrueLawHellingerSemanticallySeparatedAt
          U π penv ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_action_rule
      (A := A) (O := O) U π penv ωH pstar hIntegrable hObligations
      (trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_semanticSeparation
        (A := A) (O := O) U π penv ωH ωB ωA pstar β γ
        BbarAt qAt kernelAt refLawAt hκ hBbar_nonneg hBbar_le_one
        hq href hKernel hβ hγ hMin hPolicyMarginal hRefSemantic)

/--
Constructed true-law convergence from constrained variational minimizers and
paper-facing class-predictive Bhattacharyya separation, with true-environment
calibration on the sparse reference support.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_classPredictive
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefCal :
      ∀ h,
        KernelReferenceLawClassPredictiveCalibratedAt
          U π penv ωH pstar h (refLawAt h))
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_action_rule
      (A := A) (O := O) U π penv ωH pstar hIntegrable hObligations
      (trueLawHellingerAffinityCeilingActionRule_of_kernelFunctionalMinimizers_classPredictive
        (A := A) (O := O) U π penv ωH ωB ωA pstar β γ
        BbarAt qAt kernelAt refLawAt hκ hBbar_nonneg hBbar_le_one
        hq href hKernel hβ hγ hMin hPolicyMarginal hRefCal hRefSemantic)

/--
Constructed true-law convergence from constrained variational minimizers and
paper-facing class-predictive Bhattacharyya separation, with calibration derived
from posterior-supported observer-fiber semantic coherence.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_classPredictive_fiberSemantics
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ ⊤)
    (hRefCoherent :
      ∀ h,
        KernelReferenceLawPosteriorSupportedObserverFiberSemanticsCoherentAt
          U π penv ωH pstar h (refLawAt h))
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_classPredictive
      (A := A) (O := O) U π penv ωH ωB ωA pstar β γ
      BbarAt qAt kernelAt refLawAt hIntegrable hObligations hκ
      hBbar_nonneg hBbar_le_one hq href hKernel hβ hγ hMin hPolicyMarginal
      (fun h =>
        KernelReferenceLawClassPredictiveCalibratedAt_of_posteriorSupportedFiberSemantics
          U π penv ωH pstar h (refLawAt h)
          (hRefMass0 h) (hRefMassTop h) (hRefCoherent h))
      hRefSemantic

/--
Constructed true-law convergence from constrained variational minimizers and
paper-facing class-predictive Bhattacharyya separation, with calibration
discharged by predictive extensionality of the semantic observer.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_classPredictive_predictivelyExtensional
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωH ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ωH pstar) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv ωH pstar)
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h ωH pstar ≠ ⊤)
    (hExt : CountableObserverPredictivelyExtensional (A := A) (O := O) ωH)
    (hTruthFiber : U.observerFiber ωH pstar penv)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π ωH pstar κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ωH pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_classPredictive
      (A := A) (O := O) U π penv ωH ωB ωA pstar β γ
      BbarAt qAt kernelAt refLawAt hIntegrable hObligations hκ
      hBbar_nonneg hBbar_le_one hq href hKernel hβ hγ hMin hPolicyMarginal
      (fun h =>
        KernelReferenceLawClassPredictiveCalibratedAt_of_predictivelyExtensional
          U π penv ωH pstar h (refLawAt h)
          (hRefMass0 h) (hRefMassTop h) hExt hTruthFiber)
      hRefSemantic

/--
Canonical predictive-kernel observer version of the constructed constrained
variational-minimizer convergence theorem.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_classPredictive_predictiveKernelObserver
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
    [Fintype A]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ωB ωA : Observer (CountableConcrete.CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : ℝ)
    (BbarAt :
      CountableConcrete.CountHist A O →
        KernelScore (A := A) (O := O) ωA)
    (qAt :
      CountableConcrete.CountHist A O → U.Program → ENNReal)
    (kernelAt :
      CountableConcrete.CountHist A O → ωA.Ω → A → ENNReal)
    (refLawAt : CountableConcrete.CountHist A O → ActionLaw A)
    {κ : ℝ}
    (hIntegrable :
      ∀ n,
        Integrable
          (CountableConcrete.CountablePrefixMachine.ionescuPullbackInfiniteProcess
            (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv
              (countablePredictiveKernelObserver (A := A) (O := O))
              (U.toEncodedProgram penv)) n)
          (CountableConcrete.CountablePrefixMachine.ionescuTrajectoryMeasure
            (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      CountableConcrete.CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
        U π penv
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv))
    (hκ : 0 < κ)
    (hBbar_nonneg :
      ∀ h c a, 0 ≤ BbarAt h c a)
    (hBbar_le_one :
      ∀ h c a, BbarAt h c a ≤ 1)
    (hq :
      ∀ h,
        BeliefAdmissibleAt U π h.length h (qAt h))
    (href :
      ∀ h,
        KernelReferenceLawMassAdmissible (A := A) (refLawAt h))
    (hKernel :
      ∀ h,
        KernelLawAdmissibleAt U ωA (refLawAt h) (kernelAt h))
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      ∀ h,
        def_kernel_functional U π h.length h ωB ωA β γ
            (BbarAt h) (qAt h) (kernelAt h) (refLawAt h) =
          negativeLogBayesEvidence U π h.length h
            - γ * Real.log
              (kernelGibbsPartition U ωA β γ (BbarAt h) (refLawAt h)).toReal)
    (hPolicyMarginal :
      ∀ h a,
        π h a = kernelLawActionMarginal (kernelAt h) a)
    (hRefMass0 :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) ≠ 0)
    (hRefMassTop :
      ∀ h,
        U.observerFiberPosteriorWeight π h.length h
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) ≠ ⊤)
    (hRefSemantic :
      ∀ h,
        KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
          U π
          (countablePredictiveKernelObserver (A := A) (O := O))
          (U.toEncodedProgram penv) κ h (refLawAt h)) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_classPredictive_predictivelyExtensional
      (A := A) (O := O) U π penv
      (countablePredictiveKernelObserver (A := A) (O := O)) ωB ωA
      (U.toEncodedProgram penv) β γ BbarAt qAt kernelAt refLawAt
      hIntegrable hObligations hκ hBbar_nonneg hBbar_le_one hq href hKernel
      hβ hγ hMin hPolicyMarginal hRefMass0 hRefMassTop
      (countablePredictiveKernelObserver_predictivelyExtensional
        (A := A) (O := O))
      (observerFiber_predictiveKernelObserver_true U penv)
      hRefSemantic

/--
Variant of the constructed true-law convergence theorem when the public
trajectory-level martingale has already been established.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_martingale
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    {κ : ℝ}
    (hM_martingale :
      Martingale
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
          π penv ω pstar)
        (CountableConcrete.CountablePrefixMachine.infinitePrefixMathlibFiltration
          (A := A) (O := O))
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure)
    (hCeiling :
      CountableConcrete.CountablePrefixMachine.InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure κ) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ω pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  rcases
    infiniteBayesGibbsTrajectoryLaw_of_ionescu_trueLawHellingerConvergenceSpine_of_martingale_affinityCeiling
      (A := A) (O := O) U π penv ω pstar hM_martingale hCeiling with
  ⟨_, hSpine⟩
  exact hSpine.posteriorShare_tendsto_one

/--
Constructed infinite Bayes/Gibbs convergence for the true-environment
Hellinger envelope.

The one-step score is normalized against the actual environment kernel
`programSemantics penv`. This is the public caveat-free route: the semantic
input is a true-law Hellinger multiplier ceiling, not a class-predictive
Bhattacharyya ceiling. The local first-principles Bayes/Hellinger step beneath
the conditional-expectation hypothesis is
`observerFiberTrueLawHellinger_oneStep_sqrtResidual_normalized`.
-/
theorem thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_condExp
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    {C : ℝ≥0} {κ : ℝ}
    (hCondExp :
      ∀ n,
        U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar n =ᵐ[
          (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
            (A := A) (O := O) U π penv).measure]
          MeasureTheory.condExp
            (CountableConcrete.CountablePrefixMachine.infinitePrefixMathlibFiltration
              (A := A) (O := O) n)
            (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
              (A := A) (O := O) U π penv).measure
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar (n + 1)))
    (hBound :
      ∀ n, ∀ᵐ ξ ∂
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure,
        ‖U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar n ξ‖ₑ ≤
          (C : ℝ≥0∞))
    (hCeiling :
      CountableConcrete.CountablePrefixMachine.InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar
        (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U π penv).measure κ) :
    ∀ᵐ ξ ∂
      (CountableConcrete.CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U π penv).measure,
      Tendsto
        (fun n => (1 + U.infiniteRealizedResidualOddsProcess π ω pstar n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    (infiniteBayesGibbsTrajectoryLaw_of_ionescu_trueLawHellingerConvergenceSpine_of_condExp_affinityCeiling
        (A := A) (O := O) U π penv ω pstar hCondExp hBound hCeiling)
      |>.posteriorShare_tendsto_one

/--
Kernel-functional minimization plus the induced Hellinger spine gives semantic
posterior concentration.

The theorem separates the two proof obligations that the paper uses together:
`prop_kernel_functional_minimizer` identifies the exact Bayes posterior and
Gibbs class-action kernel as the global minimizer of the repaired variational
functional, while `HellingerConvergenceSpine` packages the soft Section 6
trajectory algebra for an explicit residual odds process. The intended
instantiation is the process induced by the Bayes/Gibbs minimizer; proving that
instantiation is the remaining first-principles construction. Supplying the
spine yields the formal convergence promise without replacing the Hellinger
argument by the stronger zero-out special case.
-/
theorem thm_kernel_functional_minimizer_convergence_of_hellinger_spine
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O] [Fintype A]
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {ℱ : MeasureTheory.Filtration Nat mΩ}
    {R M S : Nat → Ω → ℝ} {C : ℝ≥0}
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ωA)
    (hBbar_nonneg : ∀ c : ωA.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ωA.Ω, ∀ a : A, Bbar c a ≤ 1)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q)
    (refLaw : ActionLaw A)
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    (κ : ωA.Ω → A → ENNReal)
    (hκ : KernelLawAdmissibleAt U ωA refLaw κ)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hMin :
      def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw =
        negativeLogBayesEvidence U π t h
          - γ * Real.log (kernelGibbsPartition U ωA β γ Bbar refLaw).toReal)
    (hSpine : HellingerConvergenceSpine μ ℱ R M S C) :
    ((∀ p : U.Program, q p = bayesPosterior U π t h p) ∧
        (∀ c : ωA.Ω, ∀ a : A,
          κ c a = kernelGibbsLaw U ωA β γ Bbar refLaw c a)) ∧
      ∀ᵐ ξ ∂μ, Tendsto (fun n => (1 + R n ξ)⁻¹) atTop (nhds 1) := by
  obtain ⟨_, _, hEqIff⟩ :=
    prop_kernel_functional_minimizer U π t h ωB ωA β γ Bbar
      hBbar_nonneg hBbar_le_one q hq refLaw href κ hκ hβ hγ
  exact ⟨hEqIff.mp hMin, hSpine.posteriorShare_tendsto_one⟩

/-- Legacy separator extraction formerly occupying the `lem:contraction` slot. -/
theorem lem_contraction_separator_witness
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (actions : List A)
    (hSep : def_sep_condition U π h ω pstar actions) :
    ∃ a, a ∈ actions ∧ U.isSeparatingAction π h ω pstar a := by
  rcases hSep with ⟨a, ha, hSem⟩
  exact ⟨a, ha, hSem⟩

/-- Lean wrapper for `prop:full-support-behavioral` on the concrete semantic stack. -/
theorem prop_full_support_behavioral
    (κ : ActionLaw A) (actions : List A)
    (hFull : hasSupportOn κ actions) :
    def_promotion_supporting κ actions := by
  intro a ha
  exact hFull a ha

/--
Legacy zero-collapse one-step posterior concentration witness.

This is the pre-residual Section 6 predicate: a supported separating action admits an
observation that is impossible under the observer-fiber complement while remaining
possible inside the target observer fiber. The active positive-support theorem stack now
uses `oneStepResidualPosteriorConcentrates`; this weaker predicate is retained only for
comparison with the earlier counterexample scaffolding.
-/
def oneStepPosteriorConcentrates
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A) : Prop :=
  ∃ a, a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a ∧
    ∃ o,
      (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ≠ 0 ∧
      (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0 ∧
      U.oneStepComplementPosteriorMass π h a (U.observerFiber ω pstar) o = 0

/--
Concrete one-step residual posterior concentration on the positive-support substrate.

This packages the smoothed observer-fiber witness used in the strong Section 6 route:
the support-floor action, a canonical support-union reference law, the induced softening
scale, strictly positive smoothed class/complement masses at the witness observation, a
strict residual likelihood-ratio contraction, and the resulting one-step residual-odds
decay bound.
-/
def oneStepResidualPosteriorConcentrates
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A) (δ : Rat) : Prop :=
  ∃ a o refLaw ε,
    a ∈ actions ∧
    κ.mass a ≠ 0 ∧
    U.isSeparatingAction π h ω pstar a ∧
    refLaw =
      ConcreteLaw.positiveReferenceLaw
        (supportUnion
          (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar))) ∧
    ε = posteriorDecayFactor δ *
      (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o / 2 ∧
    0 < ε ∧
    0 <
      (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ∧
    0 <
      (U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ∧
    ((U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o /
      (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) < 1 ∧
    U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o ≤
      posteriorDecayFactor δ * U.residualObserverFiberPosteriorOdds π h ω pstar

/--
Hellinger-strengthened form of the one-step residual concentration witness.

In addition to the residual-odds contraction packaged by
`oneStepResidualPosteriorConcentrates`, this records the real nonnegativity of the
smoothed residual likelihood ratio and the square-root Bayes update identity used by the
martingale contraction spine.
-/
def oneStepHellingerResidualPosteriorConcentrates
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A) (δ : Rat) : Prop :=
  ∃ a o refLaw ε,
    a ∈ actions ∧
    κ.mass a ≠ 0 ∧
    U.isSeparatingAction π h ω pstar a ∧
    refLaw =
      ConcreteLaw.positiveReferenceLaw
        (supportUnion
          (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar))) ∧
    ε = posteriorDecayFactor δ *
      (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o / 2 ∧
    0 < ε ∧
    0 <
      (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ∧
    0 <
      (U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ∧
    ((U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o /
      (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) < 1 ∧
    0 ≤
      (((U.softPredictiveLawOutsideClass
          π h a (U.observerFiber ω pstar) refLaw ε).mass o /
        (U.softPredictiveLawInClass
          π h a (U.observerFiber ω pstar) refLaw ε).mass o : Rat) : Real) ∧
    Real.sqrt (U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o : Real) =
      Real.sqrt (U.residualObserverFiberPosteriorOdds π h ω pstar : Real) *
        Real.sqrt
          (((U.softPredictiveLawOutsideClass
              π h a (U.observerFiber ω pstar) refLaw ε).mass o /
            (U.softPredictiveLawInClass
              π h a (U.observerFiber ω pstar) refLaw ε).mass o : Rat) : Real) ∧
    Real.sqrt (U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o : Real) ≤
      Real.sqrt (posteriorDecayFactor δ : Real) *
        Real.sqrt (U.residualObserverFiberPosteriorOdds π h ω pstar : Real) ∧
    U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o ≤
      posteriorDecayFactor δ * U.residualObserverFiberPosteriorOdds π h ω pstar

/--
Upgrade an existing one-step residual concentration witness to the Hellinger-strengthened
form whenever the current residual odds are nonnegative.
-/
theorem oneStepHellingerResidualPosteriorConcentrates_of_concentrates
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A) (δ : Rat)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hConc : oneStepResidualPosteriorConcentrates U π h ω pstar actions κ δ) :
    oneStepHellingerResidualPosteriorConcentrates U π h ω pstar actions κ δ := by
  rcases hConc with
    ⟨a, o, refLaw, ε, ha, hMass, hSep, hRef, hEps, hEpsPos,
      hSoftInPos, hSoftOutPos, hRatioLt, hBound⟩
  have hRatio0 :
      0 ≤
        (((U.softPredictiveLawOutsideClass
            π h a (U.observerFiber ω pstar) refLaw ε).mass o /
          (U.softPredictiveLawInClass
            π h a (U.observerFiber ω pstar) refLaw ε).mass o : Rat) : Real) := by
    exact U.softObserverFiberResidualLikelihoodRatio_nonneg
      π h a ω pstar refLaw ε o (le_of_lt hSoftOutPos) hSoftInPos
  have hSqrt :
      Real.sqrt (U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o : Real) =
        Real.sqrt (U.residualObserverFiberPosteriorOdds π h ω pstar : Real) *
          Real.sqrt
            (((U.softPredictiveLawOutsideClass
                π h a (U.observerFiber ω pstar) refLaw ε).mass o /
              (U.softPredictiveLawInClass
                π h a (U.observerFiber ω pstar) refLaw ε).mass o : Rat) : Real) := by
    exact U.sqrt_softOneStepObserverFiberResidualOdds_eq_sqrt_mul_sqrt_likelihoodRatio
      π h a ω pstar refLaw ε o hOdds0 hSoftInPos
  have hSqrtBound :
      Real.sqrt (U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o : Real) ≤
        Real.sqrt (posteriorDecayFactor δ : Real) *
          Real.sqrt (U.residualObserverFiberPosteriorOdds π h ω pstar : Real) := by
    exact
      U.sqrt_softOneStepObserverFiberResidualOdds_le_sqrt_decayFactor_mul_sqrt_residual
        π h a ω pstar refLaw ε o δ hBound
  exact
    ⟨a, o, refLaw, ε, ha, hMass, hSep, hRef, hEps, hEpsPos,
      hSoftInPos, hSoftOutPos, hRatioLt, hRatio0, hSqrt, hSqrtBound, hBound⟩

/-- Concrete realization of a separating-support schedule by a family of local action laws. -/
def supportScheduleRealized
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κs : Nat → ActionLaw A) (r : Nat → Rat) : Prop :=
  ∀ n, separatingSupportWeight (κs n) actions (U.separatingActionSet π h ω pstar) = r n

/-- Concrete summability proxy on rational schedules, expressed via bounded partial sums. -/
def SummableRatSchedule (r : Nat → Rat) : Prop :=
  ∃ C : Rat, ∀ N, (Finset.range N).sum (fun n => r n) ≤ C

/-- Concrete realization of a scalar schedule on the mass of a designated action. -/
def actionMassScheduleRealized
    (actions : List A) (aStar : A) (κs : Nat → ActionLaw A) (r : Nat → Rat) : Prop :=
  aStar ∈ actions ∧ ∀ n, (κs n).mass aStar = r n

/-- Generic posterior-decay recurrence from an initial odds value and a fixed decay factor. -/
def posteriorDecayRecurrence
    (δ : Rat) (r0 : Rat) (x : Nat → Rat) : Prop :=
  x 0 = r0 ∧ ∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n

/-- Deterministic residual-odds support-floor skeleton retained as a local helper. -/
theorem thm_separating_support_convergence_deterministic
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    {δ : Rat}
    (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ)
    (hDecayPos :
      ∀ ⦃a : A⦄, a ∈ actions → κ.mass a ≠ 0 → U.isSeparatingAction π h ω pstar a →
        ∃ o,
          0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ∧
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    oneStepResidualPosteriorConcentrates U π h ω pstar actions κ δ ∧
      ∀ x : Nat → Rat,
        posteriorDecayRecurrence δ (U.residualObserverFiberPosteriorOdds π h ω pstar) x →
          ∀ N, x N ≤ nStepPosteriorDecayBound δ N
            (U.residualObserverFiberPosteriorOdds π h ω pstar) := by
  rcases exists_supported_action_of_positiveSeparatingSupportFloor
      (κ := κ) (actions := actions) (S := U.separatingActionSet π h ω pstar) hδ hFloor with
    ⟨a, ha, hMass, hSep⟩
  rcases hDecayPos ha hMass hSep with ⟨o, hIn, hOut⟩
  let refLaw :=
    ConcreteLaw.positiveReferenceLaw
      (supportUnion
        (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
        (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)))
  let ε := posteriorDecayFactor δ *
    (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o / 2
  have hEpsPos : 0 < ε := by
    dsimp [ε]
    exact div_pos
      (mul_pos (posteriorDecayFactor_pos_of_pos hδ) hIn)
      (by norm_num)
  have hWitness :=
    U.softObserverFiberResidualWitness_of_zeroOut
      π h a ω pstar o hEpsPos hIn hOut
  have hBound :
      U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o ≤
        posteriorDecayFactor δ * U.residualObserverFiberPosteriorOdds π h ω pstar := by
    simpa [refLaw, ε] using
      U.softOneStepObserverFiberResidualOdds_le_decayBound_of_zeroOut_supportUnion
        π h a ω pstar hδ hOdds0 o hIn hOut
  refine ⟨?_, ?_⟩
  · refine ⟨a, o, refLaw, ε, ha, hMass, hSep, rfl, rfl, hEpsPos, ?_, ?_, ?_, hBound⟩
    · simpa [refLaw] using hWitness.1
    · simpa [refLaw] using hWitness.2.1
    · simpa [refLaw] using hWitness.2.2
  · intro x hx N
    rcases hx with ⟨hx0, hStep⟩
    simpa [hx0] using
      (nStepPosteriorDecayBound_of_stepBound (δ := δ) (x := x) hStep N)

/--
Hellinger-strengthened deterministic support-floor skeleton.

This is the local first-principles replacement for a bare one-step contraction claim: the
same separating-support hypotheses now produce a witness carrying the residual
likelihood-ratio nonnegativity and square-root Bayes update identity needed for the
probabilistic martingale route.
-/
theorem thm_separating_support_convergence_deterministic_hellinger
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    {δ : Rat}
    (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ)
    (hDecayPos :
      ∀ ⦃a : A⦄, a ∈ actions → κ.mass a ≠ 0 → U.isSeparatingAction π h ω pstar a →
        ∃ o,
          0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ∧
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    oneStepHellingerResidualPosteriorConcentrates U π h ω pstar actions κ δ := by
  rcases thm_separating_support_convergence_deterministic
      U π h ω pstar actions κ hδ hOdds0 hFloor hDecayPos with
    ⟨hConc, _hRecurrence⟩
  exact oneStepHellingerResidualPosteriorConcentrates_of_concentrates
    U π h ω pstar actions κ δ hOdds0 hConc

/-- The next finite trajectory prefix is the current prefix plus the realized next event. -/
theorem historyPrefix_succ_eq_appendEvent_get
    (ξ : CountableConcrete.CountHist A O) {n : Nat} (hn : n < ξ.length) :
    CountableConcrete.CountablePrefixMachine.historyPrefix ξ (n + 1) =
      CountableConcrete.appendEvent
        (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n)
        (ξ.get ⟨n, hn⟩) := by
  rw [CountableConcrete.CountablePrefixMachine.historyPrefix,
    CountableConcrete.appendEvent]
  exact (List.take_concat_get' ξ n hn).symm

/-- Any nonterminal trajectory prefix has a realized next action-observation event. -/
theorem exists_historyPrefix_succ_eq_appendEvent
    (ξ : CountableConcrete.CountHist A O) {n : Nat} (hn : n < ξ.length) :
    ∃ a o,
      CountableConcrete.CountablePrefixMachine.historyPrefix ξ (n + 1) =
        CountableConcrete.appendEvent
          (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) (a, o) := by
  refine ⟨(ξ.get ⟨n, hn⟩).1, (ξ.get ⟨n, hn⟩).2, ?_⟩
  simpa using historyPrefix_succ_eq_appendEvent_get (A := A) (O := O) ξ hn

/--
Realized-prefix one-step residual update.

This is the local data needed to derive the old public `hStep`: the next concrete
prefix residual odds are identified with the explicit one-step residual Bayes update at
the current prefix, the update event is the actual next trajectory event, and that
realized update has a zero-out complement observation.
-/
def realizedPrefixResidualUpdateStep
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (ξ : CountableConcrete.CountHist A O) (n : Nat) : Prop :=
  ∃ a o,
    CountableConcrete.CountablePrefixMachine.historyPrefix ξ (n + 1) =
      CountableConcrete.appendEvent
        (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) (a, o) ∧
    U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω pstar =
      U.oneStepObserverFiberResidualOdds π (prefixFullHist ξ n) a ω pstar o ∧
    0 ≤ U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω pstar ∧
    (U.predictiveLawOutsideClass π (prefixFullHist ξ n) a (U.observerFiber ω pstar)).mass o = 0

/-- Realized-prefix update data on every supported trajectory prefix. -/
def HasRealizedPrefixResidualUpdates
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      realizedPrefixResidualUpdateStep U π ω (U.toEncodedProgram pstar) ξ n

/--
Realized-prefix posterior-mass update data.

This is the Bayes algebra immediately below `realizedPrefixResidualUpdateStep`: after
appending the realized action-observation pair, both the observer-fiber class mass and
its complement match the explicit one-step posterior update.
-/
def realizedPrefixPosteriorMassUpdateStep
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (ξ : CountableConcrete.CountHist A O) (n : Nat) : Prop :=
  ∀ a o,
    CountableConcrete.CountablePrefixMachine.historyPrefix ξ (n + 1) =
      CountableConcrete.appendEvent
        (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) (a, o) →
      U.posteriorClassMass π (prefixFullHist ξ (n + 1)) (U.observerFiber ω pstar) =
        U.oneStepClassPosteriorMass π (prefixFullHist ξ n) a
          (U.observerFiber ω pstar) o ∧
      U.complementPosteriorMass π (prefixFullHist ξ (n + 1))
          (U.observerFiber ω pstar) =
        U.oneStepComplementPosteriorMass π (prefixFullHist ξ n) a
          (U.observerFiber ω pstar) o

/-- Realized-prefix posterior-mass update data on every supported trajectory prefix. -/
def HasRealizedPrefixPosteriorMassUpdates
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      realizedPrefixPosteriorMassUpdateStep U π ω (U.toEncodedProgram pstar) ξ n

/--
Nondegenerate split condition for the normalized realized-prefix Bayes update.

The explicit one-step posterior laws divide by the current class and complement masses;
this condition records exactly the nonzero denominators needed for the normalized
class/complement snoc identities at each supported prefix.
-/
def HasRealizedPrefixPositivePosteriorSplit
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      U.posteriorClassMass π (prefixFullHist ξ n)
          (U.observerFiber ω (U.toEncodedProgram pstar)) ≠ 0 ∧
      U.complementPosteriorMass π (prefixFullHist ξ n)
          (U.observerFiber ω (U.toEncodedProgram pstar)) ≠ 0

/--
At a supported trajectory prefix with a nondegenerate class/complement split, the
normalized posterior-mass update follows from the raw concrete snoc Bayes algebra.
-/
theorem realizedPrefixPosteriorMassUpdateStep_of_positiveSplit
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    {ξ : CountableConcrete.CountHist A O} {n : Nat}
    (hξ : ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support)
    (hn : n < T)
    (hSplit :
      U.posteriorClassMass π (prefixFullHist ξ n)
          (U.observerFiber ω (U.toEncodedProgram pstar)) ≠ 0 ∧
      U.complementPosteriorMass π (prefixFullHist ξ n)
          (U.observerFiber ω (U.toEncodedProgram pstar)) ≠ 0) :
    realizedPrefixPosteriorMassUpdateStep U π ω (U.toEncodedProgram pstar) ξ n := by
  classical
  intro a o hPrefix
  let hp : CountableConcrete.CountHist A O :=
    CountableConcrete.CountablePrefixMachine.historyPrefix ξ n
  let h : Hist A O hp.length := ConcreteBridge.histOfCountHist hp
  let C : PredSet U.Program := U.observerFiber ω (U.toEncodedProgram pstar)
  have hActionSupp :
      a ∈ (toCountablePolicy π hπ hp).support :=
    trajectoryLaw_realized_action_mem_support
      (U := U.toCountablePrefixMachine hSem)
      (π := toCountablePolicy π hπ)
      (penv := U.toCountableProgram hSem penv)
      (T := T) (n := n) (ξ := ξ) hξ hn hPrefix
  have hAction : (π hp.length h).mass a ≠ 0 :=
    (mem_support_toCountablePolicy_iff
      (π := π) (hπ := hπ) (h := hp) (a := a)).1 hActionSupp
  have hCurr : prefixFullHist ξ n = asFullHist h := rfl
  have hNext :
      prefixFullHist ξ (n + 1) = asFullHist (snoc h (a, o)) := by
    unfold prefixFullHist h hp
    rw [hPrefix]
    have hCount :
        CountableConcrete.appendEvent
            (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) (a, o) =
          ConcreteBridge.countHistOfHist
            (snoc
              (ConcreteBridge.histOfCountHist
                (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n)) (a, o)) := by
      simp [ConcreteBridge.countHistOfHist_snoc,
        ConcreteBridge.countHistOfHist_histOfCountHist]
    rw [hCount]
    exact
      ConcreteBridge.asFullHist_histOfCountHist_countHistOfHist
        (snoc (ConcreteBridge.histOfCountHist
          (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n)) (a, o))
  have hClass : U.posteriorClassMass π (asFullHist h) C ≠ 0 := by
    simpa [C, hCurr] using hSplit.1
  have hComp : U.complementPosteriorMass π (asFullHist h) C ≠ 0 := by
    simpa [C, hCurr] using hSplit.2
  have hClassUpdate :
      U.posteriorClassMass π (asFullHist (snoc h (a, o))) C =
        U.oneStepClassPosteriorMass π (asFullHist h) a C o :=
    U.posteriorClassMass_snoc_eq_oneStepClassPosteriorMass_of_split_ne_zero
      π hπN hSemN h a o C hAction hClass hComp
  have hCompUpdate :
      U.complementPosteriorMass π (asFullHist (snoc h (a, o))) C =
        U.oneStepComplementPosteriorMass π (asFullHist h) a C o :=
    U.complementPosteriorMass_snoc_eq_oneStepComplementPosteriorMass_of_split_ne_zero
      π hπN hSemN h a o C hAction hClass hComp
  constructor
  · simpa [C, hCurr, hNext] using hClassUpdate
  · simpa [C, hCurr, hNext] using hCompUpdate

/--
Trajectory-level constructor for normalized posterior-mass updates from concrete snoc
Bayes algebra plus nondegenerate class/complement split on supported prefixes.
-/
theorem hasRealizedPrefixPosteriorMassUpdates_of_positiveSplit
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hSplit :
      HasRealizedPrefixPositivePosteriorSplit U π hπ hSem penv pstar ω T) :
    HasRealizedPrefixPosteriorMassUpdates U π hπ hSem penv pstar ω T := by
  intro ξ hξ n hn
  exact
    realizedPrefixPosteriorMassUpdateStep_of_positiveSplit
      U π hπ hπN hSem hSemN penv pstar ω T hξ hn
      (hSplit ξ hξ n hn)

/-- Current-prefix residual odds are nonnegative on every supported trajectory prefix. -/
def HasRealizedPrefixResidualNonneg
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      0 ≤ U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
        (U.toEncodedProgram pstar)

/-- Concrete finite-law assumptions imply realized-prefix residual nonnegativity. -/
theorem hasRealizedPrefixResidualNonneg_of_concrete
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) :
    HasRealizedPrefixResidualNonneg U π hπ hSem penv pstar ω T := by
  intro ξ _hξ n _hn
  exact
    U.residualObserverFiberPosteriorOdds_nonneg hCodes π hπ hπN hSem hSemN
      (prefixFullHist ξ n) ω (U.toEncodedProgram pstar)

/--
The realized next observation is outside-class impossible at every supported trajectory
prefix. This is the semantic zero-out input needed by the residual contraction lemma.
-/
def HasRealizedPrefixOutsideZeroOuts
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      ∀ a o,
        CountableConcrete.CountablePrefixMachine.historyPrefix ξ (n + 1) =
          CountableConcrete.appendEvent
            (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) (a, o) →
        (U.predictiveLawOutsideClass π (prefixFullHist ξ n) a
            (U.observerFiber ω (U.toEncodedProgram pstar))).mass o = 0

/--
Support-level semantic zero-out for the true environment.

This is the exact bridge needed to turn an existential zero-out witness into a realized
trajectory statement: every observation that the true environment can emit after a
supported prefix/action is outside-class impossible for the observer-fiber complement.
-/
def HasTrueEnvironmentSupportOutsideZeroOuts
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      ∀ a o,
        o ∈ ((U.toCountablePrefixMachine hSem).programSemantics
            (U.toCountableProgram hSem penv)
            (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) a).support →
        (U.predictiveLawOutsideClass π (prefixFullHist ξ n) a
            (U.observerFiber ω (U.toEncodedProgram pstar))).mass o = 0

/--
Concrete version of true-environment support-level zero-out, stated against the finite
kernel mass at the concrete realized prefix.
-/
def HasTrueEnvironmentConcreteSupportOutsideZeroOuts
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      ∀ a o,
        (U.programSemantics penv (prefixFullHist ξ n).1
            (prefixFullHist ξ n).2 a).mass o ≠ 0 →
        (U.predictiveLawOutsideClass π (prefixFullHist ξ n) a
            (U.observerFiber ω (U.toEncodedProgram pstar))).mass o = 0

/--
If every program outside a class assigns zero mass to an observation, then the
posterior predictive mixture over the class complement assigns zero mass to that
observation. This is the finite-mixture algebra behind the realized zero-out bridge.
-/
theorem ConcretePrefixMachine.predictiveLawOutsideClass_mass_eq_zero_of_complement_kernel_zero
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O)
    (hZero :
      ∀ p : U.Program, ¬ C p →
        (programObsLaw h a (U.toEncodedProgram p)).mass o = 0) :
    (U.predictiveLawOutsideClass π h a C).mass o = 0 := by
  classical
  have hTerm :
      ∀ p : U.Program,
        (U.posteriorOutsideClass π h C).mass p *
          (programObsLaw h a (U.toEncodedProgram p)).mass o = 0 := by
    intro p
    by_cases hCp : C p
    · have hOutsideMass :
          (U.posteriorOutsideClass π h C).mass p = 0 := by
        simp [ConcretePrefixMachine.posteriorOutsideClass,
          ConcretePrefixMachine.normalizeOnPrograms, ConcreteLaw.restrict, hCp]
      simp [hOutsideMass]
    · simp [hZero p hCp]
  have hList :
      ∀ xs : List U.Program,
        listWeightedSum xs
            (fun p =>
              (U.posteriorOutsideClass π h C).mass p *
                (programObsLaw h a (U.toEncodedProgram p)).mass o) = 0 := by
    intro xs
    induction xs with
    | nil =>
        simp [listWeightedSum]
    | cons p ps ih =>
        rw [listWeightedSum_cons, hTerm p, ih]
        ring
  simpa [ConcretePrefixMachine.predictiveLawOutsideClass, mixLaw] using
    hList (U.posteriorOutsideClass π h C).support

/--
Program-level support separation for the true environment.

At each supported trajectory prefix, every observation the true environment can emit is
assigned zero mass by every program outside the target observer fiber. Unlike the older
existential zero-out condition, this is stated directly against the realized
environment's support.
-/
def HasTrueEnvironmentObserverFiberSupportSeparation
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      ∀ a o,
        (U.programSemantics penv (prefixFullHist ξ n).1
            (prefixFullHist ξ n).2 a).mass o ≠ 0 →
        ∀ p : U.Program,
          ¬ U.observerFiber ω (U.toEncodedProgram pstar) p →
            (programObsLaw (prefixFullHist ξ n) a
              (U.toEncodedProgram p)).mass o = 0

/--
Observer-fiber support separation implies concrete true-environment support-level
zero-out for the posterior complement predictive law.
-/
theorem hasTrueEnvironmentConcreteSupportOutsideZeroOuts_of_observerFiberSupportSeparation
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hSep :
      HasTrueEnvironmentObserverFiberSupportSeparation U π hπ hSem penv pstar ω T) :
    HasTrueEnvironmentConcreteSupportOutsideZeroOuts U π hπ hSem penv pstar ω T := by
  intro ξ hξ n hn a o hObs
  exact
    U.predictiveLawOutsideClass_mass_eq_zero_of_complement_kernel_zero
      π (prefixFullHist ξ n) a
      (U.observerFiber ω (U.toEncodedProgram pstar)) o
      (fun p hp =>
        hSep ξ hξ n hn a o hObs p hp)

/-- Concrete true-environment support zero-out implies its countable support form. -/
theorem hasTrueEnvironmentSupportOutsideZeroOuts_of_concreteSupport
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hConcrete :
      HasTrueEnvironmentConcreteSupportOutsideZeroOuts U π hπ hSem penv pstar ω T) :
    HasTrueEnvironmentSupportOutsideZeroOuts U π hπ hSem penv pstar ω T := by
  intro ξ hξ n hn a o hObsSupp
  have hObsSupp' := hObsSupp
  rw [U.programSemantics_toCountableProgram_eq hSem penv] at hObsSupp'
  have hMassNe :
      (U.programSemantics penv
        (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n).length
        (ConcreteBridge.histOfCountHist
          (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n)) a).mass o ≠ 0 :=
    (mem_support_toCountableKernel_iff
      (κ := U.programSemantics penv)
      (hκ := by
        simpa [ConcretePrefixMachine.programSemantics] using hSem penv.1 penv.2)
      (h := CountableConcrete.CountablePrefixMachine.historyPrefix ξ n)
      (a := a) (o := o)).1 hObsSupp'
  simpa [prefixFullHist] using hConcrete ξ hξ n hn a o hMassNe

/--
Observer-fiber program-level support separation implies the countable
true-environment support-level zero-out condition.
-/
theorem hasTrueEnvironmentSupportOutsideZeroOuts_of_observerFiberSupportSeparation
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hSep :
      HasTrueEnvironmentObserverFiberSupportSeparation U π hπ hSem penv pstar ω T) :
    HasTrueEnvironmentSupportOutsideZeroOuts U π hπ hSem penv pstar ω T :=
  hasTrueEnvironmentSupportOutsideZeroOuts_of_concreteSupport
    U π hπ hSem penv pstar ω T
    (hasTrueEnvironmentConcreteSupportOutsideZeroOuts_of_observerFiberSupportSeparation
      U π hπ hSem penv pstar ω T hSep)

/--
Trajectory support turns true-environment support-level zero-out into realized
outside-class zero-out observations.
-/
theorem hasRealizedPrefixOutsideZeroOuts_of_trueEnvironmentSupport
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hSupportZero :
      HasTrueEnvironmentSupportOutsideZeroOuts U π hπ hSem penv pstar ω T) :
    HasRealizedPrefixOutsideZeroOuts U π hπ hSem penv pstar ω T := by
  intro ξ hξ n hn a o hPrefix
  have hObsSupp :
      o ∈ ((U.toCountablePrefixMachine hSem).programSemantics
          (U.toCountableProgram hSem penv)
          (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) a).support :=
    trajectoryLaw_realized_observation_mem_support
      (U := U.toCountablePrefixMachine hSem)
      (π := toCountablePolicy π hπ)
      (penv := U.toCountableProgram hSem penv)
      (T := T) (n := n) (ξ := ξ) hξ hn hPrefix
  exact hSupportZero ξ hξ n hn a o hObsSupp

/--
Program-level support separation against the true environment implies realized-prefix
outside-class zero-out observations.
-/
theorem hasRealizedPrefixOutsideZeroOuts_of_observerFiberSupportSeparation
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hSep :
      HasTrueEnvironmentObserverFiberSupportSeparation U π hπ hSem penv pstar ω T) :
    HasRealizedPrefixOutsideZeroOuts U π hπ hSem penv pstar ω T :=
  hasRealizedPrefixOutsideZeroOuts_of_trueEnvironmentSupport
    U π hπ hSem penv pstar ω T
    (hasTrueEnvironmentSupportOutsideZeroOuts_of_observerFiberSupportSeparation
      U π hπ hSem penv pstar ω T hSep)

/--
Convert posterior-mass snoc updates plus realized zero-out data into the residual-update
step consumed by `prefixwiseResidualDecay_of_realizedPrefixResidualUpdates`.
-/
theorem realizedPrefixResidualUpdateStep_of_posteriorMassUpdate
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (ξ : CountableConcrete.CountHist A O) (n : Nat)
    (hMass : realizedPrefixPosteriorMassUpdateStep U π ω pstar ξ n)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π
      (prefixFullHist ξ n) ω pstar)
    (hZero :
      ∀ a o,
        CountableConcrete.CountablePrefixMachine.historyPrefix ξ (n + 1) =
          CountableConcrete.appendEvent
            (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) (a, o) →
        (U.predictiveLawOutsideClass π (prefixFullHist ξ n) a
            (U.observerFiber ω pstar)).mass o = 0)
    (hEvent :
      ∃ a o,
        CountableConcrete.CountablePrefixMachine.historyPrefix ξ (n + 1) =
          CountableConcrete.appendEvent
            (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n) (a, o)) :
    realizedPrefixResidualUpdateStep U π ω pstar ξ n := by
  classical
  rcases hEvent with ⟨a, o, hPrefix⟩
  rcases hMass a o hPrefix with ⟨hClass, hComp⟩
  refine ⟨a, o, hPrefix, ?_, hOdds0, hZero a o hPrefix⟩
  exact
    U.residualObserverFiberPosteriorOdds_eq_oneStepObserverFiberResidualOdds_of_posteriorMass_eq
      π (prefixFullHist ξ (n + 1)) (prefixFullHist ξ n) a ω pstar o hClass hComp

/--
Trajectory-level constructor for realized residual updates.

This removes `hStep` from the public convergence surface one level further: it is enough
to verify concrete snoc posterior-mass updates, residual nonnegativity, and the realized
outside-class zero-out event on supported trajectories.
-/
theorem hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hMass :
      HasRealizedPrefixPosteriorMassUpdates U π hπ hSem penv pstar ω T)
    (hOdds :
      HasRealizedPrefixResidualNonneg U π hπ hSem penv pstar ω T)
    (hZero :
      HasRealizedPrefixOutsideZeroOuts U π hπ hSem penv pstar ω T) :
    HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T := by
  intro ξ hξ n hn
  have hξLen : ξ.length = T := by
    simpa using
      trajectoryLaw_mem_support_length
        (U := U.toCountablePrefixMachine hSem)
        (π := toCountablePolicy π hπ)
        (penv := U.toCountableProgram hSem penv)
        (T := T) hξ
  have hnLen : n < ξ.length := by
    simpa [hξLen] using hn
  exact
    realizedPrefixResidualUpdateStep_of_posteriorMassUpdate
      U π ω (U.toEncodedProgram pstar) ξ n
      (hMass ξ hξ n hn) (hOdds ξ hξ n hn) (hZero ξ hξ n hn)
      (exists_historyPrefix_succ_eq_appendEvent (A := A) (O := O) ξ hnLen)

/--
Constructor with residual nonnegativity discharged from the concrete finite-law
assumptions.
-/
theorem hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_zeroOuts
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hMass :
      HasRealizedPrefixPosteriorMassUpdates U π hπ hSem penv pstar ω T)
    (hZero :
      HasRealizedPrefixOutsideZeroOuts U π hπ hSem penv pstar ω T) :
    HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T :=
  hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates
    U π hπ hSem penv pstar ω T hMass
    (hasRealizedPrefixResidualNonneg_of_concrete
      U hCodes π hπ hπN hSem hSemN penv pstar ω T)
    hZero

/--
Constructor using the true-environment support-level zero-out bridge instead of taking
realized zero-out observations directly.
-/
theorem hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_trueEnvironmentSupport
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hMass :
      HasRealizedPrefixPosteriorMassUpdates U π hπ hSem penv pstar ω T)
    (hSupportZero :
      HasTrueEnvironmentSupportOutsideZeroOuts U π hπ hSem penv pstar ω T) :
    HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T :=
  hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_zeroOuts
    U hCodes π hπ hπN hSem hSemN penv pstar ω T hMass
    (hasRealizedPrefixOutsideZeroOuts_of_trueEnvironmentSupport
      U π hπ hSem penv pstar ω T hSupportZero)

/--
Constructor using concrete true-environment support-level zero-out at realized prefixes.
-/
theorem hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_concreteEnvironmentSupport
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hMass :
      HasRealizedPrefixPosteriorMassUpdates U π hπ hSem penv pstar ω T)
    (hConcreteZero :
      HasTrueEnvironmentConcreteSupportOutsideZeroOuts U π hπ hSem penv pstar ω T) :
    HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T :=
  hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_trueEnvironmentSupport
    U hCodes π hπ hπN hSem hSemN penv pstar ω T hMass
    (hasTrueEnvironmentSupportOutsideZeroOuts_of_concreteSupport
      U π hπ hSem penv pstar ω T hConcreteZero)

/--
Constructor from posterior-mass snoc updates plus program-level support separation
against the true environment. This is the bridge from realized environment support to
the residual update package consumed by the public Section 6 probabilistic theorem.
-/
theorem hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_observerFiberSupportSeparation
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (T : Nat)
    (hMass :
      HasRealizedPrefixPosteriorMassUpdates U π hπ hSem penv pstar ω T)
    (hSep :
      HasTrueEnvironmentObserverFiberSupportSeparation U π hπ hSem penv pstar ω T) :
    HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T :=
  hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_concreteEnvironmentSupport
    U hCodes π hπ hπN hSem hSemN penv pstar ω T hMass
    (hasTrueEnvironmentConcreteSupportOutsideZeroOuts_of_observerFiberSupportSeparation
      U π hπ hSem penv pstar ω T hSep)

/--
Derive the trajectory-level `hStep` recurrence from realized one-step prefix updates.
-/
theorem prefixwiseResidualDecay_of_realizedPrefixResidualUpdates
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hUpdates : HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T) :
    ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
      ∀ n, n < T →
        U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
            (U.toEncodedProgram pstar) ≤
          posteriorDecayFactor δ *
            U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
              (U.toEncodedProgram pstar) := by
  intro ξ hξ n hn
  rcases hUpdates ξ hξ n hn with ⟨a, o, _hPrefix, hUpdate, hOdds0, hOutZero⟩
  rw [hUpdate]
  exact
    U.oneStepObserverFiberResidualOdds_le_decayBound_of_outside_zero
      π (prefixFullHist ξ n) a ω (U.toEncodedProgram pstar) o δ hOdds0 hOutZero

/-- Lean wrapper for `thm:exploration-floor-behavioral` on the concrete semantic stack. -/
theorem thm_exploration_floor_behavioral
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    (hFull : hasSupportOn κ actions)
    (hSupport : def_kernel_sep_condition U π h ω pstar actions κ) :
    def_promotion_supporting κ actions ∧
      ∃ a, a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a := by
  exact ⟨hFull, hSupport⟩

/-- Deterministic residual-odds rate skeleton retained as a local helper. -/
theorem thm_separating_support_rate_deterministic
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    {δ : Rat}
    (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ)
    (hDecayPos :
      ∀ ⦃a : A⦄, a ∈ actions → κ.mass a ≠ 0 → U.isSeparatingAction π h ω pstar a →
        ∃ o,
          0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ∧
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    oneStepResidualPosteriorConcentrates U π h ω pstar actions κ δ ∧
      ∀ x : Nat → Rat,
        posteriorDecayRecurrence δ (U.residualObserverFiberPosteriorOdds π h ω pstar) x →
          ∀ N, x N ≤ posteriorRateFactorFromFloor N *
            U.residualObserverFiberPosteriorOdds π h ω pstar := by
  rcases thm_separating_support_convergence_deterministic
      U π h ω pstar actions κ hδ hOdds0 hFloor hDecayPos with
    ⟨hConc, _hRecurrence⟩
  refine ⟨hConc, ?_⟩
  intro x hx N
  rcases hx with ⟨hx0, hStep⟩
  exact U.residualRateBound_of_positiveFloor π h ω pstar hδ hOdds0 x hx0 hStep N

/-- Deterministic finite-time residual-odds skeleton retained as a local helper. -/
theorem cor_separating_support_finite_time_deterministic
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    {δ : Rat}
    (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ)
    (hDecayPos :
      ∀ ⦃a : A⦄, a ∈ actions → κ.mass a ≠ 0 → U.isSeparatingAction π h ω pstar a →
        ∃ o,
          0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ∧
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0)
    {N : Nat} {ε : Rat}
    (hε : posteriorRateFactorFromFloor N * U.residualObserverFiberPosteriorOdds π h ω pstar ≤ ε) :
    oneStepResidualPosteriorConcentrates U π h ω pstar actions κ δ ∧
      ∀ x : Nat → Rat,
        posteriorDecayRecurrence δ (U.residualObserverFiberPosteriorOdds π h ω pstar) x →
          x N ≤ ε := by
  rcases thm_separating_support_rate_deterministic
      U π h ω pstar actions κ hδ hOdds0 hFloor hDecayPos with
    ⟨hConc, hRate⟩
  refine ⟨hConc, ?_⟩
  intro x hx
  have hNx := hRate x hx N
  exact le_trans hNx hε

/--
Hypothesis-transport wrapper for `thm:separating-support-convergence` on the
probabilistic Section 6 stack.

This declaration upgrades a supportwise residual one-step contraction witness on
realized trajectories to an almost-sure statement under `trajectoryLaw`. In the
current countable-probabilistic track, the witness
`HasSupportwiseResidualContractionWitness` is still an explicit hypothesis of
this theorem rather than a result derived internally from the deterministic
`ConcretePrefixMachine` soft-substrate machinery; the deterministic first-principles
derivation remains exposed separately as
`thm_separating_support_convergence_deterministic`.
-/
theorem thm_separating_support_convergence_of_witness
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ n, n < T →
        U.residualObserverFiberProcess π ω pstar (n + 1) ξ ≤
          CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ *
            U.residualObserverFiberProcess π ω pstar n ξ := by
  have hSupportwise :
      U.HasSupportwiseResidualRecurrence π penv ω pstar δ T :=
    U.hasSupportwiseResidualRecurrence_of_witness π penv ω pstar δ T hWitness
  exact U.ae_residualObserverFiberRecurrence_of_supportwise π penv ω pstar δ T
    hSupportwise

/--
Bridged probabilistic wrapper for `thm:separating-support-convergence` on the
concrete Section 6 substrate.

This is the canonical paper-facing theorem name on the probabilistic track. Its contribution
is the bridge: it derives the deterministic per-trajectory per-step residual-odds
contraction from realized prefix update data, transports that recurrence to an almost-sure
statement under `trajectoryLaw`, and constructs the supportwise contraction witness via
`hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay`.

**Standing assumption.** The theorem now takes `hUpdates`, not `hStep`: each supported
trajectory prefix must identify its next residual odds with the explicit one-step residual
Bayes update for the realized local event, and that local event must be a zero-out
complement observation. The proof derives the old `hStep` recurrence internally from
`prefixwiseResidualDecay_of_realizedPrefixResidualUpdates`.
-/
theorem thm_separating_support_convergence
    {A : Type u} {O : Type v}
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hUpdates : HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ n, n < T →
        (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar) (n + 1) ξ ≤
          CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ *
            (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) n ξ := by
  let Uc := U.toCountablePrefixMachine hSem
  let πc := toCountablePolicy π hπ
  let penvc := U.toCountableProgram hSem penv
  let ωc := U.liftObserver ω
  let pstarc := U.toCountableEncodedProgram hSem pstar
  have hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar) :=
    prefixwiseResidualDecay_of_realizedPrefixResidualUpdates
      U π hπ hSem penv pstar ω δ T hUpdates
  have hWitness :
      Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pstarc δ T := by
    simpa [Uc, πc, penvc, ωc, pstarc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv pstar ω δ T hStep
  simpa [Uc, πc, penvc, ωc, pstarc] using
    thm_separating_support_convergence_of_witness Uc πc penvc ωc pstarc δ T hWitness

/--
End-to-end convergence wrapper from posterior-mass updates plus true-environment
observer-fiber support separation. This exposes the realized zero-out bridge at the
public theorem level: true-environment-supported observations are proved to be
outside-fiber impossible before the supportwise contraction witness is constructed.
-/
theorem thm_separating_support_convergence_of_observerFiberSupportSeparation
    {A : Type u} {O : Type v}
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hMass :
      HasRealizedPrefixPosteriorMassUpdates U π hπ hSem penv pstar ω T)
    (hSep :
      HasTrueEnvironmentObserverFiberSupportSeparation U π hπ hSem penv pstar ω T) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ n, n < T →
        (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar) (n + 1) ξ ≤
          CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ *
            (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) n ξ :=
  thm_separating_support_convergence U hCodes π hπ hπN hSem hSemN
    penv pstar ω δ T
    (hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_observerFiberSupportSeparation
      U hCodes π hπ hπN hSem hSemN penv pstar ω T hMass hSep)

/-- Internal witness-transport helper for `thm:separating-support-rate`. -/
theorem thm_separating_support_rate_of_witness
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ N, N ≤ T →
        U.residualObserverFiberProcess π ω pstar N ξ ≤
          CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N *
            U.initialResidualObserverFiberOdds π ω pstar := by
  have hSupportwise :
      U.HasSupportwiseResidualRecurrence π penv ω pstar δ T :=
    U.hasSupportwiseResidualRecurrence_of_witness π penv ω pstar δ T hWitness
  exact U.ae_residualObserverFiberRateBound_of_supportwise π penv ω pstar δ T
    hSupportwise

/--
Bridged probabilistic wrapper for `thm:separating-support-rate` on the first-principles
Section 6 stack.
-/
theorem thm_separating_support_rate
    {A : Type u} {O : Type v}
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hUpdates : HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ N, N ≤ T →
        (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar) N ξ ≤
          CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N *
            (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) := by
  let Uc := U.toCountablePrefixMachine hSem
  let πc := toCountablePolicy π hπ
  let penvc := U.toCountableProgram hSem penv
  let ωc := U.liftObserver ω
  let pstarc := U.toCountableEncodedProgram hSem pstar
  have hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar) :=
    prefixwiseResidualDecay_of_realizedPrefixResidualUpdates
      U π hπ hSem penv pstar ω δ T hUpdates
  have hWitness :
      Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pstarc δ T := by
    simpa [Uc, πc, penvc, ωc, pstarc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv pstar ω δ T hStep
  simpa [Uc, πc, penvc, ωc, pstarc] using
    thm_separating_support_rate_of_witness Uc πc penvc ωc pstarc δ T hWitness

/--
End-to-end rate wrapper from posterior-mass updates plus true-environment
observer-fiber support separation.
-/
theorem thm_separating_support_rate_of_observerFiberSupportSeparation
    {A : Type u} {O : Type v}
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hMass :
      HasRealizedPrefixPosteriorMassUpdates U π hπ hSem penv pstar ω T)
    (hSep :
      HasTrueEnvironmentObserverFiberSupportSeparation U π hπ hSem penv pstar ω T) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ N, N ≤ T →
        (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar) N ξ ≤
          CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N *
            (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
              (toCountablePolicy π hπ) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) :=
  thm_separating_support_rate U hCodes π hπ hπN hSem hSemN
    penv pstar ω δ T
    (hasRealizedPrefixResidualUpdates_of_posteriorMassUpdates_observerFiberSupportSeparation
      U hCodes π hπ hπN hSem hSemN penv pstar ω T hMass hSep)

/-- Internal witness-transport helper for `cor:separating-support-finite-time`. -/
theorem cor_separating_support_finite_time_of_witness
    {A : Type u} {O : Type v}
    [Encodable A] [Encodable O]
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableConcrete.CountableEncodedProgram A O))
    (pstar : CountableConcrete.CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T)
    (hInitTop : U.initialResidualObserverFiberOdds π ω pstar ≠ ⊤) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ N, N ≤ T →
        (1 + CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N *
          U.initialResidualObserverFiberOdds π ω pstar)⁻¹ ≤
          U.observerFiberPosteriorShareProcess π ω pstar N ξ := by
  filter_upwards [thm_separating_support_rate_of_witness U π penv ω pstar δ T hWitness]
    with ξ hRate N hN
  have hBound := hRate N hN
  have hFactorTop :
      CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N ≠ ⊤ := by
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hEpsTop :
      CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N *
        U.initialResidualObserverFiberOdds π ω pstar ≠ ⊤ := by
    intro hTop
    rcases (ENNReal.mul_eq_top).1 hTop with hCase | hCase
    · exact hInitTop hCase.2
    · exact hFactorTop hCase.1
  have hLower :=
    CountableConcrete.CountablePrefixMachine.posteriorShareFromResidual_lowerBound_of_le
      hEpsTop hBound
  simpa [CountableConcrete.CountablePrefixMachine.observerFiberPosteriorShareProcess,
    CountableConcrete.CountablePrefixMachine.observerFiberPosteriorShare,
    CountableConcrete.CountablePrefixMachine.residualObserverFiberProcess_zero_eq_initial] using
    hLower

/--
Bridged probabilistic wrapper for `cor:separating-support-finite-time` on the
first-principles Section 6 stack.
-/
theorem cor_separating_support_finite_time
    {A : Type u} {O : Type v}
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    [Encodable A] [Encodable O]
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hUpdates : HasRealizedPrefixResidualUpdates U π hπ hSem penv pstar ω T)
    (hInitTop :
      (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
          (toCountablePolicy π hπ) (U.liftObserver ω)
          (U.toCountableEncodedProgram hSem pstar) ≠ ⊤) :
    ∀ᵐ ξ ∂((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).toMeasure,
      ∀ N, N ≤ T →
        (1 + CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ ^ N *
          (U.toCountablePrefixMachine hSem).initialResidualObserverFiberOdds
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar))⁻¹ ≤
          (U.toCountablePrefixMachine hSem).observerFiberPosteriorShareProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar) N ξ := by
  let Uc := U.toCountablePrefixMachine hSem
  let πc := toCountablePolicy π hπ
  let penvc := U.toCountableProgram hSem penv
  let ωc := U.liftObserver ω
  let pstarc := U.toCountableEncodedProgram hSem pstar
  have hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar) :=
    prefixwiseResidualDecay_of_realizedPrefixResidualUpdates
      U π hπ hSem penv pstar ω δ T hUpdates
  have hWitness :
      Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pstarc δ T := by
    simpa [Uc, πc, penvc, ωc, pstarc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv pstar ω δ T hStep
  simpa [Uc, πc, penvc, ωc, pstarc] using
    cor_separating_support_finite_time_of_witness
      Uc πc penvc ωc pstarc δ T hWitness hInitTop

/-- Lean wrapper for `thm:semantic-convergence` on the concrete semantic stack. -/
theorem thm_semantic_convergence
    (U : ConcretePrefixMachine A O)
    (actions : List A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ actions)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar actions (def_semantic_rule actions) := by
  refine ⟨a, ha, ?_, hSep⟩
  change (def_semantic_rule actions).mass a ≠ 0
  simp [def_semantic_rule, fullSupportActionLaw, ha]

/-- Lean wrapper for `thm:kernel-semantic-convergence` on the concrete semantic stack. -/
theorem thm_kernel_semantic_convergence
    (U : ConcretePrefixMachine A O)
    (refLaw : ActionLaw A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ refLaw.support)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar refLaw.support (def_kernel_semantic_rule refLaw) := by
  refine ⟨a, ha, ?_, hSep⟩
  change (def_kernel_semantic_rule refLaw).mass a ≠ 0
  simp [def_kernel_semantic_rule, fullSupportActionLaw, ha]

/-- Lean wrapper for `cor:compact-action-kernel` on the compact kernel stack. -/
theorem cor_compact_action_kernel
    {C : Type w} {X : Type x}
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]
    (S : CompactKernel.Setup C X)
    {β γ η r : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 < γ) (hη : 0 < η) (hr : 0 < r)
    (B : CompactKernel.BoundedKernelScore C X)
    (hB_nonneg : ∀ z : C × X, 0 ≤ B.prodFun z)
    (hB_le_one : ∀ z : C × X, B.prodFun z ≤ 1)
    (c : C)
    (hscore_cont : Continuous fun a : X => B.prodFun (c, a))
    (hlocal :
      ∀ a a' : X, dist a a' < r →
        |B.prodFun (c, a) - B.prodFun (c, a')| ≤ η / 2)
    {a0 : X} (hSep : η ≤ B.prodFun (c, a0)) :
    0 < η / 2 ∧
      CompactKernel.ballMassFloor S.actionRef r ≠ 0 ∧
      MeasurableSet {a : X | η / 2 ≤ B.prodFun (c, a)} ∧
      ENNReal.ofReal (Real.exp (-(β / γ))) *
          (S.classRef {c} * CompactKernel.ballMassFloor S.actionRef r) ≤
        CompactKernel.gibbsMeasure S.reference β γ B
          ({c} ×ˢ {a : X | η / 2 ≤ B.prodFun (c, a)}) := by
  let actionSet : Set X := {a : X | η / 2 ≤ B.prodFun (c, a)}
  have hSepFloor :
      0 < η / 2 ∧
        CompactKernel.ballMassFloor S.actionRef r ≠ 0 ∧
        MeasurableSet actionSet ∧
        CompactKernel.ballMassFloor S.actionRef r ≤ S.actionRef actionSet := by
    simpa [actionSet] using
      (prop_compact_action_kernel_separation
        S.actionRef S.action_fullSupport hη hr hscore_cont hlocal hSep)
  rcases hSepFloor with ⟨heta_half_pos, hfloor_ne, hmeas, hmass⟩
  have hGibbs :
      ENNReal.ofReal (Real.exp (-(β / γ))) *
          (S.classRef {c} * S.actionRef actionSet) ≤
        CompactKernel.gibbsMeasure S.reference β γ B ({c} ×ˢ actionSet) :=
    prop_kernel_promotion_support_compact S hβ hγ B hB_nonneg hB_le_one c hmeas
  have hclass :
      S.classRef {c} * CompactKernel.ballMassFloor S.actionRef r ≤
        S.classRef {c} * S.actionRef actionSet :=
    mul_le_mul_right hmass (S.classRef {c})
  have hfloor_to_gibbs :
      ENNReal.ofReal (Real.exp (-(β / γ))) *
          (S.classRef {c} * CompactKernel.ballMassFloor S.actionRef r) ≤
      ENNReal.ofReal (Real.exp (-(β / γ))) *
          (S.classRef {c} * S.actionRef actionSet) :=
    mul_le_mul_right hclass (ENNReal.ofReal (Real.exp (-(β / γ))))
  exact ⟨heta_half_pos, hfloor_ne, by simpa [actionSet] using hmeas,
    by simpa [actionSet] using hfloor_to_gibbs.trans hGibbs⟩

/-- Lean wrapper for `cor:finite-maximin` on the concrete semantic stack. -/
theorem cor_finite_maximin
    (U : ConcretePrefixMachine A O)
    (actions : List A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ actions)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    def_kernel_sep_condition U π h ω pstar actions (def_semantic_rule actions) := by
  refine ⟨a, ha, ?_, hSep⟩
  change (def_semantic_rule actions).mass a ≠ 0
  simp [def_semantic_rule, fullSupportActionLaw, ha]

/-- Lean wrapper for `cor:support-necessary` on the concrete semantic stack. -/
theorem cor_support_necessary
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    (hNo :
      ¬ ∃ a, a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a) :
    ∀ {δ : Rat}, 0 < δ →
      ¬ hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ := by
  intro δ hδ hFloor
  rcases ConcretePrefixMachine.exists_supported_action_of_positiveSeparatingSupportFloor
      (κ := κ) (actions := actions) (S := U.separatingActionSet π h ω pstar) hδ hFloor with
    ⟨a, ha, hMass, hSep⟩
  exact hNo ⟨a, ha, hMass, hSep⟩

namespace SummableSupportCounterexample

def machine : ConcretePrefixMachine Bool Bool where
  codes := [[true]]
  prefixFree := by
    intro c₁ c₂ hc₁ hc₂ hneq hPrefix
    simp at hc₁ hc₂
    subst hc₁
    subst hc₂
    contradiction
  semantics := by
    intro c hc
    simp at hc
    subst hc
    exact (fun _ _ _ => ConcreteLaw.zero)

def policy : ConcretePolicy Bool Bool :=
  fun _ _ => ConcreteLaw.pure true

def history : FullHist Bool Bool :=
  asFullHist (emptyHist : Hist Bool Bool 0)

def observer : Observer (EncodedProgram Bool Bool) where
  Ω := Unit
  view _ := ()

def target : EncodedProgram Bool Bool :=
  machine.toEncodedProgram ⟨[true], by simp [machine]⟩

def actions : List Bool := [true]

def zeroSchedule : Nat → Rat := fun _ => 0

def scheduledActionLaw (r : Nat → Rat) (n : Nat) : ActionLaw Bool where
  mass a := if a = true then r n else 0
  support := [true]
  support_complete := by
    intro a ha
    by_cases h : a = true
    · simp [h]
    · simp [h] at ha

theorem true_mem_actions : true ∈ actions := by
  simp [actions]

theorem zeroSchedule_summable :
    SummableRatSchedule zeroSchedule := by
  refine ⟨0, ?_⟩
  intro N
  simp [zeroSchedule]

theorem schedule_realized_on_true (r : Nat → Rat) :
    actionMassScheduleRealized actions true (scheduledActionLaw r) r := by
  refine ⟨true_mem_actions, ?_⟩
  intro n
  simp [scheduledActionLaw]

theorem no_oneStepPosteriorConcentrates (r : Nat → Rat) (n : Nat) :
    ¬ oneStepPosteriorConcentrates machine policy history observer target actions (scheduledActionLaw r n) := by
  intro hConc
  rcases hConc with ⟨a, ha, hMass, _hSep, o, hIn, hOut, _hZero⟩
  have haTrue : a = true := by
    simpa [actions] using ha
  subst haTrue
  have hKernelZero :
      ∀ p : machine.Program,
        (programObsLaw history true (machine.toEncodedProgram p)).mass o = 0 := by
    intro p
    simp [programObsLaw, ConcretePrefixMachine.toEncodedProgram,
      ConcretePrefixMachine.programSemantics, machine, ConcreteLaw.zero]
  have hListZero :
      ∀ xs : List machine.Program, listWeightedSum xs (fun _ => (0 : Rat)) = 0 := by
    intro xs
    induction xs with
    | nil =>
        simp [listWeightedSum]
    | cons x xs ih =>
        simp [listWeightedSum]
  have hZero :
      (machine.predictiveLawInClass policy history true
        (machine.observerFiber observer target)).mass o = 0 := by
    simp [ConcretePrefixMachine.predictiveLawInClass, mixLaw, hKernelZero]
    exact hListZero _
  exact hIn hZero

theorem no_oneStepResidualPosteriorConcentrates (r : Nat → Rat) (n : Nat) (δ : Rat) :
    ¬ oneStepResidualPosteriorConcentrates
      machine policy history observer target actions (scheduledActionLaw r n) δ := by
  intro hConc
  rcases hConc with
    ⟨a, o, refLaw, ε, ha, hMass, _hSep, _hrefLaw, _hε, _hεpos,
      hSoftInPos, _hSoftOutPos, hRatio, _hBound⟩
  have haTrue : a = true := by
    simpa [actions] using ha
  subst haTrue
  have hKernelZero :
      ∀ p : machine.Program,
        (programObsLaw history true (machine.toEncodedProgram p)).mass o = 0 := by
    intro p
    simp [programObsLaw, ConcretePrefixMachine.toEncodedProgram,
      ConcretePrefixMachine.programSemantics, machine, ConcreteLaw.zero]
  have hListZero :
      ∀ xs : List machine.Program, listWeightedSum xs (fun _ => (0 : Rat)) = 0 := by
    intro xs
    induction xs with
    | nil =>
        simp [listWeightedSum]
    | cons x xs ih =>
        simp [listWeightedSum]
  have hInZero :
      (machine.predictiveLawInClass policy history true
        (machine.observerFiber observer target)).mass o = 0 := by
    simp [ConcretePrefixMachine.predictiveLawInClass, mixLaw, hKernelZero]
    exact hListZero _
  have hOutZero :
      (machine.predictiveLawOutsideClass policy history true
        (machine.observerFiber observer target)).mass o = 0 := by
    simp [ConcretePrefixMachine.predictiveLawOutsideClass, mixLaw, hKernelZero]
    exact hListZero _
  have hSoftEq :
      (machine.softPredictiveLawOutsideClass policy history true
        (machine.observerFiber observer target) refLaw ε).mass o =
      (machine.softPredictiveLawInClass policy history true
        (machine.observerFiber observer target) refLaw ε).mass o := by
    simp [ConcretePrefixMachine.softPredictiveLawOutsideClass,
      ConcretePrefixMachine.softPredictiveLawInClass, ConcreteLaw.soften, hInZero, hOutZero]
  rw [hSoftEq] at hRatio
  have hInNe :
      (machine.softPredictiveLawInClass policy history true
        (machine.observerFiber observer target) refLaw ε).mass o ≠ 0 :=
    ne_of_gt hSoftInPos
  have hImpossible : (1 : Rat) < 1 := by
    have hRatio' :
        (machine.softPredictiveLawInClass policy history true
          (machine.observerFiber observer target) refLaw ε).mass o /
          (machine.softPredictiveLawInClass policy history true
            (machine.observerFiber observer target) refLaw ε).mass o < 1 := hRatio
    rwa [div_self hInNe] at hRatio'
  exact (lt_irrefl (1 : Rat)) hImpossible

end SummableSupportCounterexample

/-- Lean wrapper for `thm:summable-support-insufficient` on the concrete semantic stack. -/
theorem thm_summable_support_insufficient
    (r : Nat → Rat)
    (hSummable : SummableRatSchedule r) :
    ∃ s : Nat → Rat,
      s = r ∧ SummableRatSchedule s ∧
      ∃ (U : ConcretePrefixMachine Bool Bool) (π : ConcretePolicy Bool Bool)
        (h : FullHist Bool Bool)
        (pstar : EncodedProgram Bool Bool) (actions : List Bool) (aStar : Bool)
        (κs : Nat → ActionLaw Bool),
        actionMassScheduleRealized actions aStar κs s ∧
        ∀ δ n,
          ¬ oneStepResidualPosteriorConcentrates
            U π h SummableSupportCounterexample.observer pstar actions (κs n) δ := by
  refine ⟨r, rfl, hSummable,
    SummableSupportCounterexample.machine, SummableSupportCounterexample.policy,
    SummableSupportCounterexample.history,
    SummableSupportCounterexample.target, SummableSupportCounterexample.actions, true,
    SummableSupportCounterexample.scheduledActionLaw r, ?_, ?_⟩
  · exact SummableSupportCounterexample.schedule_realized_on_true r
  · intro δ n
    exact SummableSupportCounterexample.no_oneStepResidualPosteriorConcentrates r n δ

/-- Lean wrapper for `cor:goal-dialed-payoff` on the concrete semantic stack. -/
theorem cor_goal_dialed_payoff
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A)
    (hUniform : def_uniform_history_independent_separation U π ω pstar actions)
    (h : FullHist A O) :
    def_sep_condition U π h ω pstar actions := by
  rcases hUniform h with ⟨a, ha, hSep⟩
  exact ⟨a, ha, hSep⟩

end ConcretePaperSemantic

end SemanticConvergence
