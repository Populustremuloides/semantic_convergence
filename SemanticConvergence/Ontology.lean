import SemanticConvergence.Semantic
import SemanticConvergence.Noise

/-!
# Observer/agent/coupling ontology surface

This module is an H10-facing façade. It does not move the existing proof stack;
it packages the already-proved declarations under the manuscript ontology:

* observers are passive lenses and their fibers;
* agents are variational learning architectures;
* couplings are observer-agent-environment packages with the extra hypotheses
  needed for convergence.

The final theorem in this file is a short wrapper around the existing route-2
constructed Bayes/Gibbs convergence theorem.
-/

namespace SemanticConvergence

universe u v w x

noncomputable section Ontology

open Classical
open Filter
open MeasureTheory
open CountableConcrete
open CountableConcrete.CountablePrefixMachine

namespace Ontology

/-! ## Observer layer -/

namespace Observer

/-- H10 name for a passive lens on programs. -/
abbrev Lens (P : Type u) := SemanticConvergence.Observer P

/-- The fiber of an observer at a program/view representative. -/
def fiber {P : Type u} (ω : Lens P) (p : P) : PredSet P :=
  fun q => ω.view q = ω.view p

/-- H10 name for observer refinement. -/
abbrev refines {P : Type u} (ω₁ ω₂ : Lens P) : Prop :=
  observerRefines ω₁ ω₂

theorem refines_refl {P : Type u} (ω : Lens P) : refines ω ω :=
  observerRefines_refl ω

theorem refines_trans {P : Type u} {ω₁ ω₂ ω₃ : Lens P}
    (h₁₂ : refines ω₁ ω₂) (h₂₃ : refines ω₂ ω₃) :
    refines ω₁ ω₃ :=
  observerRefines_trans h₁₂ h₂₃

section Countable

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

/-- H10 observer-layer alias for the syntactic observer. -/
abbrev syntactic : Lens (CountableEncodedProgram A O) :=
  syntacticObserver (A := A) (O := O)

/-- H10 observer-layer alias for the behavioral/interventional observer. -/
abbrev behavioral : Lens (CountableEncodedProgram A O) :=
  behavioralObserver (A := A) (O := O)

/-- H10 observer-layer alias for the policy observer. -/
abbrev policy (π : CountablePolicy A O) : Lens (CountableEncodedProgram A O) :=
  policyObserver (A := A) (O := O) π

/-- H10 observer-layer alias for the realized-history observer. -/
abbrev history (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) :
    Lens (CountableEncodedProgram A O) :=
  historyObserver (A := A) (O := O) π t h

end Countable

section CountableTheorems

variable {A : Type u} {O : Type v}

/-- The interventional semantic class is the behavioral-observer fiber. -/
theorem semanticClass_eq_behavioralFiber
    (pstar : CountableEncodedProgram A O) :
    def_int_sem_class (A := A) (O := O) pstar =
      fiber (behavioral (A := A) (O := O)) pstar := by
  funext p
  exact propext
    ((quotientObserver_eq_iff (semanticEq (A := A) (O := O)) p pstar).symm)

end CountableTheorems

end Observer

/-! ## Agent layer -/

namespace Agent

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O] [Fintype A]

/--
An H10-facing countable variational agent.

The fields are exactly the data that previously appeared as separate arguments
to the kernel-functional route-2 theorems.
-/
structure CountableAgent (U : CountablePrefixMachine A O) where
  π : CountablePolicy A O
  ωB : SemanticConvergence.Observer.{max u v, w} (CountableEncodedProgram A O)
  ωA : SemanticConvergence.Observer.{max u v, w} (CountableEncodedProgram A O)
  [omegaAEncodable : Encodable ωA.Ω]
  [omegaADecidableEq : DecidableEq ωA.Ω]
  β : ℝ
  γ : ℝ
  BbarAt : CountHist A O → KernelScore (A := A) (O := O) ωA
  qAt : CountHist A O → U.Program → ENNReal
  kernelAt : CountHist A O → ωA.Ω → A → ENNReal
  refLawAt : CountHist A O → ActionLaw A

attribute [instance] CountableAgent.omegaAEncodable CountableAgent.omegaADecidableEq

/-- The history-indexed kernel functional optimized by an agent. -/
def kernelFunctionalAt (U : CountablePrefixMachine A O)
    (𝒜 : CountableAgent (A := A) (O := O) U)
    (h : CountHist A O) : ℝ :=
  def_kernel_functional U 𝒜.π h.length h 𝒜.ωB 𝒜.ωA 𝒜.β 𝒜.γ
    (𝒜.BbarAt h) (𝒜.qAt h) (𝒜.kernelAt h) (𝒜.refLawAt h)

/-- The Gibbs minimum value associated to the agent's kernel functional. -/
def kernelFunctionalMinimumAt (U : CountablePrefixMachine A O)
    (𝒜 : CountableAgent (A := A) (O := O) U)
    (h : CountHist A O) : ℝ :=
  negativeLogBayesEvidence U 𝒜.π h.length h
    - 𝒜.γ * Real.log
      (kernelGibbsPartition U 𝒜.ωA 𝒜.β 𝒜.γ (𝒜.BbarAt h) (𝒜.refLawAt h)).toReal

/--
Agent-side admissibility/minimization package for the exact kernel-functional
route. This is the H10 "agent is in the natural variational class" surface.
-/
structure ExactKernelFunctionalAgent
    (U : CountablePrefixMachine A O)
    (𝒜 : CountableAgent (A := A) (O := O) U) : Prop where
  score_nonneg : ∀ h c a, 0 ≤ 𝒜.BbarAt h c a
  score_le_one : ∀ h c a, 𝒜.BbarAt h c a ≤ 1
  belief_admissible :
    ∀ h, BeliefAdmissibleAt U 𝒜.π h.length h (𝒜.qAt h)
  reference_admissible :
    ∀ h, KernelReferenceLawMassAdmissible (A := A) (𝒜.refLawAt h)
  kernel_admissible :
    ∀ h, KernelLawAdmissibleAt U 𝒜.ωA (𝒜.refLawAt h) (𝒜.kernelAt h)
  beta_nonneg : 0 ≤ 𝒜.β
  gamma_pos : 0 < 𝒜.γ
  exact_minimizer :
    ∀ h, kernelFunctionalAt U 𝒜 h = kernelFunctionalMinimumAt U 𝒜 h
  policy_is_kernel_marginal :
    ∀ h a, 𝒜.π h a = kernelLawActionMarginal (𝒜.kernelAt h) a

/--
Agent-layer wrapper around `prop_kernel_functional_minimizer`.
It keeps the old theorem intact while exposing the H10 package vocabulary.
-/
theorem kernelFunctional_decomposition
    (U : CountablePrefixMachine A O)
    (𝒜 : CountableAgent (A := A) (O := O) U)
    (h : CountHist A O)
    (h𝒜 : ExactKernelFunctionalAgent U 𝒜) :
    kernelFunctionalAt U 𝒜 h
      =
        kernelFunctionalMinimumAt U 𝒜 h
          + (posteriorIGap U 𝒜.π h.length h (𝒜.qAt h)).toReal
          + 𝒜.γ *
            (kernelGibbsIGap U 𝒜.ωA 𝒜.β 𝒜.γ
              (𝒜.BbarAt h) (𝒜.refLawAt h) (𝒜.kernelAt h)).toReal := by
  exact
    (prop_kernel_functional_minimizer U 𝒜.π h.length h 𝒜.ωB 𝒜.ωA
      𝒜.β 𝒜.γ (𝒜.BbarAt h)
      (h𝒜.score_nonneg h) (h𝒜.score_le_one h)
      (𝒜.qAt h) (h𝒜.belief_admissible h)
      (𝒜.refLawAt h) (h𝒜.reference_admissible h)
      (𝒜.kernelAt h) (h𝒜.kernel_admissible h)
      h𝒜.beta_nonneg h𝒜.gamma_pos).1

end Agent

/-! ## Coupling layer -/

namespace Coupling

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A]
variable [Fintype A]

/--
An observer-agent-environment coupling. This is the H10 ontology object whose
success or failure is not determined by any one constituent alone.
-/
structure ObserverAgentEnvironment
    (U : CountablePrefixMachine A O) where
  observer : SemanticConvergence.Observer.{max u v, x} (CountableEncodedProgram A O)
  agent : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U
  environment : U.Program
  target : CountableEncodedProgram A O

/-- The observer-fiber target set for a coupling. -/
def targetSet (U : CountablePrefixMachine A O)
    (𝒦 : ObserverAgentEnvironment (A := A) (O := O) U) :
    PredSet U.Program :=
  U.observerFiber 𝒦.observer 𝒦.target

/--
The canonical predictive-kernel observer-agent-environment coupling used by the
verified H10 route.
-/
def predictiveKernelCoupling
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program) :
    ObserverAgentEnvironment (A := A) (O := O) U where
  observer := countablePredictiveKernelObserver (A := A) (O := O)
  agent := 𝒜
  environment := penv
  target := U.toEncodedProgram penv

/--
The H10 semantic-learning package `𝔎 = (𝓘, 𝓙, 𝓢)`.

The `learningInstance` field is the observer-agent-environment instance `𝓘`,
`functional` is the history-indexed objective `𝓙`, and `semanticTarget` is the
posterior target set `𝓢`.
-/
structure SemanticLearningPackage
    (U : CountablePrefixMachine A O) where
  learningInstance : ObserverAgentEnvironment.{u, v, w, x} (A := A) (O := O) U
  functional : CountHist A O → ℝ
  semanticTarget : PredSet U.Program

/-- Manifest-facing alias for Definition `def:semantic-learning-package`. -/
abbrev def_semantic_learning_package
    (U : CountablePrefixMachine A O) :=
  SemanticLearningPackage (A := A) (O := O) U

/-- Canonical H10 package built from an exact kernel-functional agent. -/
def predictiveKernelSemanticLearningPackage
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program) :
    SemanticLearningPackage (A := A) (O := O) U where
  learningInstance := predictiveKernelCoupling U 𝒜 penv
  functional := Agent.kernelFunctionalAt U 𝒜
  semanticTarget := targetSet U (predictiveKernelCoupling U 𝒜 penv)

/--
The manuscript object `𝔎=(𝓘,𝓙,𝓢)` for the canonical predictive-kernel route.
-/
def 𝔎
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program) :
    SemanticLearningPackage (A := A) (O := O) U :=
  predictiveKernelSemanticLearningPackage U 𝒜 penv

/--
H10 verified coupling package for the predictive-kernel route.

The agent-side fields package exact Bayes/Gibbs and exact kernel-functional
minimization. The remaining fields are coupling-side: true-law Hellinger
prefix obligations, target-fiber normalizers, and class-predictive separation
on reference support.
-/
structure H10VerifiedPackage
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program) where
  /-- (M2)--(M3): exact Bayes/Gibbs belief and exact kernel-functional action. -/
  agent_exact : Agent.ExactKernelFunctionalAgent U 𝒜
  κ : ℝ
  /-- (M7): positive separation constant. -/
  kappa_pos : 0 < κ
  /-- (M6): true-law Hellinger envelope integrability. -/
  hellinger_integrable :
    ∀ n,
      Integrable
        (CountablePrefixMachine.ionescuPullbackInfiniteProcess
          (A := A) (O := O)
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            𝒜.π penv
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv)) n)
        (CountablePrefixMachine.ionescuTrajectoryMeasure
          (A := A) (O := O) 𝒜.π (U.programSemantics penv))
  prefix_hellinger_obligations :
    CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations
      U 𝒜.π penv
      (countablePredictiveKernelObserver (A := A) (O := O))
      (U.toEncodedProgram penv)
  target_fiber_mass_ne_zero :
    ∀ h,
      U.observerFiberPosteriorWeight 𝒜.π h.length h
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) ≠ 0
  target_fiber_mass_ne_top :
    ∀ h,
      U.observerFiberPosteriorWeight 𝒜.π h.length h
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) ≠ ⊤
  class_predictive_separation :
    ∀ h,
      KernelReferenceLawClassPredictiveBhattacharyyaSemanticallySeparatedAt
        U 𝒜.π
        (countablePredictiveKernelObserver (A := A) (O := O))
        (U.toEncodedProgram penv) κ h (𝒜.refLawAt h)

/-- Manifest-facing alias for Assumptions `ass:main-verified-package`. -/
abbrev ass_main_verified_package
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program) :=
  H10VerifiedPackage U 𝒜 penv

/-- Backward-compatible name retained for older generated references. -/
abbrev H7Verified
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program) :=
  H10VerifiedPackage U 𝒜 penv

/-- The H10 statement: verified observer-agent-environment couplings converge. -/
theorem h10_verified_semantic_learning_package_converges
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  exact
    thm_constructed_infinite_bayes_gibbs_trueLaw_hellinger_spine_convergence_of_constrained_kernel_functional_minimizers_classPredictive_predictiveKernelObserver
      (A := A) (O := O) U 𝒜.π penv 𝒜.ωB 𝒜.ωA 𝒜.β 𝒜.γ
      𝒜.BbarAt 𝒜.qAt 𝒜.kernelAt 𝒜.refLawAt
      h𝒦.hellinger_integrable
      h𝒦.prefix_hellinger_obligations
      h𝒦.kappa_pos
      h𝒦.agent_exact.score_nonneg
      h𝒦.agent_exact.score_le_one
      h𝒦.agent_exact.belief_admissible
      h𝒦.agent_exact.reference_admissible
      h𝒦.agent_exact.kernel_admissible
      h𝒦.agent_exact.beta_nonneg
      h𝒦.agent_exact.gamma_pos
      h𝒦.agent_exact.exact_minimizer
      h𝒦.agent_exact.policy_is_kernel_marginal
      h𝒦.target_fiber_mass_ne_zero
      h𝒦.target_fiber_mass_ne_top
      h𝒦.class_predictive_separation

/--
H10 discharge of the infinite-affinity bridge: in the canonical H10 package,
the martingale/affinity bridge is no longer a separate manuscript assumption.
-/
theorem h10_infinite_affinity_hellinger_bridge
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

/-- H10 discharge of the full-support exploration companion route. -/
theorem h10_exploration_floor_behavioral
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

/-- H10 discharge of the canonical selector semantic-convergence route. -/
theorem h10_semantic_convergence
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

/-- H10 discharge of the exact kernel-functional semantic-convergence route. -/
theorem h10_kernel_semantic_convergence
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

/-- H10 discharge of the compact-action kernel companion route. -/
theorem h10_compact_action_kernel
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

/-- H10 discharge of the finite-class maximin companion route. -/
theorem h10_finite_maximin
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

/-- H10 discharge of the goal-dialed payoff companion route. -/
theorem h10_goal_dialed_payoff
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

/-- H10 discharge of the amortized-surrogate asymptotic companion route. -/
theorem h10_amortized_surrogate
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) := by
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

/--
H10 discharge of the noisy/support-left-invertible companion route. The channel
witness is recorded explicitly; convergence is supplied by the verified H10
package for the observed system, not by the channel property alone.
-/
theorem h10_support_left_invertible_noisy_transfer
    {O' : Type x}
    [DecidableEq O] [BEq O] [LawfulBEq O]
    [DecidableEq O'] [BEq O'] [LawfulBEq O']
    (K : ObsChannel O O')
    (hK : def_left_invertible_channel K)
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H10VerifiedPackage U 𝒜 penv) :
    def_left_invertible_channel K ∧
      ∀ᵐ ξ ∂
        (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
          (A := A) (O := O) U 𝒜.π penv).measure,
        Tendsto
          (fun n =>
            (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
              (countablePredictiveKernelObserver (A := A) (O := O))
              (U.toEncodedProgram penv) n ξ)⁻¹)
          atTop (nhds 1) := by
  refine ⟨hK, ?_⟩
  have hMain := h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦
  exact hMain

  /-- Backward-compatible theorem name retained for older generated references. -/
  theorem h7_verified_semantic_learning_package_converges
    (U : CountablePrefixMachine A O)
    (𝒜 : Agent.CountableAgent.{u, v, w} (A := A) (O := O) U)
    (penv : U.Program)
    (h𝒦 : H7Verified U 𝒜 penv) :
    ∀ᵐ ξ ∂
      (CountablePrefixMachine.infiniteBayesGibbsTrajectoryLaw_of_ionescu
        (A := A) (O := O) U 𝒜.π penv).measure,
      Tendsto
        (fun n =>
          (1 + U.infiniteRealizedResidualOddsProcess 𝒜.π
            (countablePredictiveKernelObserver (A := A) (O := O))
            (U.toEncodedProgram penv) n ξ)⁻¹)
        atTop (nhds 1) :=
  h10_verified_semantic_learning_package_converges U 𝒜 penv h𝒦

end Coupling

end Ontology

end Ontology

end SemanticConvergence
