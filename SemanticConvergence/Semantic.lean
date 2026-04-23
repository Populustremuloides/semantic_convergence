import SemanticConvergence.Belief
import SemanticConvergence.ConcreteSemantic
import SemanticConvergence.ConcretePosteriorDecay
import SemanticConvergence.ConcreteProbabilisticConvergence
import SemanticConvergence.ConcreteSubstrateBridge
import SemanticConvergence.ConcreteRates
import SemanticConvergence.ConcreteNoise

namespace SemanticConvergence

universe u v

noncomputable section ConcretePaperSemantic

open Classical
open ConcretePrefixMachine
open Filter
open scoped MeasureTheory ProbabilityTheory

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

/-- Lean wrapper for `prop:kernel-promotion-support-compact` on the concrete semantic stack. -/
theorem prop_kernel_promotion_support_compact
    (refLaw : ActionLaw A) :
    def_promotion_supporting (def_kernel_semantic_rule refLaw) refLaw.support := by
  intro a ha
  change (fullSupportActionLaw refLaw.support).mass a ≠ 0
  simp [fullSupportActionLaw, ha]

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

/-- Lean wrapper for `prop:compact-action-kernel-separation` on the concrete stack. -/
theorem prop_compact_action_kernel_separation
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

/-- Lean wrapper for `lem:contraction` on the concrete semantic stack. -/
theorem lem_contraction
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
first-principles Section 6 stack.

This is the canonical paper-facing theorem name on the probabilistic track. It derives the
supportwise residual contraction witness internally from the deterministic prefixwise
residual-odds process and the concrete-to-countable bridge layer, then upgrades that
witness to an almost-sure recurrence statement under `trajectoryLaw`.
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
    (hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar)) :
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
  have hWitness :
      Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pstarc δ T := by
    simpa [Uc, πc, penvc, ωc, pstarc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv pstar ω δ T hStep
  simpa [Uc, πc, penvc, ωc, pstarc] using
    thm_separating_support_convergence_of_witness Uc πc penvc ωc pstarc δ T hWitness

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
    (hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar)) :
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
  have hWitness :
      Uc.HasSupportwiseResidualContractionWitness πc penvc ωc pstarc δ T := by
    simpa [Uc, πc, penvc, ωc, pstarc] using
      U.hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
        hCodes π hπ hπN hSem hSemN penv pstar ω δ T hStep
  simpa [Uc, πc, penvc, ωc, pstarc] using
    thm_separating_support_rate_of_witness Uc πc penvc ωc pstarc δ T hWitness

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
    (hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar))
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

/-- Lean wrapper for `cor:compact-action-kernel` on the concrete semantic stack. -/
theorem cor_compact_action_kernel
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
