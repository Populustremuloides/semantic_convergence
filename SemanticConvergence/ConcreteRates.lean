import SemanticConvergence.ConcretePosteriorDecay

namespace SemanticConvergence

universe u v

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Float-valued log-odds proxy for a rational posterior-odds quantity. -/
def logOddsFloat (r : Rat) : Float :=
  if r ≤ 0 then 0 else Float.log (ratToNonnegFloat r)

/-- Concrete observer-fiber log-odds process at a finite history. -/
def observerFiberLogOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  logOddsFloat (U.observerFiberPosteriorOdds π h ω pstar)

/-- Concrete one-step log-odds drift between two finite histories. -/
def oneStepLogOddsDrift (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  U.observerFiberLogOdds π h' ω pstar - U.observerFiberLogOdds π h ω pstar

/-- Expected concrete semantic gain under a local action law. -/
def expectedSemanticGain (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) : Float :=
  actionExpectation κ (fun a => U.semanticGain π h a ω pstar)

/-- Concrete lower-bound witness for expected semantic gain. -/
def hasExpectedGainLowerBound (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) (δ : Float) : Prop :=
  δ ≤ U.expectedSemanticGain π h ω pstar κ

/-- Combined one-step concentration score: drift plus expected semantic gain. -/
def concentrationScore (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) : Float :=
  U.oneStepLogOddsDrift π h h' ω pstar +
    U.expectedSemanticGain π h ω pstar κ

/--
Explicit `N`-step rate factor extracted from a positive separating-support floor.

In the current finite-support rational substrate, a positive floor forces one-step collapse,
so the reusable quantitative envelope is the fixed exponential factor `(1/2)^N`.
-/
def posteriorRateFactorFromFloor (N : Nat) : Rat :=
  ((1 : Rat) / 2) ^ N

theorem posteriorRateFactorFromFloor_succ_lt (N : Nat) :
    posteriorRateFactorFromFloor (N + 1) <
      posteriorRateFactorFromFloor N := by
  simp [posteriorRateFactorFromFloor, pow_succ]
  have hpow : 0 < (((1 : Rat) / 2) ^ N) := by
    positivity
  have hhalf : ((1 : Rat) / 2) < 1 := by
    norm_num
  have hmul :
      (((1 : Rat) / 2) ^ N) * ((1 : Rat) / 2) <
        (((1 : Rat) / 2) ^ N) * 1 := by
    exact mul_lt_mul_of_pos_left hhalf hpow
  simpa using hmul

/--
Explicit `N`-step posterior-odds rate bound from a positive one-step decay factor.

This compares the `δ`-dependent posterior-decay recurrence against the uniform envelope
`(1/2)^N`. The latter remains valid because the strengthened floor-dependent decay factor
is always at most `1/2` on positive floors. The composition theorem itself is genuinely
rate-magnitude-aware, but in the current finite-support rational substrate the one-step
process often saturates at `0` after the first zero-out observation, so this sharper
envelope is not yet exercised by the present semantic support theorems. It is kept here
because the future positive-support substrate will feed the same recurrence API with a
nonzero per-step contraction factor.
-/
theorem posteriorRateBound_of_positiveDecay
    {δ : Rat} (hδ : 0 < δ)
    {r0 : Rat} (h0 : 0 ≤ r0)
    {x : Nat → Rat}
    (hx0 : x 0 = r0)
    (hStep : ∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) :
    ∀ N, x N ≤ posteriorRateFactorFromFloor N * r0 := by
  intro N
  have hDecay :
      x N ≤ nStepPosteriorDecayBound δ N (x 0) :=
    nStepPosteriorDecayBound_of_stepBound (δ := δ) (x := x) hStep N
  have hDecay' :
      x N ≤ posteriorDecayFactor δ ^ N * r0 := by
    simpa [nStepPosteriorDecayBound, hx0] using hDecay
  have hPowLe :
      posteriorDecayFactor δ ^ N ≤ ((1 : Rat) / 2) ^ N := by
    exact pow_le_pow_left₀
      (posteriorDecayFactor_nonneg δ)
      (posteriorDecayFactor_le_half_of_pos hδ)
      N
  have hBound' :
      posteriorDecayFactor δ ^ N * r0 ≤ ((1 : Rat) / 2) ^ N * r0 := by
    exact mul_le_mul_of_nonneg_right hPowLe h0
  exact le_trans hDecay' (by simpa [posteriorRateFactorFromFloor] using hBound')

/--
Concrete rate witness package. Beyond one-step drift and gain lower bounds, it now
contains an explicit `N`-step posterior-odds decay theorem. The certificate records a
rate-magnitude-sensitive recurrence bound, but under the current substrate the semantic
layer often supplies that recurrence through a one-step zero-collapse witness rather than
through a strictly positive likelihood-ratio contraction. The stronger quantitative shape
is retained so later positive-support kernels can inhabit the same certificate without
changing downstream theorem statements.
-/
def hasConcentrationCertificate (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) (δDrift δGain : Float) : Prop :=
  ∃ δ : Rat, 0 < δ ∧
    δDrift ≤ U.oneStepLogOddsDrift π h h' ω pstar ∧
    U.hasExpectedGainLowerBound π h ω pstar κ δGain ∧
    0 ≤ U.observerFiberPosteriorOdds π h ω pstar ∧
    ∀ x : Nat → Rat,
      x 0 = U.observerFiberPosteriorOdds π h ω pstar →
      (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
      ∀ N, x N ≤ posteriorRateFactorFromFloor N *
        U.observerFiberPosteriorOdds π h ω pstar

theorem observerFiberLogOdds_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberLogOdds π h ω p =
      U.observerFiberLogOdds π h ω q := by
  have hOdds := U.observerFiberPosteriorOdds_eq_of_sameView π h ω hView
  simp [observerFiberLogOdds, hOdds]

theorem oneStepLogOddsDrift_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.oneStepLogOddsDrift π h h' ω p =
      U.oneStepLogOddsDrift π h h' ω q := by
  have hNow := U.observerFiberLogOdds_eq_of_sameView π h ω hView
  have hNext := U.observerFiberLogOdds_eq_of_sameView π h' ω hView
  simp [oneStepLogOddsDrift, hNow, hNext]

theorem expectedSemanticGain_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (κ : ActionLaw A)
    (hView : ω.view p = ω.view q) :
    U.expectedSemanticGain π h ω p κ =
      U.expectedSemanticGain π h ω q κ := by
  have hFun :
      (fun a => U.semanticGain π h a ω p) =
        (fun a => U.semanticGain π h a ω q) := by
    funext a
    exact U.semanticGain_eq_of_sameView π h a ω hView
  simp [expectedSemanticGain, hFun]

theorem concentrationScore_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (κ : ActionLaw A)
    (hView : ω.view p = ω.view q) :
    U.concentrationScore π h h' ω p κ =
      U.concentrationScore π h h' ω q κ := by
  have hDrift := U.oneStepLogOddsDrift_eq_of_sameView π h h' ω hView
  have hGain := U.expectedSemanticGain_eq_of_sameView π h ω κ hView
  simp [concentrationScore, hDrift, hGain]

theorem hasConcentrationCertificate_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (κ : ActionLaw A)
    {δDrift δGain : Float}
    (hView : ω.view p = ω.view q) :
    U.hasConcentrationCertificate π h h' ω p κ δDrift δGain →
      U.hasConcentrationCertificate π h h' ω q κ δDrift δGain := by
  intro hCert
  rcases hCert with ⟨δ, hδ, hDrift, hGain, hOdds0, hRate⟩
  have hDriftEq := U.oneStepLogOddsDrift_eq_of_sameView π h h' ω hView
  have hGainEq := U.expectedSemanticGain_eq_of_sameView π h ω κ hView
  have hOddsEq := U.observerFiberPosteriorOdds_eq_of_sameView π h ω hView
  refine ⟨δ, hδ, ?_, ?_, ?_, ?_⟩
  · simpa [hDriftEq] using hDrift
  · simpa [hasExpectedGainLowerBound, hGainEq] using hGain
  · simpa [hOddsEq] using hOdds0
  · intro x hx0 hStep N
    have hx0' : x 0 = U.observerFiberPosteriorOdds π h ω p := by
      simpa [hOddsEq] using hx0
    have hBound := hRate x hx0' hStep N
    simpa [hOddsEq] using hBound

set_option linter.unusedSectionVars false in
theorem hasSeparatingSupportFloor_of_weight
    (κ : ActionLaw A) (actions : List A)
    (S : PredSet A) [DecidablePred S] {δ : Rat}
    (hWeight : δ ≤ separatingSupportWeight κ actions S) :
    hasSeparatingSupportFloor κ actions S δ :=
  hWeight

theorem hasExpectedGainLowerBound_of_value
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) {δ : Float}
    (hGain : δ ≤ U.expectedSemanticGain π h ω pstar κ) :
    hasExpectedGainLowerBound U π h ω pstar κ δ :=
  hGain

/-- Extract the explicit `N`-step rate theorem from a concentration certificate. -/
theorem certificate_implies_rateBound
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) {δDrift δGain : Float}
    (hCert : U.hasConcentrationCertificate π h h' ω pstar κ δDrift δGain) :
    ∃ δ : Rat, 0 < δ ∧
      ∀ x : Nat → Rat,
        x 0 = U.observerFiberPosteriorOdds π h ω pstar →
        (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
        ∀ N, x N ≤ posteriorRateFactorFromFloor N *
          U.observerFiberPosteriorOdds π h ω pstar := by
  rcases hCert with ⟨δ, hδ, _hDrift, _hGain, _hOdds0, hRate⟩
  exact ⟨δ, hδ, hRate⟩

theorem hasConcentrationCertificate_of_drift_and_gain
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A)
    {δ : Rat} (hδ : 0 < δ)
    {δDrift δGain : Float}
    (hDrift : δDrift ≤ U.oneStepLogOddsDrift π h h' ω pstar)
    (hGain : U.hasExpectedGainLowerBound π h ω pstar κ δGain)
    (hOdds0 : 0 ≤ U.observerFiberPosteriorOdds π h ω pstar) :
    U.hasConcentrationCertificate π h h' ω pstar κ δDrift δGain := by
  refine ⟨δ, hδ, hDrift, hGain, hOdds0, ?_⟩
  intro x hx0 hStep N
  exact posteriorRateBound_of_positiveDecay
    (δ := δ) hδ hOdds0 hx0 hStep N

/-- Direct explicit `N`-step rate bound from a positive separating-support floor. -/
theorem rateBound_of_positiveFloor
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {δ : Rat} (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.observerFiberPosteriorOdds π h ω pstar) :
    ∀ x : Nat → Rat,
      x 0 = U.observerFiberPosteriorOdds π h ω pstar →
      (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
      ∀ N, x N ≤ posteriorRateFactorFromFloor N *
        U.observerFiberPosteriorOdds π h ω pstar := by
  intro x hx0 hStep N
  exact posteriorRateBound_of_positiveDecay
    (δ := δ) hδ hOdds0 hx0 hStep N

/--
Direct explicit `N`-step rate bound for the positive-support residual-odds substrate.

This is the rate-layer bridge for the strong Section 6 path: once the semantic layer
supplies a recurrence on `residualObserverFiberPosteriorOdds` through the smoothed
positive-support contraction theorems in `ConcretePosteriorDecay`, the same envelope
`posteriorRateFactorFromFloor N` composes it without relying on the old one-step
zero-collapse proxy.
-/
theorem residualRateBound_of_positiveFloor
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {δ : Rat} (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar) :
    ∀ x : Nat → Rat,
      x 0 = U.residualObserverFiberPosteriorOdds π h ω pstar →
      (∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) →
      ∀ N, x N ≤ posteriorRateFactorFromFloor N *
        U.residualObserverFiberPosteriorOdds π h ω pstar := by
  intro x hx0 hStep N
  exact posteriorRateBound_of_positiveDecay
    (δ := δ) hδ hOdds0 hx0 hStep N

end ConcretePrefixMachine

end

end SemanticConvergence
