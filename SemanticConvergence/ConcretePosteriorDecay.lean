import SemanticConvergence.ConcreteSemantic

namespace SemanticConvergence

universe u v

open Classical

noncomputable section

namespace ConcretePrefixMachine

/--
Explicit posterior-decay rate extracted from a separating-support floor.

In the current finite-support substrate, any positive floor is strong enough to force
one-step complement extinction at a zero-out witness. We package that witness against a
nondegenerate floor-dependent rate which is strictly increasing on `(0, 1]` and stays
below `1`, so the induced multiplicative decay factor remains positive and uniformly at
most `1/2` on positive floors.
-/
def posteriorDecayRate (δ : Rat) : Rat :=
  if _hδ : 0 < δ then (1 / 2 : Rat) + min δ 1 / 4 else 0

/-- Multiplicative posterior-decay factor corresponding to `posteriorDecayRate`. -/
def posteriorDecayFactor (δ : Rat) : Rat :=
  1 - posteriorDecayRate δ

/-- `N`-step multiplicative posterior-decay bound from an initial odds value. -/
def nStepPosteriorDecayBound (δ : Rat) (N : Nat) (r0 : Rat) : Rat :=
  posteriorDecayFactor δ ^ N * r0

theorem posteriorDecayRate_pos_of_pos {δ : Rat} (hδ : 0 < δ) :
    0 < posteriorDecayRate δ := by
  have hmin_nonneg : 0 ≤ min δ (1 : Rat) := by
    exact le_min (le_of_lt hδ) (by norm_num)
  have hquarter_nonneg : 0 ≤ min δ (1 : Rat) / 4 := by
    exact div_nonneg hmin_nonneg (by norm_num)
  have hhalf : (0 : Rat) < 1 / 2 := by norm_num
  simp [posteriorDecayRate, hδ]
  linarith

theorem posteriorDecayRate_eq_of_pos {δ : Rat} (hδ : 0 < δ) :
    posteriorDecayRate δ = (1 / 2 : Rat) + min δ 1 / 4 := by
  simp [posteriorDecayRate, hδ]

theorem posteriorDecayRate_lt_one_of_pos {δ : Rat} (hδ : 0 < δ) :
    posteriorDecayRate δ < 1 := by
  have hmin_le : min δ (1 : Rat) ≤ 1 := by
    exact min_le_right _ _
  have hquarter_le : min δ (1 : Rat) / 4 ≤ (1 : Rat) / 4 := by
    exact div_le_div_of_nonneg_right hmin_le (by norm_num : (0 : Rat) ≤ 4)
  simp [posteriorDecayRate, hδ]
  linarith

theorem posteriorDecayRate_strictMonoOn_unit :
    StrictMonoOn posteriorDecayRate (Set.Ioc (0 : Rat) 1) := by
  intro δ₁ hδ₁ δ₂ hδ₂ hlt
  have hδ₁pos : 0 < δ₁ := hδ₁.1
  have hδ₂pos : 0 < δ₂ := hδ₂.1
  have hδ₁le : δ₁ ≤ 1 := hδ₁.2
  have hδ₂le : δ₂ ≤ 1 := hδ₂.2
  have hmin₁ : min δ₁ (1 : Rat) = δ₁ := min_eq_left hδ₁le
  have hmin₂ : min δ₂ (1 : Rat) = δ₂ := min_eq_left hδ₂le
  simp [posteriorDecayRate, hδ₁pos, hδ₂pos, hmin₁, hmin₂]
  linarith

theorem posteriorDecayFactor_nonneg (δ : Rat) :
    0 ≤ posteriorDecayFactor δ := by
  by_cases hδ : 0 < δ
  · have hlt : posteriorDecayRate δ < 1 := posteriorDecayRate_lt_one_of_pos hδ
    simp [posteriorDecayFactor]
    linarith [hlt]
  · simp [posteriorDecayFactor, posteriorDecayRate, hδ]

theorem posteriorDecayFactor_eq_of_pos {δ : Rat} (hδ : 0 < δ) :
    posteriorDecayFactor δ = (1 / 2 : Rat) - min δ 1 / 4 := by
  have hRate := posteriorDecayRate_eq_of_pos hδ
  rw [posteriorDecayFactor, hRate]
  ring

theorem posteriorDecayFactor_le_half_of_pos {δ : Rat} (hδ : 0 < δ) :
    posteriorDecayFactor δ ≤ (1 / 2 : Rat) := by
  have hmin_nonneg : 0 ≤ min δ (1 : Rat) := by
    exact le_min (le_of_lt hδ) (by norm_num)
  rw [posteriorDecayFactor_eq_of_pos hδ]
  linarith

theorem posteriorDecayFactor_pos_of_pos {δ : Rat} (hδ : 0 < δ) :
    0 < posteriorDecayFactor δ := by
  have hlt : posteriorDecayRate δ < 1 := posteriorDecayRate_lt_one_of_pos hδ
  simp [posteriorDecayFactor]
  linarith [hlt]

/--
Generic `N`-step composition for any odds process satisfying the one-step decay
recurrence with factor `posteriorDecayFactor δ`.
-/
theorem nStepPosteriorDecayBound_of_stepBound
    {δ : Rat} {x : Nat → Rat}
    (hStep : ∀ n, x (n + 1) ≤ posteriorDecayFactor δ * x n) :
    ∀ N, x N ≤ nStepPosteriorDecayBound δ N (x 0) := by
  intro N
  induction N with
  | zero =>
      simp [nStepPosteriorDecayBound]
  | succ n ih =>
      calc
        x (n + 1) ≤ posteriorDecayFactor δ * x n := hStep n
        _ ≤ posteriorDecayFactor δ * nStepPosteriorDecayBound δ n (x 0) := by
          exact mul_le_mul_of_nonneg_left ih (posteriorDecayFactor_nonneg δ)
        _ = nStepPosteriorDecayBound δ (n + 1) (x 0) := by
          simp [nStepPosteriorDecayBound, pow_succ, mul_left_comm, mul_comm]

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/--
Unnormalized one-step class mass after taking action `a` at history `h` and observing `o`.
This is the current posterior class mass multiplied by the class-conditional predictive
probability of `o`.
-/
def oneStepClassObservationMass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O) : Rat :=
  U.posteriorClassMass π h C * (U.predictiveLawInClass π h a C).mass o

/--
Unnormalized one-step complement mass after taking action `a` at history `h` and
observing `o`.
-/
def oneStepComplementObservationMass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O) : Rat :=
  U.complementPosteriorMass π h C * (U.predictiveLawOutsideClass π h a C).mass o

/--
Raw one-step odds update before renormalization. This is the class-vs-complement
observation odds for the next observation `o`.
-/
def oneStepObservationOddsRaw (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O) : Rat :=
  let den := U.oneStepComplementObservationMass π h a C o
  if den = 0 then 0 else U.oneStepClassObservationMass π h a C o / den

/-- Total one-step evidence for observation `o` under the class-vs-complement split. -/
def oneStepObservationEvidence (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O) : Rat :=
  U.oneStepClassObservationMass π h a C o +
    U.oneStepComplementObservationMass π h a C o

/-- Posterior class mass after one explicit action-observation update. -/
def oneStepClassPosteriorMass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O) : Rat :=
  let Z := U.oneStepObservationEvidence π h a C o
  if _hZ : Z = 0 then 0 else U.oneStepClassObservationMass π h a C o / Z

/-- Posterior complement mass after one explicit action-observation update. -/
def oneStepComplementPosteriorMass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O) : Rat :=
  let Z := U.oneStepObservationEvidence π h a C o
  if _hZ : Z = 0 then 0 else U.oneStepComplementObservationMass π h a C o / Z

/-- Class-vs-complement odds after one explicit action-observation update. -/
def oneStepClassPosteriorOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O) : Rat :=
  let den := U.oneStepComplementPosteriorMass π h a C o
  if den = 0 then 0 else U.oneStepClassPosteriorMass π h a C o / den

/-- One-step posterior odds specialized to an observer fiber. -/
def oneStepObserverFiberPosteriorOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (o : O) : Rat := by
  classical
  exact U.oneStepClassPosteriorOdds π h a (U.observerFiber ω pstar) o

/--
Residual class posterior odds, oriented as complement-versus-class rather than class-versus-
complement.

This is the positive-support companion to the current zero-collapse proxy. Later phases use
it to state load-bearing contraction bounds where the one-step multiplier is genuinely
strictly between `0` and `1`.
-/
def residualClassPosteriorOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] : Rat :=
  let mC := U.posteriorClassMass π h C
  let mComp := U.complementPosteriorMass π h C
  if _ : mC = 0 then 0 else mComp / mC

/-- Residual observer-fiber posterior odds in the positive-support companion substrate. -/
def residualObserverFiberPosteriorOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat := by
  classical
  exact U.residualClassPosteriorOdds π h (U.observerFiber ω pstar)

/-- Smoothed one-step class observation mass in the positive-support companion substrate. -/
def softOneStepClassObservationMass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O) : Rat :=
  U.posteriorClassMass π h C * (U.softPredictiveLawInClass π h a C refLaw ε).mass o

/-- Smoothed one-step complement observation mass in the positive-support companion substrate. -/
def softOneStepComplementObservationMass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O) : Rat :=
  U.complementPosteriorMass π h C * (U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o

/--
Residual one-step odds update under the smoothed positive-support predictive laws.

This keeps the same finite-horizon Bayes ingredients as the current substrate while
avoiding zero-out observations by adding positive reference mass on the observation side.
-/
def softOneStepClassResidualOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O) : Rat :=
  let den := U.softOneStepClassObservationMass π h a C refLaw ε o
  if den = 0 then 0 else U.softOneStepComplementObservationMass π h a C refLaw ε o / den

/-- Smoothed residual one-step odds update specialized to an observer fiber. -/
def softOneStepObserverFiberResidualOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O) : Rat := by
  classical
  exact U.softOneStepClassResidualOdds π h a (U.observerFiber ω pstar) refLaw ε o

theorem residualObserverFiberPosteriorOdds_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.residualObserverFiberPosteriorOdds π h ω p =
      U.residualObserverFiberPosteriorOdds π h ω q := by
  have hClassMass :
      U.posteriorClassMass π h (U.observerFiber ω p) =
        U.posteriorClassMass π h (U.observerFiber ω q) := by
    simpa [ConcretePrefixMachine.observerFiberPosteriorMass] using
      U.observerFiberPosteriorMass_eq_of_sameView π h ω hView
  have hComp := U.complementPosteriorMass_eq_of_sameView π h ω hView
  simp [residualObserverFiberPosteriorOdds, residualClassPosteriorOdds, hClassMass, hComp]

theorem softOneStepObserverFiberResidualOdds_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (hView : ω.view p = ω.view q) :
    U.softOneStepObserverFiberResidualOdds π h a ω p refLaw ε o =
      U.softOneStepObserverFiberResidualOdds π h a ω q refLaw ε o := by
  have hClassMass :
      U.posteriorClassMass π h (U.observerFiber ω p) =
        U.posteriorClassMass π h (U.observerFiber ω q) := by
    simpa [ConcretePrefixMachine.observerFiberPosteriorMass] using
      U.observerFiberPosteriorMass_eq_of_sameView π h ω hView
  have hComp := U.complementPosteriorMass_eq_of_sameView π h ω hView
  have hIn := U.softPredictiveLawInClass_eq_of_sameView π h a ω refLaw ε hView
  have hOut := U.softPredictiveLawOutsideClass_eq_of_sameView π h a ω refLaw ε hView
  simp [softOneStepObserverFiberResidualOdds, softOneStepClassResidualOdds,
    softOneStepClassObservationMass, softOneStepComplementObservationMass,
    hClassMass, hComp, hIn, hOut]

set_option linter.unusedSectionVars false in
theorem exists_supported_action_of_positiveSeparatingSupportFloor
    (κ : ActionLaw A) (actions : List A) (S : PredSet A) [DecidablePred S]
    {δ : Rat} (hδ : 0 < δ)
    (hFloor : hasSeparatingSupportFloor κ actions S δ) :
    ∃ a, a ∈ actions ∧ κ.mass a ≠ 0 ∧ S a := by
  have hWeightPos : 0 < separatingSupportWeight κ actions S := lt_of_lt_of_le hδ hFloor
  have hWeightNe : separatingSupportWeight κ actions S ≠ 0 := ne_of_gt hWeightPos
  rcases listWeightedSum_ne_zero_exists
      (xs := actions) (f := fun a => if S a then κ.mass a else 0)
      (by simpa [separatingSupportWeight] using hWeightNe) with ⟨a, ha, hTerm⟩
  by_cases hSa : S a
  · have hMass : κ.mass a ≠ 0 := by
      simpa [hSa] using hTerm
    exact ⟨a, ha, hMass, hSa⟩
  · simp [hSa] at hTerm

theorem oneStepComplementObservationMass_eq_zero_of_predictiveLawOutsideClass_zero
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O)
    (hZero : (U.predictiveLawOutsideClass π h a C).mass o = 0) :
    U.oneStepComplementObservationMass π h a C o = 0 := by
  simp [oneStepComplementObservationMass, hZero]

theorem oneStepComplementPosteriorMass_eq_zero_of_predictiveLawOutsideClass_zero
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O)
    (hZero : (U.predictiveLawOutsideClass π h a C).mass o = 0) :
    U.oneStepComplementPosteriorMass π h a C o = 0 := by
  unfold oneStepComplementPosteriorMass
  simp [oneStepComplementObservationMass_eq_zero_of_predictiveLawOutsideClass_zero, hZero]

theorem oneStepObservationOddsRaw_eq_classPosteriorOdds_mul_likelihoodRatio
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O)
    (hComp : U.complementPosteriorMass π h C ≠ 0)
    (hOut : (U.predictiveLawOutsideClass π h a C).mass o ≠ 0) :
    U.oneStepObservationOddsRaw π h a C o =
      U.classPosteriorOdds π h C *
        ((U.predictiveLawInClass π h a C).mass o /
          (U.predictiveLawOutsideClass π h a C).mass o) := by
  unfold oneStepObservationOddsRaw classPosteriorOdds
  simp [oneStepClassObservationMass, oneStepComplementObservationMass, hComp, hOut]
  field_simp [hComp, hOut]

theorem oneStepClassPosteriorOdds_eq_oneStepObservationOddsRaw
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O)
    (hZ : U.oneStepObservationEvidence π h a C o ≠ 0)
    (hDen : U.oneStepComplementObservationMass π h a C o ≠ 0) :
    U.oneStepClassPosteriorOdds π h a C o =
      U.oneStepObservationOddsRaw π h a C o := by
  unfold oneStepClassPosteriorOdds oneStepObservationOddsRaw
  unfold oneStepClassPosteriorMass oneStepComplementPosteriorMass
  simp [hZ, hDen]
  field_simp [hZ, hDen]

/-- Observer-fiber specialization of the raw one-step posterior-odds update. -/
theorem oneStepObserverFiberPosteriorOdds_eq_mul_likelihoodRatio
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (o : O)
    (hComp : U.complementPosteriorMass π h (U.observerFiber ω pstar) ≠ 0)
    (hOut : (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o ≠ 0) :
    U.oneStepObservationOddsRaw π h a (U.observerFiber ω pstar) o =
      U.observerFiberPosteriorOdds π h ω pstar *
        ((U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o /
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o) := by
  simpa [observerFiberPosteriorOdds] using
    U.oneStepObservationOddsRaw_eq_classPosteriorOdds_mul_likelihoodRatio
      π h a (U.observerFiber ω pstar) o hComp hOut

theorem softOneStepClassResidualOdds_eq_mul_likelihoodRatio
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (hClass : U.posteriorClassMass π h C ≠ 0)
    (hIn : (U.softPredictiveLawInClass π h a C refLaw ε).mass o ≠ 0) :
    U.softOneStepClassResidualOdds π h a C refLaw ε o =
      U.residualClassPosteriorOdds π h C *
        ((U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o /
          (U.softPredictiveLawInClass π h a C refLaw ε).mass o) := by
  unfold softOneStepClassResidualOdds residualClassPosteriorOdds
  simp [softOneStepClassObservationMass, softOneStepComplementObservationMass, hClass, hIn]
  field_simp [hClass, hIn]

/--
Observer-fiber specialization of the smoothed residual one-step update.
-/
theorem softOneStepObserverFiberResidualOdds_eq_mul_likelihoodRatio
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (hClass : U.posteriorClassMass π h (U.observerFiber ω pstar) ≠ 0)
    (hIn : (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ≠ 0) :
    U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o =
      U.residualObserverFiberPosteriorOdds π h ω pstar *
        ((U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o /
          (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) := by
  simpa [residualObserverFiberPosteriorOdds, softOneStepObserverFiberResidualOdds] using
    U.softOneStepClassResidualOdds_eq_mul_likelihoodRatio
      π h a (U.observerFiber ω pstar) refLaw ε o hClass hIn

theorem softOneStepObserverFiberResidualOdds_pos_of_positive
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ConcreteLaw O) (ε : Rat) (o : O)
    (hOdds : 0 < U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hInPos :
      0 < (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o)
    (hOutPos :
      0 < (U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) :
    0 < U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o := by
  have hClass :
      U.posteriorClassMass π h (U.observerFiber ω pstar) ≠ 0 := by
    by_cases hZero : U.posteriorClassMass π h (U.observerFiber ω pstar) = 0
    · have hOddsZero : U.residualObserverFiberPosteriorOdds π h ω pstar = 0 := by
        simp [residualObserverFiberPosteriorOdds, residualClassPosteriorOdds, hZero]
      linarith [hOddsZero]
    · exact hZero
  have hIn : (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ≠ 0 :=
    ne_of_gt hInPos
  rw [U.softOneStepObserverFiberResidualOdds_eq_mul_likelihoodRatio
      π h a ω pstar refLaw ε o hClass hIn]
  have hRatio : 0 <
      (U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o /
      (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o := by
    exact div_pos hOutPos hInPos
  exact mul_pos hOdds hRatio

/--
Under additive positive-support smoothing, a zero-out observation becomes a strict but
nonzero contraction of the residual odds multiplier.
-/
theorem softPredictiveResidualLikelihoodRatio_lt_one_of_zeroOut
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) {ε : Rat} (o : O)
    (hε : 0 < ε)
    (hIn : 0 < (U.predictiveLawInClass π h a C).mass o)
    (hOut : (U.predictiveLawOutsideClass π h a C).mass o = 0)
    (hRef : 0 < refLaw.mass o) :
    ((U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o /
      (U.softPredictiveLawInClass π h a C refLaw ε).mass o) < 1 := by
  have hNum :
      (U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o = ε * refLaw.mass o := by
    simp [ConcretePrefixMachine.softPredictiveLawOutsideClass, ConcreteLaw.soften, hOut]
  have hDen :
      (U.softPredictiveLawInClass π h a C refLaw ε).mass o =
        (U.predictiveLawInClass π h a C).mass o + ε * refLaw.mass o := by
    simp [ConcretePrefixMachine.softPredictiveLawInClass, ConcreteLaw.soften]
  have hEpsRef : 0 < ε * refLaw.mass o := mul_pos hε hRef
  have hDenGt :
      ε * refLaw.mass o <
        (U.predictiveLawInClass π h a C).mass o + ε * refLaw.mass o := by
    linarith
  have hDenPos :
      0 < (U.predictiveLawInClass π h a C).mass o + ε * refLaw.mass o := by
    linarith
  rw [hNum, hDen]
  exact (div_lt_one hDenPos).2 hDenGt

theorem softPredictiveResidualLikelihoodRatio_lt_one_of_zeroOut_supportUnion
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    {ε : Rat} (o : O)
    (hε : 0 < ε)
    (hIn : 0 < (U.predictiveLawInClass π h a C).mass o)
    (hOut : (U.predictiveLawOutsideClass π h a C).mass o = 0) :
    ((U.softPredictiveLawOutsideClass π h a C
        (ConcreteLaw.positiveReferenceLaw
          (supportUnion (U.predictiveLawInClass π h a C)
            (U.predictiveLawOutsideClass π h a C)))
        ε).mass o /
      (U.softPredictiveLawInClass π h a C
        (ConcreteLaw.positiveReferenceLaw
          (supportUnion (U.predictiveLawInClass π h a C)
            (U.predictiveLawOutsideClass π h a C)))
        ε).mass o) < 1 := by
  have hRef :
      0 <
        (ConcreteLaw.positiveReferenceLaw
          (supportUnion (U.predictiveLawInClass π h a C)
            (U.predictiveLawOutsideClass π h a C))).mass o :=
    positiveReferenceLaw_supportUnion_mass_pos_of_left_mass_ne_zero
      (μ := U.predictiveLawInClass π h a C)
      (ν := U.predictiveLawOutsideClass π h a C)
      (ne_of_gt hIn)
  simpa using
    U.softPredictiveResidualLikelihoodRatio_lt_one_of_zeroOut
      π h a C
      (ConcreteLaw.positiveReferenceLaw
        (supportUnion (U.predictiveLawInClass π h a C)
          (U.predictiveLawOutsideClass π h a C)))
      o hε hIn hOut hRef

/--
With canonical support-union smoothing and a floor-dependent softening strength, the
smoothed residual likelihood ratio is bounded by `posteriorDecayFactor δ`.

Unlike the legacy zero-collapse theorem for `oneStepObserverFiberPosteriorOdds`, this
bound is genuinely load-bearing: the factor on the right is used quantitatively through
the chosen softening scale and not merely threaded through a proof whose left-hand side
has already collapsed to `0`.
-/
theorem softPredictiveResidualLikelihoodRatio_le_decayFactor_of_zeroOut_supportUnion
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    {δ : Rat} (hδ : 0 < δ)
    (o : O)
    (hIn : 0 < (U.predictiveLawInClass π h a C).mass o)
    (hOut : (U.predictiveLawOutsideClass π h a C).mass o = 0) :
    let refLaw :=
      ConcreteLaw.positiveReferenceLaw
        (supportUnion (U.predictiveLawInClass π h a C)
          (U.predictiveLawOutsideClass π h a C))
    let ε := posteriorDecayFactor δ * (U.predictiveLawInClass π h a C).mass o / 2
    ((U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o /
      (U.softPredictiveLawInClass π h a C refLaw ε).mass o) ≤ posteriorDecayFactor δ := by
  let refLaw :=
    ConcreteLaw.positiveReferenceLaw
      (supportUnion (U.predictiveLawInClass π h a C)
        (U.predictiveLawOutsideClass π h a C))
  let ε := posteriorDecayFactor δ * (U.predictiveLawInClass π h a C).mass o / 2
  have hRefOne : refLaw.mass o = 1 := by
    simpa [refLaw] using
      positiveReferenceLaw_supportUnion_mass_eq_one_of_left_mass_ne_zero
        (μ := U.predictiveLawInClass π h a C)
        (ν := U.predictiveLawOutsideClass π h a C)
        (ne_of_gt hIn)
  have hFactorPos : 0 < posteriorDecayFactor δ := posteriorDecayFactor_pos_of_pos hδ
  have hEpsPos : 0 < ε := by
    dsimp [ε]
    positivity
  have hNum :
      (U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o = ε := by
    simp [ConcretePrefixMachine.softPredictiveLawOutsideClass, ConcreteLaw.soften, hOut, hRefOne]
  have hDen :
      (U.softPredictiveLawInClass π h a C refLaw ε).mass o =
        (U.predictiveLawInClass π h a C).mass o + ε := by
    simp [ConcretePrefixMachine.softPredictiveLawInClass, ConcreteLaw.soften, hRefOne]
  have hDenPos :
      0 < (U.predictiveLawInClass π h a C).mass o + ε := by
    linarith
  dsimp [refLaw, ε]
  rw [hNum, hDen]
  refine (div_le_iff₀ hDenPos).2 ?_
  have hMassNonneg : 0 ≤ (U.predictiveLawInClass π h a C).mass o := le_of_lt hIn
  have hProdNonneg :
      0 ≤ posteriorDecayFactor δ * (U.predictiveLawInClass π h a C).mass o := by
    exact mul_nonneg (le_of_lt hFactorPos) hMassNonneg
  have hHalfLe :
      (1 / 2 : Rat) ≤ 1 + posteriorDecayFactor δ / 2 := by
    linarith
  calc
    posteriorDecayFactor δ * (U.predictiveLawInClass π h a C).mass o / 2
        = (posteriorDecayFactor δ * (U.predictiveLawInClass π h a C).mass o) * (1 / 2 : Rat) := by
            ring
    _ ≤ (posteriorDecayFactor δ * (U.predictiveLawInClass π h a C).mass o) *
          (1 + posteriorDecayFactor δ / 2) := by
            exact mul_le_mul_of_nonneg_left hHalfLe hProdNonneg
    _ = posteriorDecayFactor δ *
          ((U.predictiveLawInClass π h a C).mass o +
            posteriorDecayFactor δ * (U.predictiveLawInClass π h a C).mass o / 2) := by
            ring

theorem softObserverFiberResidualWitness_of_zeroOut
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {ε : Rat} (o : O)
    (hε : 0 < ε)
    (hIn :
      0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o)
    (hOut :
      (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    let refLaw :=
      ConcreteLaw.positiveReferenceLaw
        (supportUnion
          (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)))
    0 <
        (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ∧
      0 <
        (U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ∧
      ((U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o /
        (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) < 1 := by
  let refLaw :=
    ConcreteLaw.positiveReferenceLaw
      (supportUnion
        (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
        (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)))
  have hInPos :
      0 <
        (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o := by
    exact U.softPredictiveLawInClass_mass_pos_of_positiveReferenceLaw_supportUnion
      π h a (U.observerFiber ω pstar) (le_of_lt hIn) (ne_of_gt hIn) hε
  have hOutPos :
      0 <
        (U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o := by
    have hOutNonneg :
        0 ≤ (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o := by
      simp [hOut]
    have hRef :
        0 < refLaw.mass o := by
      simpa [refLaw] using
        positiveReferenceLaw_supportUnion_mass_pos_of_left_mass_ne_zero
          (μ := U.predictiveLawInClass π h a (U.observerFiber ω pstar))
          (ν := U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar))
          (ne_of_gt hIn)
    exact U.softPredictiveLawOutsideClass_mass_pos_of_reference
      π h a (U.observerFiber ω pstar) refLaw hOutNonneg hε hRef
  have hRatio :
      ((U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o /
        (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) < 1 := by
    simpa [refLaw] using
      U.softPredictiveResidualLikelihoodRatio_lt_one_of_zeroOut_supportUnion
        π h a (U.observerFiber ω pstar) o hε hIn hOut
  exact ⟨hInPos, hOutPos, hRatio⟩

theorem exists_softObserverFiberResidualWitness_of_positiveFloor
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    {δ ε : Rat} (hδ : 0 < δ) (hε : 0 < ε)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ)
    (hDecayPos :
      ∀ ⦃a : A⦄, a ∈ actions → κ.mass a ≠ 0 → U.isSeparatingAction π h ω pstar a →
        ∃ o,
          0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ∧
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    ∃ a o refLaw,
      a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a ∧
      refLaw =
        ConcreteLaw.positiveReferenceLaw
          (supportUnion
            (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
            (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar))) ∧
      0 < (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ∧
      0 < (U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ∧
      ((U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o /
        (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) < 1 := by
  rcases exists_supported_action_of_positiveSeparatingSupportFloor
      (κ := κ) (actions := actions) (S := U.separatingActionSet π h ω pstar) hδ hFloor with
    ⟨a, ha, hMass, hSep⟩
  rcases hDecayPos ha hMass hSep with ⟨o, hIn, hOut⟩
  let refLaw :=
    ConcreteLaw.positiveReferenceLaw
      (supportUnion
        (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
        (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)))
  have hWitness :=
    U.softObserverFiberResidualWitness_of_zeroOut π h a ω pstar o hε hIn hOut
  refine ⟨a, o, refLaw, ha, hMass, hSep, rfl, ?_, ?_, ?_⟩
  · simpa [refLaw] using hWitness.1
  · simpa [refLaw] using hWitness.2.1
  · simpa [refLaw] using hWitness.2.2

/--
Load-bearing positive-support one-step contraction on the residual observer-fiber odds.

This theorem uses the smoothed positive-support substrate introduced for the strong
Section 6 closure. The factor `posteriorDecayFactor δ` on the right is actually used to
choose the softening scale and to bound the residual likelihood ratio; the proof does not
pass through a zero-collapse shortcut.
-/
theorem softOneStepObserverFiberResidualOdds_le_decayBound_of_zeroOut_supportUnion
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {δ : Rat} (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (o : O)
    (hIn :
      0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o)
    (hOut :
      (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    let refLaw :=
      ConcreteLaw.positiveReferenceLaw
        (supportUnion
          (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)))
    let ε := posteriorDecayFactor δ *
      (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o / 2
    U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o ≤
      posteriorDecayFactor δ * U.residualObserverFiberPosteriorOdds π h ω pstar := by
  let refLaw :=
    ConcreteLaw.positiveReferenceLaw
      (supportUnion
        (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
        (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)))
  let ε := posteriorDecayFactor δ *
    (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o / 2
  by_cases hClass :
      U.posteriorClassMass π h (U.observerFiber ω pstar) = 0
  · have hResidualZero :
        U.residualObserverFiberPosteriorOdds π h ω pstar = 0 := by
      simp [residualObserverFiberPosteriorOdds, residualClassPosteriorOdds, hClass]
    have hSoftZero :
        U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o = 0 := by
      simp [softOneStepObserverFiberResidualOdds, softOneStepClassResidualOdds,
        softOneStepClassObservationMass, hClass]
    simp [refLaw, ε, hResidualZero, hSoftZero]
  · have hInSoftPos :
        0 <
          (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o := by
      have hFactorPos : 0 < posteriorDecayFactor δ := posteriorDecayFactor_pos_of_pos hδ
      have hEpsPos : 0 < ε := by
        dsimp [ε]
        positivity
      exact U.softPredictiveLawInClass_mass_pos_of_positiveReferenceLaw_supportUnion
        π h a (U.observerFiber ω pstar) (le_of_lt hIn) (ne_of_gt hIn) hEpsPos
    have hInSoft :
        (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o ≠ 0 :=
      ne_of_gt hInSoftPos
    dsimp [refLaw, ε]
    rw [U.softOneStepObserverFiberResidualOdds_eq_mul_likelihoodRatio
        π h a ω pstar refLaw ε o hClass hInSoft]
    have hRatioLe :
        ((U.softPredictiveLawOutsideClass π h a (U.observerFiber ω pstar) refLaw ε).mass o /
          (U.softPredictiveLawInClass π h a (U.observerFiber ω pstar) refLaw ε).mass o) ≤
          posteriorDecayFactor δ := by
      simpa [refLaw, ε] using
        U.softPredictiveResidualLikelihoodRatio_le_decayFactor_of_zeroOut_supportUnion
          π h a (U.observerFiber ω pstar) hδ o hIn hOut
    have hMul := mul_le_mul_of_nonneg_left hRatioLe hOdds0
    simpa [mul_comm] using hMul

/--
Positive separating-support floor yields a smoothed positive-support contraction witness
for the residual observer-fiber odds.
-/
theorem exists_softOneStepObserverFiberResidualOdds_le_decayBound_of_positiveFloor
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    {δ : Rat} (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.residualObserverFiberPosteriorOdds π h ω pstar)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ)
    (hDecayPos :
      ∀ ⦃a : A⦄, a ∈ actions → κ.mass a ≠ 0 → U.isSeparatingAction π h ω pstar a →
        ∃ o,
          0 < (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ∧
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    ∃ a o refLaw ε,
      a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a ∧
      refLaw =
        ConcreteLaw.positiveReferenceLaw
          (supportUnion
            (U.predictiveLawInClass π h a (U.observerFiber ω pstar))
            (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar))) ∧
      ε = posteriorDecayFactor δ *
        (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o / 2 ∧
      0 < ε ∧
      U.softOneStepObserverFiberResidualOdds π h a ω pstar refLaw ε o ≤
        posteriorDecayFactor δ * U.residualObserverFiberPosteriorOdds π h ω pstar := by
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
  have hFactorPos : 0 < posteriorDecayFactor δ := posteriorDecayFactor_pos_of_pos hδ
  have hEpsPos : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨a, o, refLaw, ε, ha, hMass, hSep, rfl, rfl, hEpsPos, ?_⟩
  simpa [refLaw, ε] using
    U.softOneStepObserverFiberResidualOdds_le_decayBound_of_zeroOut_supportUnion
      π h a ω pstar hδ hOdds0 o hIn hOut

theorem oneStepClassPosteriorOdds_eq_zero_of_complementPosteriorMass_eq_zero
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] (o : O)
    (hZero : U.oneStepComplementPosteriorMass π h a C o = 0) :
    U.oneStepClassPosteriorOdds π h a C o = 0 := by
  unfold oneStepClassPosteriorOdds
  simp [hZero]

/-- Observer-fiber specialization of complement extinction under a zero outside witness. -/
theorem oneStepObserverFiberComplementPosteriorMass_eq_zero_of_outside_zero
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (o : O)
    (hZero : (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    U.oneStepComplementPosteriorMass π h a (U.observerFiber ω pstar) o = 0 := by
  simpa using
    U.oneStepComplementPosteriorMass_eq_zero_of_predictiveLawOutsideClass_zero
      π h a (U.observerFiber ω pstar) o hZero

/--
Observer-fiber one-step posterior odds collapse to zero at any zero-out observation.
-/
theorem oneStepObserverFiberPosteriorOdds_eq_zero_of_outside_zero
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (o : O)
    (hZero : (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    U.oneStepObserverFiberPosteriorOdds π h a ω pstar o = 0 := by
  classical
  unfold oneStepObserverFiberPosteriorOdds
  exact U.oneStepClassPosteriorOdds_eq_zero_of_complementPosteriorMass_eq_zero
    π h a (U.observerFiber ω pstar) o
    (U.oneStepObserverFiberComplementPosteriorMass_eq_zero_of_outside_zero
      π h a ω pstar o hZero)

/--
Per-step posterior-decay bound at a zero-out observation.

Under the current finite-support rational substrate, this inequality is established by
the stronger fact `hCollapse`: the updated observer-fiber posterior odds are exactly `0`
once the complement predictive law vanishes at the observed `o`. The nondegenerate
factor `posteriorDecayFactor δ` is therefore not load-bearing in this local proof; it is
threaded here so the downstream `N`-step recurrence and rate composition theorems can
reuse the same interface when the substrate is later upgraded to a positive-support
likelihood model where the per-step multiplier is no longer forced to collapse to zero.
-/
theorem oneStepObserverFiberPosteriorOdds_le_decayBound_of_outside_zero
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (o : O)
    {δ : Rat} (_hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.observerFiberPosteriorOdds π h ω pstar)
    (hZero : (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    U.oneStepObserverFiberPosteriorOdds π h a ω pstar o ≤
      posteriorDecayFactor δ * U.observerFiberPosteriorOdds π h ω pstar := by
  have hCollapse :
      U.oneStepObserverFiberPosteriorOdds π h a ω pstar o = 0 :=
    U.oneStepObserverFiberPosteriorOdds_eq_zero_of_outside_zero π h a ω pstar o hZero
  have hBoundNonneg :
      0 ≤ posteriorDecayFactor δ * U.observerFiberPosteriorOdds π h ω pstar := by
    exact mul_nonneg (posteriorDecayFactor_nonneg δ) hOdds0
  simpa [hCollapse] using hBoundNonneg

/--
Positive separating-support floor yields an explicit one-step posterior-decay witness.

This theorem extracts a supported separating action from the floor, obtains the zero-out
observation from the decay witness hypothesis, and packages the resulting explicit
multiplicative posterior bound. In the current substrate that bound is still proved by
the zero-collapse route above; the value of exposing it with `posteriorDecayFactor δ`
is that the same witness shape feeds the later recurrence and rate composition layer
without needing a separate API once a positive-support substrate is installed.
-/
theorem oneStepObserverFiberPosteriorOdds_le_decayBound_of_positiveFloor
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (actions : List A) (κ : ActionLaw A)
    [DecidablePred (U.separatingActionSet π h ω pstar)]
    {δ : Rat} (hδ : 0 < δ)
    (hOdds0 : 0 ≤ U.observerFiberPosteriorOdds π h ω pstar)
    (hFloor : hasSeparatingSupportFloor κ actions (U.separatingActionSet π h ω pstar) δ)
    (hDecay :
      ∀ ⦃a : A⦄, a ∈ actions → κ.mass a ≠ 0 → U.isSeparatingAction π h ω pstar a →
        ∃ o,
          (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ≠ 0 ∧
          (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0) :
    ∃ a o, a ∈ actions ∧ κ.mass a ≠ 0 ∧ U.isSeparatingAction π h ω pstar a ∧
      (U.predictiveLawInClass π h a (U.observerFiber ω pstar)).mass o ≠ 0 ∧
      (U.predictiveLawOutsideClass π h a (U.observerFiber ω pstar)).mass o = 0 ∧
      U.oneStepObserverFiberPosteriorOdds π h a ω pstar o ≤
        posteriorDecayFactor δ * U.observerFiberPosteriorOdds π h ω pstar := by
  rcases exists_supported_action_of_positiveSeparatingSupportFloor
      (κ := κ) (actions := actions) (S := U.separatingActionSet π h ω pstar) hδ hFloor with
    ⟨a, ha, hMass, hSep⟩
  rcases hDecay ha hMass hSep with ⟨o, hIn, hOut⟩
  refine ⟨a, o, ha, hMass, hSep, hIn, hOut, ?_⟩
  exact U.oneStepObserverFiberPosteriorOdds_le_decayBound_of_outside_zero
    π h a ω pstar o hδ hOdds0 hOut

end ConcretePrefixMachine

end

end SemanticConvergence
