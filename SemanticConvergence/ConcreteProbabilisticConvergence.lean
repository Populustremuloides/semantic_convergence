import SemanticConvergence.ConcretePosteriorDecay

namespace SemanticConvergence

universe u v w

open Classical
open scoped MeasureTheory ProbabilityTheory

noncomputable section

namespace CountableConcrete

namespace CountablePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

/-- Realized countable interaction trajectories at a fixed finite horizon. -/
abbrev Trajectory (A : Type u) (O : Type v) := CountHist A O

instance instMeasurableSpaceTrajectory : MeasurableSpace (Trajectory A O) := ⊤

instance instMeasurableSingletonClassTrajectory :
    MeasurableSingletonClass (Trajectory A O) where
  measurableSet_singleton _ := by
    trivial

/-- Finite-horizon trajectory law under a concrete policy and realized environment program. -/
def trajectoryLaw (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program) (T : Nat) :
    PMF (Trajectory A O) :=
  CountableConcrete.histPMF π (U.programSemantics penv) T

/-- Prefix of a realized trajectory up to time `t`. -/
def historyPrefix (ξ : Trajectory A O) (t : Nat) : CountHist A O :=
  ξ.take t

/--
Events in the prefix filtration at time `t`: membership depends only on the first `t`
realized action-observation pairs.
-/
def prefixFiltration (t : Nat) : Set (Set (Trajectory A O)) :=
  {E | ∀ ⦃ξ ζ : Trajectory A O⦄, historyPrefix ξ t = historyPrefix ζ t → (ξ ∈ E ↔ ζ ∈ E)}

/--
Adaptedness to the concrete prefix filtration: every level-set event of `X_t` depends only
on the realized trajectory prefix up to time `t`.
-/
def AdaptedToPrefixFiltration {β : Type w} (X : Nat → Trajectory A O → β) : Prop :=
  ∀ t (s : Set β), {ξ | X t ξ ∈ s} ∈ prefixFiltration (A := A) (O := O) t

/--
Residual observer-fiber posterior odds in the countable substrate, oriented as complement
versus class. This is the probabilistic-process companion to the finite-support residual
odds used in the deterministic Section 6 rate skeleton.
-/
def residualObserverFiberPosteriorOdds (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  let mC := U.observerFiberPosteriorWeight π t h ω pstar
  let mComp := U.observerFiberComplementWeight π t h ω pstar
  if mC = 0 then 0 else mComp / mC

/-- Posterior class share induced by a residual-odds value. -/
def posteriorShareFromResidual (r : ENNReal) : ENNReal :=
  if r = ⊤ then 0 else (1 + r)⁻¹

/-- Countable observer-fiber posterior share, viewed through the residual-odds transform. -/
def observerFiberPosteriorShare (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  posteriorShareFromResidual (U.residualObserverFiberPosteriorOdds π t h ω pstar)

/-- Residual observer-fiber odds process along a realized trajectory. -/
def residualObserverFiberProcess (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → Trajectory A O → ENNReal :=
  fun t ξ => U.residualObserverFiberPosteriorOdds π t (historyPrefix ξ t) ω pstar

/-- Observer-fiber posterior-share process along a realized trajectory. -/
def observerFiberPosteriorShareProcess (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → Trajectory A O → ENNReal :=
  fun t ξ => U.observerFiberPosteriorShare π t (historyPrefix ξ t) ω pstar

/-- Initial residual observer-fiber odds at the empty history. -/
def initialResidualObserverFiberOdds (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.residualObserverFiberPosteriorOdds π 0 [] ω pstar

/-- Same-view targets have the same residual observer-fiber posterior odds. -/
theorem residualObserverFiberPosteriorOdds_eq_of_sameView (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.residualObserverFiberPosteriorOdds π t h ω p =
      U.residualObserverFiberPosteriorOdds π t h ω q := by
  have hMass := U.observerFiberPosteriorWeight_eq_of_sameView π t h ω hView
  have hComp := U.observerFiberComplementWeight_eq_of_sameView π t h ω hView
  simp [residualObserverFiberPosteriorOdds, hMass, hComp]

/-- The residual-odds process starts from the empty-history residual odds. -/
theorem residualObserverFiberProcess_zero_eq_initial (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (ξ : Trajectory A O) :
    U.residualObserverFiberProcess π ω pstar 0 ξ =
      U.initialResidualObserverFiberOdds π ω pstar := by
  simp [residualObserverFiberProcess, initialResidualObserverFiberOdds, historyPrefix]

/-- Same-view targets have the same initial residual observer-fiber odds. -/
theorem initialResidualObserverFiberOdds_eq_of_sameView (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.initialResidualObserverFiberOdds π ω p =
      U.initialResidualObserverFiberOdds π ω q := by
  simpa [initialResidualObserverFiberOdds] using
    U.residualObserverFiberPosteriorOdds_eq_of_sameView π 0 ([] : CountHist A O) ω hView

/-- Same-view targets have the same realized residual-odds process. -/
theorem residualObserverFiberProcess_eq_of_sameView (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    ∀ t ξ,
      U.residualObserverFiberProcess π ω p t ξ =
        U.residualObserverFiberProcess π ω q t ξ := by
  intro t ξ
  simpa [residualObserverFiberProcess] using
    U.residualObserverFiberPosteriorOdds_eq_of_sameView π t (historyPrefix ξ t) ω hView

/-- The residual-odds process is adapted to the prefix filtration. -/
theorem residualObserverFiberProcess_adapted (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    AdaptedToPrefixFiltration
      (U.residualObserverFiberProcess π ω pstar) := by
  intro t s ξ ζ hEq
  have hProc :
      U.residualObserverFiberProcess π ω pstar t ξ =
        U.residualObserverFiberProcess π ω pstar t ζ := by
    simpa [residualObserverFiberProcess] using
      congrArg (fun h => U.residualObserverFiberPosteriorOdds π t h ω pstar) hEq
  change U.residualObserverFiberProcess π ω pstar t ξ ∈ s ↔
    U.residualObserverFiberProcess π ω pstar t ζ ∈ s
  rw [hProc]

/-- The posterior-share process is adapted to the prefix filtration. -/
theorem observerFiberPosteriorShareProcess_adapted (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    AdaptedToPrefixFiltration
      (U.observerFiberPosteriorShareProcess π ω pstar) := by
  intro t s ξ ζ hEq
  have hProc :
      U.observerFiberPosteriorShareProcess π ω pstar t ξ =
        U.observerFiberPosteriorShareProcess π ω pstar t ζ := by
    simpa [observerFiberPosteriorShareProcess, observerFiberPosteriorShare,
      residualObserverFiberPosteriorOdds] using
      congrArg (fun h => U.observerFiberPosteriorShare π t h ω pstar) hEq
  change U.observerFiberPosteriorShareProcess π ω pstar t ξ ∈ s ↔
    U.observerFiberPosteriorShareProcess π ω pstar t ζ ∈ s
  rw [hProc]

/-- The posterior share equals one when the residual odds vanish. -/
theorem observerFiberPosteriorShare_eq_one_of_residual_eq_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hRes : U.residualObserverFiberPosteriorOdds π t h ω pstar = 0) :
    U.observerFiberPosteriorShare π t h ω pstar = 1 := by
  simp [observerFiberPosteriorShare, posteriorShareFromResidual, hRes]

/-- `ENNReal`-valued version of the floor-dependent decay factor. -/
def posteriorDecayFactorENNReal (δ : Rat) : ENNReal :=
  ENNReal.ofReal (ConcretePrefixMachine.posteriorDecayFactor δ : ℝ)

/--
Supportwise one-step residual contraction along realized trajectories. This is the
probabilistic-process form of the Section 6 one-step witness package.
-/
def HasSupportwiseResidualRecurrence (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ (U.trajectoryLaw π penv T).support →
    ∀ n, n < T →
      U.residualObserverFiberProcess π ω pstar (n + 1) ξ ≤
        posteriorDecayFactorENNReal δ * U.residualObserverFiberProcess π ω pstar n ξ

/--
Witness-packaged one-step residual contraction along realized trajectories. This is the
bridge point between local Section 6 contraction witnesses and the actual trajectory-side
recurrence used in the probabilistic wrapper.
-/
def HasSupportwiseResidualContractionWitness (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat) : Prop :=
  ∀ ξ, ξ ∈ (U.trajectoryLaw π penv T).support →
    ∀ n, n < T →
      ∃ y : ENNReal,
        y = U.residualObserverFiberProcess π ω pstar (n + 1) ξ ∧
        y ≤ posteriorDecayFactorENNReal δ * U.residualObserverFiberProcess π ω pstar n ξ

/-- Same-view targets inherit the same supportwise residual contraction witness. -/
theorem hasSupportwiseResidualContractionWitness_of_sameView
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (δ : Rat) (T : Nat)
    (hView : ω.view p = ω.view q) :
    U.HasSupportwiseResidualContractionWitness π penv ω p δ T →
      U.HasSupportwiseResidualContractionWitness π penv ω q δ T := by
  intro hWitness ξ hξ n hn
  rcases hWitness ξ hξ n hn with ⟨y, hyEq, hyLe⟩
  refine ⟨y, ?_, ?_⟩
  · rw [← U.residualObserverFiberProcess_eq_of_sameView π ω hView (n + 1) ξ]
    exact hyEq
  · simpa [U.residualObserverFiberProcess_eq_of_sameView π ω hView n ξ] using hyLe

/-- A one-step contraction witness yields the supportwise residual recurrence. -/
theorem hasSupportwiseResidualRecurrence_of_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T) :
    U.HasSupportwiseResidualRecurrence π penv ω pstar δ T := by
  intro ξ hξ n hn
  rcases hWitness ξ hξ n hn with ⟨y, rfl, hy⟩
  exact hy

/--
Supportwise residual recurrence yields the explicit `N`-step bound on the realized
residual-odds process.
-/
theorem supportwise_residualObserverFiberRateBound_of_recurrence
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hStep : U.HasSupportwiseResidualRecurrence π penv ω pstar δ T) :
    ∀ ξ, ξ ∈ (U.trajectoryLaw π penv T).support →
      ∀ N, N ≤ T →
        U.residualObserverFiberProcess π ω pstar N ξ ≤
          posteriorDecayFactorENNReal δ ^ N * U.initialResidualObserverFiberOdds π ω pstar := by
  intro ξ hξ N
  induction N with
  | zero =>
      intro _hN
      simp [initialResidualObserverFiberOdds, residualObserverFiberProcess, historyPrefix]
  | succ n ih =>
      intro hN
      have hnT : n < T := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hN
      calc
        U.residualObserverFiberProcess π ω pstar (n + 1) ξ ≤
            posteriorDecayFactorENNReal δ * U.residualObserverFiberProcess π ω pstar n ξ :=
          hStep ξ hξ n hnT
        _ ≤ posteriorDecayFactorENNReal δ *
            (posteriorDecayFactorENNReal δ ^ n * U.initialResidualObserverFiberOdds π ω pstar) := by
          exact mul_le_mul_left' (ih (Nat.le_of_succ_le hN)) _
        _ = posteriorDecayFactorENNReal δ ^ (n + 1) * U.initialResidualObserverFiberOdds π ω pstar := by
          simp [pow_succ, mul_left_comm, mul_comm]

/--
Supportwise residual recurrence implies almost-sure residual recurrence for the actual
posterior process under the realized trajectory law.
-/
theorem ae_residualObserverFiberRecurrence_of_supportwise
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hStep : U.HasSupportwiseResidualRecurrence π penv ω pstar δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ n, n < T →
        U.residualObserverFiberProcess π ω pstar (n + 1) ξ ≤
          posteriorDecayFactorENNReal δ * U.residualObserverFiberProcess π ω pstar n ξ := by
  rw [MeasureTheory.ae_iff]
  refine (PMF.toMeasure_apply_eq_zero_iff (p := U.trajectoryLaw π penv T) ?_).2 ?_
  · trivial
  · rw [Set.disjoint_left]
    intro ξ hξ hbad
    exact hbad (hStep ξ hξ)

/--
The supportwise residual recurrence yields an almost-sure explicit `N`-step rate bound on
the realized residual-odds process.
-/
theorem ae_residualObserverFiberRateBound_of_supportwise
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hStep : U.HasSupportwiseResidualRecurrence π penv ω pstar δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ N, N ≤ T →
        U.residualObserverFiberProcess π ω pstar N ξ ≤
          posteriorDecayFactorENNReal δ ^ N * U.initialResidualObserverFiberOdds π ω pstar := by
  rw [MeasureTheory.ae_iff]
  refine (PMF.toMeasure_apply_eq_zero_iff (p := U.trajectoryLaw π penv T) ?_).2 ?_
  · trivial
  · rw [Set.disjoint_left]
    intro ξ hξ hbad
    exact hbad (U.supportwise_residualObserverFiberRateBound_of_recurrence π penv ω pstar δ T
      hStep ξ hξ)

/--
Witness-packaged one-step contraction therefore induces almost-sure residual recurrence
for the actual posterior process on realized trajectories.
-/
theorem ae_residualObserverFiberRecurrence_of_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ n, n < T →
        U.residualObserverFiberProcess π ω pstar (n + 1) ξ ≤
          posteriorDecayFactorENNReal δ * U.residualObserverFiberProcess π ω pstar n ξ := by
  exact U.ae_residualObserverFiberRecurrence_of_supportwise π penv ω pstar δ T
    (U.hasSupportwiseResidualRecurrence_of_witness π penv ω pstar δ T hWitness)

/--
Witness-packaged one-step contraction therefore induces the explicit `N`-step rate bound
on realized residual odds, almost surely under the trajectory law.
-/
theorem ae_residualObserverFiberRateBound_of_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ N, N ≤ T →
        U.residualObserverFiberProcess π ω pstar N ξ ≤
          posteriorDecayFactorENNReal δ ^ N * U.initialResidualObserverFiberOdds π ω pstar := by
  exact U.ae_residualObserverFiberRateBound_of_supportwise π penv ω pstar δ T
    (U.hasSupportwiseResidualRecurrence_of_witness π penv ω pstar δ T hWitness)

/-- Residual-odds upper bounds turn into posterior-share lower bounds. -/
theorem posteriorShareFromResidual_lowerBound_of_le {r ε : ENNReal}
    (hεTop : ε ≠ ⊤) (hr : r ≤ ε) :
    (1 + ε)⁻¹ ≤ posteriorShareFromResidual r := by
  have hrTop : r ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hr (lt_top_iff_ne_top.mpr hεTop))
  have hInv :
      (1 + ε)⁻¹ ≤ (1 + r)⁻¹ := by
    simpa [add_comm] using (ENNReal.inv_le_inv).2 (add_le_add_left hr 1)
  simpa [posteriorShareFromResidual, hrTop] using hInv

/--
The `N`-step residual-odds rate bound implies an almost-sure lower bound on the realized
observer-fiber posterior share.
-/
theorem ae_observerFiberPosteriorShareLowerBound_of_witness
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (δ : Rat) (T : Nat)
    (hWitness :
      U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T)
    (hInitTop : U.initialResidualObserverFiberOdds π ω pstar ≠ ⊤) :
    ∀ᵐ ξ ∂(U.trajectoryLaw π penv T).toMeasure,
      ∀ N, N ≤ T →
        (1 + posteriorDecayFactorENNReal δ ^ N *
          U.initialResidualObserverFiberOdds π ω pstar)⁻¹ ≤
          U.observerFiberPosteriorShareProcess π ω pstar N ξ := by
  filter_upwards [U.ae_residualObserverFiberRateBound_of_witness π penv ω pstar δ T hWitness]
    with ξ hRate N hN
  have hBound := hRate N hN
  have hFactorTop : posteriorDecayFactorENNReal δ ^ N ≠ ⊤ := by
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hEpsTop :
      posteriorDecayFactorENNReal δ ^ N * U.initialResidualObserverFiberOdds π ω pstar ≠ ⊤ := by
    intro hTop
    rcases (ENNReal.mul_eq_top).1 hTop with hCase | hCase
    · exact hInitTop hCase.2
    · exact hFactorTop hCase.1
  have hLower :=
    posteriorShareFromResidual_lowerBound_of_le hEpsTop hBound
  simpa [observerFiberPosteriorShareProcess, observerFiberPosteriorShare,
    residualObserverFiberProcess_zero_eq_initial] using hLower

end CountablePrefixMachine

end CountableConcrete

end

end SemanticConvergence
