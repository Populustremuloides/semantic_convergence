import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Process.Filtration
import SemanticConvergence.ConcretePosteriorDecay
import SemanticConvergence.MartingaleContraction

namespace SemanticConvergence

universe u v w

open Classical
open Filter MeasureTheory
open scoped BigOperators MeasureTheory ProbabilityTheory NNReal ENNReal

noncomputable section

namespace CountableConcrete

namespace CountablePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

/-- Discrete measurable structure used for individual countable action-observation events. -/
@[reducible]
def histEventMeasurableSpace (A : Type u) (O : Type v) :
    MeasurableSpace (HistEvent A O) := ⊤

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
Infinite realized action-observation stream.

This is the H5 substrate for all-time realized-process claims. The existing
`Trajectory` type remains the finite-horizon list substrate used by
`trajectoryLaw T`; infinite streams are separate so terminal finite tails cannot
accidentally satisfy or falsify all-time Section 6 hypotheses.
-/
structure InfiniteTrajectory (A : Type u) (O : Type v) where
  event : Nat → HistEvent A O

instance instMeasurableSpaceInfiniteTrajectory :
    MeasurableSpace (InfiniteTrajectory A O) :=
  letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
  MeasurableSpace.comap (fun ξ : InfiniteTrajectory A O => ξ.event)
    (inferInstance : MeasurableSpace (Nat → HistEvent A O))

/-- Prefix of an infinite realized stream up to time `t`. -/
def infiniteHistoryPrefix (ξ : InfiniteTrajectory A O) (t : Nat) : CountHist A O :=
  List.ofFn (fun i : Fin t => ξ.event i)

/--
Infinite stream obtained by following a finite prefix and then repeating a
specified tail event. The explicit tail avoids adding global inhabitedness
assumptions on the action/observation spaces.
-/
def infiniteTrajectoryOfPrefixWithTail
    (h : CountHist A O) (tail : HistEvent A O) : InfiniteTrajectory A O where
  event i := if hi : i < h.length then h.get ⟨i, hi⟩ else tail

/-- Realized action at time `n` on an infinite stream. -/
def infiniteRealizedAction (ξ : InfiniteTrajectory A O) (n : Nat) : A :=
  (ξ.event n).1

/-- Realized observation at time `n` on an infinite stream. -/
def infiniteRealizedObservation (ξ : InfiniteTrajectory A O) (n : Nat) : O :=
  (ξ.event n).2

omit [Encodable A] [Encodable O] in
theorem infiniteHistoryPrefix_length (ξ : InfiniteTrajectory A O) (t : Nat) :
    (infiniteHistoryPrefix ξ t).length = t := by
  simp [infiniteHistoryPrefix]

omit [Encodable A] [Encodable O] in
theorem infiniteHistoryPrefix_ofPrefixWithTail_of_le
    (h : CountHist A O) (tail : HistEvent A O) {t : Nat}
    (ht : t ≤ h.length) :
    infiniteHistoryPrefix (A := A) (O := O)
        (infiniteTrajectoryOfPrefixWithTail (A := A) (O := O) h tail) t =
      h.take t := by
  apply List.ext_getElem
  · simp [infiniteHistoryPrefix, Nat.min_eq_left ht]
  · intro i hiLeft hiRight
    have hit : i < h.length := by
      exact lt_of_lt_of_le (by simpa [infiniteHistoryPrefix] using hiLeft) ht
    simp [infiniteHistoryPrefix, infiniteTrajectoryOfPrefixWithTail, hit]

omit [Encodable A] [Encodable O] in
theorem infiniteHistoryPrefix_ofPrefixWithTail
    (h : CountHist A O) (tail : HistEvent A O) :
    infiniteHistoryPrefix (A := A) (O := O)
        (infiniteTrajectoryOfPrefixWithTail (A := A) (O := O) h tail) h.length =
      h := by
  simpa using
    infiniteHistoryPrefix_ofPrefixWithTail_of_le
      (A := A) (O := O) h tail (le_rfl : h.length ≤ h.length)

omit [Encodable A] [Encodable O] in
theorem infiniteHistoryPrefix_ofPrefixWithTail_appendEvent_current
    (h : CountHist A O) (e tail : HistEvent A O) :
    infiniteHistoryPrefix (A := A) (O := O)
        (infiniteTrajectoryOfPrefixWithTail (A := A) (O := O)
          (appendEvent h e) tail) h.length =
      h := by
  have hle : h.length ≤ (appendEvent h e).length := by
    simp [appendEvent]
  calc
    infiniteHistoryPrefix (A := A) (O := O)
        (infiniteTrajectoryOfPrefixWithTail (A := A) (O := O)
          (appendEvent h e) tail) h.length
        = (appendEvent h e).take h.length := by
            exact infiniteHistoryPrefix_ofPrefixWithTail_of_le
              (A := A) (O := O) (appendEvent h e) tail hle
    _ = h := by
            simp [appendEvent]

omit [Encodable A] [Encodable O] in
/-- Taking the first `t` entries of a longer infinite prefix recovers the `t`-prefix. -/
theorem infiniteHistoryPrefix_take_of_le
    (ξ : InfiniteTrajectory A O) {t u : Nat} (htu : t ≤ u) :
    (infiniteHistoryPrefix ξ u).take t = infiniteHistoryPrefix ξ t := by
  apply List.ext_getElem
  · simp [infiniteHistoryPrefix, Nat.min_eq_left htu]
  · intro i hiLeft hiRight
    simp [infiniteHistoryPrefix]

omit [Encodable A] [Encodable O] in
/--
Equality of a longer prefix determines equality of every shorter prefix.
This is the monotonicity fact used by the canonical prefix filtration.
-/
theorem infiniteHistoryPrefix_eq_of_le_eq
    {ξ ζ : InfiniteTrajectory A O} {t u : Nat} (htu : t ≤ u)
    (hEq : infiniteHistoryPrefix ξ u = infiniteHistoryPrefix ζ u) :
    infiniteHistoryPrefix ξ t = infiniteHistoryPrefix ζ t := by
  have hTake := congrArg (fun h : CountHist A O => h.take t) hEq
  simpa [infiniteHistoryPrefix_take_of_le (A := A) (O := O) ξ htu,
    infiniteHistoryPrefix_take_of_le (A := A) (O := O) ζ htu] using hTake

omit [Encodable A] [Encodable O] in
/-- The `(t+1)`-prefix is obtained by appending the realized event at time `t`. -/
theorem infiniteHistoryPrefix_succ_eq_appendEvent
    (ξ : InfiniteTrajectory A O) (t : Nat) :
    infiniteHistoryPrefix ξ (t + 1) =
      appendEvent (infiniteHistoryPrefix ξ t) (ξ.event t) := by
  simpa [infiniteHistoryPrefix, appendEvent, Nat.succ_eq_add_one] using
    (List.ofFn_succ' (f := fun i : Fin (Nat.succ t) => ξ.event i))

omit [Encodable A] [Encodable O] in
/--
The `(t+1)`-prefix appends the realized action-observation pair at time `t`.
This is the form used by support and adaptedness statements.
-/
theorem infiniteHistoryPrefix_succ_eq_appendEvent_realized
    (ξ : InfiniteTrajectory A O) (t : Nat) :
    infiniteHistoryPrefix ξ (t + 1) =
      appendEvent (infiniteHistoryPrefix ξ t)
        (infiniteRealizedAction ξ t, infiniteRealizedObservation ξ t) := by
  simpa [infiniteRealizedAction, infiniteRealizedObservation] using
    infiniteHistoryPrefix_succ_eq_appendEvent (A := A) (O := O) ξ t

omit [Encodable A] [Encodable O] in
/-- Appending one event is injective in both the prefix and terminal event. -/
theorem appendEvent_eq_appendEvent_iff
    {h₁ h₂ : CountHist A O} {e₁ e₂ : HistEvent A O} :
    appendEvent h₁ e₁ = appendEvent h₂ e₂ ↔ h₁ = h₂ ∧ e₁ = e₂ := by
  constructor
  · intro hEq
    have hDrop := congrArg List.dropLast hEq
    have hLast := congrArg List.getLast? hEq
    constructor
    · simpa [appendEvent] using hDrop
    · simpa [appendEvent] using hLast
  · rintro ⟨rfl, rfl⟩
    rfl

omit [Encodable A] [Encodable O] in
/--
First-principles finite recursive likelihood step: the mass of an appended
history factors into the previous-prefix mass, the chosen action probability,
and the observation-kernel probability.
-/
theorem histPMF_appendEvent
    (π : CountablePolicy A O) (κ : CountableKernel A O)
    (t : Nat) (h : CountHist A O) (a : A) (o : O) :
    histPMF π κ (t + 1) (appendEvent h (a, o)) =
      histPMF π κ t h * π h a * κ h a o := by
  simp [histPMF, PMF.bind_apply, appendEvent_eq_appendEvent_iff]
  rw [ENNReal.tsum_eq_add_tsum_ite h]
  simp only [true_and]
  have hSumAZero :
      ∀ x : CountHist A O, x ≠ h →
        (∑' (a₁ : A), (π x) a₁ *
            ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) = 0 := by
    intro x hx
    rw [ENNReal.tsum_eq_zero]
    intro a₁
    have hSumO :
        (∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro o₁
      have hx' : ¬ h = x := by
        intro hEq
        exact hx hEq.symm
      simp [hx']
    simp [hSumO]
  have hOuter :
      (∑' (x : CountHist A O), if x = h then 0 else
          histPMF π κ t x *
            ∑' (a₁ : A), (π x) a₁ *
              ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : x = h
    · simp [hx]
    · simp [hx, hSumAZero x hx]
  have hOuter' :
      ((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
        ∑' (x : CountHist A O), if x = h then 0 else
          histPMF π κ t x *
            ∑' (a₁ : A), (π x) a₁ *
              ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) =
        histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0 := by
    simp [hOuter]
  have hOuter'' :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) =
        histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0 := by
    simpa using hOuter'
  have hSumOMid :
      ∀ x : A, x ≠ a →
        (∑' (o₁ : O), if a = x ∧ o = o₁ then (κ h x) o₁ else 0) = 0 := by
    intro x hx
    rw [ENNReal.tsum_eq_zero]
    intro o₁
    have hx' : ¬ a = x := by
      intro hEq
      exact hx hEq.symm
    simp [hx']
  have hMidEval :
      (∑' (a₁ : A), (π h) a₁ *
          ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) =
        π h a * κ h a o := by
    rw [ENNReal.tsum_eq_add_tsum_ite a]
    have hMid :
        (∑' (x : A), if x = a then 0 else
            (π h) x * ∑' (o₁ : O), if a = x ∧ o = o₁ then (κ h x) o₁ else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro x
      by_cases hx : x = a
      · simp [hx]
      · simp [hx, hSumOMid x hx]
    rw [hMid, add_zero]
    rw [ENNReal.tsum_eq_add_tsum_ite o]
    have hInnerEval :
        (∑' (x : O), if x = o then 0 else if a = a ∧ o = x then (κ h a) x else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro x
      by_cases hx : x = o
      · simp [hx]
      · have hx' : ¬ o = x := by
          intro hEq
          exact hx hEq.symm
        simp [hx, hx']
    rw [hInnerEval, add_zero]
    simp
  have hOuterGoal :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) =
        histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0 := by
    simpa using hOuter''
  have hOuterSimple :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) =
        histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0 := by
    simpa using hOuterGoal
  have hCollapse :
      (histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) =
        histPMF π κ t h * π h a * κ h a o := by
    calc
      (histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) =
        histPMF π κ t h *
          (∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) := by
        simp
      _ = histPMF π κ t h * (π h a * κ h a o) := by rw [hMidEval]
      _ = histPMF π κ t h * π h a * κ h a o := by simp [mul_assoc]
  have hStartSimplify :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) =
        (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) := by
    simp [true_and]
  have hDecider :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O),
            @ite ENNReal (x = h) (propDecidable (x = h)) 0
              (histPMF π κ t x *
                ∑' (a₁ : A), (π x) a₁ *
                  ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0)) : ENNReal) =
        (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O),
            @ite ENNReal (x = h) (instDecidableEqList x h) 0
              (histPMF π κ t x *
                ∑' (a₁ : A), (π x) a₁ *
                  ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0)) : ENNReal) := by
    congr 1
    refine tsum_congr (fun x => ?_)
    by_cases hx : x = h <;> simp [hx]
  exact hDecider.trans (hStartSimplify.trans (hOuterSimple.trans hCollapse))

omit [Encodable A] [Encodable O] in
/-- Equality of `(t+1)`-prefixes determines equality of the `t`-prefixes. -/
theorem infiniteHistoryPrefix_eq_of_succ_eq
    {ξ ζ : InfiniteTrajectory A O} {t : Nat}
    (hEq : infiniteHistoryPrefix ξ (t + 1) = infiniteHistoryPrefix ζ (t + 1)) :
    infiniteHistoryPrefix ξ t = infiniteHistoryPrefix ζ t := by
  have hApp :
      appendEvent (infiniteHistoryPrefix ξ t)
          (infiniteRealizedAction ξ t, infiniteRealizedObservation ξ t) =
        appendEvent (infiniteHistoryPrefix ζ t)
          (infiniteRealizedAction ζ t, infiniteRealizedObservation ζ t) := by
    rw [← infiniteHistoryPrefix_succ_eq_appendEvent_realized (A := A) (O := O) ξ t,
      ← infiniteHistoryPrefix_succ_eq_appendEvent_realized (A := A) (O := O) ζ t]
    exact hEq
  exact (appendEvent_eq_appendEvent_iff (A := A) (O := O)).1 hApp |>.1

omit [Encodable A] [Encodable O] in
/-- Equality of `(t+1)`-prefixes determines equality of the realized event at time `t`. -/
theorem infiniteRealizedEvent_eq_of_prefix_succ_eq
    {ξ ζ : InfiniteTrajectory A O} {t : Nat}
    (hEq : infiniteHistoryPrefix ξ (t + 1) = infiniteHistoryPrefix ζ (t + 1)) :
    (infiniteRealizedAction ξ t, infiniteRealizedObservation ξ t) =
      (infiniteRealizedAction ζ t, infiniteRealizedObservation ζ t) := by
  have hApp :
      appendEvent (infiniteHistoryPrefix ξ t)
          (infiniteRealizedAction ξ t, infiniteRealizedObservation ξ t) =
        appendEvent (infiniteHistoryPrefix ζ t)
          (infiniteRealizedAction ζ t, infiniteRealizedObservation ζ t) := by
    rw [← infiniteHistoryPrefix_succ_eq_appendEvent_realized (A := A) (O := O) ξ t,
      ← infiniteHistoryPrefix_succ_eq_appendEvent_realized (A := A) (O := O) ζ t]
    exact hEq
  exact (appendEvent_eq_appendEvent_iff (A := A) (O := O)).1 hApp |>.2

omit [Encodable A] [Encodable O] in
/-- Equality of `(t+1)`-prefixes determines equality of realized actions at time `t`. -/
theorem infiniteRealizedAction_eq_of_prefix_succ_eq
    {ξ ζ : InfiniteTrajectory A O} {t : Nat}
    (hEq : infiniteHistoryPrefix ξ (t + 1) = infiniteHistoryPrefix ζ (t + 1)) :
    infiniteRealizedAction ξ t = infiniteRealizedAction ζ t := by
  exact congrArg Prod.fst
    (infiniteRealizedEvent_eq_of_prefix_succ_eq (A := A) (O := O) hEq)

omit [Encodable A] [Encodable O] in
/-- Equality of an `n`-prefix determines equality of any realized action strictly before `n`. -/
theorem infiniteRealizedAction_eq_of_prefix_eq_of_lt
    {ξ ζ : InfiniteTrajectory A O} {i n : Nat} (hi : i < n)
    (hEq : infiniteHistoryPrefix ξ n = infiniteHistoryPrefix ζ n) :
    infiniteRealizedAction ξ i = infiniteRealizedAction ζ i := by
  have hSucc :
      infiniteHistoryPrefix ξ (i + 1) = infiniteHistoryPrefix ζ (i + 1) :=
    infiniteHistoryPrefix_eq_of_le_eq (A := A) (O := O) (Nat.succ_le_of_lt hi) hEq
  exact infiniteRealizedAction_eq_of_prefix_succ_eq (A := A) (O := O) hSucc

omit [Encodable A] [Encodable O] in
/-- Equality of `(t+1)`-prefixes determines equality of realized observations at time `t`. -/
theorem infiniteRealizedObservation_eq_of_prefix_succ_eq
    {ξ ζ : InfiniteTrajectory A O} {t : Nat}
    (hEq : infiniteHistoryPrefix ξ (t + 1) = infiniteHistoryPrefix ζ (t + 1)) :
    infiniteRealizedObservation ξ t = infiniteRealizedObservation ζ t := by
  exact congrArg Prod.snd
    (infiniteRealizedEvent_eq_of_prefix_succ_eq (A := A) (O := O) hEq)

omit [Encodable A] [Encodable O] in
/-- Equality of an `n`-prefix determines equality of any realized observation strictly before `n`. -/
theorem infiniteRealizedObservation_eq_of_prefix_eq_of_lt
    {ξ ζ : InfiniteTrajectory A O} {i n : Nat} (hi : i < n)
    (hEq : infiniteHistoryPrefix ξ n = infiniteHistoryPrefix ζ n) :
    infiniteRealizedObservation ξ i = infiniteRealizedObservation ζ i := by
  have hSucc :
      infiniteHistoryPrefix ξ (i + 1) = infiniteHistoryPrefix ζ (i + 1) :=
    infiniteHistoryPrefix_eq_of_le_eq (A := A) (O := O) (Nat.succ_le_of_lt hi) hEq
  exact infiniteRealizedObservation_eq_of_prefix_succ_eq (A := A) (O := O) hSucc

/-- Prefix cylinder at a specified length and history. -/
def infinitePrefixCylinderAt (t : Nat) (h : CountHist A O) :
    Set (InfiniteTrajectory A O) :=
  {ξ | infiniteHistoryPrefix ξ t = h}

/-- Prefix cylinder at the intrinsic length of the supplied history. -/
def infinitePrefixCylinder (h : CountHist A O) : Set (InfiniteTrajectory A O) :=
  infinitePrefixCylinderAt (A := A) (O := O) h.length h

/--
Bundled infinite trajectory law induced by a countable policy/kernel pair.

The defining contract is finite-prefix agreement: every cylinder determined by
the first `t` action-observation events has the same mass as the finite
recursive law `histPMF π κ t`. This is the Lean surface that later martingale
and Section 6 arguments consume as the infinite Bayes/Gibbs process law.
-/
structure InfiniteTrajectoryLaw
    (π : CountablePolicy A O) (κ : CountableKernel A O) where
  measure : Measure (InfiniteTrajectory A O)
  isProbabilityMeasure : IsProbabilityMeasure measure
  prefix_cylinder_eq_histPMF :
    ∀ t h,
      measure (infinitePrefixCylinderAt (A := A) (O := O) t h) =
        CountableConcrete.histPMF π κ t h

instance instIsProbabilityMeasureInfiniteTrajectoryLaw
    {π : CountablePolicy A O} {κ : CountableKernel A O}
    (P : InfiniteTrajectoryLaw (A := A) (O := O) π κ) :
    IsProbabilityMeasure P.measure :=
  P.isProbabilityMeasure

/-- Environment-specialized infinite Bayes/Gibbs law type. -/
abbrev InfiniteBayesGibbsTrajectoryLaw
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program) :=
  InfiniteTrajectoryLaw (A := A) (O := O) π (U.programSemantics penv)

omit [Encodable A] [Encodable O] in
theorem InfiniteTrajectoryLaw.prefixCylinderAt_eq_histPMF
    {π : CountablePolicy A O} {κ : CountableKernel A O}
    (P : InfiniteTrajectoryLaw (A := A) (O := O) π κ)
    (t : Nat) (h : CountHist A O) :
    P.measure (infinitePrefixCylinderAt (A := A) (O := O) t h) =
      CountableConcrete.histPMF π κ t h :=
  P.prefix_cylinder_eq_histPMF t h

omit [Encodable A] [Encodable O] in
theorem InfiniteTrajectoryLaw.prefixCylinder_eq_histPMF_length
    {π : CountablePolicy A O} {κ : CountableKernel A O}
    (P : InfiniteTrajectoryLaw (A := A) (O := O) π κ)
    (h : CountHist A O) :
    P.measure (infinitePrefixCylinder (A := A) (O := O) h) =
      CountableConcrete.histPMF π κ h.length h := by
  exact P.prefix_cylinder_eq_histPMF h.length h

omit [Encodable A] [Encodable O] in
theorem InfiniteBayesGibbsTrajectoryLaw.prefixCylinderAt_eq_trajectoryLaw
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (P : InfiniteBayesGibbsTrajectoryLaw (A := A) (O := O) U π penv)
    (t : Nat) (h : CountHist A O) :
    P.measure (infinitePrefixCylinderAt (A := A) (O := O) t h) =
      U.trajectoryLaw π penv t h := by
  simpa [InfiniteBayesGibbsTrajectoryLaw, trajectoryLaw] using
    P.prefix_cylinder_eq_histPMF t h

/--
Shifted coordinate space used by the Ionescu-Tulcea constructor for countable
interaction streams. Coordinate `0` is a deterministic dummy; coordinate
`n + 1` is the realized action-observation event at interaction time `n`.
-/
def ionescuTrajectoryState (A : Type u) (O : Type v) : Nat → Type (max u v)
  | 0 => PUnit
  | _ + 1 => HistEvent A O

instance instMeasurableSpaceIonescuTrajectoryState (n : Nat) :
    MeasurableSpace (ionescuTrajectoryState A O n) := by
  cases n with
  | zero =>
      change MeasurableSpace PUnit
      infer_instance
  | succ n =>
      exact histEventMeasurableSpace A O

instance instCountableIonescuTrajectoryState (n : Nat) :
    Countable (ionescuTrajectoryState A O n) := by
  cases n with
  | zero =>
      change Countable PUnit
      infer_instance
  | succ n =>
      change Countable (HistEvent A O)
      infer_instance

instance instDiscreteMeasurableSpaceIonescuTrajectoryState (n : Nat) :
    DiscreteMeasurableSpace (ionescuTrajectoryState A O n) := by
  cases n with
  | zero =>
      change DiscreteMeasurableSpace PUnit
      infer_instance
  | succ n =>
      change @DiscreteMeasurableSpace (HistEvent A O) (histEventMeasurableSpace A O)
      infer_instance

/-- The first `n` genuine events encoded in coordinates `1, ..., n` of an `Iic n` tuple. -/
def ionescuIicPrefix (n : Nat)
    (x : (i : Finset.Iic n) → ionescuTrajectoryState A O i) :
    CountHist A O :=
  List.ofFn fun j : Fin n =>
    x ⟨j.1 + 1, by
      simp [Finset.mem_Iic, Nat.succ_le_of_lt j.2]⟩

/-- The first `t` genuine events of a full shifted Ionescu stream. -/
def ionescuStreamPrefix
    (x : (n : Nat) → ionescuTrajectoryState A O n) (t : Nat) :
    CountHist A O :=
  List.ofFn fun j : Fin t => x (j.1 + 1)

omit [Encodable A] [Encodable O] in
theorem ionescuIicPrefix_frestrictLe
    (x : (n : Nat) → ionescuTrajectoryState A O n) (t : Nat) :
    ionescuIicPrefix (A := A) (O := O) t (Preorder.frestrictLe t x) =
      ionescuStreamPrefix (A := A) (O := O) x t := by
  rfl

omit [Encodable A] [Encodable O] in
theorem ionescuIicPrefix_length
    (n : Nat) (x : (i : Finset.Iic n) → ionescuTrajectoryState A O i) :
    (ionescuIicPrefix (A := A) (O := O) n x).length = n := by
  simp [ionescuIicPrefix]

omit [Encodable A] [Encodable O] in
theorem ionescuStreamPrefix_length
    (x : (n : Nat) → ionescuTrajectoryState A O n) (t : Nat) :
    (ionescuStreamPrefix (A := A) (O := O) x t).length = t := by
  simp [ionescuStreamPrefix]

omit [Encodable A] [Encodable O] in
theorem ionescuStreamPrefix_succ_eq_appendEvent
    (x : (n : Nat) → ionescuTrajectoryState A O n) (t : Nat) :
    ionescuStreamPrefix (A := A) (O := O) x (t + 1) =
      appendEvent (ionescuStreamPrefix (A := A) (O := O) x t) (x (t + 1)) := by
  simpa [ionescuStreamPrefix, appendEvent, Nat.succ_eq_add_one] using
    (List.ofFn_succ' (f := fun i : Fin (Nat.succ t) => x (i.1 + 1)))

theorem measurable_eventStreamPrefix (t : Nat) :
    letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
    Measurable
      (fun x : Nat → HistEvent A O => List.ofFn fun j : Fin t => x j.1) := by
  letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
  have hVec :
      Measurable
        (fun x : Nat → HistEvent A O => fun j : Fin t => x j.1) := by
    exact measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
  have hList :
      Measurable (fun v : Fin t → HistEvent A O => List.ofFn v) := by
    exact measurable_of_countable _
  exact hList.comp hVec

omit [Encodable A] [Encodable O] in
theorem measurable_infiniteTrajectory_event :
    letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
    Measurable (fun ξ : InfiniteTrajectory A O => ξ.event) := by
  letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
  exact comap_measurable (fun ξ : InfiniteTrajectory A O => ξ.event)

theorem measurable_infiniteHistoryPrefix (t : Nat) :
    Measurable (fun ξ : InfiniteTrajectory A O =>
      infiniteHistoryPrefix (A := A) (O := O) ξ t) := by
  letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
  exact (measurable_eventStreamPrefix (A := A) (O := O) t).comp
    (measurable_infiniteTrajectory_event (A := A) (O := O))

theorem measurableSet_infinitePrefixCylinderAt (t : Nat) (h : CountHist A O) :
    MeasurableSet (infinitePrefixCylinderAt (A := A) (O := O) t h) := by
  change MeasurableSet
    ((fun ξ : InfiniteTrajectory A O =>
      infiniteHistoryPrefix (A := A) (O := O) ξ t) ⁻¹' {h})
  exact (measurable_infiniteHistoryPrefix (A := A) (O := O) t)
    (measurableSet_singleton h)

theorem measurable_ionescuStreamPrefix (t : Nat) :
    Measurable
      (fun x : (n : Nat) → ionescuTrajectoryState A O n =>
        ionescuStreamPrefix (A := A) (O := O) x t) := by
  letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
  have hVec :
      Measurable
        (fun x : (n : Nat) → ionescuTrajectoryState A O n =>
          fun j : Fin t => x (j.1 + 1)) := by
    refine measurable_pi_iff.mpr fun j => ?_
    simpa using
      (measurable_pi_apply (X := ionescuTrajectoryState A O) (j.1 + 1))
  have hList :
      Measurable (fun v : Fin t → HistEvent A O => List.ofFn v) := by
    exact measurable_of_countable _
  exact hList.comp hVec

/-- The one-step event distribution induced by policy and environment kernels. -/
def ionescuNextEventPMF
    (π : CountablePolicy A O) (κ : CountableKernel A O)
    (h : CountHist A O) : PMF (HistEvent A O) :=
  (π h).bind fun a =>
    (κ h a).bind fun o =>
      PMF.pure (a, o)

omit [Encodable A] [Encodable O] in
theorem pmf_tsum_toReal_eq_one {α : Type*} (p : PMF α) :
    (∑' x : α, (p x).toReal) = 1 := by
  calc
    (∑' x : α, (p x).toReal)
        = (∑' x : α, p x).toReal := by
            exact (ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x)).symm
    _ = 1 := by
            simp [PMF.tsum_coe]

omit [Encodable A] [Encodable O] in
theorem pmf_summable_toReal_mul_of_integrable
    {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (f : α → ℝ)
    (hf : Integrable f p.toMeasure) :
    Summable fun x : α => (p x).toReal * f x := by
  have hfSum :
      Integrable f
        (Measure.sum fun x : α => (p.toMeasure {x}) • Measure.dirac x) := by
    simpa [Measure.sum_smul_dirac] using hf
  have hAbs :
      Summable fun x : α => (p.toMeasure {x}).toReal * ‖f x‖ :=
    hfSum.summable_of_dirac
  have hAbs' :
      Summable fun x : α => (p x).toReal * ‖f x‖ := by
    refine hAbs.congr ?_
    intro x
    rw [PMF.toMeasure_apply_singleton p x (measurableSet_singleton x)]
  have hNorm :
      Summable fun x : α => ‖(p x).toReal * f x‖ := by
    have hEq :
        (fun x : α => ‖(p x).toReal * f x‖) =
          fun x : α => (p x).toReal * ‖f x‖ := by
      funext x
      simp [norm_mul, abs_of_nonneg ENNReal.toReal_nonneg, mul_comm]
    simpa [hEq] using hAbs'
  exact hNorm.of_norm

omit [Encodable A] [Encodable O] in
theorem ionescuNextEventPMF_apply'
    (π : CountablePolicy A O) (κ : CountableKernel A O)
    (h : CountHist A O) (a : A) (o : O) :
    ionescuNextEventPMF (A := A) (O := O) π κ h (a, o) =
      π h a * κ h a o := by
  simp [ionescuNextEventPMF, PMF.bind_apply]
  rw [ENNReal.tsum_eq_add_tsum_ite a]
  simp only [true_and]
  have hInner :
      (∑' (o₁ : O), if o = o₁ then (κ h a) o₁ else 0) =
        (κ h a) o := by
    rw [ENNReal.tsum_eq_add_tsum_ite o]
    have hTail :
        (∑' (x : O), if x = o then 0 else if o = x then (κ h a) x else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro x
      by_cases hx : x = o
      · simp [hx]
      · have hox : ¬ o = x := by
          intro hEq
          exact hx hEq.symm
        simp [hx, hox]
    simp [hTail]
  have hOuter :
      (∑' (x : A), if x = a then 0 else
        (π h) x *
          ∑' (o₁ : O), if a = x ∧ o = o₁ then (κ h x) o₁ else 0) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : x = a
    · simp [hx]
    · have hax : ¬ a = x := by
        intro hEq
        exact hx hEq.symm
      simp [hx, hax]
  simp [hInner, hOuter]

/-- Markov kernel emitting the next shifted event from the already-realized finite prefix. -/
noncomputable def ionescuStepKernel
    (π : CountablePolicy A O) (κ : CountableKernel A O) (n : Nat) :
    ProbabilityTheory.Kernel
      ((i : Finset.Iic n) → ionescuTrajectoryState A O i)
      (ionescuTrajectoryState A O (n + 1)) where
  toFun x :=
    by
      change @Measure (HistEvent A O) (histEventMeasurableSpace A O)
      letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
      exact
        (ionescuNextEventPMF (A := A) (O := O) π κ
          (ionescuIicPrefix (A := A) (O := O) n x)).toMeasure
  measurable' := by
    exact Measurable.of_discrete

instance instIsMarkovKernelIonescuStepKernel
    (π : CountablePolicy A O) (κ : CountableKernel A O) (n : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (ionescuStepKernel (A := A) (O := O) π κ n) where
  isProbabilityMeasure x := by
    rw [ionescuStepKernel]
    dsimp
    change IsProbabilityMeasure
      (@PMF.toMeasure (HistEvent A O) (histEventMeasurableSpace A O)
        (ionescuNextEventPMF (A := A) (O := O) π κ
          (ionescuIicPrefix (A := A) (O := O) n x)))
    infer_instance

theorem integral_ionescuStepKernel_eq_tsum_action_observation
    (π : CountablePolicy A O) (κ : CountableKernel A O) (n : Nat)
    (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
    (f : HistEvent A O → ℝ)
    (hInt :
      Integrable f
        (ionescuStepKernel (A := A) (O := O) π κ n y))
    (hSumm :
      Summable fun e : HistEvent A O =>
        (π (ionescuIicPrefix (A := A) (O := O) n y) e.1).toReal *
          (κ (ionescuIicPrefix (A := A) (O := O) n y) e.1 e.2).toReal *
          f e) :
    ∫ e, f e ∂(ionescuStepKernel (A := A) (O := O) π κ n y) =
      ∑' a : A, ∑' o : O,
        (π (ionescuIicPrefix (A := A) (O := O) n y) a).toReal *
          ((κ (ionescuIicPrefix (A := A) (O := O) n y) a o).toReal *
            f (a, o)) := by
  letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
  let h := ionescuIicPrefix (A := A) (O := O) n y
  let p := ionescuNextEventPMF (A := A) (O := O) π κ h
  have hStepMeasure :
      ionescuStepKernel (A := A) (O := O) π κ n y = p.toMeasure := by
    rw [ionescuStepKernel]
    rfl
  have hIntP : Integrable f p.toMeasure := by
    simpa [p, h, hStepMeasure] using hInt
  have hIntegral :
      ∫ e, f e ∂p.toMeasure =
        ∑' e : HistEvent A O, (p e).toReal * f e := by
    simpa using (PMF.integral_eq_tsum p f hIntP)
  change
    ∫ e : HistEvent A O, f e ∂(ionescuStepKernel (A := A) (O := O) π κ n y) =
      ∑' a : A, ∑' o : O,
        (π (ionescuIicPrefix (A := A) (O := O) n y) a).toReal *
          ((κ (ionescuIicPrefix (A := A) (O := O) n y) a o).toReal *
            f (a, o))
  calc
    ∫ e : HistEvent A O, f e ∂(ionescuStepKernel (A := A) (O := O) π κ n y)
        = ∫ e : HistEvent A O, f e ∂p.toMeasure := by
            rw [hStepMeasure]
            rfl
    _ = ∑' e : HistEvent A O, (p e).toReal * f e := hIntegral
    _ =
        ∑' e : HistEvent A O,
          (((π h e.1) * (κ h e.1 e.2)).toReal) * f e := by
            apply tsum_congr
            intro e
            rcases e with ⟨a, o⟩
            simp [p, h, ionescuNextEventPMF_apply']
    _ =
        ∑' e : HistEvent A O,
          (π h e.1).toReal * (κ h e.1 e.2).toReal * f e := by
            apply tsum_congr
            intro e
            simp [ENNReal.toReal_mul, mul_assoc]
    _ =
        ∑' a : A, ∑' o : O,
          (π h a).toReal * ((κ h a o).toReal * f (a, o)) := by
            simpa [h, mul_assoc] using
              (hSumm.tsum_prod' hSumm.prod_factor)

theorem integral_ionescuStepKernel_eq_tsum_action_observation_of_integrable
    (π : CountablePolicy A O) (κ : CountableKernel A O) (n : Nat)
    (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
    (f : HistEvent A O → ℝ)
    (hInt :
      Integrable f
        (ionescuStepKernel (A := A) (O := O) π κ n y)) :
    ∫ e, f e ∂(ionescuStepKernel (A := A) (O := O) π κ n y) =
      ∑' a : A, ∑' o : O,
        (π (ionescuIicPrefix (A := A) (O := O) n y) a).toReal *
          ((κ (ionescuIicPrefix (A := A) (O := O) n y) a o).toReal *
            f (a, o)) := by
  letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
  let h := ionescuIicPrefix (A := A) (O := O) n y
  let p := ionescuNextEventPMF (A := A) (O := O) π κ h
  have hStepMeasure :
      ionescuStepKernel (A := A) (O := O) π κ n y = p.toMeasure := by
    rw [ionescuStepKernel]
    rfl
  have hIntP : Integrable f p.toMeasure := by
    simpa [p, h, hStepMeasure] using hInt
  have hSummP :
      Summable fun e : HistEvent A O => (p e).toReal * f e :=
    pmf_summable_toReal_mul_of_integrable
      (α := HistEvent A O) p f hIntP
  have hSumm :
      Summable fun e : HistEvent A O =>
        (π (ionescuIicPrefix (A := A) (O := O) n y) e.1).toReal *
          (κ (ionescuIicPrefix (A := A) (O := O) n y) e.1 e.2).toReal *
          f e := by
    have hEq :
        (fun e : HistEvent A O =>
          (π (ionescuIicPrefix (A := A) (O := O) n y) e.1).toReal *
            (κ (ionescuIicPrefix (A := A) (O := O) n y) e.1 e.2).toReal *
            f e) =
          fun e : HistEvent A O => (p e).toReal * f e := by
      funext e
      rcases e with ⟨a, o⟩
      simp [p, h, ionescuNextEventPMF_apply', ENNReal.toReal_mul, mul_assoc]
    simpa [hEq] using hSummP
  exact integral_ionescuStepKernel_eq_tsum_action_observation
    (A := A) (O := O) π κ n y f hInt hSumm

/-- Deterministic dummy law at coordinate zero for the shifted constructor. -/
noncomputable def ionescuInitialMeasure :
    Measure (ionescuTrajectoryState A O 0) :=
  Measure.dirac (PUnit.unit : ionescuTrajectoryState A O 0)

instance instIsProbabilityMeasureIonescuInitialMeasure :
    IsProbabilityMeasure (ionescuInitialMeasure (A := A) (O := O)) := by
  rw [ionescuInitialMeasure]
  infer_instance

/-- Ionescu-Tulcea measure on shifted coordinate streams. -/
noncomputable def ionescuTrajectoryMeasure
    (π : CountablePolicy A O) (κ : CountableKernel A O) :
    Measure ((n : Nat) → ionescuTrajectoryState A O n) :=
  ProbabilityTheory.Kernel.trajMeasure
    (ionescuInitialMeasure (A := A) (O := O))
    (ionescuStepKernel (A := A) (O := O) π κ)

instance instIsProbabilityMeasureIonescuTrajectoryMeasure
    (π : CountablePolicy A O) (κ : CountableKernel A O) :
    IsProbabilityMeasure
      (ionescuTrajectoryMeasure (A := A) (O := O) π κ) := by
  rw [ionescuTrajectoryMeasure]
  infer_instance

/--
Ionescu-Tulcea conditional expectation on the raw shifted coordinate stream.

This is Mathlib's `Kernel.condExp_traj` specialized to the concrete
action-observation stream constructor: conditional on the first `n` shifted
coordinates, the conditional expectation is integration against the continuation
kernel starting from that realized prefix.
-/
theorem condExp_ionescuTrajectory_traj
    (π : CountablePolicy A O) (κ : CountableKernel A O)
    {x₀ : (i : Finset.Iic 0) → ionescuTrajectoryState A O i}
    {n : Nat} {f : ((k : Nat) → ionescuTrajectoryState A O k) → ℝ}
    (hf :
      Integrable f
        (ProbabilityTheory.Kernel.traj
          (ionescuStepKernel (A := A) (O := O) π κ) 0 x₀)) :
    (ProbabilityTheory.Kernel.traj
        (ionescuStepKernel (A := A) (O := O) π κ) 0 x₀)[f |
          Filtration.piLE n] =ᵐ[
        ProbabilityTheory.Kernel.traj
          (ionescuStepKernel (A := A) (O := O) π κ) 0 x₀]
      fun x =>
        ∫ y, f y ∂
          ProbabilityTheory.Kernel.traj
            (ionescuStepKernel (A := A) (O := O) π κ) n
            (Preorder.frestrictLe n x) := by
  exact ProbabilityTheory.Kernel.condExp_traj
    (κ := ionescuStepKernel (A := A) (O := O) π κ)
    (a := 0) (b := n) (x₀ := x₀) (f := f) (Nat.zero_le n) hf

/--
Martingale constructor for processes on the raw Ionescu coordinate stream.

The theorem reduces martingality to the finite one-step kernel identity
`X_n = ∫ X_{n+1} d traj_n(prefix)`. The conditional-expectation step itself is
provided by Ionescu-Tulcea, not assumed as a martingale hypothesis.
-/
theorem martingale_ionescuTrajectory_of_kernel_integral
    (π : CountablePolicy A O) (κ : CountableKernel A O)
    {x₀ : (i : Finset.Iic 0) → ionescuTrajectoryState A O i}
    {X : Nat → ((k : Nat) → ionescuTrajectoryState A O k) → ℝ}
    (hStrong :
      StronglyAdapted
        (Filtration.piLE (X := ionescuTrajectoryState A O)) X)
    (hIntegrable :
      ∀ n,
        Integrable (X n)
          (ProbabilityTheory.Kernel.traj
            (ionescuStepKernel (A := A) (O := O) π κ) 0 x₀))
    (hKernel :
      ∀ n,
        X n =ᵐ[
          ProbabilityTheory.Kernel.traj
            (ionescuStepKernel (A := A) (O := O) π κ) 0 x₀]
          fun x =>
            ∫ y, X (n + 1) y ∂
              ProbabilityTheory.Kernel.traj
                (ionescuStepKernel (A := A) (O := O) π κ) n
                (Preorder.frestrictLe n x)) :
    Martingale X
      (Filtration.piLE (X := ionescuTrajectoryState A O))
      (ProbabilityTheory.Kernel.traj
        (ionescuStepKernel (A := A) (O := O) π κ) 0 x₀) := by
  refine martingale_nat hStrong hIntegrable fun n => ?_
  exact (hKernel n).trans
    ((condExp_ionescuTrajectory_traj (A := A) (O := O) π κ
      (x₀ := x₀) (n := n) (f := X (n + 1)) (hIntegrable (n + 1))).symm)

/--
Extend a shifted Ionescu prefix on coordinates `0, ..., n` by the next
coordinate `n+1`.

This is the finite-prefix version of appending the next realized
action-observation event.
-/
def ionescuIicSuccExtend (n : Nat)
    (x : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
    (e : ionescuTrajectoryState A O (n + 1)) :
    (i : Finset.Iic (n + 1)) → ionescuTrajectoryState A O i :=
  IicProdIoc (X := ionescuTrajectoryState A O) n (n + 1)
    (x, (MeasurableEquiv.piSingleton (X := ionescuTrajectoryState A O) n) e)

omit [Encodable A] [Encodable O] in
theorem ionescuIicSuccExtend_frestrictLe₂
    (n : Nat)
    (x : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
    (e : ionescuTrajectoryState A O (n + 1)) :
    Preorder.frestrictLe₂ (π := ionescuTrajectoryState A O) n.le_succ
      (ionescuIicSuccExtend (A := A) (O := O) n x e) = x := by
  change ((Preorder.frestrictLe₂ (π := ionescuTrajectoryState A O) n.le_succ) ∘
      IicProdIoc (X := ionescuTrajectoryState A O) n (n + 1))
      (x, (MeasurableEquiv.piSingleton (X := ionescuTrajectoryState A O) n) e) = x
  rw [frestrictLe₂_comp_IicProdIoc]

omit [Encodable A] [Encodable O] in
theorem ionescuIicSuccExtend_last
    (n : Nat)
    (x : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
    (e : ionescuTrajectoryState A O (n + 1)) :
    ionescuIicSuccExtend (A := A) (O := O) n x e
      ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ = e := by
  simp [ionescuIicSuccExtend, IicProdIoc, MeasurableEquiv.piSingleton]

omit [Encodable A] [Encodable O] in
theorem ionescuIicPrefix_succ_eq_appendEvent
    (n : Nat) (x : (i : Finset.Iic (n + 1)) → ionescuTrajectoryState A O i) :
    ionescuIicPrefix (A := A) (O := O) (n + 1) x =
      appendEvent
        (ionescuIicPrefix (A := A) (O := O) n
          (Preorder.frestrictLe₂ (π := ionescuTrajectoryState A O) n.le_succ x))
        (x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) := by
  simpa [ionescuIicPrefix, appendEvent, Nat.succ_eq_add_one,
    Preorder.frestrictLe₂_apply] using
    (List.ofFn_succ' (f := fun i : Fin (Nat.succ n) =>
      x ⟨i.1 + 1, by
        simp [Finset.mem_Iic, Nat.succ_le_of_lt i.2]⟩))

omit [Encodable A] [Encodable O] in
theorem ionescuIicPrefix_succExtend
    (n : Nat)
    (x : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
    (e : ionescuTrajectoryState A O (n + 1)) :
    ionescuIicPrefix (A := A) (O := O) (n + 1)
      (ionescuIicSuccExtend (A := A) (O := O) n x e) =
      appendEvent (ionescuIicPrefix (A := A) (O := O) n x) e := by
  rw [ionescuIicPrefix_succ_eq_appendEvent,
    ionescuIicSuccExtend_frestrictLe₂,
    ionescuIicSuccExtend_last]

omit [Encodable A] [Encodable O] in
theorem ionescuIicSuccExtend_frestrictLe
    (n : Nat) (y : (k : Nat) → ionescuTrajectoryState A O k) :
    ionescuIicSuccExtend (A := A) (O := O) n
      (Preorder.frestrictLe n y) (y (n + 1)) =
      Preorder.frestrictLe (n + 1) y := by
  ext i
  by_cases hi : i.1 ≤ n
  · simp [ionescuIicSuccExtend, IicProdIoc, hi, Preorder.frestrictLe_apply]
  · have hgt : n < i.1 := Nat.lt_of_not_ge hi
    have hle : i.1 ≤ n + 1 := Finset.mem_Iic.mp i.2
    have heq : i.1 = n + 1 := le_antisymm hle (Nat.succ_le_of_lt hgt)
    have hi_sub : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext heq
    subst i
    simp [ionescuIicSuccExtend, IicProdIoc, MeasurableEquiv.piSingleton]

/--
Raw shifted-Ionescu martingale constructor over the actual `trajMeasure`.

If a process has finite-prefix representatives `Vₙ` and those representatives
satisfy the one-step kernel identity on every prefix, then the induced raw
coordinate process is a martingale under the Ionescu-Tulcea trajectory measure.
The proof uses the `trajMeasure` one-step composition-product law directly:
`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`.
-/
theorem martingale_ionescuTrajectoryMeasure_of_prefix_kernel_integral
    (π : CountablePolicy A O) (κ : CountableKernel A O)
    {V : (n : Nat) → ((i : Finset.Iic n) → ionescuTrajectoryState A O i) → ℝ}
    (hIntegrable :
      ∀ n, Integrable
        (fun x : (k : Nat) → ionescuTrajectoryState A O k =>
          V n (Preorder.frestrictLe n x))
        (ionescuTrajectoryMeasure (A := A) (O := O) π κ))
    (hStep :
      ∀ n (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i),
        V n y =
          ∫ e, V (n + 1)
            (ionescuIicSuccExtend (A := A) (O := O) n y e)
            ∂(ionescuStepKernel (A := A) (O := O) π κ n y)) :
    Martingale
      (fun n (x : (k : Nat) → ionescuTrajectoryState A O k) =>
        V n (Preorder.frestrictLe n x))
      (Filtration.piLE (X := ionescuTrajectoryState A O))
      (ionescuTrajectoryMeasure (A := A) (O := O) π κ) := by
  let M : Measure ((k : Nat) → ionescuTrajectoryState A O k) :=
    ionescuTrajectoryMeasure (A := A) (O := O) π κ
  let X : Nat → ((k : Nat) → ionescuTrajectoryState A O k) → ℝ :=
    fun n x => V n (Preorder.frestrictLe n x)
  have hStrong : StronglyAdapted (Filtration.piLE (X := ionescuTrajectoryState A O)) X := by
    intro n
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact (Measurable.of_discrete (f := V n)).stronglyMeasurable.comp_measurable
      (comap_measurable (Preorder.frestrictLe (π := ionescuTrajectoryState A O) n))
  refine martingale_of_setIntegral_eq_succ (μ := M) hStrong ?_ ?_
  · intro n
    simpa [X, M] using hIntegrable n
  · intro n s hs
    rw [Filtration.piLE_eq_comap_frestrictLe] at hs
    rcases hs with ⟨S, hS, rfl⟩
    let μn : Measure ((i : Finset.Iic n) → ionescuTrajectoryState A O i) :=
      M.map (Preorder.frestrictLe (π := ionescuTrajectoryState A O) n)
    let K := ionescuStepKernel (A := A) (O := O) π κ n
    let joint : ((k : Nat) → ionescuTrajectoryState A O k) →
        (((i : Finset.Iic n) → ionescuTrajectoryState A O i) ×
          ionescuTrajectoryState A O (n + 1)) :=
      fun x => (Preorder.frestrictLe n x, x (n + 1))
    let g : (((i : Finset.Iic n) → ionescuTrajectoryState A O i) ×
          ionescuTrajectoryState A O (n + 1)) → ℝ :=
      fun z => V (n + 1)
        (ionescuIicSuccExtend (A := A) (O := O) n z.1 z.2)
    have hfrestrict :
        Measurable (Preorder.frestrictLe (π := ionescuTrajectoryState A O) n) :=
      Preorder.measurable_frestrictLe (X := ionescuTrajectoryState A O) n
    have hjoint : Measurable joint := by
      exact hfrestrict.prod (measurable_pi_apply (X := ionescuTrajectoryState A O) (n + 1))
    have hg_asm_map : AEStronglyMeasurable g (Measure.map joint M) := by
      exact (Measurable.of_discrete (f := g)).aestronglyMeasurable
    have hVn_asm : AEStronglyMeasurable (V n) μn := by
      exact (Measurable.of_discrete (f := V n)).aestronglyMeasurable
    have hStepFun : (fun y => V n y) = fun y => ∫ e, g (y, e) ∂K y := by
      funext y
      simpa [g, K] using hStep n y
    have hJointMeasure : μn ⊗ₘ K = Measure.map joint M := by
      change
        (ProbabilityTheory.Kernel.trajMeasure
          (ionescuInitialMeasure (A := A) (O := O))
          (ionescuStepKernel (A := A) (O := O) π κ)).map
            (Preorder.frestrictLe (π := ionescuTrajectoryState A O) n) ⊗ₘ
          ionescuStepKernel (A := A) (O := O) π κ n =
        (ProbabilityTheory.Kernel.trajMeasure
          (ionescuInitialMeasure (A := A) (O := O))
          (ionescuStepKernel (A := A) (O := O) π κ)).map joint
      rw [ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]
    have hIntPair : Integrable g (μn ⊗ₘ K) := by
      rw [hJointMeasure]
      refine (integrable_map_measure hg_asm_map hjoint.aemeasurable).2 ?_
      simpa [g, joint, Function.comp_def,
        ionescuIicSuccExtend_frestrictLe (A := A) (O := O) n, M] using
        hIntegrable (n + 1)
    have hPreimage : joint ⁻¹' (S ×ˢ Set.univ) =
        (Preorder.frestrictLe (π := ionescuTrajectoryState A O) n) ⁻¹' S := by
      ext x
      simp [joint]
    have hFun : (fun x => g (joint x)) = fun x => X (n + 1) x := by
      funext x
      simp [X, g, joint, ionescuIicSuccExtend_frestrictLe (A := A) (O := O) n]
    calc
      ∫ x in (Preorder.frestrictLe (π := ionescuTrajectoryState A O) n) ⁻¹' S,
          X n x ∂M
          = ∫ y in S, V n y ∂μn := by
              rw [setIntegral_map hS hVn_asm hfrestrict.aemeasurable]
      _ = ∫ y in S, ∫ e, g (y, e) ∂K y ∂μn := by
              rw [hStepFun]
      _ = ∫ z in S ×ˢ Set.univ, g z ∂(μn ⊗ₘ K) := by
              rw [MeasureTheory.Measure.setIntegral_compProd hS MeasurableSet.univ
                hIntPair.integrableOn]
              simp
      _ = ∫ z in S ×ˢ Set.univ, g z ∂Measure.map joint M := by
              rw [hJointMeasure]
      _ = ∫ x in joint ⁻¹' (S ×ˢ Set.univ), g (joint x) ∂M := by
              rw [setIntegral_map (hS.prod MeasurableSet.univ) hg_asm_map
                hjoint.aemeasurable]
      _ = ∫ x in (Preorder.frestrictLe (π := ionescuTrajectoryState A O) n) ⁻¹' S,
          X (n + 1) x ∂M := by
              rw [hPreimage, hFun]

/-- Forget the dummy coordinate and expose the genuine event stream. -/
def ionescuStreamToInfiniteTrajectory
    (x : (n : Nat) → ionescuTrajectoryState A O n) :
    InfiniteTrajectory A O where
  event n := x (n + 1)

omit [Encodable A] [Encodable O] in
@[simp]
theorem infiniteHistoryPrefix_ionescuStreamToInfiniteTrajectory
    (x : (n : Nat) → ionescuTrajectoryState A O n) (t : Nat) :
    infiniteHistoryPrefix (A := A) (O := O)
        (ionescuStreamToInfiniteTrajectory (A := A) (O := O) x) t =
      ionescuStreamPrefix (A := A) (O := O) x t := by
  rfl

theorem measurable_ionescuStreamPrefix_piLE (t : Nat) :
    Measurable[
      Filtration.piLE (X := ionescuTrajectoryState A O) t]
      (fun x : (n : Nat) → ionescuTrajectoryState A O n =>
        ionescuStreamPrefix (A := A) (O := O) x t) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hIic :
      Measurable
        (fun y : (i : Finset.Iic t) → ionescuTrajectoryState A O i =>
          ionescuIicPrefix (A := A) (O := O) t y) := by
    exact Measurable.of_discrete
  have hComp :
      Measurable[
        MeasurableSpace.comap
          (Preorder.frestrictLe (π := ionescuTrajectoryState A O) t)
          (inferInstance :
            MeasurableSpace ((i : Finset.Iic t) → ionescuTrajectoryState A O i))]
        (fun x : (n : Nat) → ionescuTrajectoryState A O n =>
          ionescuIicPrefix (A := A) (O := O) t
            (Preorder.frestrictLe t x)) := by
    exact hIic.comp (comap_measurable _)
  simpa [ionescuIicPrefix_frestrictLe (A := A) (O := O)] using hComp

omit [Encodable A] [Encodable O] in
theorem measurable_ionescuStreamToInfiniteTrajectory :
    Measurable
      (ionescuStreamToInfiniteTrajectory (A := A) (O := O)) := by
  letI : MeasurableSpace (HistEvent A O) := histEventMeasurableSpace A O
  change Measurable[
    inferInstance,
    MeasurableSpace.comap (fun ξ : InfiniteTrajectory A O => ξ.event)
      (inferInstance : MeasurableSpace (Nat → HistEvent A O))]
    (ionescuStreamToInfiniteTrajectory (A := A) (O := O))
  rw [measurable_comap_iff]
  refine measurable_pi_iff.mpr fun n => ?_
  simpa [ionescuStreamToInfiniteTrajectory] using
    (measurable_pi_apply (X := ionescuTrajectoryState A O) (n + 1))

/-- Infinite event-stream measure obtained by pushing forward the shifted Ionescu measure. -/
noncomputable def ionescuInfiniteTrajectoryMeasure
    (π : CountablePolicy A O) (κ : CountableKernel A O) :
    Measure (InfiniteTrajectory A O) :=
  (ionescuTrajectoryMeasure (A := A) (O := O) π κ).map
    (ionescuStreamToInfiniteTrajectory (A := A) (O := O))

theorem ionescuInfiniteTrajectoryMeasure_isProbabilityMeasure
    (π : CountablePolicy A O) (κ : CountableKernel A O) :
    IsProbabilityMeasure
      (ionescuInfiniteTrajectoryMeasure (A := A) (O := O) π κ) := by
  rw [ionescuInfiniteTrajectoryMeasure]
  exact Measure.isProbabilityMeasure_map
    (measurable_ionescuStreamToInfiniteTrajectory (A := A) (O := O)).aemeasurable

/--
Events in the infinite-prefix filtration at time `t`: membership depends only
on the first `t` realized action-observation pairs.
-/
def infinitePrefixFiltration (t : Nat) : Set (Set (InfiniteTrajectory A O)) :=
  {E | ∀ ⦃ξ ζ : InfiniteTrajectory A O⦄,
    infiniteHistoryPrefix ξ t = infiniteHistoryPrefix ζ t → (ξ ∈ E ↔ ζ ∈ E)}

/-- The genuine sub-σ-algebra generated by the length-`t` infinite-history prefix. -/
@[reducible]
def infinitePrefixMeasurableSpace (t : Nat) :
    MeasurableSpace (InfiniteTrajectory A O) :=
  MeasurableSpace.comap
    (fun ξ : InfiniteTrajectory A O => infiniteHistoryPrefix (A := A) (O := O) ξ t)
    (inferInstance : MeasurableSpace (CountHist A O))

theorem infinitePrefixMeasurableSpace_le (t : Nat) :
    infinitePrefixMeasurableSpace (A := A) (O := O) t ≤
      (inferInstance : MeasurableSpace (InfiniteTrajectory A O)) := by
  exact (measurable_infiniteHistoryPrefix (A := A) (O := O) t).comap_le

omit [Encodable A] [Encodable O] in
theorem measurable_infiniteHistoryPrefix_prefixMeasurableSpace (t : Nat) :
    Measurable[infinitePrefixMeasurableSpace (A := A) (O := O) t]
      (fun ξ : InfiniteTrajectory A O => infiniteHistoryPrefix (A := A) (O := O) ξ t) := by
  exact comap_measurable _

omit [Encodable A] [Encodable O] in
theorem infinitePrefixMeasurableSpace_mono :
    Monotone (infinitePrefixMeasurableSpace (A := A) (O := O)) := by
  intro t u htu
  have hPrefixU :
      Measurable[infinitePrefixMeasurableSpace (A := A) (O := O) u]
        (fun ξ : InfiniteTrajectory A O => infiniteHistoryPrefix (A := A) (O := O) ξ u) := by
    exact measurable_infiniteHistoryPrefix_prefixMeasurableSpace (A := A) (O := O) u
  have hTake :
      Measurable
        (fun h : CountHist A O => h.take t) := by
    exact Measurable.of_discrete
  have hMeas :
      Measurable[infinitePrefixMeasurableSpace (A := A) (O := O) u]
        (fun ξ : InfiniteTrajectory A O =>
          (infiniteHistoryPrefix (A := A) (O := O) ξ u).take t) :=
    hTake.comp hPrefixU
  refine Measurable.comap_le ?_
  have hFun :
      (fun ξ : InfiniteTrajectory A O =>
          (infiniteHistoryPrefix (A := A) (O := O) ξ u).take t) =
        (fun ξ : InfiniteTrajectory A O => infiniteHistoryPrefix (A := A) (O := O) ξ t) := by
    funext ξ
    exact infiniteHistoryPrefix_take_of_le (A := A) (O := O) ξ htu
  simpa [hFun] using hMeas

/--
Mathlib filtration generated by the canonical infinite prefix maps.
This is the public filtration used by martingale statements.
-/
def infinitePrefixMathlibFiltration :
    Filtration Nat (inferInstance : MeasurableSpace (InfiniteTrajectory A O)) where
  seq := infinitePrefixMeasurableSpace (A := A) (O := O)
  mono' := infinitePrefixMeasurableSpace_mono (A := A) (O := O)
  le' := infinitePrefixMeasurableSpace_le (A := A) (O := O)

theorem measurable_ionescuStreamToInfiniteTrajectory_prefix (t : Nat) :
    Measurable[
      Filtration.piLE (X := ionescuTrajectoryState A O) t,
      infinitePrefixMeasurableSpace (A := A) (O := O) t]
      (ionescuStreamToInfiniteTrajectory (A := A) (O := O)) := by
  rw [infinitePrefixMeasurableSpace]
  rw [measurable_comap_iff]
  simpa [Function.comp_def,
    infiniteHistoryPrefix_ionescuStreamToInfiniteTrajectory (A := A) (O := O)]
    using measurable_ionescuStreamPrefix_piLE (A := A) (O := O) t

/-- Pull a public infinite-trajectory process back to the raw shifted Ionescu stream. -/
def ionescuPullbackInfiniteProcess
    (Y : Nat → InfiniteTrajectory A O → ℝ) :
    Nat → ((k : Nat) → ionescuTrajectoryState A O k) → ℝ :=
  fun n x => Y n (ionescuStreamToInfiniteTrajectory (A := A) (O := O) x)

/--
Prefix-adapted public infinite-trajectory processes remain adapted after
pullback to the raw shifted Ionescu coordinate stream.
-/
theorem stronglyAdapted_ionescuPullbackInfiniteProcess
    {Y : Nat → InfiniteTrajectory A O → ℝ}
    (hYStrong :
      StronglyAdapted (infinitePrefixMathlibFiltration (A := A) (O := O)) Y) :
    StronglyAdapted (Filtration.piLE (X := ionescuTrajectoryState A O))
      (ionescuPullbackInfiniteProcess (A := A) (O := O) Y) := by
  intro n
  exact
    (hYStrong n).comp_measurable
      (measurable_ionescuStreamToInfiniteTrajectory_prefix (A := A) (O := O) n)

set_option maxHeartbeats 1000000

/-- Integrability transfers from the raw pullback process to the pushed-forward stream law. -/
theorem integrable_infiniteTrajectory_of_ionescuPullback
    {μ : Measure ((n : Nat) → ionescuTrajectoryState A O n)}
    {Y : Nat → InfiniteTrajectory A O → ℝ}
    (hYStrong :
      StronglyAdapted (infinitePrefixMathlibFiltration (A := A) (O := O)) Y)
    {n : Nat}
    (hRawIntegrable :
      Integrable (ionescuPullbackInfiniteProcess (A := A) (O := O) Y n) μ) :
    Integrable (Y n)
      (μ.map (ionescuStreamToInfiniteTrajectory (A := A) (O := O))) := by
  let φ := ionescuStreamToInfiniteTrajectory (A := A) (O := O)
  have hφ : Measurable φ :=
    measurable_ionescuStreamToInfiniteTrajectory (A := A) (O := O)
  have hYAE : AEStronglyMeasurable (Y n) (μ.map φ) :=
    ((hYStrong n).mono
      ((infinitePrefixMathlibFiltration (A := A) (O := O)).le n)).aestronglyMeasurable
  exact
    (integrable_map_measure hYAE hφ.aemeasurable).2
      (by simpa [ionescuPullbackInfiniteProcess, φ] using hRawIntegrable)

/--
Prefix-event set-integral equality transfers from the raw stream martingale to
the pushed-forward infinite trajectory law.
-/
theorem setIntegral_infiniteTrajectory_eq_of_ionescuPullback_martingale
    {μ : Measure ((n : Nat) → ionescuTrajectoryState A O n)} [IsFiniteMeasure μ]
    {Y : Nat → InfiniteTrajectory A O → ℝ}
    (hRaw :
      Martingale (ionescuPullbackInfiniteProcess (A := A) (O := O) Y)
        (Filtration.piLE (X := ionescuTrajectoryState A O)) μ)
    (hYStrong :
      StronglyAdapted (infinitePrefixMathlibFiltration (A := A) (O := O)) Y)
    (n : Nat) (s : Set (InfiniteTrajectory A O))
    (hs :
      MeasurableSet[infinitePrefixMathlibFiltration (A := A) (O := O) n] s) :
    ∫ ξ in s, Y n ξ
        ∂(μ.map (ionescuStreamToInfiniteTrajectory (A := A) (O := O))) =
      ∫ ξ in s, Y (n + 1) ξ
        ∂(μ.map (ionescuStreamToInfiniteTrajectory (A := A) (O := O))) := by
  let φ := ionescuStreamToInfiniteTrajectory (A := A) (O := O)
  have hφ : Measurable φ :=
    measurable_ionescuStreamToInfiniteTrajectory (A := A) (O := O)
  have hYAE :
      ∀ m, AEStronglyMeasurable (Y m) (μ.map φ) := by
    intro m
    exact
      ((hYStrong m).mono
        ((infinitePrefixMathlibFiltration (A := A) (O := O)).le m)).aestronglyMeasurable
  have hsFull : MeasurableSet s :=
    (infinitePrefixMathlibFiltration (A := A) (O := O)).le n s hs
  have hPre :
      MeasurableSet[Filtration.piLE (X := ionescuTrajectoryState A O) n]
        (φ ⁻¹' s) :=
    measurable_ionescuStreamToInfiniteTrajectory_prefix (A := A) (O := O) n hs
  have hRawEq :=
    hRaw.setIntegral_eq (Nat.le_succ n) hPre
  rw [setIntegral_map hsFull (hYAE n) hφ.aemeasurable,
    setIntegral_map hsFull (hYAE (n + 1)) hφ.aemeasurable]
  change
    (∫ x in φ ⁻¹' s,
        ionescuPullbackInfiniteProcess (A := A) (O := O) Y n x ∂μ) =
      ∫ x in φ ⁻¹' s,
        ionescuPullbackInfiniteProcess (A := A) (O := O) Y (n + 1) x ∂μ
  exact hRawEq

/--
Push a raw Ionescu-coordinate martingale through the map that forgets the
dummy coordinate. This is the global prefix-filtration lift: conditional
expectations on public infinite trajectories are obtained from Mathlib's
Ionescu-Tulcea martingale theorem plus equality of set integrals on every
public prefix event.
-/
theorem martingale_infiniteTrajectory_of_ionescuPullback_martingale
    {μ : Measure ((n : Nat) → ionescuTrajectoryState A O n)} [IsFiniteMeasure μ]
    {Y : Nat → InfiniteTrajectory A O → ℝ}
    (hRaw :
      Martingale (ionescuPullbackInfiniteProcess (A := A) (O := O) Y)
        (Filtration.piLE (X := ionescuTrajectoryState A O)) μ)
    (hYStrong :
      StronglyAdapted (infinitePrefixMathlibFiltration (A := A) (O := O)) Y) :
    Martingale Y (infinitePrefixMathlibFiltration (A := A) (O := O))
      (μ.map (ionescuStreamToInfiniteTrajectory (A := A) (O := O))) := by
  refine martingale_of_setIntegral_eq_succ hYStrong ?_ ?_
  · intro n
    exact
      integrable_infiniteTrajectory_of_ionescuPullback
        (A := A) (O := O) hYStrong (hRaw.integrable n)
  · intro n s hs
    exact
      setIntegral_infiniteTrajectory_eq_of_ionescuPullback_martingale
        (A := A) (O := O) hRaw hYStrong n s hs

/--
An integrable nonnegative martingale has a uniform `L¹` envelope bounded by its
initial integral.

This is the global replacement for a pointwise finite envelope bound in the
true-law Hellinger route: once the envelope is a nonnegative martingale, a
single initial-integral bound controls every `eLpNorm · 1`.
-/
theorem martingale_eLpNorm_one_bounded_of_nonneg_initial_integral_le
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace Ω)}
    {M : Nat → Ω → ℝ} {C : ℝ≥0}
    (hM : Martingale M ℱ μ)
    (hNonneg : ∀ n, 0 ≤ᵐ[μ] M n)
    (hInit : ∫ x, M 0 x ∂μ ≤ (C : ℝ)) :
    ∀ n, eLpNorm (M n) 1 μ ≤ (C : ℝ≥0∞) := by
  intro n
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hIntEq : ∫ x, M 0 x ∂μ = ∫ x, M n x ∂μ := by
    simpa using
      hM.setIntegral_eq (zero_le n)
        (s := Set.univ)
        (by exact MeasurableSet.univ)
  calc
    (∫⁻ x, ‖M n x‖ₑ ∂μ)
        =
          ∫⁻ x, ENNReal.ofReal (M n x) ∂μ := by
            apply lintegral_congr_ae
            filter_upwards [hNonneg n] with x hx
            exact Real.enorm_eq_ofReal hx
    _ = ENNReal.ofReal (∫ x, M n x ∂μ) := by
          exact (ofReal_integral_eq_lintegral_ofReal (hM.integrable n) (hNonneg n)).symm
    _ = ENNReal.ofReal (∫ x, M 0 x ∂μ) := by
          rw [← hIntEq]
    _ ≤ ENNReal.ofReal (C : ℝ) :=
          ENNReal.ofReal_le_ofReal hInit
    _ = (C : ℝ≥0∞) := by
          exact ENNReal.ofReal_coe_nnreal

/--
Adaptedness to the infinite-prefix filtration: every level-set event of `X_t`
depends only on the realized infinite-stream prefix up to time `t`.
-/
def AdaptedToInfinitePrefixFiltration {β : Type w}
    (X : Nat → InfiniteTrajectory A O → β) : Prop :=
  ∀ t (s : Set β), {ξ | X t ξ ∈ s} ∈
    infinitePrefixFiltration (A := A) (O := O) t

omit [Encodable A] [Encodable O] in
/-- A prefix-adapted level-set process has equal values on trajectories with equal prefixes. -/
theorem eq_of_adaptedToInfinitePrefixFiltration
    {β : Type w} {X : Nat → InfiniteTrajectory A O → β}
    (hX : AdaptedToInfinitePrefixFiltration (A := A) (O := O) X)
    {t : Nat} {ξ ζ : InfiniteTrajectory A O}
    (hEq : infiniteHistoryPrefix ξ t = infiniteHistoryPrefix ζ t) :
    X t ξ = X t ζ := by
  have hIff := hX t {X t ζ} hEq
  exact Set.mem_singleton_iff.mp (hIff.mpr rfl)

omit [Encodable A] [Encodable O] in
/-- A single prefix-dependent real random variable has equal values on equal prefixes. -/
theorem eq_of_infinitePrefixFiltration_levelsets
    {X : InfiniteTrajectory A O → ℝ} {t : Nat}
    (hX : ∀ s : Set ℝ, {ξ | X ξ ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) t)
    {ξ ζ : InfiniteTrajectory A O}
    (hEq : infiniteHistoryPrefix ξ t = infiniteHistoryPrefix ζ t) :
    X ξ = X ζ := by
  have hIff := hX {X ζ} hEq
  exact Set.mem_singleton_iff.mp (hIff.mpr rfl)

/-- Canonical factor through the finite prefix for a prefix-dependent real random variable. -/
noncomputable def infinitePrefixFactor (t : Nat)
    (X : InfiniteTrajectory A O → ℝ) : CountHist A O → ℝ :=
  fun h =>
    if hEx : ∃ ξ : InfiniteTrajectory A O,
        infiniteHistoryPrefix (A := A) (O := O) ξ t = h then
      X hEx.choose
    else
      0

omit [Encodable A] [Encodable O] in
theorem infinitePrefixFactor_comp_eq
    {X : InfiniteTrajectory A O → ℝ} {t : Nat}
    (hX : ∀ s : Set ℝ, {ξ | X ξ ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) t)
    (ξ : InfiniteTrajectory A O) :
    infinitePrefixFactor (A := A) (O := O) t X
        (infiniteHistoryPrefix (A := A) (O := O) ξ t) = X ξ := by
  classical
  unfold infinitePrefixFactor
  have hEx : ∃ ζ : InfiniteTrajectory A O,
      infiniteHistoryPrefix (A := A) (O := O) ζ t =
        infiniteHistoryPrefix (A := A) (O := O) ξ t := ⟨ξ, rfl⟩
  rw [dif_pos hEx]
  exact eq_of_infinitePrefixFiltration_levelsets (A := A) (O := O) hX hEx.choose_spec

omit [Encodable A] [Encodable O] in
theorem infinitePrefixFactor_eq_of_prefix
    {X : InfiniteTrajectory A O → ℝ} {t : Nat} {h : CountHist A O}
    (hX : ∀ s : Set ℝ, {ξ | X ξ ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) t)
    {ξ : InfiniteTrajectory A O}
    (hξ : infiniteHistoryPrefix (A := A) (O := O) ξ t = h) :
    infinitePrefixFactor (A := A) (O := O) t X h = X ξ := by
  rw [← hξ]
  exact infinitePrefixFactor_comp_eq (A := A) (O := O) hX ξ

omit [Encodable A] [Encodable O] in
theorem measurable_of_infinitePrefixFiltration_levelsets_real
    {X : InfiniteTrajectory A O → ℝ} {t : Nat}
    (hX : ∀ s : Set ℝ, {ξ | X ξ ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) t) :
    Measurable[infinitePrefixMeasurableSpace (A := A) (O := O) t] X := by
  classical
  let F := infinitePrefixFactor (A := A) (O := O) t X
  have hF : Measurable F := by
    exact Measurable.of_discrete
  have hPrefix :
      Measurable[infinitePrefixMeasurableSpace (A := A) (O := O) t]
        (fun ξ : InfiniteTrajectory A O => infiniteHistoryPrefix (A := A) (O := O) ξ t) := by
    exact measurable_infiniteHistoryPrefix_prefixMeasurableSpace (A := A) (O := O) t
  have hComp :
      Measurable[infinitePrefixMeasurableSpace (A := A) (O := O) t]
        (fun ξ : InfiniteTrajectory A O => F (infiniteHistoryPrefix (A := A) (O := O) ξ t)) :=
    hF.comp hPrefix
  convert hComp using 1
  ext ξ
  exact (infinitePrefixFactor_comp_eq (A := A) (O := O) hX ξ).symm

omit [Encodable A] [Encodable O] in
theorem stronglyMeasurable_of_infinitePrefixFiltration_levelsets_real
    {X : InfiniteTrajectory A O → ℝ} {t : Nat}
    (hX : ∀ s : Set ℝ, {ξ | X ξ ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) t) :
    StronglyMeasurable[infinitePrefixMeasurableSpace (A := A) (O := O) t] X := by
  exact (measurable_of_infinitePrefixFiltration_levelsets_real (A := A) (O := O) hX).stronglyMeasurable

theorem stronglyAdapted_of_adaptedToInfinitePrefixFiltration_real
    {X : Nat → InfiniteTrajectory A O → ℝ}
    (hX : AdaptedToInfinitePrefixFiltration (A := A) (O := O) X) :
    StronglyAdapted (infinitePrefixMathlibFiltration (A := A) (O := O)) X := by
  intro t
  exact stronglyMeasurable_of_infinitePrefixFiltration_levelsets_real
    (A := A) (O := O) (hX t)

omit [Encodable A] [Encodable O] in
/-- Prefix cylinders are events in the corresponding infinite-prefix filtration. -/
theorem infinitePrefixCylinderAt_mem_infinitePrefixFiltration
    (t : Nat) (h : CountHist A O) :
    infinitePrefixCylinderAt (A := A) (O := O) t h ∈
      infinitePrefixFiltration (A := A) (O := O) t := by
  intro ξ ζ hEq
  simp [infinitePrefixCylinderAt, hEq]

omit [Encodable A] [Encodable O] in
/-- The prefix process is adapted to the infinite-prefix filtration. -/
theorem infiniteHistoryPrefix_adapted :
    AdaptedToInfinitePrefixFiltration (A := A) (O := O)
      (fun t ξ => infiniteHistoryPrefix ξ t) := by
  intro t s ξ ζ hEq
  change infiniteHistoryPrefix ξ t ∈ s ↔ infiniteHistoryPrefix ζ t ∈ s
  rw [hEq]

omit [Encodable A] [Encodable O] in
/-- The realized action at time `t` is measurable with respect to the `(t+1)`-prefix. -/
theorem infiniteRealizedAction_mem_infinitePrefixFiltration_succ
    (t : Nat) (s : Set A) :
    {ξ : InfiniteTrajectory A O | infiniteRealizedAction ξ t ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) (t + 1) := by
  intro ξ ζ hEq
  have hAct :
      infiniteRealizedAction ξ t = infiniteRealizedAction ζ t :=
    infiniteRealizedAction_eq_of_prefix_succ_eq (A := A) (O := O) hEq
  change infiniteRealizedAction ξ t ∈ s ↔ infiniteRealizedAction ζ t ∈ s
  rw [hAct]

omit [Encodable A] [Encodable O] in
/-- The realized observation at time `t` is measurable with respect to the `(t+1)`-prefix. -/
theorem infiniteRealizedObservation_mem_infinitePrefixFiltration_succ
    (t : Nat) (s : Set O) :
    {ξ : InfiniteTrajectory A O | infiniteRealizedObservation ξ t ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) (t + 1) := by
  intro ξ ζ hEq
  have hObs :
      infiniteRealizedObservation ξ t = infiniteRealizedObservation ζ t :=
    infiniteRealizedObservation_eq_of_prefix_succ_eq (A := A) (O := O) hEq
  change infiniteRealizedObservation ξ t ∈ s ↔ infiniteRealizedObservation ζ t ∈ s
  rw [hObs]

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

omit [Encodable A] [Encodable O] in
/-- Countable code weights are strictly positive on every machine-domain program. -/
theorem universalWeight_ne_zero (U : CountablePrefixMachine A O)
    (p : U.Program) :
    U.universalWeight p ≠ 0 := by
  rw [CountablePrefixMachine.universalWeight,
    CountableConcrete.CountablePrefixMachine.codeWeightENNReal]
  rw [ENNReal.ofReal_ne_zero_iff]
  have hNonnegRat : (0 : Rat) ≤ codeWeight (U.programCode p) := by
    unfold codeWeight
    exact Rat.divInt_nonneg (by decide)
      (by exact_mod_cast Nat.zero_le (pow2 (U.programCode p).length))
  have hNeRat : codeWeight (U.programCode p) ≠ 0 := by
    unfold codeWeight
    exact Rat.divInt_ne_zero_of_ne_zero (by decide)
      (by exact_mod_cast pow2_ne_zero (U.programCode p).length)
  have hNeZeroRat : (0 : Rat) ≠ codeWeight (U.programCode p) := by
    simpa [eq_comm] using hNeRat
  have hPosRat : (0 : Rat) < codeWeight (U.programCode p) :=
    lt_of_le_of_ne hNonnegRat hNeZeroRat
  exact_mod_cast hPosRat

/-- Positive likelihood makes the unnormalized posterior weight nonzero. -/
theorem posteriorWeight_ne_zero_of_likelihood_ne_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (p : U.Program)
    (hLik : U.likelihood π t h p ≠ 0) :
    U.posteriorWeight π t h p ≠ 0 := by
  exact ne_of_gt (by
    simpa [CountablePrefixMachine.posteriorWeight] using
      ENNReal.mul_pos (U.universalWeight_ne_zero p) hLik)

/--
Total unnormalized posterior mass over the countable machine domain.

This is the single finiteness denominator from which the class and complement
posterior denominators inherit `≠ ⊤`.
-/
def posteriorTotalWeight (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) : ENNReal :=
  ∑' p : U.Program, U.posteriorWeight π t h p

theorem posteriorTotalWeight_le_universalWeightMass
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) :
    U.posteriorTotalWeight π t h ≤
      ∑' p : U.Program, U.universalWeight p := by
  unfold posteriorTotalWeight
  exact ENNReal.tsum_le_tsum fun p => by
    have hLikLe : U.likelihood π t h p ≤ 1 := by
      simpa [CountablePrefixMachine.likelihood] using
        (CountableConcrete.histPMF π (U.programSemantics p) t).coe_le_one h
    calc
      U.posteriorWeight π t h p
          = U.universalWeight p * U.likelihood π t h p := by
              rfl
      _ ≤ U.universalWeight p * 1 := by
              exact mul_le_mul_right hLikLe (U.universalWeight p)
      _ = U.universalWeight p := by
              simp

theorem posteriorTotalWeight_ne_top_of_universalWeightMass_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (hPrior : (∑' p : U.Program, U.universalWeight p) ≠ ⊤) :
    U.posteriorTotalWeight π t h ≠ ⊤ := by
  intro hTop
  have hTopLe : (⊤ : ENNReal) ≤ ∑' p : U.Program, U.universalWeight p := by
    simpa [hTop] using U.posteriorTotalWeight_le_universalWeightMass π t h
  have hPriorTop : (∑' p : U.Program, U.universalWeight p) = ⊤ := by
    exact le_antisymm le_top hTopLe
  exact hPrior hPriorTop

theorem observerFiberPosteriorWeight_le_posteriorTotalWeight
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.observerFiberPosteriorWeight π t h ω pstar ≤
      U.posteriorTotalWeight π t h := by
  unfold observerFiberPosteriorWeight posteriorTotalWeight
  exact ENNReal.tsum_le_tsum fun p => by
    by_cases hp : U.observerFiber ω pstar p
    · simp [hp]
    · simp [hp]

theorem observerFiberComplementWeight_le_posteriorTotalWeight
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.observerFiberComplementWeight π t h ω pstar ≤
      U.posteriorTotalWeight π t h := by
  unfold observerFiberComplementWeight posteriorTotalWeight
  exact ENNReal.tsum_le_tsum fun p => by
    by_cases hp : U.observerFiber ω pstar p
    · simp [hp]
    · simp [hp]

theorem observerFiberPosteriorWeight_ne_top_of_posteriorTotalWeight_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hTotal : U.posteriorTotalWeight π t h ≠ ⊤) :
    U.observerFiberPosteriorWeight π t h ω pstar ≠ ⊤ := by
  intro hTop
  have hTopLe : (⊤ : ENNReal) ≤ U.posteriorTotalWeight π t h := by
    simpa [hTop] using
      U.observerFiberPosteriorWeight_le_posteriorTotalWeight π t h ω pstar
  have hTotalTop : U.posteriorTotalWeight π t h = ⊤ := by
    exact le_antisymm le_top hTopLe
  exact hTotal hTotalTop

theorem observerFiberComplementWeight_ne_top_of_posteriorTotalWeight_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hTotal : U.posteriorTotalWeight π t h ≠ ⊤) :
    U.observerFiberComplementWeight π t h ω pstar ≠ ⊤ := by
  intro hTop
  have hTopLe : (⊤ : ENNReal) ≤ U.posteriorTotalWeight π t h := by
    simpa [hTop] using
      U.observerFiberComplementWeight_le_posteriorTotalWeight π t h ω pstar
  have hTotalTop : U.posteriorTotalWeight π t h = ⊤ := by
    exact le_antisymm le_top hTopLe
  exact hTotal hTotalTop

/--
Countable likelihood update after appending one realized action-observation
event. This is the Bayes-side companion to `histPMF_appendEvent`.
-/
theorem likelihood_appendEvent
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (a : A) (o : O) (p : U.Program) :
    U.likelihood π (t + 1) (appendEvent h (a, o)) p =
      U.likelihood π t h p * π h a * U.programSemantics p h a o := by
  simpa [CountablePrefixMachine.likelihood] using
    histPMF_appendEvent (π := π) (κ := U.programSemantics p) t h a o

/--
Unnormalized posterior numerator update after one realized event.
-/
theorem posteriorWeight_appendEvent
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (a : A) (o : O) (p : U.Program) :
    U.posteriorWeight π (t + 1) (appendEvent h (a, o)) p =
      U.posteriorWeight π t h p * π h a * U.programSemantics p h a o := by
  unfold CountablePrefixMachine.posteriorWeight
  rw [U.likelihood_appendEvent π t h a o p]
  simp [mul_assoc]

/--
If a positive-likelihood program belongs to the observer fiber, then the
observer-fiber posterior denominator is nonzero.
-/
theorem observerFiberPosteriorWeight_ne_zero_of_program_likelihood_ne_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (p : U.Program)
    (hFiber : U.observerFiber ω pstar p)
    (hLik : U.likelihood π t h p ≠ 0) :
    U.observerFiberPosteriorWeight π t h ω pstar ≠ 0 := by
  have hTermNe : U.posteriorWeight π t h p ≠ 0 :=
    U.posteriorWeight_ne_zero_of_likelihood_ne_zero π t h p hLik
  have hTermLe :
      U.posteriorWeight π t h p ≤
        U.observerFiberPosteriorWeight π t h ω pstar := by
    calc
      U.posteriorWeight π t h p =
          (if U.observerFiber ω pstar p then U.posteriorWeight π t h p else 0) := by
            simp [hFiber]
      _ ≤ ∑' q : U.Program,
          if U.observerFiber ω pstar q then U.posteriorWeight π t h q else 0 :=
            ENNReal.le_tsum p
  intro hZero
  have hTermZero : U.posteriorWeight π t h p = 0 :=
    le_antisymm (by simpa [hZero] using hTermLe) bot_le
  exact hTermNe hTermZero

/--
If a positive-likelihood program lies outside the observer fiber, then the
complement posterior denominator is nonzero.
-/
theorem observerFiberComplementWeight_ne_zero_of_program_likelihood_ne_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (p : U.Program)
    (hNotFiber : ¬ U.observerFiber ω pstar p)
    (hLik : U.likelihood π t h p ≠ 0) :
    U.observerFiberComplementWeight π t h ω pstar ≠ 0 := by
  have hTermNe : U.posteriorWeight π t h p ≠ 0 :=
    U.posteriorWeight_ne_zero_of_likelihood_ne_zero π t h p hLik
  have hTermLe :
      U.posteriorWeight π t h p ≤
        U.observerFiberComplementWeight π t h ω pstar := by
    calc
      U.posteriorWeight π t h p =
          (if U.observerFiber ω pstar p then 0 else U.posteriorWeight π t h p) := by
            simp [hNotFiber]
      _ ≤ ∑' q : U.Program,
          if U.observerFiber ω pstar q then 0 else U.posteriorWeight π t h q :=
            ENNReal.le_tsum p
  intro hZero
  have hTermZero : U.posteriorWeight π t h p = 0 :=
    le_antisymm (by simpa [hZero] using hTermLe) bot_le
  exact hTermNe hTermZero

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

/--
Real-valued residual odds process `Rₙ`.

This is the process consumed by the soft Hellinger martingale spine. It is the
`ENNReal` residual observer-fiber odds process converted to `Real`; future
phases discharge finiteness/non-top side conditions where they are needed.
-/
def realizedResidualOddsProcess (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → Trajectory A O → ℝ :=
  fun t ξ => (U.residualObserverFiberProcess π ω pstar t ξ).toReal

/--
Paper-level one-step Bhattacharyya score shape.

An input `B t h a` is intended to denote the manuscript quantity
`B_t(c*, a; h)`. Phase H1 keeps this as an explicit score so the trajectory
process can be defined before the later phases prove the predictive-law
realization of the score.
-/
abbrev StepBhattacharyyaScore (A : Type u) (O : Type v) :=
  Nat → CountHist A O → A → ℝ

/-- Countable observation law used by the predictive-law Bhattacharyya score. -/
abbrev CountableObservationLaw (O : Type v) :=
  O → ENNReal

/--
Unnormalized one-step class predictive weight.

At history `h` and action `a`, this is the posterior-weighted mixture of the
program kernels over the observer fiber of `pstar`.
-/
def observerFiberPredictiveWeight (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (o : O) : ENNReal :=
  ∑' p : U.Program,
    if U.observerFiber ω pstar p then
      U.posteriorWeight π t h p * U.programSemantics p h a o
    else
      0

/--
Unnormalized one-step complement predictive weight.

This is the posterior-weighted mixture of program kernels outside the observer
fiber of `pstar`.
-/
def observerFiberComplementPredictiveWeight (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (o : O) : ENNReal :=
  ∑' p : U.Program,
    if U.observerFiber ω pstar p then
      0
    else
      U.posteriorWeight π t h p * U.programSemantics p h a o

/--
If a positive-likelihood in-fiber program assigns positive mass to the next
observation, then the in-class predictive denominator for that observation is
nonzero.
-/
theorem observerFiberPredictiveWeight_ne_zero_of_program_support
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (o : O)
    (p : U.Program)
    (hFiber : U.observerFiber ω pstar p)
    (hLik : U.likelihood π t h p ≠ 0)
    (hObs : U.programSemantics p h a o ≠ 0) :
    U.observerFiberPredictiveWeight π t h a ω pstar o ≠ 0 := by
  have hPostNe : U.posteriorWeight π t h p ≠ 0 :=
    U.posteriorWeight_ne_zero_of_likelihood_ne_zero π t h p hLik
  have hTermNe :
      U.posteriorWeight π t h p * U.programSemantics p h a o ≠ 0 := by
    simpa [mul_eq_zero] using
      (show ¬ (U.posteriorWeight π t h p = 0 ∨
          U.programSemantics p h a o = 0) from
        fun hZero => hZero.elim hPostNe hObs)
  have hTermLe :
      U.posteriorWeight π t h p * U.programSemantics p h a o ≤
        U.observerFiberPredictiveWeight π t h a ω pstar o := by
    calc
      U.posteriorWeight π t h p * U.programSemantics p h a o =
          (if U.observerFiber ω pstar p then
            U.posteriorWeight π t h p * U.programSemantics p h a o
          else
            0) := by
            simp [hFiber]
      _ ≤ ∑' q : U.Program,
          if U.observerFiber ω pstar q then
            U.posteriorWeight π t h q * U.programSemantics q h a o
          else
            0 := ENNReal.le_tsum p
  intro hZero
  have hTermZero :
      U.posteriorWeight π t h p * U.programSemantics p h a o = 0 :=
    le_antisymm (by simpa [hZero] using hTermLe) bot_le
  exact hTermNe hTermZero

/--
Observer-fiber posterior mass after appending `(a,o)` is the policy action
mass times the unnormalized in-class predictive observation weight.
-/
theorem observerFiberPosteriorWeight_appendEvent
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A) (o : O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.observerFiberPosteriorWeight π (t + 1) (appendEvent h (a, o)) ω pstar =
      π h a * U.observerFiberPredictiveWeight π t h a ω pstar o := by
  unfold observerFiberPosteriorWeight observerFiberPredictiveWeight
  calc
    (∑' p : U.Program,
        if U.observerFiber ω pstar p then
          U.posteriorWeight π (t + 1) (appendEvent h (a, o)) p
        else
          0)
        =
      ∑' p : U.Program,
        if U.observerFiber ω pstar p then
          U.posteriorWeight π t h p * π h a * U.programSemantics p h a o
        else
          0 := by
            apply tsum_congr
            intro p
            by_cases hp : U.observerFiber ω pstar p
            · simp [hp, U.posteriorWeight_appendEvent π t h a o p]
            · simp [hp]
    _ =
      ∑' p : U.Program,
        π h a *
          (if U.observerFiber ω pstar p then
            U.posteriorWeight π t h p * U.programSemantics p h a o
          else
            0) := by
            apply tsum_congr
            intro p
            by_cases hp : U.observerFiber ω pstar p
            · simp [hp, mul_assoc, mul_left_comm]
            · simp [hp]
    _ = π h a *
        ∑' p : U.Program,
          if U.observerFiber ω pstar p then
            U.posteriorWeight π t h p * U.programSemantics p h a o
          else
            0 := by
          rw [ENNReal.tsum_mul_left]

/--
Observer-fiber complement posterior mass after appending `(a,o)` is the policy
action mass times the unnormalized outside-class predictive observation weight.
-/
theorem observerFiberComplementWeight_appendEvent
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A) (o : O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.observerFiberComplementWeight π (t + 1) (appendEvent h (a, o)) ω pstar =
      π h a * U.observerFiberComplementPredictiveWeight π t h a ω pstar o := by
  unfold observerFiberComplementWeight observerFiberComplementPredictiveWeight
  calc
    (∑' p : U.Program,
        if U.observerFiber ω pstar p then
          0
        else
          U.posteriorWeight π (t + 1) (appendEvent h (a, o)) p)
        =
      ∑' p : U.Program,
        if U.observerFiber ω pstar p then
          0
        else
          U.posteriorWeight π t h p * π h a * U.programSemantics p h a o := by
            apply tsum_congr
            intro p
            by_cases hp : U.observerFiber ω pstar p
            · simp [hp]
            · simp [hp, U.posteriorWeight_appendEvent π t h a o p]
    _ =
      ∑' p : U.Program,
        π h a *
          (if U.observerFiber ω pstar p then
            0
          else
            U.posteriorWeight π t h p * U.programSemantics p h a o) := by
            apply tsum_congr
            intro p
            by_cases hp : U.observerFiber ω pstar p
            · simp [hp]
            · simp [hp, mul_assoc, mul_left_comm]
    _ = π h a *
        ∑' p : U.Program,
          if U.observerFiber ω pstar p then
            0
          else
            U.posteriorWeight π t h p * U.programSemantics p h a o := by
          rw [ENNReal.tsum_mul_left]

/--
Residual odds after an appended event are the outside/in-class predictive
weight ratio, once the realized action and in-class predictive observation
weight are nonzero. This is the local Bayes update in residual-odds form.
-/
theorem residualObserverFiberPosteriorOdds_appendEvent_eq_predictiveWeight_ratio
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A) (o : O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hPolicy : π h a ≠ 0)
    (hPred :
      U.observerFiberPredictiveWeight π t h a ω pstar o ≠ 0) :
    U.residualObserverFiberPosteriorOdds π (t + 1) (appendEvent h (a, o)) ω pstar =
      U.observerFiberComplementPredictiveWeight π t h a ω pstar o /
        U.observerFiberPredictiveWeight π t h a ω pstar o := by
  unfold residualObserverFiberPosteriorOdds
  rw [U.observerFiberPosteriorWeight_appendEvent,
    U.observerFiberComplementWeight_appendEvent]
  have hClassNext :
      π h a * U.observerFiberPredictiveWeight π t h a ω pstar o ≠ 0 := by
    simpa [mul_eq_zero] using
      (show ¬ (π h a = 0 ∨
          U.observerFiberPredictiveWeight π t h a ω pstar o = 0) from
        fun hZero => hZero.elim hPolicy hPred)
  simp [hClassNext]
  exact ENNReal.mul_div_mul_left
    (U.observerFiberComplementPredictiveWeight π t h a ω pstar o)
    (U.observerFiberPredictiveWeight π t h a ω pstar o)
    hPolicy ((π h).apply_ne_top a)

omit [Encodable A] [Encodable O] in
/--
Algebraic residual-odds identity for nondegenerate `ENNReal` masses.
-/
theorem ennreal_residual_mul_predictiveRatio_eq_predictiveWeightRatio
    {mC mD wC wD : ENNReal}
    (hmC0 : mC ≠ 0) (hmCtop : mC ≠ ⊤)
    (hmD0 : mD ≠ 0) (hmDtop : mD ≠ ⊤)
    (hwC0 : wC ≠ 0) (hwCtop : wC ≠ ⊤) :
    mD / mC * ((wD / mD) / (wC / mC)) = wD / wC := by
  rw [(ENNReal.eq_div_iff hwC0 hwCtop)]
  calc
    wC * (mD / mC * ((wD / mD) / (wC / mC)))
        = (mD / mC) * (wC * ((wD / mD) / (wC / mC))) := by
            ac_rfl
    _ = (mD / mC) * ((wD / mD) * (wC / (wC / mC))) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm]
    _ = (mD / mC) * ((wD / mD) * mC) := by
            rw [ENNReal.div_div_cancel hwC0 hwCtop]
    _ = ((mD / mC) * mC) * (wD / mD) := by
            ac_rfl
    _ = mD * (wD / mD) := by
            rw [ENNReal.div_mul_cancel hmC0 hmCtop]
    _ = wD := by
            rw [ENNReal.mul_div_cancel hmD0 hmDtop]

/--
Normalized class predictive law for the next observation.

The zero-total convention is explicit. Later martingale phases should discharge
the nondegenerate posterior-mass hypotheses needed to remove this fallback on
the realized path.
-/
def observerFiberPredictiveLawInClass (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : CountableObservationLaw O :=
  fun o =>
    let mC := U.observerFiberPosteriorWeight π t h ω pstar
    if mC = 0 then 0 else U.observerFiberPredictiveWeight π t h a ω pstar o / mC

/-- Normalized complement predictive law for the next observation. -/
def observerFiberPredictiveLawOutsideClass (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : CountableObservationLaw O :=
  fun o =>
    let mComp := U.observerFiberComplementWeight π t h ω pstar
    if mComp = 0 then 0 else
      U.observerFiberComplementPredictiveWeight π t h a ω pstar o / mComp

/--
Residual odds after an appended event equal the previous residual odds times
the normalized outside/in-class predictive likelihood ratio, under the explicit
nondegeneracy assumptions needed to remove all zero/top fallbacks.
-/
theorem residualObserverFiberPosteriorOdds_appendEvent_eq_residual_mul_predictiveRatio
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A) (o : O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hPolicy : π h a ≠ 0)
    (hClass0 : U.observerFiberPosteriorWeight π t h ω pstar ≠ 0)
    (hClassTop : U.observerFiberPosteriorWeight π t h ω pstar ≠ ⊤)
    (hComp0 : U.observerFiberComplementWeight π t h ω pstar ≠ 0)
    (hCompTop : U.observerFiberComplementWeight π t h ω pstar ≠ ⊤)
    (hPred :
      U.observerFiberPredictiveWeight π t h a ω pstar o ≠ 0)
    (hPredTop :
      U.observerFiberPredictiveWeight π t h a ω pstar o ≠ ⊤) :
    U.residualObserverFiberPosteriorOdds π (t + 1) (appendEvent h (a, o)) ω pstar =
      U.residualObserverFiberPosteriorOdds π t h ω pstar *
        (U.observerFiberPredictiveLawOutsideClass π t h a ω pstar o /
          U.observerFiberPredictiveLawInClass π t h a ω pstar o) := by
  rw [U.residualObserverFiberPosteriorOdds_appendEvent_eq_predictiveWeight_ratio
    π t h a o ω pstar hPolicy hPred]
  unfold residualObserverFiberPosteriorOdds observerFiberPredictiveLawInClass
    observerFiberPredictiveLawOutsideClass
  simp [hClass0, hComp0]
  exact (ennreal_residual_mul_predictiveRatio_eq_predictiveWeightRatio
    (mC := U.observerFiberPosteriorWeight π t h ω pstar)
    (mD := U.observerFiberComplementWeight π t h ω pstar)
    (wC := U.observerFiberPredictiveWeight π t h a ω pstar o)
    (wD := U.observerFiberComplementPredictiveWeight π t h a ω pstar o)
    hClass0 hClassTop hComp0 hCompTop hPred hPredTop).symm

/--
Square-root residual-odds update induced by the local Bayes update.
This is the pointwise multiplicative identity used by the Hellinger envelope.
-/
theorem sqrt_residualObserverFiberPosteriorOdds_appendEvent_eq
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A) (o : O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hPolicy : π h a ≠ 0)
    (hClass0 : U.observerFiberPosteriorWeight π t h ω pstar ≠ 0)
    (hClassTop : U.observerFiberPosteriorWeight π t h ω pstar ≠ ⊤)
    (hComp0 : U.observerFiberComplementWeight π t h ω pstar ≠ 0)
    (hCompTop : U.observerFiberComplementWeight π t h ω pstar ≠ ⊤)
    (hPred :
      U.observerFiberPredictiveWeight π t h a ω pstar o ≠ 0)
    (hPredTop :
      U.observerFiberPredictiveWeight π t h a ω pstar o ≠ ⊤) :
    Real.sqrt
        ((U.residualObserverFiberPosteriorOdds π (t + 1)
          (appendEvent h (a, o)) ω pstar).toReal) =
      Real.sqrt ((U.residualObserverFiberPosteriorOdds π t h ω pstar).toReal) *
        Real.sqrt
          (((U.observerFiberPredictiveLawOutsideClass π t h a ω pstar o) /
            (U.observerFiberPredictiveLawInClass π t h a ω pstar o)).toReal) := by
  rw [U.residualObserverFiberPosteriorOdds_appendEvent_eq_residual_mul_predictiveRatio
    π t h a o ω pstar hPolicy hClass0 hClassTop hComp0 hCompTop hPred hPredTop]
  rw [ENNReal.toReal_mul]
  rw [Real.sqrt_mul ENNReal.toReal_nonneg]

theorem observerFiberPredictiveWeight_tsum_eq_posteriorWeight
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    (∑' o : O, U.observerFiberPredictiveWeight π t h a ω pstar o) =
      U.observerFiberPosteriorWeight π t h ω pstar := by
  unfold observerFiberPredictiveWeight observerFiberPosteriorWeight
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro p
  by_cases hp : U.observerFiber ω pstar p
  · simp [hp, ENNReal.tsum_mul_left, PMF.tsum_coe]
  · simp [hp]

theorem observerFiberPredictiveWeight_le_posteriorWeight
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (o : O) :
    U.observerFiberPredictiveWeight π t h a ω pstar o ≤
      U.observerFiberPosteriorWeight π t h ω pstar := by
  calc
    U.observerFiberPredictiveWeight π t h a ω pstar o
        ≤ ∑' o' : O, U.observerFiberPredictiveWeight π t h a ω pstar o' :=
          ENNReal.le_tsum o
    _ = U.observerFiberPosteriorWeight π t h ω pstar :=
          U.observerFiberPredictiveWeight_tsum_eq_posteriorWeight π t h a ω pstar

theorem observerFiberPredictiveWeight_ne_top_of_posteriorWeight_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (o : O)
    (hMassTop : U.observerFiberPosteriorWeight π t h ω pstar ≠ ⊤) :
    U.observerFiberPredictiveWeight π t h a ω pstar o ≠ ⊤ := by
  intro hTop
  have hTopLe : (⊤ : ENNReal) ≤ U.observerFiberPosteriorWeight π t h ω pstar := by
    simpa [hTop] using
      U.observerFiberPredictiveWeight_le_posteriorWeight π t h a ω pstar o
  have hMassEq : U.observerFiberPosteriorWeight π t h ω pstar = ⊤ := by
    exact le_antisymm le_top hTopLe
  exact hMassTop hMassEq

/--
If every posterior-supported in-fiber program has the same next-observation law
as `penv`, then the unnormalized in-class predictive weight is just the
observer-fiber posterior mass times the true environment kernel.
-/
theorem observerFiberPredictiveWeight_eq_posteriorWeight_mul_programSemantics_of_fiber_semantics
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (o : O)
    (hCoherent :
      ∀ p : U.Program,
        U.observerFiber ω pstar p →
          U.posteriorWeight π t h p ≠ 0 →
            (fun o : O => U.programSemantics p h a o) =
              fun o : O => U.programSemantics penv h a o) :
    U.observerFiberPredictiveWeight π t h a ω pstar o =
      U.observerFiberPosteriorWeight π t h ω pstar *
        U.programSemantics penv h a o := by
  unfold observerFiberPredictiveWeight observerFiberPosteriorWeight
  calc
    (∑' p : U.Program,
        if U.observerFiber ω pstar p then
          U.posteriorWeight π t h p * U.programSemantics p h a o
        else
          0)
        =
      ∑' p : U.Program,
        (if U.observerFiber ω pstar p then U.posteriorWeight π t h p else 0) *
          U.programSemantics penv h a o := by
            apply tsum_congr
            intro p
            by_cases hp : U.observerFiber ω pstar p
            · by_cases hPost : U.posteriorWeight π t h p = 0
              · simp [hp, hPost]
              · have hSem := congrFun (hCoherent p hp hPost) o
                simp [hp, hSem]
            · simp [hp]
    _ =
      (∑' p : U.Program,
        if U.observerFiber ω pstar p then U.posteriorWeight π t h p else 0) *
          U.programSemantics penv h a o := by
            rw [ENNReal.tsum_mul_right]

/--
Posterior-supported in-fiber semantic coherence derives the calibration
condition used by the class-predictive-to-true-law bridge.
-/
theorem observerFiberPredictiveLawInClass_eq_programSemantics_of_fiber_semantics
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hMass0 : U.observerFiberPosteriorWeight π t h ω pstar ≠ 0)
    (hMassTop : U.observerFiberPosteriorWeight π t h ω pstar ≠ ⊤)
    (hCoherent :
      ∀ p : U.Program,
        U.observerFiber ω pstar p →
          U.posteriorWeight π t h p ≠ 0 →
            (fun o : O => U.programSemantics p h a o) =
              fun o : O => U.programSemantics penv h a o) :
    U.observerFiberPredictiveLawInClass π t h a ω pstar =
      fun o : O => U.programSemantics penv h a o := by
  funext o
  unfold observerFiberPredictiveLawInClass
  simp [hMass0]
  rw [U.observerFiberPredictiveWeight_eq_posteriorWeight_mul_programSemantics_of_fiber_semantics
    π penv t h a ω pstar o hCoherent]
  rw [mul_comm, ENNReal.mul_div_cancel_right hMass0 hMassTop]

theorem observerFiberComplementPredictiveWeight_tsum_eq_complementWeight
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    (∑' o : O, U.observerFiberComplementPredictiveWeight π t h a ω pstar o) =
      U.observerFiberComplementWeight π t h ω pstar := by
  unfold observerFiberComplementPredictiveWeight observerFiberComplementWeight
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro p
  by_cases hp : U.observerFiber ω pstar p
  · simp [hp]
  · simp [hp, ENNReal.tsum_mul_left, PMF.tsum_coe]

theorem observerFiberComplementPredictiveWeight_le_complementWeight
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (o : O) :
    U.observerFiberComplementPredictiveWeight π t h a ω pstar o ≤
      U.observerFiberComplementWeight π t h ω pstar := by
  calc
    U.observerFiberComplementPredictiveWeight π t h a ω pstar o
        ≤ ∑' o' : O, U.observerFiberComplementPredictiveWeight π t h a ω pstar o' :=
          ENNReal.le_tsum o
    _ = U.observerFiberComplementWeight π t h ω pstar :=
          U.observerFiberComplementPredictiveWeight_tsum_eq_complementWeight
            π t h a ω pstar

theorem observerFiberComplementPredictiveWeight_ne_top_of_complementWeight_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (o : O)
    (hMassTop : U.observerFiberComplementWeight π t h ω pstar ≠ ⊤) :
    U.observerFiberComplementPredictiveWeight π t h a ω pstar o ≠ ⊤ := by
  intro hTop
  have hTopLe : (⊤ : ENNReal) ≤ U.observerFiberComplementWeight π t h ω pstar := by
    simpa [hTop] using
      U.observerFiberComplementPredictiveWeight_le_complementWeight π t h a ω pstar o
  have hMassEq : U.observerFiberComplementWeight π t h ω pstar = ⊤ := by
    exact le_antisymm le_top hTopLe
  exact hMassTop hMassEq

theorem observerFiberPredictiveLawInClass_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hMass0 : U.observerFiberPosteriorWeight π t h ω pstar ≠ 0)
    (hMassTop : U.observerFiberPosteriorWeight π t h ω pstar ≠ ⊤) :
    (∑' o : O, U.observerFiberPredictiveLawInClass π t h a ω pstar o) = 1 := by
  unfold observerFiberPredictiveLawInClass
  simp [hMass0]
  calc
    (∑' o : O,
        U.observerFiberPredictiveWeight π t h a ω pstar o /
          U.observerFiberPosteriorWeight π t h ω pstar)
        =
          (∑' o : O, U.observerFiberPredictiveWeight π t h a ω pstar o) /
            U.observerFiberPosteriorWeight π t h ω pstar := by
            simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ = U.observerFiberPosteriorWeight π t h ω pstar /
          U.observerFiberPosteriorWeight π t h ω pstar := by
          rw [U.observerFiberPredictiveWeight_tsum_eq_posteriorWeight π t h a ω pstar]
    _ = 1 := ENNReal.div_self hMass0 hMassTop

theorem observerFiberPredictiveLawOutsideClass_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hMass0 : U.observerFiberComplementWeight π t h ω pstar ≠ 0)
    (hMassTop : U.observerFiberComplementWeight π t h ω pstar ≠ ⊤) :
    (∑' o : O, U.observerFiberPredictiveLawOutsideClass π t h a ω pstar o) = 1 := by
  unfold observerFiberPredictiveLawOutsideClass
  simp [hMass0]
  calc
    (∑' o : O,
        U.observerFiberComplementPredictiveWeight π t h a ω pstar o /
          U.observerFiberComplementWeight π t h ω pstar)
        =
          (∑' o : O, U.observerFiberComplementPredictiveWeight π t h a ω pstar o) /
            U.observerFiberComplementWeight π t h ω pstar := by
            simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ = U.observerFiberComplementWeight π t h ω pstar /
          U.observerFiberComplementWeight π t h ω pstar := by
          rw [U.observerFiberComplementPredictiveWeight_tsum_eq_complementWeight
            π t h a ω pstar]
    _ = 1 := ENNReal.div_self hMass0 hMassTop

/-- Bhattacharyya affinity of two countable observation laws, in `Real`. -/
def predictiveLawBhattacharyyaAffinity
    (μ ν : CountableObservationLaw O) : ℝ :=
  ∑' o : O, Real.sqrt ((μ o).toReal * (ν o).toReal)

omit [Encodable O] in
/--
Pointwise Hellinger change-of-measure identity.

For nonnegative real masses, weighting the square-root likelihood ratio by the
reference mass gives the geometric mean term. This is the algebraic core of the
local Bayes/Gibbs Hellinger conditional-step identity.
-/
theorem real_mul_sqrt_div_eq_sqrt_mul_of_nonneg
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * Real.sqrt (y / x) = Real.sqrt (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hsqrtx_ne : Real.sqrt x ≠ 0 := (Real.sqrt_ne_zero hx).2 hx0
  calc
    x * Real.sqrt (y / x)
        = (Real.sqrt x * Real.sqrt x) * Real.sqrt (y / x) := by
            rw [Real.mul_self_sqrt hx]
    _ = Real.sqrt x * (Real.sqrt x * Real.sqrt (y / x)) := by ring
    _ = Real.sqrt x * (Real.sqrt x * (Real.sqrt y / Real.sqrt x)) := by
            rw [Real.sqrt_div hy x]
    _ = Real.sqrt x * Real.sqrt y := by
            field_simp [hsqrtx_ne]
    _ = Real.sqrt (x * y) := by
            rw [Real.sqrt_mul hx y]

omit [Encodable O] in
/--
The countable Bhattacharyya affinity is the expectation, under the first law,
of the square-root likelihood ratio of the second law against the first.

This is the local conditional-step identity before applying the
`exp(-log BC)` normalizer.
-/
theorem predictiveLawBhattacharyyaAffinity_eq_expect_sqrt_likelihoodRatio
    (μ ν : CountableObservationLaw O) :
    (∑' o : O, (μ o).toReal * Real.sqrt ((ν o / μ o).toReal)) =
      predictiveLawBhattacharyyaAffinity μ ν := by
  unfold predictiveLawBhattacharyyaAffinity
  apply tsum_congr
  intro o
  rw [ENNReal.toReal_div]
  exact real_mul_sqrt_div_eq_sqrt_mul_of_nonneg
    (ENNReal.toReal_nonneg : 0 ≤ (μ o).toReal)
    (ENNReal.toReal_nonneg : 0 ≤ (ν o).toReal)

/--
Bhattacharyya separation of two countable observation laws.

This is the paper's `-log BC` transform, with the same nonpositive-affinity
guard used by the finite concrete layer.
-/
def predictiveLawBhattacharyyaSeparation
    (μ ν : CountableObservationLaw O) : ℝ :=
  let aff := predictiveLawBhattacharyyaAffinity μ ν
  if aff ≤ 0 then 0 else -Real.log aff

omit [Encodable O] in
theorem predictiveLawBhattacharyyaSeparation_eq_zero_of_nonpos
    {μ ν : CountableObservationLaw O}
    (hAff : predictiveLawBhattacharyyaAffinity μ ν ≤ 0) :
    predictiveLawBhattacharyyaSeparation μ ν = 0 := by
  simp [predictiveLawBhattacharyyaSeparation, hAff]

omit [Encodable O] in
theorem predictiveLawBhattacharyyaSeparation_eq_neg_log_of_pos
    {μ ν : CountableObservationLaw O}
    (hAff : 0 < predictiveLawBhattacharyyaAffinity μ ν) :
    predictiveLawBhattacharyyaSeparation μ ν =
      -Real.log (predictiveLawBhattacharyyaAffinity μ ν) := by
  simp [predictiveLawBhattacharyyaSeparation, not_le_of_gt hAff]

omit [Encodable O] in
/--
The `-log BC` separation exactly normalizes a positive Bhattacharyya affinity.
-/
theorem exp_predictiveLawBhattacharyyaSeparation_mul_affinity
    {μ ν : CountableObservationLaw O}
    (hAff : 0 < predictiveLawBhattacharyyaAffinity μ ν) :
    Real.exp (predictiveLawBhattacharyyaSeparation μ ν) *
      predictiveLawBhattacharyyaAffinity μ ν = 1 := by
  rw [predictiveLawBhattacharyyaSeparation_eq_neg_log_of_pos hAff]
  rw [Real.exp_neg, Real.exp_log hAff]
  field_simp [ne_of_gt hAff]

omit [Encodable O] in
/--
Local class-predictive Hellinger normalization: under the first observation law,
the exponential Bhattacharyya-separation factor cancels the expected
square-root likelihood ratio.
-/
theorem classPredictiveHellingerNormalizer
    {μ ν : CountableObservationLaw O}
    (hAff : 0 < predictiveLawBhattacharyyaAffinity μ ν) :
    Real.exp (predictiveLawBhattacharyyaSeparation μ ν) *
      (∑' o : O, (μ o).toReal * Real.sqrt ((ν o / μ o).toReal)) = 1 := by
  rw [predictiveLawBhattacharyyaAffinity_eq_expect_sqrt_likelihoodRatio]
  exact exp_predictiveLawBhattacharyyaSeparation_mul_affinity hAff

omit [Encodable O] in
/--
The local Hellinger normalizer transfers to another conditional observation law
only when that law is definitionally/equationally the class-predictive law.

This theorem makes the previously implicit caveat explicit: an arbitrary
realized-environment kernel cannot use the class-predictive martingale
normalizer unless it is identified with the class-predictive law.
-/
theorem conditionalLawHellingerNormalizer_of_eq_classPredictive
    {ρ μ ν : CountableObservationLaw O}
    (hρ : ρ = μ)
    (hAff : 0 < predictiveLawBhattacharyyaAffinity μ ν) :
    Real.exp (predictiveLawBhattacharyyaSeparation μ ν) *
      (∑' o : O, (ρ o).toReal * Real.sqrt ((ν o / μ o).toReal)) = 1 := by
  subst ρ
  exact classPredictiveHellingerNormalizer hAff

omit [Encodable O] in
/--
True-law Hellinger multiplier for one posterior-residual step.

Here `ρ` is the actual next-observation law, `μ` is the in-class predictive law
in the denominator of the Bayes update, and `ν` is the outside-class predictive
law in the numerator. Unlike `predictiveLawBhattacharyyaAffinity`, this is not
silently a class-predictive expectation; it is explicitly the expectation under
the true data-generating law.
-/
def predictiveLawTrueHellingerAffinity
    (ρ μ ν : CountableObservationLaw O) : ℝ :=
  ∑' o : O, (ρ o).toReal * Real.sqrt ((ν o / μ o).toReal)

omit [Encodable O] in
/--
If the true next-observation law is calibrated to the in-class predictive law,
then the true-law Hellinger multiplier is exactly the class-predictive
Bhattacharyya affinity.

This is the analytic core of the ambitious semantic bridge: the class-predictive
paper score can drive the true-law martingale only after the realized law has
been identified with the in-class predictive law.
-/
theorem predictiveLawTrueHellingerAffinity_eq_bhattacharyyaAffinity_of_eq_classPredictive
    {ρ μ ν : CountableObservationLaw O}
    (hρ : ρ = μ) :
    predictiveLawTrueHellingerAffinity ρ μ ν =
      predictiveLawBhattacharyyaAffinity μ ν := by
  subst ρ
  simpa [predictiveLawTrueHellingerAffinity] using
    predictiveLawBhattacharyyaAffinity_eq_expect_sqrt_likelihoodRatio
      (μ := μ) (ν := ν)

omit [Encodable O] in
/--
True-law Hellinger separation, defined as the `-log` transform of the true-law
one-step multiplier.
-/
def predictiveLawTrueHellingerSeparation
    (ρ μ ν : CountableObservationLaw O) : ℝ :=
  let aff := predictiveLawTrueHellingerAffinity ρ μ ν
  if aff ≤ 0 then 0 else -Real.log aff

omit [Encodable O] in
theorem predictiveLawTrueHellingerSeparation_eq_neg_log_of_pos
    {ρ μ ν : CountableObservationLaw O}
    (hAff : 0 < predictiveLawTrueHellingerAffinity ρ μ ν) :
    predictiveLawTrueHellingerSeparation ρ μ ν =
      -Real.log (predictiveLawTrueHellingerAffinity ρ μ ν) := by
  simp [predictiveLawTrueHellingerSeparation, not_le_of_gt hAff]

omit [Encodable O] in
/--
Under the same calibration, the true-law Hellinger score is the paper's
class-predictive Bhattacharyya score.
-/
theorem predictiveLawTrueHellingerSeparation_eq_bhattacharyyaSeparation_of_eq_classPredictive
    {ρ μ ν : CountableObservationLaw O}
    (hρ : ρ = μ) :
    predictiveLawTrueHellingerSeparation ρ μ ν =
      predictiveLawBhattacharyyaSeparation μ ν := by
  subst ρ
  have hAff :
      predictiveLawTrueHellingerAffinity μ μ ν =
        predictiveLawBhattacharyyaAffinity μ ν :=
    predictiveLawTrueHellingerAffinity_eq_bhattacharyyaAffinity_of_eq_classPredictive
      (ρ := μ) (μ := μ) (ν := ν) rfl
  simp [predictiveLawTrueHellingerSeparation, predictiveLawBhattacharyyaSeparation,
    hAff]

omit [Encodable O] in
/--
The true-law Hellinger separation exactly normalizes the true-law one-step
square-root multiplier.
-/
theorem exp_predictiveLawTrueHellingerSeparation_mul_affinity
    {ρ μ ν : CountableObservationLaw O}
    (hAff : 0 < predictiveLawTrueHellingerAffinity ρ μ ν) :
    Real.exp (predictiveLawTrueHellingerSeparation ρ μ ν) *
      predictiveLawTrueHellingerAffinity ρ μ ν = 1 := by
  rw [predictiveLawTrueHellingerSeparation_eq_neg_log_of_pos hAff]
  rw [Real.exp_neg, Real.exp_log hAff]
  field_simp [ne_of_gt hAff]

omit [Encodable O] in
/--
Local true-law Hellinger normalization: the exponential separation factor
cancels the expected square-root residual multiplier under the actual
observation law `ρ`.
-/
theorem trueLawHellingerNormalizer
    {ρ μ ν : CountableObservationLaw O}
    (hAff : 0 < predictiveLawTrueHellingerAffinity ρ μ ν) :
    Real.exp (predictiveLawTrueHellingerSeparation ρ μ ν) *
      (∑' o : O, (ρ o).toReal * Real.sqrt ((ν o / μ o).toReal)) = 1 := by
  exact exp_predictiveLawTrueHellingerSeparation_mul_affinity hAff

omit [Encodable O] in
/--
A true-law Hellinger multiplier ceiling gives a lower bound on true-law
Hellinger separation.
-/
theorem predictiveLawTrueHellingerSeparation_ge_of_affinity_le_exp_neg
    {ρ μ ν : CountableObservationLaw O} {κ : ℝ}
    (_hκ : 0 < κ)
    (hAffPos : 0 < predictiveLawTrueHellingerAffinity ρ μ ν)
    (hAffLe : predictiveLawTrueHellingerAffinity ρ μ ν ≤ Real.exp (-κ)) :
    κ ≤ predictiveLawTrueHellingerSeparation ρ μ ν := by
  rw [predictiveLawTrueHellingerSeparation_eq_neg_log_of_pos hAffPos]
  have hLogLe :
      Real.log (predictiveLawTrueHellingerAffinity ρ μ ν) ≤
        Real.log (Real.exp (-κ)) :=
    Real.log_le_log hAffPos hAffLe
  rw [Real.log_exp] at hLogLe
  linarith

omit [Encodable O] in
/--
Conversely, a lower bound on true-law Hellinger separation gives the
corresponding upper bound on the true-law multiplier.
-/
theorem predictiveLawTrueHellingerAffinity_le_exp_neg_of_separation_ge
    {ρ μ ν : CountableObservationLaw O} {κ : ℝ}
    (hAffPos : 0 < predictiveLawTrueHellingerAffinity ρ μ ν)
    (hSep : κ ≤ predictiveLawTrueHellingerSeparation ρ μ ν) :
    predictiveLawTrueHellingerAffinity ρ μ ν ≤ Real.exp (-κ) := by
  rw [predictiveLawTrueHellingerSeparation_eq_neg_log_of_pos hAffPos] at hSep
  have hLogLe :
      Real.log (predictiveLawTrueHellingerAffinity ρ μ ν) ≤ -κ := by
    linarith
  exact (Real.log_le_iff_le_exp hAffPos).mp hLogLe

omit [Encodable O] in
/--
A Bhattacharyya-affinity ceiling gives a lower bound on Bhattacharyya separation.

This is the local analytic bridge from the paper's semantic distinguishability
condition, expressed as `BC ≤ exp(-κ)`, to the additive separation floor consumed
by the Hellinger spine.
-/
theorem predictiveLawBhattacharyyaSeparation_ge_of_affinity_le_exp_neg
    {μ ν : CountableObservationLaw O} {κ : ℝ}
    (_hκ : 0 < κ)
    (hAffPos : 0 < predictiveLawBhattacharyyaAffinity μ ν)
    (hAffLe : predictiveLawBhattacharyyaAffinity μ ν ≤ Real.exp (-κ)) :
    κ ≤ predictiveLawBhattacharyyaSeparation μ ν := by
  rw [predictiveLawBhattacharyyaSeparation_eq_neg_log_of_pos hAffPos]
  have hLogLe :
      Real.log (predictiveLawBhattacharyyaAffinity μ ν) ≤
        Real.log (Real.exp (-κ)) :=
    Real.log_le_log hAffPos hAffLe
  rw [Real.log_exp] at hLogLe
  linarith

omit [Encodable O] in
/--
Conversely, a lower bound on Bhattacharyya separation gives the corresponding
upper bound on Bhattacharyya affinity.
-/
theorem predictiveLawBhattacharyyaAffinity_le_exp_neg_of_separation_ge
    {μ ν : CountableObservationLaw O} {κ : ℝ}
    (hAffPos : 0 < predictiveLawBhattacharyyaAffinity μ ν)
    (hSep : κ ≤ predictiveLawBhattacharyyaSeparation μ ν) :
    predictiveLawBhattacharyyaAffinity μ ν ≤ Real.exp (-κ) := by
  rw [predictiveLawBhattacharyyaSeparation_eq_neg_log_of_pos hAffPos] at hSep
  have hLogLe :
      Real.log (predictiveLawBhattacharyyaAffinity μ ν) ≤ -κ := by
    linarith
  exact (Real.log_le_iff_le_exp hAffPos).mp hLogLe

/-- Bhattacharyya affinity of the observer-fiber class/complement predictive pair. -/
def observerFiberPredictiveLawAffinity (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ℝ :=
  predictiveLawBhattacharyyaAffinity
    (U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)

/--
Paper-level one-step Bhattacharyya score induced by the countable
observer-fiber predictive laws.
-/
def observerFiberBhattacharyyaScore (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ℝ :=
  predictiveLawBhattacharyyaSeparation
    (U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)

/--
The canonical H2 instance of the H1 `StepBhattacharyyaScore` interface.
-/
def observerFiberStepBhattacharyyaScore (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : StepBhattacharyyaScore A O :=
  fun t h a => U.observerFiberBhattacharyyaScore π t h a ω pstar

theorem observerFiberBhattacharyyaScore_eq_predictiveLawSeparation
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.observerFiberBhattacharyyaScore π t h a ω pstar =
      predictiveLawBhattacharyyaSeparation
        (U.observerFiberPredictiveLawInClass π t h a ω pstar)
        (U.observerFiberPredictiveLawOutsideClass π t h a ω pstar) :=
  rfl

theorem observerFiberStepBhattacharyyaScore_eq
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (t : Nat) (h : CountHist A O) (a : A) :
    U.observerFiberStepBhattacharyyaScore π ω pstar t h a =
      U.observerFiberBhattacharyyaScore π t h a ω pstar :=
  rfl

/--
Observer-fiber specialization of the local Hellinger normalization.

This is the exact one-step identity available when the next observation is
conditioned according to the in-class observer-fiber predictive law.
-/
theorem observerFiberClassPredictiveHellingerNormalizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hAff : 0 < U.observerFiberPredictiveLawAffinity π t h a ω pstar) :
    Real.exp (U.observerFiberBhattacharyyaScore π t h a ω pstar) *
      (∑' o : O,
        (U.observerFiberPredictiveLawInClass π t h a ω pstar o).toReal *
          Real.sqrt
            (((U.observerFiberPredictiveLawOutsideClass π t h a ω pstar o) /
              (U.observerFiberPredictiveLawInClass π t h a ω pstar o)).toReal)) =
        1 := by
  exact classPredictiveHellingerNormalizer
    (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
    (by simpa [observerFiberPredictiveLawAffinity] using hAff)

/--
Program-kernel version of the local Hellinger normalizer, with the necessary
bridge exposed as a hypothesis: the realized program's next-observation kernel
must agree with the observer-fiber in-class predictive law at this prefix and
action.
-/
theorem observerFiberProgramLawHellingerNormalizer_of_eq_classPredictive
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (penv : U.Program)
    (hKernel :
      (fun o : O => U.programSemantics penv h a o) =
        U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (hAff : 0 < U.observerFiberPredictiveLawAffinity π t h a ω pstar) :
    Real.exp (U.observerFiberBhattacharyyaScore π t h a ω pstar) *
      (∑' o : O,
        (U.programSemantics penv h a o).toReal *
          Real.sqrt
            (((U.observerFiberPredictiveLawOutsideClass π t h a ω pstar o) /
              (U.observerFiberPredictiveLawInClass π t h a ω pstar o)).toReal)) =
        1 := by
  exact conditionalLawHellingerNormalizer_of_eq_classPredictive
    (ρ := fun o : O => U.programSemantics penv h a o)
    (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
    hKernel
    (by simpa [observerFiberPredictiveLawAffinity] using hAff)

/--
True-environment one-step Hellinger multiplier for observer-fiber residual
odds. The expectation is taken under `programSemantics penv`, not under the
in-class predictive mixture.
-/
def observerFiberTrueLawHellingerAffinity (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ℝ :=
  predictiveLawTrueHellingerAffinity
    (fun o : O => U.programSemantics penv h a o)
    (U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)

/--
True-environment one-step Hellinger score for observer-fiber residual odds.
-/
def observerFiberTrueLawHellingerScore (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ℝ :=
  predictiveLawTrueHellingerSeparation
    (fun o : O => U.programSemantics penv h a o)
    (U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)

/--
Observer-fiber calibrated law equality turns the true-law multiplier into the
paper-facing class-predictive Bhattacharyya affinity.
-/
theorem observerFiberTrueLawHellingerAffinity_eq_predictiveLawAffinity_of_calibrated
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hKernel :
      (fun o : O => U.programSemantics penv h a o) =
        U.observerFiberPredictiveLawInClass π t h a ω pstar) :
    U.observerFiberTrueLawHellingerAffinity π penv t h a ω pstar =
      U.observerFiberPredictiveLawAffinity π t h a ω pstar := by
  simpa [observerFiberTrueLawHellingerAffinity, observerFiberPredictiveLawAffinity]
    using
      predictiveLawTrueHellingerAffinity_eq_bhattacharyyaAffinity_of_eq_classPredictive
        (ρ := fun o : O => U.programSemantics penv h a o)
        (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
        (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
        hKernel

/--
Observer-fiber calibrated law equality turns the true-law score into the
paper-facing class-predictive Bhattacharyya score.
-/
theorem observerFiberTrueLawHellingerScore_eq_bhattacharyyaScore_of_calibrated
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hKernel :
      (fun o : O => U.programSemantics penv h a o) =
        U.observerFiberPredictiveLawInClass π t h a ω pstar) :
    U.observerFiberTrueLawHellingerScore π penv t h a ω pstar =
      U.observerFiberBhattacharyyaScore π t h a ω pstar := by
  simpa [observerFiberTrueLawHellingerScore, observerFiberBhattacharyyaScore]
    using
      predictiveLawTrueHellingerSeparation_eq_bhattacharyyaSeparation_of_eq_classPredictive
        (ρ := fun o : O => U.programSemantics penv h a o)
        (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
        (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
        hKernel

/--
Step-score instance for the true-environment Hellinger spine.
-/
def observerFiberTrueLawStepHellingerScore (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : StepBhattacharyyaScore A O :=
  fun t h a => U.observerFiberTrueLawHellingerScore π penv t h a ω pstar

/--
The true-environment observer-fiber score is exactly the true-law separation
of the realized program kernel against the class/complement predictive ratio.
-/
theorem observerFiberTrueLawHellingerScore_eq
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.observerFiberTrueLawHellingerScore π penv t h a ω pstar =
      predictiveLawTrueHellingerSeparation
        (fun o : O => U.programSemantics penv h a o)
        (U.observerFiberPredictiveLawInClass π t h a ω pstar)
        (U.observerFiberPredictiveLawOutsideClass π t h a ω pstar) :=
  rfl

/--
True-environment local Hellinger normalization for the observer-fiber residual
Bayes update. This is the caveat-free replacement for the class-predictive
normalizer when the trajectory law is generated by `penv`.
-/
theorem observerFiberTrueLawHellingerNormalizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hAff : 0 < U.observerFiberTrueLawHellingerAffinity π penv t h a ω pstar) :
    Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
      (∑' o : O,
        (U.programSemantics penv h a o).toReal *
          Real.sqrt
            (((U.observerFiberPredictiveLawOutsideClass π t h a ω pstar o) /
              (U.observerFiberPredictiveLawInClass π t h a ω pstar o)).toReal)) =
        1 := by
  exact trueLawHellingerNormalizer
    (ρ := fun o : O => U.programSemantics penv h a o)
    (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
    (by simpa [observerFiberTrueLawHellingerAffinity] using hAff)

/--
True-environment local Bayes/Gibbs Hellinger conditional-step identity.

After a fixed supported action `a`, averaging the next square-root residual
odds over the actual environment kernel and multiplying by the true-law
Hellinger normalizer recovers the current square-root residual odds. The
zero/top assumptions are exactly the denominators needed by the Bayes update;
they are not hidden inside the statement.
-/
theorem observerFiberTrueLawHellinger_oneStep_sqrtResidual_normalized
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hPolicy : π h a ≠ 0)
    (hClass0 : U.observerFiberPosteriorWeight π t h ω pstar ≠ 0)
    (hClassTop : U.observerFiberPosteriorWeight π t h ω pstar ≠ ⊤)
    (hComp0 : U.observerFiberComplementWeight π t h ω pstar ≠ 0)
    (hCompTop : U.observerFiberComplementWeight π t h ω pstar ≠ ⊤)
    (hPred :
      ∀ o,
        U.programSemantics penv h a o ≠ 0 →
          U.observerFiberPredictiveWeight π t h a ω pstar o ≠ 0 ∧
          U.observerFiberPredictiveWeight π t h a ω pstar o ≠ ⊤)
    (hAff : 0 < U.observerFiberTrueLawHellingerAffinity π penv t h a ω pstar) :
    Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
      (∑' o : O,
        (U.programSemantics penv h a o).toReal *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π (t + 1)
              (appendEvent h (a, o)) ω pstar).toReal)) =
      Real.sqrt ((U.residualObserverFiberPosteriorOdds π t h ω pstar).toReal) := by
  let sqrtR :=
    Real.sqrt ((U.residualObserverFiberPosteriorOdds π t h ω pstar).toReal)
  let ratioTerm : O → ℝ := fun o =>
    Real.sqrt
      (((U.observerFiberPredictiveLawOutsideClass π t h a ω pstar o) /
        (U.observerFiberPredictiveLawInClass π t h a ω pstar o)).toReal)
  have hPoint :
      ∀ o : O,
        (U.programSemantics penv h a o).toReal *
            Real.sqrt
              ((U.residualObserverFiberPosteriorOdds π (t + 1)
                (appendEvent h (a, o)) ω pstar).toReal) =
          (U.programSemantics penv h a o).toReal *
            (sqrtR * ratioTerm o) := by
    intro o
    by_cases hρ : U.programSemantics penv h a o = 0
    · simp [hρ]
    · rcases hPred o hρ with ⟨hPred0, hPredTop⟩
      rw [U.sqrt_residualObserverFiberPosteriorOdds_appendEvent_eq
        π t h a o ω pstar hPolicy hClass0 hClassTop hComp0 hCompTop
        hPred0 hPredTop]
  have hSum :
      (∑' o : O,
        (U.programSemantics penv h a o).toReal *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π (t + 1)
              (appendEvent h (a, o)) ω pstar).toReal)) =
        sqrtR *
          (∑' o : O,
            (U.programSemantics penv h a o).toReal * ratioTerm o) := by
    calc
      (∑' o : O,
        (U.programSemantics penv h a o).toReal *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π (t + 1)
              (appendEvent h (a, o)) ω pstar).toReal))
          =
            ∑' o : O,
              (U.programSemantics penv h a o).toReal *
                (sqrtR * ratioTerm o) := by
              exact tsum_congr hPoint
      _ = ∑' o : O,
            sqrtR *
              ((U.programSemantics penv h a o).toReal * ratioTerm o) := by
            apply tsum_congr
            intro o
            ring
      _ = sqrtR *
            (∑' o : O,
              (U.programSemantics penv h a o).toReal * ratioTerm o) := by
            rw [tsum_mul_left]
  have hNorm :
      Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
        (∑' o : O,
          (U.programSemantics penv h a o).toReal * ratioTerm o) = 1 := by
    simpa [ratioTerm] using
      U.observerFiberTrueLawHellingerNormalizer π penv t h a ω pstar hAff
  rw [hSum]
  calc
    Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
        (sqrtR *
          (∑' o : O,
            (U.programSemantics penv h a o).toReal * ratioTerm o))
        =
          sqrtR *
            (Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
              (∑' o : O,
                (U.programSemantics penv h a o).toReal * ratioTerm o)) := by
            ring
    _ = Real.sqrt ((U.residualObserverFiberPosteriorOdds π t h ω pstar).toReal) := by
          rw [hNorm]
          simp [sqrtR]

/--
Action-observation averaging form of the true-law local Hellinger identity.

The fixed-action identity above normalizes the observation average for each
supported action. This theorem performs the extra policy averaging step used by
`ionescuStepKernel`: unsupported actions contribute zero mass, while supported
actions use `observerFiberTrueLawHellinger_oneStep_sqrtResidual_normalized`.
-/
theorem observerFiberTrueLawHellinger_actionObservation_tsum_normalized
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (E : ℝ)
    (hClass0 : U.observerFiberPosteriorWeight π t h ω pstar ≠ 0)
    (hClassTop : U.observerFiberPosteriorWeight π t h ω pstar ≠ ⊤)
    (hComp0 : U.observerFiberComplementWeight π t h ω pstar ≠ 0)
    (hCompTop : U.observerFiberComplementWeight π t h ω pstar ≠ ⊤)
    (hPred :
      ∀ a,
        π h a ≠ 0 →
          ∀ o,
            U.programSemantics penv h a o ≠ 0 →
              U.observerFiberPredictiveWeight π t h a ω pstar o ≠ 0 ∧
              U.observerFiberPredictiveWeight π t h a ω pstar o ≠ ⊤)
    (hAff :
      ∀ a,
        π h a ≠ 0 →
          0 < U.observerFiberTrueLawHellingerAffinity π penv t h a ω pstar) :
    (∑' a : A, ∑' o : O,
      (π h a).toReal *
        ((U.programSemantics penv h a o).toReal *
          (E *
            Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
            Real.sqrt
              ((U.residualObserverFiberPosteriorOdds π (t + 1)
                (appendEvent h (a, o)) ω pstar).toReal)))) =
      E * Real.sqrt ((U.residualObserverFiberPosteriorOdds π t h ω pstar).toReal) := by
  let sqrtR :=
    Real.sqrt ((U.residualObserverFiberPosteriorOdds π t h ω pstar).toReal)
  let stepTerm : A → ℝ := fun a =>
    ∑' o : O,
      (π h a).toReal *
        ((U.programSemantics penv h a o).toReal *
          (E *
            Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
            Real.sqrt
              ((U.residualObserverFiberPosteriorOdds π (t + 1)
                (appendEvent h (a, o)) ω pstar).toReal)))
  have hAction :
      ∀ a, stepTerm a = (π h a).toReal * (E * sqrtR) := by
    intro a
    by_cases hPolicy : π h a = 0
    · simp [stepTerm, hPolicy]
    · have hFixed :=
        U.observerFiberTrueLawHellinger_oneStep_sqrtResidual_normalized
          π penv t h a ω pstar hPolicy hClass0 hClassTop hComp0 hCompTop
          (hPred a hPolicy) (hAff a hPolicy)
      calc
        stepTerm a =
            ∑' o : O,
              ((π h a).toReal * E *
                Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar)) *
                ((U.programSemantics penv h a o).toReal *
                  Real.sqrt
                    ((U.residualObserverFiberPosteriorOdds π (t + 1)
                      (appendEvent h (a, o)) ω pstar).toReal)) := by
              apply tsum_congr
              intro o
              dsimp [stepTerm]
              ring
        _ =
            ((π h a).toReal * E *
              Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar)) *
              (∑' o : O,
                (U.programSemantics penv h a o).toReal *
                  Real.sqrt
                    ((U.residualObserverFiberPosteriorOdds π (t + 1)
                      (appendEvent h (a, o)) ω pstar).toReal)) := by
              rw [tsum_mul_left]
        _ = (π h a).toReal * (E * sqrtR) := by
              have hFixed' :
                  Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
                    (∑' o : O,
                      (U.programSemantics penv h a o).toReal *
                        Real.sqrt
                          ((U.residualObserverFiberPosteriorOdds π (t + 1)
                            (appendEvent h (a, o)) ω pstar).toReal)) = sqrtR := by
                simpa [sqrtR] using hFixed
              have hMul := congrArg (fun z => (π h a).toReal * E * z) hFixed'
              simpa [mul_assoc] using hMul
  calc
    (∑' a : A, ∑' o : O,
      (π h a).toReal *
        ((U.programSemantics penv h a o).toReal *
          (E *
            Real.exp (U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) *
            Real.sqrt
              ((U.residualObserverFiberPosteriorOdds π (t + 1)
                (appendEvent h (a, o)) ω pstar).toReal))))
        = ∑' a : A, (π h a).toReal * (E * sqrtR) := by
            exact tsum_congr hAction
    _ = (∑' a : A, (π h a).toReal) * (E * sqrtR) := by
            rw [tsum_mul_right]
    _ = E * Real.sqrt ((U.residualObserverFiberPosteriorOdds π t h ω pstar).toReal) := by
            rw [pmf_tsum_toReal_eq_one (π h)]
            simp [sqrtR]

/--
A true-law Hellinger multiplier ceiling gives a lower bound on the
observer-fiber true-law Hellinger score.
-/
theorem observerFiberTrueLawHellingerScore_ge_of_affinity_ceiling
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) {κ : ℝ}
    (hκ : 0 < κ)
    (hAffPos : 0 < U.observerFiberTrueLawHellingerAffinity π penv t h a ω pstar)
    (hAffLe :
      U.observerFiberTrueLawHellingerAffinity π penv t h a ω pstar ≤
        Real.exp (-κ)) :
    κ ≤ U.observerFiberTrueLawHellingerScore π penv t h a ω pstar := by
  exact predictiveLawTrueHellingerSeparation_ge_of_affinity_le_exp_neg
    (ρ := fun o : O => U.programSemantics penv h a o)
    (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
    hκ
    (by simpa [observerFiberTrueLawHellingerAffinity] using hAffPos)
    (by simpa [observerFiberTrueLawHellingerAffinity] using hAffLe)

/--
A true-law Hellinger score floor is equivalent to the multiplier ceiling needed
by the safe-action predicate, once multiplier positivity is known.
-/
theorem observerFiberTrueLawHellingerAffinity_le_exp_neg_of_score_ge
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (penv : U.Program)
    (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) {κ : ℝ}
    (hAffPos : 0 < U.observerFiberTrueLawHellingerAffinity π penv t h a ω pstar)
    (hScore : κ ≤ U.observerFiberTrueLawHellingerScore π penv t h a ω pstar) :
      U.observerFiberTrueLawHellingerAffinity π penv t h a ω pstar ≤
        Real.exp (-κ) := by
  exact predictiveLawTrueHellingerAffinity_le_exp_neg_of_separation_ge
    (ρ := fun o : O => U.programSemantics penv h a o)
    (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
    (by simpa [observerFiberTrueLawHellingerAffinity] using hAffPos)
    (by simpa [observerFiberTrueLawHellingerScore] using hScore)

/--
Observer-fiber affinity ceiling implies a lower bound on the observer-fiber
Bhattacharyya score.
-/
theorem observerFiberBhattacharyyaScore_ge_of_affinity_ceiling
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) {κ : ℝ}
    (hκ : 0 < κ)
    (hAffPos : 0 < U.observerFiberPredictiveLawAffinity π t h a ω pstar)
    (hAffLe : U.observerFiberPredictiveLawAffinity π t h a ω pstar ≤
      Real.exp (-κ)) :
    κ ≤ U.observerFiberBhattacharyyaScore π t h a ω pstar := by
  exact predictiveLawBhattacharyyaSeparation_ge_of_affinity_le_exp_neg
    (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
    hκ
    (by simpa [observerFiberPredictiveLawAffinity] using hAffPos)
    (by simpa [observerFiberPredictiveLawAffinity] using hAffLe)

/--
An observer-fiber Bhattacharyya score floor is equivalent to the semantic
affinity ceiling, once affinity positivity is known.
-/
theorem observerFiberPredictiveLawAffinity_le_exp_neg_of_score_ge
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) {κ : ℝ}
    (hAffPos : 0 < U.observerFiberPredictiveLawAffinity π t h a ω pstar)
    (hScore : κ ≤ U.observerFiberBhattacharyyaScore π t h a ω pstar) :
      U.observerFiberPredictiveLawAffinity π t h a ω pstar ≤
        Real.exp (-κ) := by
  exact predictiveLawBhattacharyyaAffinity_le_exp_neg_of_separation_ge
    (μ := U.observerFiberPredictiveLawInClass π t h a ω pstar)
    (ν := U.observerFiberPredictiveLawOutsideClass π t h a ω pstar)
    (by simpa [observerFiberPredictiveLawAffinity] using hAffPos)
    (by simpa [observerFiberBhattacharyyaScore] using hScore)

theorem observerFiberPredictiveWeight_eq_of_sameView
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O} (o : O)
    (hView : ω.view p = ω.view q) :
    U.observerFiberPredictiveWeight π t h a ω p o =
      U.observerFiberPredictiveWeight π t h a ω q o := by
  unfold observerFiberPredictiveWeight observerFiber
  apply tsum_congr
  intro r
  rw [hView]

theorem observerFiberComplementPredictiveWeight_eq_of_sameView
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O} (o : O)
    (hView : ω.view p = ω.view q) :
    U.observerFiberComplementPredictiveWeight π t h a ω p o =
      U.observerFiberComplementPredictiveWeight π t h a ω q o := by
  unfold observerFiberComplementPredictiveWeight observerFiber
  apply tsum_congr
  intro r
  rw [hView]

theorem observerFiberPredictiveLawInClass_eq_of_sameView
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberPredictiveLawInClass π t h a ω p =
      U.observerFiberPredictiveLawInClass π t h a ω q := by
  funext o
  have hMass := U.observerFiberPosteriorWeight_eq_of_sameView π t h ω hView
  have hWeight := U.observerFiberPredictiveWeight_eq_of_sameView π t h a ω o hView
  simp [observerFiberPredictiveLawInClass, hMass, hWeight]

theorem observerFiberPredictiveLawOutsideClass_eq_of_sameView
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberPredictiveLawOutsideClass π t h a ω p =
      U.observerFiberPredictiveLawOutsideClass π t h a ω q := by
  funext o
  have hMass := U.observerFiberComplementWeight_eq_of_sameView π t h ω hView
  have hWeight := U.observerFiberComplementPredictiveWeight_eq_of_sameView π t h a ω o hView
  simp [observerFiberPredictiveLawOutsideClass, hMass, hWeight]

theorem observerFiberBhattacharyyaScore_eq_of_sameView
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) (a : A)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberBhattacharyyaScore π t h a ω p =
      U.observerFiberBhattacharyyaScore π t h a ω q := by
  have hIn := U.observerFiberPredictiveLawInClass_eq_of_sameView π t h a ω hView
  have hOut := U.observerFiberPredictiveLawOutsideClass_eq_of_sameView π t h a ω hView
  simp [observerFiberBhattacharyyaScore, hIn, hOut]

/-- Realized next action, when the finite trajectory has an event at index `n`. -/
def realizedNextAction? (ξ : Trajectory A O) (n : Nat) : Option A :=
  if h : n < ξ.length then some (ξ.get ⟨n, h⟩).1 else none

/--
Realized Bhattacharyya separation process `Bₙ`.

At a nonterminal trajectory prefix this evaluates the paper-level score at the
realized prefix `Hₙ` and realized next action `Aₙ₊₁`. Beyond the finite
trajectory horizon it is set to zero; infinite-horizon phases should instantiate
the generic process builders directly on their infinite trajectory space.
-/
def realizedBhattacharyyaSeparationProcess
    (B : StepBhattacharyyaScore A O) :
    Nat → Trajectory A O → ℝ :=
  fun n ξ =>
    if h : n < ξ.length then
      B n (historyPrefix ξ n) (ξ.get ⟨n, h⟩).1
    else
      0

/-- Cumulative realized separation process `Sₙ = ∑_{i<n} Bᵢ`. -/
def realizedCumulativeSeparationProcess
    (B : StepBhattacharyyaScore A O) :
    Nat → Trajectory A O → ℝ :=
  cumulativeSeparationProcess (realizedBhattacharyyaSeparationProcess B)

/-- Realized Hellinger envelope `Mₙ = exp(Sₙ) * sqrt(Rₙ)`. -/
def realizedHellingerEnvelopeProcess (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O) :
    Nat → Trajectory A O → ℝ :=
  hellingerEnvelopeProcess
    (U.realizedResidualOddsProcess π ω pstar)
    (realizedCumulativeSeparationProcess B)

/--
Realized one-step Bhattacharyya process for the canonical observer-fiber
predictive-law score.
-/
def realizedObserverFiberBhattacharyyaSeparationProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → Trajectory A O → ℝ :=
  realizedBhattacharyyaSeparationProcess
    (U.observerFiberStepBhattacharyyaScore π ω pstar)

/-- Cumulative realized observer-fiber Bhattacharyya separation. -/
def realizedObserverFiberCumulativeBhattacharyyaSeparationProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → Trajectory A O → ℝ :=
  cumulativeSeparationProcess
    (U.realizedObserverFiberBhattacharyyaSeparationProcess π ω pstar)

/-- Hellinger envelope built from the canonical observer-fiber Bhattacharyya score. -/
def realizedObserverFiberHellingerEnvelopeProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → Trajectory A O → ℝ :=
  hellingerEnvelopeProcess
    (U.realizedResidualOddsProcess π ω pstar)
    (U.realizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar)

theorem realizedResidualOddsProcess_nonneg (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    ∀ n ξ, 0 ≤ U.realizedResidualOddsProcess π ω pstar n ξ := by
  intro n ξ
  exact ENNReal.toReal_nonneg

theorem ae_realizedResidualOddsProcess_nonneg (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (Trajectory A O)} :
    ∀ᵐ ξ ∂μ, ∀ n, 0 ≤ U.realizedResidualOddsProcess π ω pstar n ξ :=
  Filter.Eventually.of_forall
    (fun ξ n => U.realizedResidualOddsProcess_nonneg π ω pstar n ξ)

omit [Encodable A] [Encodable O] in
theorem realizedBhattacharyyaSeparationProcess_of_lt
    (B : StepBhattacharyyaScore A O)
    {ξ : Trajectory A O} {n : Nat} (hn : n < ξ.length) :
    realizedBhattacharyyaSeparationProcess B n ξ =
      B n (historyPrefix ξ n) (ξ.get ⟨n, hn⟩).1 := by
  simp [realizedBhattacharyyaSeparationProcess, hn]

omit [Encodable A] [Encodable O] in
theorem realizedBhattacharyyaSeparationProcess_of_not_lt
    (B : StepBhattacharyyaScore A O)
    {ξ : Trajectory A O} {n : Nat} (hn : ¬ n < ξ.length) :
    realizedBhattacharyyaSeparationProcess B n ξ = 0 := by
  simp [realizedBhattacharyyaSeparationProcess, hn]

theorem realizedObserverFiberBhattacharyyaSeparationProcess_of_lt
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {ξ : Trajectory A O} {n : Nat} (hn : n < ξ.length) :
    U.realizedObserverFiberBhattacharyyaSeparationProcess π ω pstar n ξ =
      U.observerFiberBhattacharyyaScore π n (historyPrefix ξ n)
        (ξ.get ⟨n, hn⟩).1 ω pstar := by
  simp [realizedObserverFiberBhattacharyyaSeparationProcess,
    realizedBhattacharyyaSeparationProcess, observerFiberStepBhattacharyyaScore, hn]

theorem realizedObserverFiberBhattacharyyaSeparationProcess_of_not_lt
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {ξ : Trajectory A O} {n : Nat} (hn : ¬ n < ξ.length) :
    U.realizedObserverFiberBhattacharyyaSeparationProcess π ω pstar n ξ = 0 := by
  simp [realizedObserverFiberBhattacharyyaSeparationProcess,
    realizedBhattacharyyaSeparationProcess, hn]

omit [Encodable A] [Encodable O] in
theorem realizedCumulativeSeparationProcess_eq_sum
    (B : StepBhattacharyyaScore A O) (n : Nat) (ξ : Trajectory A O) :
    realizedCumulativeSeparationProcess B n ξ =
      ∑ i ∈ Finset.range n, realizedBhattacharyyaSeparationProcess B i ξ :=
  rfl

theorem realizedHellingerEnvelopeProcess_eq
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O) (n : Nat) (ξ : Trajectory A O) :
    U.realizedHellingerEnvelopeProcess π ω pstar B n ξ =
      Real.exp (realizedCumulativeSeparationProcess B n ξ) *
        Real.sqrt (U.realizedResidualOddsProcess π ω pstar n ξ) :=
  rfl

theorem realizedObserverFiberCumulativeBhattacharyyaSeparationProcess_eq_sum
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat) (ξ : Trajectory A O) :
    U.realizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar n ξ =
      ∑ i ∈ Finset.range n,
        U.realizedObserverFiberBhattacharyyaSeparationProcess π ω pstar i ξ :=
  rfl

theorem realizedObserverFiberCumulativeBhattacharyyaSeparationProcess_eq_realizedCumulative
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.realizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar =
      realizedCumulativeSeparationProcess
        (U.observerFiberStepBhattacharyyaScore π ω pstar) :=
  rfl

theorem realizedObserverFiberHellingerEnvelopeProcess_eq
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat) (ξ : Trajectory A O) :
    U.realizedObserverFiberHellingerEnvelopeProcess π ω pstar n ξ =
      Real.exp
          (U.realizedObserverFiberCumulativeBhattacharyyaSeparationProcess
            π ω pstar n ξ) *
        Real.sqrt (U.realizedResidualOddsProcess π ω pstar n ξ) :=
  rfl

theorem realizedObserverFiberHellingerEnvelopeProcess_eq_realizedHellingerEnvelope
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.realizedObserverFiberHellingerEnvelopeProcess π ω pstar =
      U.realizedHellingerEnvelopeProcess π ω pstar
        (U.observerFiberStepBhattacharyyaScore π ω pstar) :=
  rfl

/--
Target constructor for the countable realized processes.

Future hardening phases should prove the martingale, L¹-bound, and divergence
hypotheses here from Bayes/Gibbs updates, semantic separation, and realized
policy support. Phase H1 only fixes the exact process names and their assembly
into `HellingerConvergenceSpine`.
-/
theorem hellingerConvergenceSpine_of_realized_processes
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O)
    {μ : Measure (Trajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (Trajectory A O))}
    {C : ℝ≥0}
    (hM_martingale :
      Martingale (U.realizedHellingerEnvelopeProcess π ω pstar B) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm (U.realizedHellingerEnvelopeProcess π ω pstar B n) 1 μ ≤
          (C : ℝ≥0∞))
    (hS_diverges :
      ∀ᵐ ξ ∂μ,
        Tendsto (fun n => realizedCumulativeSeparationProcess B n ξ) atTop atTop) :
    HellingerConvergenceSpine μ ℱ
      (U.realizedResidualOddsProcess π ω pstar)
      (U.realizedHellingerEnvelopeProcess π ω pstar B)
      (realizedCumulativeSeparationProcess B) C := by
  exact HellingerConvergenceSpine.of_processes
    (U.ae_realizedResidualOddsProcess_nonneg π ω pstar)
    hM_martingale hM_bdd hS_diverges

/--
Target constructor for the H2 predictive-law Bhattacharyya process.

This is the paper-facing specialization of the H1 process constructor: the
separation process is no longer an arbitrary external score but the
observer-fiber class/complement Bhattacharyya score built from the countable
predictive laws above.
-/
theorem hellingerConvergenceSpine_of_observerFiberBhattacharyya_processes
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (Trajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (Trajectory A O))}
    {C : ℝ≥0}
    (hM_martingale :
      Martingale (U.realizedObserverFiberHellingerEnvelopeProcess π ω pstar) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm (U.realizedObserverFiberHellingerEnvelopeProcess π ω pstar n) 1 μ ≤
          (C : ℝ≥0∞))
    (hS_diverges :
      ∀ᵐ ξ ∂μ,
        Tendsto
          (fun n =>
            U.realizedObserverFiberCumulativeBhattacharyyaSeparationProcess
              π ω pstar n ξ)
          atTop atTop) :
    HellingerConvergenceSpine μ ℱ
      (U.realizedResidualOddsProcess π ω pstar)
      (U.realizedObserverFiberHellingerEnvelopeProcess π ω pstar)
      (U.realizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar)
      C := by
  exact HellingerConvergenceSpine.of_processes
    (U.ae_realizedResidualOddsProcess_nonneg π ω pstar)
    hM_martingale hM_bdd hS_diverges

/--
Residual observer-fiber odds process along an infinite realized stream.

Unlike `residualObserverFiberProcess` on finite `Trajectory` lists, this process
is defined at every time by taking the finite prefix of the infinite stream.
-/
def infiniteResidualObserverFiberProcess (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → InfiniteTrajectory A O → ENNReal :=
  fun t ξ => U.residualObserverFiberPosteriorOdds π t (infiniteHistoryPrefix ξ t) ω pstar

/-- Real-valued residual odds process along an infinite realized stream. -/
def infiniteRealizedResidualOddsProcess (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  fun t ξ => (U.infiniteResidualObserverFiberProcess π ω pstar t ξ).toReal

/--
Infinite-stream realized Bhattacharyya separation process.

There is no terminal fallback: the next action is always the action component of
the infinite stream event at time `n`.
-/
def infiniteRealizedBhattacharyyaSeparationProcess
    (B : StepBhattacharyyaScore A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  fun n ξ => B n (infiniteHistoryPrefix ξ n) (infiniteRealizedAction ξ n)

/-- Cumulative infinite-stream separation process `Sₙ = ∑_{i<n} Bᵢ`. -/
def infiniteRealizedCumulativeSeparationProcess
    (B : StepBhattacharyyaScore A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  cumulativeSeparationProcess (infiniteRealizedBhattacharyyaSeparationProcess B)

/-- Infinite-stream Hellinger envelope `Mₙ = exp(Sₙ) * sqrt(Rₙ)`. -/
def infiniteRealizedHellingerEnvelopeProcess (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  hellingerEnvelopeProcess
    (U.infiniteRealizedResidualOddsProcess π ω pstar)
    (infiniteRealizedCumulativeSeparationProcess B)

/--
Infinite-stream one-step Bhattacharyya process for the canonical observer-fiber
predictive-law score.
-/
def infiniteRealizedObserverFiberBhattacharyyaSeparationProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  infiniteRealizedBhattacharyyaSeparationProcess
    (U.observerFiberStepBhattacharyyaScore π ω pstar)

/-- Cumulative infinite-stream observer-fiber Bhattacharyya separation. -/
def infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  cumulativeSeparationProcess
    (U.infiniteRealizedObserverFiberBhattacharyyaSeparationProcess π ω pstar)

/-- Infinite-stream Hellinger envelope for the canonical observer-fiber score. -/
def infiniteRealizedObserverFiberHellingerEnvelopeProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  hellingerEnvelopeProcess
    (U.infiniteRealizedResidualOddsProcess π ω pstar)
    (U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar)

/--
Infinite-stream one-step true-law Hellinger process for the observer-fiber
residual update under the realized environment program `penv`.
-/
def infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  infiniteRealizedBhattacharyyaSeparationProcess
    (U.observerFiberTrueLawStepHellingerScore π penv ω pstar)

/-- Cumulative infinite-stream true-law observer-fiber Hellinger separation. -/
def infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  cumulativeSeparationProcess
    (U.infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess π penv ω pstar)

/--
Infinite-stream Hellinger envelope normalized by the true-environment
conditional law.
-/
def infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    Nat → InfiniteTrajectory A O → ℝ :=
  hellingerEnvelopeProcess
    (U.infiniteRealizedResidualOddsProcess π ω pstar)
    (U.infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
      π penv ω pstar)

theorem infiniteRealizedResidualOddsProcess_nonneg
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    ∀ n ξ, 0 ≤ U.infiniteRealizedResidualOddsProcess π ω pstar n ξ := by
  intro n ξ
  exact ENNReal.toReal_nonneg

theorem ae_infiniteRealizedResidualOddsProcess_nonneg
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} :
    ∀ᵐ ξ ∂μ, ∀ n, 0 ≤ U.infiniteRealizedResidualOddsProcess π ω pstar n ξ :=
  Filter.Eventually.of_forall
    (fun ξ n => U.infiniteRealizedResidualOddsProcess_nonneg π ω pstar n ξ)

theorem infiniteRealizedHellingerEnvelopeProcess_nonneg
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O) :
    ∀ n ξ, 0 ≤ U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ξ := by
  intro n ξ
  exact mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.sqrt_nonneg _)

theorem infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess_nonneg
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    ∀ n ξ,
      0 ≤
        U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
          π penv ω pstar n ξ := by
  simpa [infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
    infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
    infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess,
    infiniteRealizedHellingerEnvelopeProcess] using
    U.infiniteRealizedHellingerEnvelopeProcess_nonneg π ω pstar
      (U.observerFiberTrueLawStepHellingerScore π penv ω pstar)

omit [Encodable A] [Encodable O] in
theorem infiniteRealizedBhattacharyyaSeparationProcess_eq
    (B : StepBhattacharyyaScore A O) (n : Nat) (ξ : InfiniteTrajectory A O) :
    infiniteRealizedBhattacharyyaSeparationProcess B n ξ =
      B n (infiniteHistoryPrefix ξ n) (infiniteRealizedAction ξ n) :=
  rfl

theorem infiniteRealizedObserverFiberBhattacharyyaSeparationProcess_eq
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat) (ξ : InfiniteTrajectory A O) :
    U.infiniteRealizedObserverFiberBhattacharyyaSeparationProcess π ω pstar n ξ =
      U.observerFiberBhattacharyyaScore π n (infiniteHistoryPrefix ξ n)
        (infiniteRealizedAction ξ n) ω pstar := by
  rfl

omit [Encodable A] [Encodable O] in
theorem infiniteRealizedCumulativeSeparationProcess_eq_sum
    (B : StepBhattacharyyaScore A O) (n : Nat) (ξ : InfiniteTrajectory A O) :
    infiniteRealizedCumulativeSeparationProcess B n ξ =
      ∑ i ∈ Finset.range n, infiniteRealizedBhattacharyyaSeparationProcess B i ξ :=
  rfl

theorem infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess_eq_sum
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat) (ξ : InfiniteTrajectory A O) :
    U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar n ξ =
      ∑ i ∈ Finset.range n,
        U.infiniteRealizedObserverFiberBhattacharyyaSeparationProcess π ω pstar i ξ :=
  rfl

theorem infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess_eq_realizedCumulative
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar =
      infiniteRealizedCumulativeSeparationProcess
        (U.observerFiberStepBhattacharyyaScore π ω pstar) :=
  rfl

theorem infiniteRealizedObserverFiberHellingerEnvelopeProcess_eq
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat) (ξ : InfiniteTrajectory A O) :
    U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n ξ =
      Real.exp
          (U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess
            π ω pstar n ξ) *
        Real.sqrt (U.infiniteRealizedResidualOddsProcess π ω pstar n ξ) :=
  rfl

theorem infiniteRealizedObserverFiberHellingerEnvelopeProcess_eq_realizedHellingerEnvelope
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar =
      U.infiniteRealizedHellingerEnvelopeProcess π ω pstar
        (U.observerFiberStepBhattacharyyaScore π ω pstar) :=
  rfl

/--
Uniform realized separation floor for an arbitrary paper-level Bhattacharyya
score process.

For the current finite `Trajectory` type this is a deliberately strong
infinite-horizon hypothesis: it cannot be obtained from a fixed finite
`trajectoryLaw T` alone, because terminal extensions contribute zero. The point
of the predicate is to make the required infinite support/separation input
explicit rather than hiding it inside `Sₙ → ∞`.
-/
def HasRealizedBhattacharyyaUniformSeparationFloor
    (B : StepBhattacharyyaScore A O)
    (μ : Measure (Trajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ᵐ ξ ∂μ, ∀ n, κ ≤ realizedBhattacharyyaSeparationProcess B n ξ

omit [Encodable A] [Encodable O] in
/--
Uniform one-step Bhattacharyya separation implies almost-sure divergence of the
realized cumulative separation process.
-/
theorem ae_realizedCumulativeSeparationProcess_tendsto_atTop_of_uniform_floor
    (B : StepBhattacharyyaScore A O)
    {μ : Measure (Trajectory A O)} {κ : ℝ}
    (hFloor : HasRealizedBhattacharyyaUniformSeparationFloor B μ κ) :
    ∀ᵐ ξ ∂μ,
      Tendsto (fun n => realizedCumulativeSeparationProcess B n ξ) atTop atTop := by
  rcases hFloor with ⟨hκ, hStep⟩
  exact ae_cumulativeSeparationProcess_tendsto_atTop_of_uniform_step_lower_bound
    (realizedBhattacharyyaSeparationProcess B) hκ hStep

/--
Hellinger spine constructor with the divergence leg derived from a uniform
realized Bhattacharyya separation floor.

After this theorem, the only remaining probabilistic inputs for the arbitrary
score route are the martingality and L¹ boundedness of the Hellinger envelope.
-/
theorem hellingerConvergenceSpine_of_realized_processes_uniform_separation_floor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O)
    {μ : Measure (Trajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (Trajectory A O))}
    {C : ℝ≥0} {κ : ℝ}
    (hM_martingale :
      Martingale (U.realizedHellingerEnvelopeProcess π ω pstar B) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm (U.realizedHellingerEnvelopeProcess π ω pstar B n) 1 μ ≤
          (C : ℝ≥0∞))
    (hFloor : HasRealizedBhattacharyyaUniformSeparationFloor B μ κ) :
    HellingerConvergenceSpine μ ℱ
      (U.realizedResidualOddsProcess π ω pstar)
      (U.realizedHellingerEnvelopeProcess π ω pstar B)
      (realizedCumulativeSeparationProcess B) C := by
  exact U.hellingerConvergenceSpine_of_realized_processes π ω pstar B
    hM_martingale hM_bdd
    (ae_realizedCumulativeSeparationProcess_tendsto_atTop_of_uniform_floor
      B hFloor)

/--
Uniform realized separation floor for the canonical observer-fiber predictive
Bhattacharyya process.
-/
def HasObserverFiberBhattacharyyaUniformSeparationFloor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (μ : Measure (Trajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ᵐ ξ ∂μ, ∀ n,
      κ ≤ U.realizedObserverFiberBhattacharyyaSeparationProcess π ω pstar n ξ

/--
All-time realized policy support.

This is the honest infinite-trajectory side condition needed to turn a
policy-support floor into the H3 all-`n` realized floor. It is intentionally not
derived from the current finite-horizon `trajectoryLaw T`, whose samples have
terminal tails.
-/
def HasRealizedPolicySupportAtAllTimes
    (π : CountablePolicy A O)
    (μ : Measure (Trajectory A O)) : Prop :=
  ∀ᵐ ξ ∂μ, ∀ n,
    ∃ hn : n < ξ.length,
      (ξ.get ⟨n, hn⟩).1 ∈ (π (historyPrefix ξ n)).support

/--
Observer-fiber Bhattacharyya score floor on actions supported by the realized
policy at the current prefix.
-/
def HasObserverFiberBhattacharyyaFloorOnPolicySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (μ : Measure (Trajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ᵐ ξ ∂μ, ∀ n a,
      a ∈ (π (historyPrefix ξ n)).support →
        κ ≤ U.observerFiberBhattacharyyaScore π n (historyPrefix ξ n) a ω pstar

/--
Observer-fiber Bhattacharyya affinity ceiling on policy-supported actions.

This is the H4 semantic-separation input: the class/complement predictive
affinity is uniformly at most `exp(-κ)` whenever the policy can realize the
action.
-/
def HasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (μ : Measure (Trajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ᵐ ξ ∂μ, ∀ n a,
      a ∈ (π (historyPrefix ξ n)).support →
        0 < U.observerFiberPredictiveLawAffinity π n (historyPrefix ξ n) a ω pstar ∧
          U.observerFiberPredictiveLawAffinity π n (historyPrefix ξ n) a ω pstar ≤
            Real.exp (-κ)

/--
The semantic affinity ceiling gives the corresponding policy-support
Bhattacharyya score floor.
-/
theorem hasObserverFiberBhattacharyyaFloorOnPolicySupport_of_affinityCeiling
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (Trajectory A O)} {κ : ℝ}
    (hCeiling :
      HasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport U π ω pstar μ κ) :
    HasObserverFiberBhattacharyyaFloorOnPolicySupport U π ω pstar μ κ := by
  rcases hCeiling with ⟨hκ, hCeilingAE⟩
  refine ⟨hκ, ?_⟩
  filter_upwards [hCeilingAE] with ξ hξ n a ha
  rcases hξ n a ha with ⟨hAffPos, hAffLe⟩
  exact U.observerFiberBhattacharyyaScore_ge_of_affinity_ceiling
    π n (historyPrefix ξ n) a ω pstar hκ hAffPos hAffLe

/--
Policy-support score floors plus all-time realized policy support produce the
H3 uniform realized observer-fiber Bhattacharyya floor.
-/
theorem hasObserverFiberBhattacharyyaUniformSeparationFloor_of_policySupportFloor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (Trajectory A O)} {κ : ℝ}
    (hPolicyFloor :
      HasObserverFiberBhattacharyyaFloorOnPolicySupport U π ω pstar μ κ)
    (hRealizedSupport : HasRealizedPolicySupportAtAllTimes π μ) :
    HasObserverFiberBhattacharyyaUniformSeparationFloor U π ω pstar μ κ := by
  rcases hPolicyFloor with ⟨hκ, hFloorAE⟩
  refine ⟨hκ, ?_⟩
  filter_upwards [hFloorAE, hRealizedSupport] with ξ hFloorξ hSupportξ n
  rcases hSupportξ n with ⟨hn, hActSupport⟩
  rw [U.realizedObserverFiberBhattacharyyaSeparationProcess_of_lt π ω pstar hn]
  exact hFloorξ n (ξ.get ⟨n, hn⟩).1 hActSupport

/--
H4 bridge from semantic affinity ceilings and realized policy support directly
to the H3 uniform observer-fiber Bhattacharyya floor.
-/
theorem hasObserverFiberBhattacharyyaUniformSeparationFloor_of_affinityCeiling_policySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (Trajectory A O)} {κ : ℝ}
    (hCeiling :
      HasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport U π ω pstar μ κ)
    (hRealizedSupport : HasRealizedPolicySupportAtAllTimes π μ) :
    HasObserverFiberBhattacharyyaUniformSeparationFloor U π ω pstar μ κ :=
  U.hasObserverFiberBhattacharyyaUniformSeparationFloor_of_policySupportFloor
    π ω pstar
    (U.hasObserverFiberBhattacharyyaFloorOnPolicySupport_of_affinityCeiling
      π ω pstar hCeiling)
    hRealizedSupport

/--
Finite-horizon version of the observer-fiber affinity ceiling on policy-supported
actions. This is the exact statement that the current finite `trajectoryLaw T`
can support; H3's all-time floor requires an infinite-trajectory substrate or an
explicit all-time support hypothesis.
-/
def HasFiniteHorizonObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (T : Nat) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ ξ, ξ ∈ (U.trajectoryLaw π penv T).support →
      ∀ n, n < T →
        ∀ a, a ∈ (π (historyPrefix ξ n)).support →
          0 < U.observerFiberPredictiveLawAffinity π n (historyPrefix ξ n) a ω pstar ∧
            U.observerFiberPredictiveLawAffinity π n (historyPrefix ξ n) a ω pstar ≤
              Real.exp (-κ)

/--
Uniform realized separation floor for an arbitrary paper-level score on
infinite realized streams.
-/
def InfiniteHasRealizedBhattacharyyaUniformSeparationFloor
    (B : StepBhattacharyyaScore A O)
    (μ : Measure (InfiniteTrajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ᵐ ξ ∂μ, ∀ n,
      κ ≤ infiniteRealizedBhattacharyyaSeparationProcess B n ξ

/--
All-time realized policy support on infinite streams.

This is the H5 version of `HasRealizedPolicySupportAtAllTimes`: the realized
action is available at every time by construction, so the condition has no
finite-list nonterminal witness.
-/
def InfiniteHasRealizedPolicySupportAtAllTimes
    (π : CountablePolicy A O)
    (μ : Measure (InfiniteTrajectory A O)) : Prop :=
  ∀ᵐ ξ ∂μ, ∀ n,
    infiniteRealizedAction ξ n ∈ (π (infiniteHistoryPrefix ξ n)).support

/--
Observer-fiber Bhattacharyya score floor on policy-supported actions along
infinite streams.
-/
def InfiniteHasObserverFiberBhattacharyyaFloorOnPolicySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (μ : Measure (InfiniteTrajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ᵐ ξ ∂μ, ∀ n a,
      a ∈ (π (infiniteHistoryPrefix ξ n)).support →
        κ ≤ U.observerFiberBhattacharyyaScore π n (infiniteHistoryPrefix ξ n) a ω pstar

/--
Observer-fiber Bhattacharyya affinity ceiling on policy-supported actions along
infinite streams.
-/
def InfiniteHasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (μ : Measure (InfiniteTrajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ᵐ ξ ∂μ, ∀ n a,
      a ∈ (π (infiniteHistoryPrefix ξ n)).support →
        0 < U.observerFiberPredictiveLawAffinity π n
            (infiniteHistoryPrefix ξ n) a ω pstar ∧
          U.observerFiberPredictiveLawAffinity π n
              (infiniteHistoryPrefix ξ n) a ω pstar ≤
            Real.exp (-κ)

/--
True-law Hellinger multiplier ceiling on policy-supported actions along
infinite streams. This is the caveat-free ceiling for the constructed
Bayes/Gibbs law generated by `penv`.
-/
def InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (μ : Measure (InfiniteTrajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ᵐ ξ ∂μ, ∀ n a,
      a ∈ (π (infiniteHistoryPrefix ξ n)).support →
        0 < U.observerFiberTrueLawHellingerAffinity π penv n
            (infiniteHistoryPrefix ξ n) a ω pstar ∧
          U.observerFiberTrueLawHellingerAffinity π penv n
              (infiniteHistoryPrefix ξ n) a ω pstar ≤
            Real.exp (-κ)

/--
Finite-prefix action-rule form of the true-law Hellinger affinity ceiling.

This is the semantic-to-Hellinger bridge surface: the selected policy may put
mass only on actions whose true-law Hellinger multiplier is positive and at
most `exp (-κ)`. A full-support soft rule will not satisfy this unless every
action is already safe; hard thresholding or a zero-mass reference outside the
safe set is the intended way to discharge the predicate.
-/
def TrueLawHellingerAffinityCeilingActionRule
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ h a,
      a ∈ (π h).support →
        0 < U.observerFiberTrueLawHellingerAffinity π penv h.length h a ω pstar ∧
          U.observerFiberTrueLawHellingerAffinity π penv h.length h a ω pstar ≤
            Real.exp (-κ)

/--
If the finite-prefix action rule only supports true-law Hellinger-safe actions,
then the infinite constructed-law affinity ceiling required by the Hellinger
spine holds under any infinite trajectory law.
-/
theorem infiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport_of_actionRule
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} {κ : ℝ}
    (hRule :
      U.TrueLawHellingerAffinityCeilingActionRule π penv ω pstar κ) :
    InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
      U π penv ω pstar μ κ := by
  rcases hRule with ⟨hκ, hSafe⟩
  refine ⟨hκ, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro ξ n a ha
  have hLen :
      (infiniteHistoryPrefix (A := A) (O := O) ξ n).length = n := by
    simp [infiniteHistoryPrefix]
  simpa [hLen] using
    hSafe (infiniteHistoryPrefix (A := A) (O := O) ξ n) a ha

/--
Uniform observer-fiber Bhattacharyya floor along infinite realized streams.
-/
def InfiniteHasObserverFiberBhattacharyyaUniformSeparationFloor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (μ : Measure (InfiniteTrajectory A O)) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ᵐ ξ ∂μ, ∀ n,
      κ ≤ U.infiniteRealizedObserverFiberBhattacharyyaSeparationProcess π ω pstar n ξ

omit [Encodable A] [Encodable O] in
/--
Infinite-stream cumulative divergence from a uniform one-step separation floor.
-/
theorem ae_infiniteRealizedCumulativeSeparationProcess_tendsto_atTop_of_uniform_floor
    (B : StepBhattacharyyaScore A O)
    {μ : Measure (InfiniteTrajectory A O)} {κ : ℝ}
    (hFloor : InfiniteHasRealizedBhattacharyyaUniformSeparationFloor B μ κ) :
    ∀ᵐ ξ ∂μ,
      Tendsto
        (fun n => infiniteRealizedCumulativeSeparationProcess B n ξ)
        atTop atTop := by
  rcases hFloor with ⟨hκ, hStep⟩
  exact ae_cumulativeSeparationProcess_tendsto_atTop_of_uniform_step_lower_bound
    (infiniteRealizedBhattacharyyaSeparationProcess B) hκ hStep

/--
H5 generic infinite-stream constructor: a uniform realized score floor gives the
divergence leg of the Hellinger spine on an infinite realized process.
-/
theorem hellingerConvergenceSpine_of_infinite_realized_processes_uniform_separation_floor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (InfiniteTrajectory A O))}
    {C : ℝ≥0} {κ : ℝ}
    (hM_martingale :
      Martingale (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) 1 μ ≤
          (C : ℝ≥0∞))
    (hFloor : InfiniteHasRealizedBhattacharyyaUniformSeparationFloor B μ κ) :
    HellingerConvergenceSpine μ ℱ
      (U.infiniteRealizedResidualOddsProcess π ω pstar)
      (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B)
      (infiniteRealizedCumulativeSeparationProcess B) C := by
  simpa [infiniteRealizedHellingerEnvelopeProcess,
    infiniteRealizedCumulativeSeparationProcess] using
    (HellingerConvergenceSpine.of_processes
      (U.ae_infiniteRealizedResidualOddsProcess_nonneg π ω pstar)
      hM_martingale hM_bdd
      (ae_infiniteRealizedCumulativeSeparationProcess_tendsto_atTop_of_uniform_floor
        B hFloor))

/--
The infinite-stream semantic affinity ceiling gives the corresponding
policy-support Bhattacharyya score floor.
-/
theorem infiniteHasObserverFiberBhattacharyyaFloorOnPolicySupport_of_affinityCeiling
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} {κ : ℝ}
    (hCeiling :
      InfiniteHasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport
        U π ω pstar μ κ) :
    InfiniteHasObserverFiberBhattacharyyaFloorOnPolicySupport U π ω pstar μ κ := by
  rcases hCeiling with ⟨hκ, hCeilingAE⟩
  refine ⟨hκ, ?_⟩
  filter_upwards [hCeilingAE] with ξ hξ n a ha
  rcases hξ n a ha with ⟨hAffPos, hAffLe⟩
  exact U.observerFiberBhattacharyyaScore_ge_of_affinity_ceiling
    π n (infiniteHistoryPrefix ξ n) a ω pstar hκ hAffPos hAffLe

/--
Policy-support score floors plus all-time infinite realized support produce the
uniform infinite-stream observer-fiber Bhattacharyya floor.
-/
theorem infiniteHasObserverFiberBhattacharyyaUniformSeparationFloor_of_policySupportFloor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} {κ : ℝ}
    (hPolicyFloor :
      InfiniteHasObserverFiberBhattacharyyaFloorOnPolicySupport U π ω pstar μ κ)
    (hRealizedSupport : InfiniteHasRealizedPolicySupportAtAllTimes π μ) :
    InfiniteHasObserverFiberBhattacharyyaUniformSeparationFloor U π ω pstar μ κ := by
  rcases hPolicyFloor with ⟨hκ, hFloorAE⟩
  refine ⟨hκ, ?_⟩
  filter_upwards [hFloorAE, hRealizedSupport] with ξ hFloorξ hSupportξ n
  have hScore :=
    hFloorξ n (infiniteRealizedAction ξ n) (hSupportξ n)
  simpa [infiniteRealizedObserverFiberBhattacharyyaSeparationProcess,
    infiniteRealizedBhattacharyyaSeparationProcess, observerFiberStepBhattacharyyaScore,
    infiniteRealizedAction] using hScore

/--
H5 bridge from semantic affinity ceilings and infinite realized policy support
directly to the uniform infinite-stream observer-fiber Bhattacharyya floor.
-/
theorem infiniteHasObserverFiberBhattacharyyaUniformSeparationFloor_of_affinityCeiling_policySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} {κ : ℝ}
    (hCeiling :
      InfiniteHasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport
        U π ω pstar μ κ)
    (hRealizedSupport : InfiniteHasRealizedPolicySupportAtAllTimes π μ) :
    InfiniteHasObserverFiberBhattacharyyaUniformSeparationFloor U π ω pstar μ κ :=
  U.infiniteHasObserverFiberBhattacharyyaUniformSeparationFloor_of_policySupportFloor
    π ω pstar
    (U.infiniteHasObserverFiberBhattacharyyaFloorOnPolicySupport_of_affinityCeiling
      π ω pstar hCeiling)
    hRealizedSupport

/--
True-law multiplier ceilings plus all-time realized policy support give a
uniform realized true-law Hellinger separation floor.
-/
theorem infiniteHasObserverFiberTrueLawHellingerUniformSeparationFloor_of_affinityCeiling_policySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} {κ : ℝ}
    (hCeiling :
      InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar μ κ)
    (hRealizedSupport : InfiniteHasRealizedPolicySupportAtAllTimes π μ) :
    InfiniteHasRealizedBhattacharyyaUniformSeparationFloor
      (U.observerFiberTrueLawStepHellingerScore π penv ω pstar) μ κ := by
  rcases hCeiling with ⟨hκ, hCeilingAE⟩
  refine ⟨hκ, ?_⟩
  filter_upwards [hCeilingAE, hRealizedSupport] with ξ hCeilingξ hSupportξ n
  have hAff := hCeilingξ n (infiniteRealizedAction ξ n) (hSupportξ n)
  exact U.observerFiberTrueLawHellingerScore_ge_of_affinity_ceiling
    π penv n (infiniteHistoryPrefix ξ n) (infiniteRealizedAction ξ n)
    ω pstar hκ hAff.1 hAff.2

/--
The true-law uniform Hellinger floor implies almost-sure divergence of the
true-law cumulative Hellinger separation process.
-/
theorem ae_infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparation_tendsto_atTop_of_uniform_floor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} {κ : ℝ}
    (hFloor :
      InfiniteHasRealizedBhattacharyyaUniformSeparationFloor
        (U.observerFiberTrueLawStepHellingerScore π penv ω pstar) μ κ) :
    ∀ᵐ ξ ∂μ,
      Tendsto
        (fun n =>
          U.infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
            π penv ω pstar n ξ)
        atTop atTop := by
  simpa [infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
    infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess] using
    ae_infiniteRealizedCumulativeSeparationProcess_tendsto_atTop_of_uniform_floor
      (A := A) (O := O)
      (U.observerFiberTrueLawStepHellingerScore π penv ω pstar) hFloor

/--
The infinite observer-fiber uniform Bhattacharyya floor implies almost-sure
divergence of the infinite cumulative Bhattacharyya separation process.
-/
theorem ae_infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparation_tendsto_atTop_of_uniform_floor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} {κ : ℝ}
    (hFloor :
      InfiniteHasObserverFiberBhattacharyyaUniformSeparationFloor U π ω pstar μ κ) :
    ∀ᵐ ξ ∂μ,
      Tendsto
        (fun n =>
          U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess
            π ω pstar n ξ)
        atTop atTop := by
  rcases hFloor with ⟨hκ, hStep⟩
  exact ae_cumulativeSeparationProcess_tendsto_atTop_of_uniform_step_lower_bound
    (U.infiniteRealizedObserverFiberBhattacharyyaSeparationProcess π ω pstar)
    hκ hStep

/--
Paper-facing H5 constructor for the canonical observer-fiber predictive-law
Bhattacharyya process on infinite realized streams.
-/
theorem hellingerConvergenceSpine_of_infiniteObserverFiberBhattacharyya_uniform_separation_floor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (InfiniteTrajectory A O))}
    {C : ℝ≥0} {κ : ℝ}
    (hM_martingale :
      Martingale (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm
            (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n) 1 μ ≤
          (C : ℝ≥0∞))
    (hFloor :
      InfiniteHasObserverFiberBhattacharyyaUniformSeparationFloor U π ω pstar μ κ) :
    HellingerConvergenceSpine μ ℱ
      (U.infiniteRealizedResidualOddsProcess π ω pstar)
      (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar)
      (U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar)
      C := by
  simpa [infiniteRealizedObserverFiberHellingerEnvelopeProcess,
    infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess] using
    (HellingerConvergenceSpine.of_processes
      (U.ae_infiniteRealizedResidualOddsProcess_nonneg π ω pstar)
      hM_martingale hM_bdd
      (U.ae_infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparation_tendsto_atTop_of_uniform_floor
        π ω pstar hFloor))

/--
H5 soft Section 6 constructor: semantic affinity ceiling plus all-time realized
policy support provide the divergence leg of the infinite-stream Hellinger
spine. The remaining inputs are exactly the Bayes/Gibbs martingale and L1 bound.
-/
theorem hellingerConvergenceSpine_of_infiniteObserverFiberBhattacharyya_affinityCeiling_policySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (InfiniteTrajectory A O))}
    {C : ℝ≥0} {κ : ℝ}
    (hM_martingale :
      Martingale (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm
            (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n) 1 μ ≤
          (C : ℝ≥0∞))
    (hCeiling :
      InfiniteHasObserverFiberBhattacharyyaAffinityCeilingOnPolicySupport
        U π ω pstar μ κ)
    (hRealizedSupport : InfiniteHasRealizedPolicySupportAtAllTimes π μ) :
    HellingerConvergenceSpine μ ℱ
      (U.infiniteRealizedResidualOddsProcess π ω pstar)
      (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar)
      (U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar)
      C :=
  U.hellingerConvergenceSpine_of_infiniteObserverFiberBhattacharyya_uniform_separation_floor
    π ω pstar hM_martingale hM_bdd
    (U.infiniteHasObserverFiberBhattacharyyaUniformSeparationFloor_of_affinityCeiling_policySupport
      π ω pstar hCeiling hRealizedSupport)

/--
Caveat-free H5 soft Section 6 constructor: true-law Hellinger multiplier ceiling
plus all-time realized policy support provides the divergence leg for the
Hellinger envelope whose local normalization is computed under the actual
environment program `penv`.
-/
theorem hellingerConvergenceSpine_of_infiniteObserverFiberTrueLawHellinger_affinityCeiling_policySupport
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (InfiniteTrajectory A O))}
    {C : ℝ≥0} {κ : ℝ}
    (hM_martingale :
      Martingale
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar n) 1 μ ≤
          (C : ℝ≥0∞))
    (hCeiling :
      InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar μ κ)
    (hRealizedSupport : InfiniteHasRealizedPolicySupportAtAllTimes π μ) :
    HellingerConvergenceSpine μ ℱ
      (U.infiniteRealizedResidualOddsProcess π ω pstar)
      (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar)
      (U.infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
        π penv ω pstar)
      C := by
  have hFloor :
      InfiniteHasRealizedBhattacharyyaUniformSeparationFloor
        (U.observerFiberTrueLawStepHellingerScore π penv ω pstar) μ κ :=
    U.infiniteHasObserverFiberTrueLawHellingerUniformSeparationFloor_of_affinityCeiling_policySupport
      π penv ω pstar hCeiling hRealizedSupport
  simpa [infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
    infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
    infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess] using
    U.hellingerConvergenceSpine_of_infinite_realized_processes_uniform_separation_floor
      π ω pstar (U.observerFiberTrueLawStepHellingerScore π penv ω pstar)
      hM_martingale hM_bdd hFloor

/--
True-law Hellinger spine from martingality alone.

The true-law envelope is nonnegative, so its martingale property gives the
uniform `L¹` bound required by the convergence spine from the initial integral.
This removes the separate pointwise envelope-bound hypothesis from the true-law
route.
-/
theorem hellingerConvergenceSpine_of_infiniteObserverFiberTrueLawHellinger_affinityCeiling_policySupport_of_martingale
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (InfiniteTrajectory A O))}
    {κ : ℝ}
    (hM_martingale :
      Martingale
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
          π penv ω pstar) ℱ μ)
    (hCeiling :
      InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar μ κ)
    (hRealizedSupport : InfiniteHasRealizedPolicySupportAtAllTimes π μ) :
    ∃ C : ℝ≥0,
      HellingerConvergenceSpine μ ℱ
        (U.infiniteRealizedResidualOddsProcess π ω pstar)
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar)
        (U.infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
          π penv ω pstar)
        C := by
  let C : ℝ≥0 :=
    Real.toNNReal
      (∫ ξ,
        U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
          π penv ω pstar 0 ξ ∂μ)
  have hNonneg :
      ∀ n,
        0 ≤ᵐ[μ]
          U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar n := by
    intro n
    exact Filter.Eventually.of_forall
      (fun ξ =>
        U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess_nonneg
          π penv ω pstar n ξ)
  have hBdd :
      ∀ n,
        eLpNorm
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar n) 1 μ ≤
          (C : ℝ≥0∞) := by
    refine martingale_eLpNorm_one_bounded_of_nonneg_initial_integral_le
      hM_martingale hNonneg ?_
    exact Real.le_coe_toNNReal _
  exact ⟨C,
    U.hellingerConvergenceSpine_of_infiniteObserverFiberTrueLawHellinger_affinityCeiling_policySupport
      π penv ω pstar hM_martingale hBdd hCeiling hRealizedSupport⟩

/--
The observer-fiber uniform Bhattacharyya floor implies almost-sure divergence of
the observer-fiber cumulative Bhattacharyya separation process.
-/
theorem ae_realizedObserverFiberCumulativeBhattacharyyaSeparation_tendsto_atTop_of_uniform_floor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (Trajectory A O)} {κ : ℝ}
    (hFloor :
      HasObserverFiberBhattacharyyaUniformSeparationFloor U π ω pstar μ κ) :
    ∀ᵐ ξ ∂μ,
      Tendsto
        (fun n =>
          U.realizedObserverFiberCumulativeBhattacharyyaSeparationProcess
            π ω pstar n ξ)
        atTop atTop := by
  rcases hFloor with ⟨hκ, hStep⟩
  exact ae_cumulativeSeparationProcess_tendsto_atTop_of_uniform_step_lower_bound
    (U.realizedObserverFiberBhattacharyyaSeparationProcess π ω pstar) hκ hStep

/--
Paper-facing H3 constructor for the canonical observer-fiber predictive-law
Bhattacharyya process.

Compared with `hellingerConvergenceSpine_of_observerFiberBhattacharyya_processes`,
this removes `Sₙ → ∞` as a raw input: it is derived from a uniform per-step
Bhattacharyya floor. The remaining open obligations are exactly the martingale
and L¹ envelope hypotheses.
-/
theorem hellingerConvergenceSpine_of_observerFiberBhattacharyya_uniform_separation_floor
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (Trajectory A O)} [IsFiniteMeasure μ]
    {ℱ : Filtration Nat (inferInstance : MeasurableSpace (Trajectory A O))}
    {C : ℝ≥0} {κ : ℝ}
    (hM_martingale :
      Martingale (U.realizedObserverFiberHellingerEnvelopeProcess π ω pstar) ℱ μ)
    (hM_bdd :
      ∀ n,
        eLpNorm (U.realizedObserverFiberHellingerEnvelopeProcess π ω pstar n) 1 μ ≤
          (C : ℝ≥0∞))
    (hFloor :
      HasObserverFiberBhattacharyyaUniformSeparationFloor U π ω pstar μ κ) :
    HellingerConvergenceSpine μ ℱ
      (U.realizedResidualOddsProcess π ω pstar)
      (U.realizedObserverFiberHellingerEnvelopeProcess π ω pstar)
      (U.realizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar)
      C := by
  exact U.hellingerConvergenceSpine_of_observerFiberBhattacharyya_processes
    π ω pstar hM_martingale hM_bdd
    (U.ae_realizedObserverFiberCumulativeBhattacharyyaSeparation_tendsto_atTop_of_uniform_floor
      π ω pstar hFloor)

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

/-- The infinite residual-odds process is adapted to the infinite-prefix filtration. -/
theorem infiniteResidualObserverFiberProcess_adapted (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    AdaptedToInfinitePrefixFiltration
      (U.infiniteResidualObserverFiberProcess π ω pstar) := by
  intro t s ξ ζ hEq
  have hProc :
      U.infiniteResidualObserverFiberProcess π ω pstar t ξ =
        U.infiniteResidualObserverFiberProcess π ω pstar t ζ := by
    simpa [infiniteResidualObserverFiberProcess] using
      congrArg (fun h => U.residualObserverFiberPosteriorOdds π t h ω pstar) hEq
  change U.infiniteResidualObserverFiberProcess π ω pstar t ξ ∈ s ↔
    U.infiniteResidualObserverFiberProcess π ω pstar t ζ ∈ s
  rw [hProc]

/-- The real-valued infinite residual-odds process is adapted to the infinite-prefix filtration. -/
theorem infiniteRealizedResidualOddsProcess_adapted (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    AdaptedToInfinitePrefixFiltration
      (U.infiniteRealizedResidualOddsProcess π ω pstar) := by
  intro t s ξ ζ hEq
  have hProc :
      U.infiniteRealizedResidualOddsProcess π ω pstar t ξ =
        U.infiniteRealizedResidualOddsProcess π ω pstar t ζ := by
    simp [infiniteRealizedResidualOddsProcess, infiniteResidualObserverFiberProcess, hEq]
  change U.infiniteRealizedResidualOddsProcess π ω pstar t ξ ∈ s ↔
    U.infiniteRealizedResidualOddsProcess π ω pstar t ζ ∈ s
  rw [hProc]

omit [Encodable A] [Encodable O] in
/--
The one-step infinite Bhattacharyya score at time `t` is measurable with respect
to the next prefix, since it depends on the `t`-prefix and the realized action
at time `t`.
-/
theorem infiniteRealizedBhattacharyyaSeparationProcess_mem_infinitePrefixFiltration_succ
    (B : StepBhattacharyyaScore A O) (t : Nat) (s : Set ℝ) :
    {ξ : InfiniteTrajectory A O | infiniteRealizedBhattacharyyaSeparationProcess B t ξ ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) (t + 1) := by
  intro ξ ζ hEq
  have hPrefix :
      infiniteHistoryPrefix ξ t = infiniteHistoryPrefix ζ t :=
    infiniteHistoryPrefix_eq_of_succ_eq (A := A) (O := O) hEq
  have hAct :
      infiniteRealizedAction ξ t = infiniteRealizedAction ζ t :=
    infiniteRealizedAction_eq_of_prefix_succ_eq (A := A) (O := O) hEq
  have hProc :
      infiniteRealizedBhattacharyyaSeparationProcess B t ξ =
        infiniteRealizedBhattacharyyaSeparationProcess B t ζ := by
    simp [infiniteRealizedBhattacharyyaSeparationProcess, hPrefix, hAct]
  change infiniteRealizedBhattacharyyaSeparationProcess B t ξ ∈ s ↔
    infiniteRealizedBhattacharyyaSeparationProcess B t ζ ∈ s
  rw [hProc]

/--
The canonical observer-fiber one-step Bhattacharyya score is measurable with
respect to the next infinite prefix.
-/
theorem infiniteRealizedObserverFiberBhattacharyyaSeparationProcess_mem_infinitePrefixFiltration_succ
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (t : Nat) (s : Set ℝ) :
    {ξ : InfiniteTrajectory A O |
        U.infiniteRealizedObserverFiberBhattacharyyaSeparationProcess π ω pstar t ξ ∈ s} ∈
      infinitePrefixFiltration (A := A) (O := O) (t + 1) := by
  simpa [infiniteRealizedObserverFiberBhattacharyyaSeparationProcess] using
    infiniteRealizedBhattacharyyaSeparationProcess_mem_infinitePrefixFiltration_succ
      (A := A) (O := O)
      (U.observerFiberStepBhattacharyyaScore π ω pstar) t s

omit [Encodable A] [Encodable O] in
/-- A one-step infinite Bhattacharyya score before time `n` is determined by the `n`-prefix. -/
theorem infiniteRealizedBhattacharyyaSeparationProcess_eq_of_prefix_eq_of_lt
    (B : StepBhattacharyyaScore A O) {ξ ζ : InfiniteTrajectory A O} {i n : Nat}
    (hi : i < n)
    (hEq : infiniteHistoryPrefix ξ n = infiniteHistoryPrefix ζ n) :
    infiniteRealizedBhattacharyyaSeparationProcess B i ξ =
      infiniteRealizedBhattacharyyaSeparationProcess B i ζ := by
  have hPrefix :
      infiniteHistoryPrefix ξ i = infiniteHistoryPrefix ζ i :=
    infiniteHistoryPrefix_eq_of_le_eq (A := A) (O := O) (Nat.le_of_lt hi) hEq
  have hAct :
      infiniteRealizedAction ξ i = infiniteRealizedAction ζ i :=
    infiniteRealizedAction_eq_of_prefix_eq_of_lt (A := A) (O := O) hi hEq
  simp [infiniteRealizedBhattacharyyaSeparationProcess, hPrefix, hAct]

omit [Encodable A] [Encodable O] in
/-- The cumulative infinite separation process is adapted to the canonical prefix filtration. -/
theorem infiniteRealizedCumulativeSeparationProcess_adapted
    (B : StepBhattacharyyaScore A O) :
    AdaptedToInfinitePrefixFiltration (A := A) (O := O)
      (infiniteRealizedCumulativeSeparationProcess B) := by
  intro n s ξ ζ hEq
  have hProc :
      infiniteRealizedCumulativeSeparationProcess B n ξ =
        infiniteRealizedCumulativeSeparationProcess B n ζ := by
    rw [infiniteRealizedCumulativeSeparationProcess_eq_sum (A := A) (O := O) B n ξ,
      infiniteRealizedCumulativeSeparationProcess_eq_sum (A := A) (O := O) B n ζ]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact infiniteRealizedBhattacharyyaSeparationProcess_eq_of_prefix_eq_of_lt
      (A := A) (O := O) B (Finset.mem_range.mp hi) hEq
  change infiniteRealizedCumulativeSeparationProcess B n ξ ∈ s ↔
    infiniteRealizedCumulativeSeparationProcess B n ζ ∈ s
  rw [hProc]

/--
The cumulative observer-fiber Bhattacharyya separation process is adapted to the
canonical infinite-prefix filtration.
-/
theorem infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess_adapted
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    AdaptedToInfinitePrefixFiltration (A := A) (O := O)
      (U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar) := by
  simpa [infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess,
    infiniteRealizedObserverFiberBhattacharyyaSeparationProcess,
    infiniteRealizedCumulativeSeparationProcess] using
    infiniteRealizedCumulativeSeparationProcess_adapted (A := A) (O := O)
      (U.observerFiberStepBhattacharyyaScore π ω pstar)

/-- The infinite-stream Hellinger envelope is adapted to the canonical prefix filtration. -/
theorem infiniteRealizedHellingerEnvelopeProcess_adapted
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O) :
    AdaptedToInfinitePrefixFiltration (A := A) (O := O)
      (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B) := by
  intro n s ξ ζ hEq
  have hResidual :
      U.infiniteRealizedResidualOddsProcess π ω pstar n ξ =
        U.infiniteRealizedResidualOddsProcess π ω pstar n ζ := by
    simp [infiniteRealizedResidualOddsProcess, infiniteResidualObserverFiberProcess, hEq]
  have hSeparation :
      infiniteRealizedCumulativeSeparationProcess B n ξ =
        infiniteRealizedCumulativeSeparationProcess B n ζ :=
    eq_of_adaptedToInfinitePrefixFiltration (A := A) (O := O)
      (infiniteRealizedCumulativeSeparationProcess_adapted (A := A) (O := O) B) hEq
  have hProc :
      U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ξ =
        U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ζ := by
    simp [infiniteRealizedHellingerEnvelopeProcess, hellingerEnvelopeProcess,
      hResidual, hSeparation]
  change U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ξ ∈ s ↔
    U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ζ ∈ s
  rw [hProc]

/--
The canonical observer-fiber Hellinger envelope is adapted to the canonical
infinite-prefix filtration.
-/
theorem infiniteRealizedObserverFiberHellingerEnvelopeProcess_adapted
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    AdaptedToInfinitePrefixFiltration (A := A) (O := O)
      (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar) := by
  simpa [infiniteRealizedObserverFiberHellingerEnvelopeProcess,
    infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess,
    infiniteRealizedHellingerEnvelopeProcess] using
    U.infiniteRealizedHellingerEnvelopeProcess_adapted π ω pstar
      (U.observerFiberStepBhattacharyyaScore π ω pstar)

/--
The infinite-stream Hellinger envelope is strongly adapted to the Mathlib prefix
filtration.
-/
theorem infiniteRealizedHellingerEnvelopeProcess_stronglyAdapted_prefixFiltration
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O) :
    StronglyAdapted (infinitePrefixMathlibFiltration (A := A) (O := O))
      (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B) :=
  stronglyAdapted_of_adaptedToInfinitePrefixFiltration_real (A := A) (O := O)
    (U.infiniteRealizedHellingerEnvelopeProcess_adapted π ω pstar B)

/--
The observer-fiber Hellinger envelope is strongly adapted to the Mathlib prefix
filtration.
-/
theorem infiniteRealizedObserverFiberHellingerEnvelopeProcess_stronglyAdapted_prefixFiltration
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    StronglyAdapted (infinitePrefixMathlibFiltration (A := A) (O := O))
      (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar) :=
  stronglyAdapted_of_adaptedToInfinitePrefixFiltration_real (A := A) (O := O)
    (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess_adapted π ω pstar)

theorem infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess_stronglyAdapted_prefixFiltration
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    StronglyAdapted (infinitePrefixMathlibFiltration (A := A) (O := O))
      (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
        π penv ω pstar) := by
  simpa [infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
    infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
    infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess,
    infiniteRealizedHellingerEnvelopeProcess] using
    U.infiniteRealizedHellingerEnvelopeProcess_stronglyAdapted_prefixFiltration
      π ω pstar (U.observerFiberTrueLawStepHellingerScore π penv ω pstar)

omit [Encodable A] [Encodable O] in
theorem infiniteRealizedCumulativeSeparationProcess_succ
    (B : StepBhattacharyyaScore A O)
    (n : Nat) (ξ : InfiniteTrajectory A O) :
    infiniteRealizedCumulativeSeparationProcess B (n + 1) ξ =
      infiniteRealizedCumulativeSeparationProcess B n ξ +
        infiniteRealizedBhattacharyyaSeparationProcess B n ξ := by
  simp [infiniteRealizedCumulativeSeparationProcess, cumulativeSeparationProcess,
    Finset.sum_range_succ]

/--
Prefix-factor shape of the infinite Hellinger envelope: on any prefix that is
actually realized by some infinite stream, the canonical prefix factor is the
closed-form envelope at that prefix.
-/
theorem infiniteRealizedHellingerEnvelopeProcess_prefixFactor_shape
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O)
    (n : Nat) (h : CountHist A O)
    (hEx : ∃ ξ : InfiniteTrajectory A O,
      infiniteHistoryPrefix (A := A) (O := O) ξ n = h) :
    infinitePrefixFactor (A := A) (O := O) n
        (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) h =
      Real.exp
          (infinitePrefixFactor (A := A) (O := O) n
            (infiniteRealizedCumulativeSeparationProcess B n) h) *
        Real.sqrt
          ((U.residualObserverFiberPosteriorOdds π n h ω pstar).toReal) := by
  rcases hEx with ⟨ξ, hξ⟩
  have hEnvFactor :
      infinitePrefixFactor (A := A) (O := O) n
          (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) h =
        U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ξ := by
    exact infinitePrefixFactor_eq_of_prefix (A := A) (O := O)
      (U.infiniteRealizedHellingerEnvelopeProcess_adapted π ω pstar B n) hξ
  have hSepFactor :
      infinitePrefixFactor (A := A) (O := O) n
          (infiniteRealizedCumulativeSeparationProcess B n) h =
        infiniteRealizedCumulativeSeparationProcess B n ξ := by
    exact infinitePrefixFactor_eq_of_prefix (A := A) (O := O)
      (infiniteRealizedCumulativeSeparationProcess_adapted (A := A) (O := O) B n) hξ
  calc
    infinitePrefixFactor (A := A) (O := O) n
        (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) h
        = U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ξ := hEnvFactor
    _ =
        Real.exp (infiniteRealizedCumulativeSeparationProcess B n ξ) *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π n h ω pstar).toReal) := by
          simp [infiniteRealizedHellingerEnvelopeProcess, hellingerEnvelopeProcess,
            infiniteRealizedResidualOddsProcess, infiniteResidualObserverFiberProcess, hξ]
    _ =
        Real.exp
            (infinitePrefixFactor (A := A) (O := O) n
              (infiniteRealizedCumulativeSeparationProcess B n) h) *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π n h ω pstar).toReal) := by
          rw [hSepFactor]

theorem infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess_prefixFactor_shape
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat) (h : CountHist A O)
    (hEx : ∃ ξ : InfiniteTrajectory A O,
      infiniteHistoryPrefix (A := A) (O := O) ξ n = h) :
    infinitePrefixFactor (A := A) (O := O) n
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
          π penv ω pstar n) h =
      Real.exp
          (infinitePrefixFactor (A := A) (O := O) n
            (U.infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
              π penv ω pstar n) h) *
        Real.sqrt
          ((U.residualObserverFiberPosteriorOdds π n h ω pstar).toReal) := by
  simpa [infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
    infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
    infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess,
    infiniteRealizedHellingerEnvelopeProcess] using
    infiniteRealizedHellingerEnvelopeProcess_prefixFactor_shape
      (A := A) (O := O) U
      π ω pstar (U.observerFiberTrueLawStepHellingerScore π penv ω pstar)
      n h hEx

/--
Successor-prefix shape of the infinite Hellinger envelope. Extending a length
`n` prefix by event `e` multiplies the prefix envelope by the one-step
exponential score and updates the residual odds to the appended prefix.
-/
theorem infiniteRealizedHellingerEnvelopeProcess_prefixFactor_succ_shape
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O)
    (n : Nat) (h : CountHist A O) (e : HistEvent A O)
    (hLen : h.length = n) :
    infinitePrefixFactor (A := A) (O := O) (n + 1)
        (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B (n + 1))
        (appendEvent h e) =
      Real.exp
          (infinitePrefixFactor (A := A) (O := O) n
            (infiniteRealizedCumulativeSeparationProcess B n) h) *
        Real.exp (B n h e.1) *
        Real.sqrt
          ((U.residualObserverFiberPosteriorOdds π (n + 1)
            (appendEvent h e) ω pstar).toReal) := by
  let ζ : InfiniteTrajectory A O :=
    infiniteTrajectoryOfPrefixWithTail (A := A) (O := O) (appendEvent h e) e
  have hζn : infiniteHistoryPrefix (A := A) (O := O) ζ n = h := by
    have hcurrent :=
      infiniteHistoryPrefix_ofPrefixWithTail_appendEvent_current
        (A := A) (O := O) h e e
    simpa [ζ, hLen] using hcurrent
  have hζsucc :
      infiniteHistoryPrefix (A := A) (O := O) ζ (n + 1) = appendEvent h e := by
    have hfull :=
      infiniteHistoryPrefix_ofPrefixWithTail
        (A := A) (O := O) (appendEvent h e) e
    have hLenApp : (appendEvent h e).length = n + 1 := by
      simp [appendEvent_length, hLen]
    simpa [ζ, hLenApp] using hfull
  have hEvent :
      (infiniteRealizedAction ζ n, infiniteRealizedObservation ζ n) = e := by
    have hAppend :
        appendEvent h e =
          appendEvent h (infiniteRealizedAction ζ n, infiniteRealizedObservation ζ n) := by
      rw [← hζsucc, infiniteHistoryPrefix_succ_eq_appendEvent_realized, hζn]
    exact ((appendEvent_eq_appendEvent_iff (A := A) (O := O)).1 hAppend).2.symm
  have hAct : infiniteRealizedAction ζ n = e.1 := by
    exact congrArg Prod.fst hEvent
  have hStep :
      infiniteRealizedBhattacharyyaSeparationProcess B n ζ = B n h e.1 := by
    simp [infiniteRealizedBhattacharyyaSeparationProcess, hζn, hAct]
  have hCumSucc :
      infiniteRealizedCumulativeSeparationProcess B (n + 1) ζ =
        infiniteRealizedCumulativeSeparationProcess B n ζ + B n h e.1 := by
    rw [infiniteRealizedCumulativeSeparationProcess_succ]
    simp [hStep]
  have hEnvFactor :
      infinitePrefixFactor (A := A) (O := O) (n + 1)
          (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B (n + 1))
          (appendEvent h e) =
        U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B (n + 1) ζ := by
    exact infinitePrefixFactor_eq_of_prefix (A := A) (O := O)
      (U.infiniteRealizedHellingerEnvelopeProcess_adapted π ω pstar B (n + 1)) hζsucc
  have hSepFactor :
      infinitePrefixFactor (A := A) (O := O) n
          (infiniteRealizedCumulativeSeparationProcess B n) h =
        infiniteRealizedCumulativeSeparationProcess B n ζ := by
    exact infinitePrefixFactor_eq_of_prefix (A := A) (O := O)
      (infiniteRealizedCumulativeSeparationProcess_adapted (A := A) (O := O) B n) hζn
  calc
    infinitePrefixFactor (A := A) (O := O) (n + 1)
        (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B (n + 1))
        (appendEvent h e)
        = U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B (n + 1) ζ := hEnvFactor
    _ =
        Real.exp (infiniteRealizedCumulativeSeparationProcess B (n + 1) ζ) *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π (n + 1)
              (appendEvent h e) ω pstar).toReal) := by
          simp [infiniteRealizedHellingerEnvelopeProcess, hellingerEnvelopeProcess,
            infiniteRealizedResidualOddsProcess, infiniteResidualObserverFiberProcess, hζsucc]
    _ =
        Real.exp (infiniteRealizedCumulativeSeparationProcess B n ζ + B n h e.1) *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π (n + 1)
              (appendEvent h e) ω pstar).toReal) := by
          rw [hCumSucc]
    _ =
        Real.exp (infiniteRealizedCumulativeSeparationProcess B n ζ) *
          Real.exp (B n h e.1) *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π (n + 1)
              (appendEvent h e) ω pstar).toReal) := by
          rw [Real.exp_add]
    _ =
        Real.exp
            (infinitePrefixFactor (A := A) (O := O) n
              (infiniteRealizedCumulativeSeparationProcess B n) h) *
          Real.exp (B n h e.1) *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π (n + 1)
              (appendEvent h e) ω pstar).toReal) := by
          rw [hSepFactor]

theorem infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess_prefixFactor_succ_shape
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat) (h : CountHist A O) (a : A) (o : O)
    (hLen : h.length = n) :
    infinitePrefixFactor (A := A) (O := O) (n + 1)
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
          π penv ω pstar (n + 1))
        (appendEvent h (a, o)) =
      Real.exp
          (infinitePrefixFactor (A := A) (O := O) n
            (U.infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
              π penv ω pstar n) h) *
        Real.exp
          (U.observerFiberTrueLawHellingerScore π penv n h a ω pstar) *
        Real.sqrt
          ((U.residualObserverFiberPosteriorOdds π (n + 1)
            (appendEvent h (a, o)) ω pstar).toReal) := by
  simpa [infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
    infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
    infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess,
    infiniteRealizedHellingerEnvelopeProcess,
    observerFiberTrueLawStepHellingerScore] using
    infiniteRealizedHellingerEnvelopeProcess_prefixFactor_succ_shape
      (A := A) (O := O) U
      π ω pstar (U.observerFiberTrueLawStepHellingerScore π penv ω pstar)
      n h (a, o) hLen

set_option maxHeartbeats 800000

/--
Finite-prefix kernel identity for the true-law Hellinger envelope, assuming the
prefix representative has the expected one-step exponential shape.

This is the local bridge from the fixed-action Bayes/Hellinger identity to the
`hPrefixStep` input used by the raw Ionescu martingale theorem. The proof
unpacks `ionescuStepKernel` into the policy/environment action-observation
average, applies the fixed-action normalization on supported actions, and uses
zero policy mass for unsupported actions.
-/
theorem infiniteRealizedObserverFiberTrueLawHellinger_prefix_kernel_integral_of_step_shape
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat)
    (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
    (E : ℝ)
    (hIntStep :
      Integrable
        (fun e : HistEvent A O =>
          infinitePrefixFactor (A := A) (O := O) (n + 1)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar (n + 1))
            (ionescuIicPrefix (A := A) (O := O) (n + 1)
              (ionescuIicSuccExtend (A := A) (O := O) n y e)))
        (ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y))
    (hCurr :
      infinitePrefixFactor (A := A) (O := O) n
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar n)
          (ionescuIicPrefix (A := A) (O := O) n y) =
        E *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π n
              (ionescuIicPrefix (A := A) (O := O) n y) ω pstar).toReal))
    (hSucc :
      ∀ a o,
        infinitePrefixFactor (A := A) (O := O) (n + 1)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar (n + 1))
            (appendEvent (ionescuIicPrefix (A := A) (O := O) n y) (a, o)) =
          E *
            Real.exp
              (U.observerFiberTrueLawHellingerScore π penv n
                (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar) *
            Real.sqrt
              ((U.residualObserverFiberPosteriorOdds π (n + 1)
                (appendEvent (ionescuIicPrefix (A := A) (O := O) n y) (a, o))
                ω pstar).toReal))
    (hClass0 :
      U.observerFiberPosteriorWeight π n
        (ionescuIicPrefix (A := A) (O := O) n y) ω pstar ≠ 0)
    (hClassTop :
      U.observerFiberPosteriorWeight π n
        (ionescuIicPrefix (A := A) (O := O) n y) ω pstar ≠ ⊤)
    (hComp0 :
      U.observerFiberComplementWeight π n
        (ionescuIicPrefix (A := A) (O := O) n y) ω pstar ≠ 0)
    (hCompTop :
      U.observerFiberComplementWeight π n
        (ionescuIicPrefix (A := A) (O := O) n y) ω pstar ≠ ⊤)
    (hPred :
      ∀ a,
        π (ionescuIicPrefix (A := A) (O := O) n y) a ≠ 0 →
          ∀ o,
            U.programSemantics penv
                (ionescuIicPrefix (A := A) (O := O) n y) a o ≠ 0 →
              U.observerFiberPredictiveWeight π n
                  (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar o ≠ 0 ∧
              U.observerFiberPredictiveWeight π n
                  (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar o ≠ ⊤)
    (hAff :
      ∀ a,
        π (ionescuIicPrefix (A := A) (O := O) n y) a ≠ 0 →
          0 <
            U.observerFiberTrueLawHellingerAffinity π penv n
              (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar) :
    infinitePrefixFactor (A := A) (O := O) n
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
          π penv ω pstar n)
        (ionescuIicPrefix (A := A) (O := O) n y) =
      ∫ e,
        infinitePrefixFactor (A := A) (O := O) (n + 1)
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar (n + 1))
          (ionescuIicPrefix (A := A) (O := O) (n + 1)
            (ionescuIicSuccExtend (A := A) (O := O) n y e))
        ∂(ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y) := by
  let h := ionescuIicPrefix (A := A) (O := O) n y
  let Y :=
    U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar
  let f : HistEvent A O → ℝ := fun e =>
    infinitePrefixFactor (A := A) (O := O) (n + 1) (Y (n + 1))
      (ionescuIicPrefix (A := A) (O := O) (n + 1)
        (ionescuIicSuccExtend (A := A) (O := O) n y e))
  have hIntegral :
      ∫ e, f e
        ∂(ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y) =
        ∑' a : A, ∑' o : O,
          (π h a).toReal *
            ((U.programSemantics penv h a o).toReal * f (a, o)) := by
    exact integral_ionescuStepKernel_eq_tsum_action_observation_of_integrable
      (A := A) (O := O) π (U.programSemantics penv) n y f hIntStep
  have hAvg :=
    U.observerFiberTrueLawHellinger_actionObservation_tsum_normalized
      π penv n h ω pstar E
      (by simpa [h] using hClass0)
      (by simpa [h] using hClassTop)
      (by simpa [h] using hComp0)
      (by simpa [h] using hCompTop)
      (by simpa [h] using hPred)
      (by simpa [h] using hAff)
  have hTsumShape :
      (∑' a : A, ∑' o : O,
          (π h a).toReal *
            ((U.programSemantics penv h a o).toReal * f (a, o))) =
        (∑' a : A, ∑' o : O,
          (π h a).toReal *
            ((U.programSemantics penv h a o).toReal *
              (E *
                Real.exp (U.observerFiberTrueLawHellingerScore π penv n h a ω pstar) *
                Real.sqrt
                  ((U.residualObserverFiberPosteriorOdds π (n + 1)
                    (appendEvent h (a, o)) ω pstar).toReal)))) := by
    apply tsum_congr
    intro a
    apply tsum_congr
    intro o
    have hf :
        f (a, o) =
          E *
            Real.exp (U.observerFiberTrueLawHellingerScore π penv n h a ω pstar) *
            Real.sqrt
              ((U.residualObserverFiberPosteriorOdds π (n + 1)
                (appendEvent h (a, o)) ω pstar).toReal) := by
      simpa [f, h, Y, ionescuIicPrefix_succExtend] using hSucc a o
    rw [hf]
  calc
    infinitePrefixFactor (A := A) (O := O) n (Y n) h
        = E *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π n h ω pstar).toReal) := by
            simpa [Y, h] using hCurr
    _ =
        ∑' a : A, ∑' o : O,
          (π h a).toReal *
            ((U.programSemantics penv h a o).toReal *
              (E *
                Real.exp (U.observerFiberTrueLawHellingerScore π penv n h a ω pstar) *
                Real.sqrt
                  ((U.residualObserverFiberPosteriorOdds π (n + 1)
                    (appendEvent h (a, o)) ω pstar).toReal))) := by
            simpa [h] using hAvg.symm
    _ =
        ∑' a : A, ∑' o : O,
          (π h a).toReal *
            ((U.programSemantics penv h a o).toReal * f (a, o)) := by
            exact hTsumShape.symm
    _ =
        ∫ e, f e
          ∂(ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y) := by
            exact hIntegral.symm

/--
Finite-prefix kernel identity for the true-law Hellinger envelope with the
envelope shape discharged internally.

Compared with `..._of_step_shape`, this theorem no longer takes the current
and successor envelope-shape equations as hypotheses. They are derived from the
definition of the exponential Hellinger envelope, the cumulative one-step score
process, and the canonical prefix factor.
-/
theorem infiniteRealizedObserverFiberTrueLawHellinger_prefix_kernel_integral
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (n : Nat)
    (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
    (hIntStep :
      Integrable
        (fun e : HistEvent A O =>
          infinitePrefixFactor (A := A) (O := O) (n + 1)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar (n + 1))
            (ionescuIicPrefix (A := A) (O := O) (n + 1)
              (ionescuIicSuccExtend (A := A) (O := O) n y e)))
        (ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y))
    (hClass0 :
      U.observerFiberPosteriorWeight π n
        (ionescuIicPrefix (A := A) (O := O) n y) ω pstar ≠ 0)
    (hClassTop :
      U.observerFiberPosteriorWeight π n
        (ionescuIicPrefix (A := A) (O := O) n y) ω pstar ≠ ⊤)
    (hComp0 :
      U.observerFiberComplementWeight π n
        (ionescuIicPrefix (A := A) (O := O) n y) ω pstar ≠ 0)
    (hCompTop :
      U.observerFiberComplementWeight π n
        (ionescuIicPrefix (A := A) (O := O) n y) ω pstar ≠ ⊤)
    (hPred :
      ∀ a,
        π (ionescuIicPrefix (A := A) (O := O) n y) a ≠ 0 →
          ∀ o,
            U.programSemantics penv
                (ionescuIicPrefix (A := A) (O := O) n y) a o ≠ 0 →
              U.observerFiberPredictiveWeight π n
                  (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar o ≠ 0 ∧
              U.observerFiberPredictiveWeight π n
                  (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar o ≠ ⊤)
    (hAff :
      ∀ a,
        π (ionescuIicPrefix (A := A) (O := O) n y) a ≠ 0 →
          0 <
            U.observerFiberTrueLawHellingerAffinity π penv n
              (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar) :
    infinitePrefixFactor (A := A) (O := O) n
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
          π penv ω pstar n)
        (ionescuIicPrefix (A := A) (O := O) n y) =
      ∫ e,
        infinitePrefixFactor (A := A) (O := O) (n + 1)
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar (n + 1))
          (ionescuIicPrefix (A := A) (O := O) (n + 1)
            (ionescuIicSuccExtend (A := A) (O := O) n y e))
        ∂(ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y) := by
  let h := ionescuIicPrefix (A := A) (O := O) n y
  let S :=
    U.infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
      π penv ω pstar
  let E :=
    Real.exp
      (infinitePrefixFactor (A := A) (O := O) n (S n) h)
  have hLen : h.length = n := by
    simpa [h] using ionescuIicPrefix_length (A := A) (O := O) n y
  have hExCurr :
      ∃ ξ : InfiniteTrajectory A O,
        infiniteHistoryPrefix (A := A) (O := O) ξ n = h := by
    let a0 : A := (π h).support_nonempty.some
    let o0 : O := (U.programSemantics penv h a0).support_nonempty.some
    let tail : HistEvent A O := (a0, o0)
    refine ⟨infiniteTrajectoryOfPrefixWithTail (A := A) (O := O) h tail, ?_⟩
    have hPrefix :=
      infiniteHistoryPrefix_ofPrefixWithTail (A := A) (O := O) h tail
    simpa [hLen] using hPrefix
  have hCurr :
      infinitePrefixFactor (A := A) (O := O) n
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar n)
          h =
        E *
          Real.sqrt
            ((U.residualObserverFiberPosteriorOdds π n h ω pstar).toReal) := by
    simpa [E, S] using
      infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess_prefixFactor_shape
        (A := A) (O := O) U π penv ω pstar n h hExCurr
  have hSucc :
      ∀ a o,
        infinitePrefixFactor (A := A) (O := O) (n + 1)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar (n + 1))
            (appendEvent h (a, o)) =
          E *
            Real.exp
              (U.observerFiberTrueLawHellingerScore π penv n h a ω pstar) *
            Real.sqrt
              ((U.residualObserverFiberPosteriorOdds π (n + 1)
                (appendEvent h (a, o)) ω pstar).toReal) := by
    intro a o
    simpa [E, S] using
      infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess_prefixFactor_succ_shape
        (A := A) (O := O) U π penv ω pstar n h a o hLen
  exact
    infiniteRealizedObserverFiberTrueLawHellinger_prefix_kernel_integral_of_step_shape
      (A := A) (O := O) U π penv ω pstar n y E
      hIntStep
      (by simpa [h] using hCurr)
      (by
        intro a o
        simpa [h] using hSucc a o)
      hClass0 hClassTop hComp0 hCompTop hPred hAff

/--
Local per-prefix hypotheses needed to derive the true-law Hellinger
`ionescuStepKernel` identity everywhere.

This package is intentionally only the remaining analytic/support surface:
summability is derived from integrability, top-finiteness is derived from a
single global universal-weight mass bound, and zero denominators are derived
from explicit support witnesses. The envelope shape itself is no longer a
hypothesis, and the action-observation averaging is proved from
`ionescuStepKernel`.
-/
structure HasTrueLawHellingerPrefixKernelObligations
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : Prop where
  integrable_step :
    ∀ n
      (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i),
      Integrable
        (fun e : HistEvent A O =>
          infinitePrefixFactor (A := A) (O := O) (n + 1)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar (n + 1))
            (ionescuIicPrefix (A := A) (O := O) (n + 1)
              (ionescuIicSuccExtend (A := A) (O := O) n y e)))
        (ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y)
  posteriorSupportWitness :
    ∀ n
      (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i),
      ∃ p : U.Program,
        U.observerFiber ω pstar p ∧
          U.likelihood π n (ionescuIicPrefix (A := A) (O := O) n y) p ≠ 0
  universalWeightMass_ne_top :
    (∑' p : U.Program, U.universalWeight p) ≠ ⊤
  complementSupportWitness :
    ∀ n
      (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i),
      ∃ p : U.Program,
        ¬ U.observerFiber ω pstar p ∧
          U.likelihood π n (ionescuIicPrefix (A := A) (O := O) n y) p ≠ 0
  predictiveSupportWitness :
    ∀ n
      (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
      (a : A),
      π (ionescuIicPrefix (A := A) (O := O) n y) a ≠ 0 →
        ∀ o,
          U.programSemantics penv
              (ionescuIicPrefix (A := A) (O := O) n y) a o ≠ 0 →
            ∃ p : U.Program,
              U.observerFiber ω pstar p ∧
                U.likelihood π n
                  (ionescuIicPrefix (A := A) (O := O) n y) p ≠ 0 ∧
                U.programSemantics p
                  (ionescuIicPrefix (A := A) (O := O) n y) a o ≠ 0
  trueLawHellingerAffinity_pos :
    ∀ n
      (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i)
      (a : A),
      π (ionescuIicPrefix (A := A) (O := O) n y) a ≠ 0 →
        0 <
          U.observerFiberTrueLawHellingerAffinity π penv n
            (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar

theorem infiniteRealizedObserverFiberTrueLawHellinger_prefix_kernel_integral_of_obligations
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hObligations :
      U.HasTrueLawHellingerPrefixKernelObligations π penv ω pstar) :
    ∀ n (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i),
      infinitePrefixFactor (A := A) (O := O) n
          (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar n)
          (ionescuIicPrefix (A := A) (O := O) n y) =
        ∫ e,
          infinitePrefixFactor (A := A) (O := O) (n + 1)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar (n + 1))
            (ionescuIicPrefix (A := A) (O := O) (n + 1)
              (ionescuIicSuccExtend (A := A) (O := O) n y e))
          ∂(ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y) := by
  intro n y
  exact
    infiniteRealizedObserverFiberTrueLawHellinger_prefix_kernel_integral
      (A := A) (O := O) U π penv ω pstar n y
      (hObligations.integrable_step n y)
      (by
        rcases hObligations.posteriorSupportWitness n y with ⟨p, hFiber, hLik⟩
        exact
          U.observerFiberPosteriorWeight_ne_zero_of_program_likelihood_ne_zero
            π n (ionescuIicPrefix (A := A) (O := O) n y) ω pstar p hFiber hLik)
      (U.observerFiberPosteriorWeight_ne_top_of_posteriorTotalWeight_ne_top
        π n (ionescuIicPrefix (A := A) (O := O) n y) ω pstar
        (U.posteriorTotalWeight_ne_top_of_universalWeightMass_ne_top
          π n (ionescuIicPrefix (A := A) (O := O) n y)
          hObligations.universalWeightMass_ne_top))
      (by
        rcases hObligations.complementSupportWitness n y with ⟨p, hNotFiber, hLik⟩
        exact
          U.observerFiberComplementWeight_ne_zero_of_program_likelihood_ne_zero
            π n (ionescuIicPrefix (A := A) (O := O) n y) ω pstar p hNotFiber hLik)
      (U.observerFiberComplementWeight_ne_top_of_posteriorTotalWeight_ne_top
        π n (ionescuIicPrefix (A := A) (O := O) n y) ω pstar
        (U.posteriorTotalWeight_ne_top_of_universalWeightMass_ne_top
          π n (ionescuIicPrefix (A := A) (O := O) n y)
          hObligations.universalWeightMass_ne_top))
      (by
        intro a ha o ho
        refine ⟨?_, ?_⟩
        · rcases hObligations.predictiveSupportWitness n y a ha o ho with
            ⟨p, hFiber, hLik, hObs⟩
          exact
            U.observerFiberPredictiveWeight_ne_zero_of_program_support
              π n (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar o
              p hFiber hLik hObs
        · exact
            U.observerFiberPredictiveWeight_ne_top_of_posteriorWeight_ne_top
              π n (ionescuIicPrefix (A := A) (O := O) n y) a ω pstar o
              (U.observerFiberPosteriorWeight_ne_top_of_posteriorTotalWeight_ne_top
                π n (ionescuIicPrefix (A := A) (O := O) n y) ω pstar
                (U.posteriorTotalWeight_ne_top_of_universalWeightMass_ne_top
                  π n (ionescuIicPrefix (A := A) (O := O) n y)
                  hObligations.universalWeightMass_ne_top)))
      (by
        intro a ha
        exact hObligations.trueLawHellingerAffinity_pos n y a ha)

/--
Raw Ionescu-coordinate martingale for the true-law Hellinger envelope from a
finite-prefix one-step kernel identity.

This theorem is the model-specific bridge from the local Bayes/Hellinger
calculation to the global raw martingale layer: the only remaining input is the
one-step identity on finite prefixes for the `infinitePrefixFactor` of the
true-law envelope. The martingale proof itself is discharged by the direct
`trajMeasure` composition-product constructor above, not by a public
conditional-expectation assumption.
-/
theorem infiniteRealizedObserverFiberTrueLawHellinger_rawIonescuMartingale_of_prefix_kernel_integral
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hIntegrable :
      ∀ n,
        Integrable
          (ionescuPullbackInfiniteProcess (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar) n)
          (ionescuTrajectoryMeasure (A := A) (O := O) π (U.programSemantics penv)))
    (hPrefixStep :
      ∀ n (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i),
        infinitePrefixFactor (A := A) (O := O) n
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar n)
            (ionescuIicPrefix (A := A) (O := O) n y) =
          ∫ e,
            infinitePrefixFactor (A := A) (O := O) (n + 1)
              (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar
                (n + 1))
              (ionescuIicPrefix (A := A) (O := O) (n + 1)
                (ionescuIicSuccExtend (A := A) (O := O) n y e))
            ∂(ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y)) :
    Martingale
      (ionescuPullbackInfiniteProcess (A := A) (O := O)
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar))
      (Filtration.piLE (X := ionescuTrajectoryState A O))
      (ionescuTrajectoryMeasure (A := A) (O := O) π (U.programSemantics penv)) := by
  let Y := U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar
  let V : (n : Nat) → ((i : Finset.Iic n) → ionescuTrajectoryState A O i) → ℝ :=
    fun n y => infinitePrefixFactor (A := A) (O := O) n (Y n)
      (ionescuIicPrefix (A := A) (O := O) n y)
  have hAdaptY : AdaptedToInfinitePrefixFiltration (A := A) (O := O) Y := by
    simpa [Y, infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
      infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
      infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess,
      infiniteRealizedHellingerEnvelopeProcess] using
      U.infiniteRealizedHellingerEnvelopeProcess_adapted π ω pstar
        (U.observerFiberTrueLawStepHellingerScore π penv ω pstar)
  have hFactor :
      ∀ n (x : (k : Nat) → ionescuTrajectoryState A O k),
        V n (Preorder.frestrictLe n x) =
          ionescuPullbackInfiniteProcess (A := A) (O := O) Y n x := by
    intro n x
    have hComp := infinitePrefixFactor_comp_eq (A := A) (O := O)
      (X := Y n) (t := n) (hAdaptY n)
      (ionescuStreamToInfiniteTrajectory (A := A) (O := O) x)
    simpa [V, ionescuPullbackInfiniteProcess,
      infiniteHistoryPrefix_ionescuStreamToInfiniteTrajectory (A := A) (O := O) x n,
      ionescuIicPrefix_frestrictLe (A := A) (O := O) x n] using hComp
  have hIntegrableV :
      ∀ n, Integrable
        (fun x : (k : Nat) → ionescuTrajectoryState A O k =>
          V n (Preorder.frestrictLe n x))
        (ionescuTrajectoryMeasure (A := A) (O := O) π (U.programSemantics penv)) := by
    intro n
    rw [integrable_congr (Filter.Eventually.of_forall (hFactor n))]
    simpa [Y] using hIntegrable n
  have hStepV :
      ∀ n (y : (i : Finset.Iic n) → ionescuTrajectoryState A O i),
        V n y =
          ∫ e, V (n + 1)
            (ionescuIicSuccExtend (A := A) (O := O) n y e)
            ∂(ionescuStepKernel (A := A) (O := O) π (U.programSemantics penv) n y) := by
    intro n y
    simpa [V, Y] using hPrefixStep n y
  have hMartV :=
    martingale_ionescuTrajectoryMeasure_of_prefix_kernel_integral
      (A := A) (O := O) π (U.programSemantics penv)
      (V := V) hIntegrableV hStepV
  have hProcEq :
      (fun n (x : (k : Nat) → ionescuTrajectoryState A O k) =>
        V n (Preorder.frestrictLe n x)) =
      ionescuPullbackInfiniteProcess (A := A) (O := O) Y := by
    funext n x
    exact hFactor n x
  simpa [hProcEq, Y] using hMartV

/--
Raw Ionescu-coordinate martingale with the all-prefix kernel identity derived
from the compact local true-law Hellinger obligation package.
-/
theorem infiniteRealizedObserverFiberTrueLawHellinger_rawIonescuMartingale_of_prefix_kernel_obligations
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (hIntegrable :
      ∀ n,
        Integrable
          (ionescuPullbackInfiniteProcess (A := A) (O := O)
            (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar) n)
          (ionescuTrajectoryMeasure (A := A) (O := O) π (U.programSemantics penv)))
    (hObligations :
      U.HasTrueLawHellingerPrefixKernelObligations π penv ω pstar) :
    Martingale
      (ionescuPullbackInfiniteProcess (A := A) (O := O)
        (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar))
      (Filtration.piLE (X := ionescuTrajectoryState A O))
      (ionescuTrajectoryMeasure (A := A) (O := O) π (U.programSemantics penv)) := by
  exact
    infiniteRealizedObserverFiberTrueLawHellinger_rawIonescuMartingale_of_prefix_kernel_integral
      (A := A) (O := O) U π penv ω pstar hIntegrable
      (infiniteRealizedObserverFiberTrueLawHellinger_prefix_kernel_integral_of_obligations
        (A := A) (O := O) U π penv ω pstar hObligations)

theorem infiniteRealizedHellingerEnvelopeProcess_martingale_of_condExp_succ
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    (hIntegrable :
      ∀ n, Integrable (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) μ)
    (hCondExp :
      ∀ n,
        U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n =ᵐ[μ]
          μ[U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B (n + 1) |
            infinitePrefixMathlibFiltration (A := A) (O := O) n]) :
    Martingale (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B)
      (infinitePrefixMathlibFiltration (A := A) (O := O)) μ := by
  exact martingale_nat
    (U.infiniteRealizedHellingerEnvelopeProcess_stronglyAdapted_prefixFiltration π ω pstar B)
    hIntegrable hCondExp

theorem infiniteRealizedObserverFiberHellingerEnvelopeProcess_martingale_of_condExp_succ
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    (hIntegrable :
      ∀ n, Integrable (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n) μ)
    (hCondExp :
      ∀ n,
        U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n =ᵐ[μ]
          μ[U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar (n + 1) |
            infinitePrefixMathlibFiltration (A := A) (O := O) n]) :
    Martingale (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar)
      (infinitePrefixMathlibFiltration (A := A) (O := O)) μ := by
  exact martingale_nat
    (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess_stronglyAdapted_prefixFiltration π ω pstar)
    hIntegrable hCondExp

theorem infiniteRealizedHellingerEnvelopeProcess_integrable_of_ae_enorm_bound
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    {C : ℝ≥0}
    (hBound :
      ∀ n, ∀ᵐ ξ ∂μ,
        ‖U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ξ‖ₑ ≤
          (C : ℝ≥0∞)) :
    ∀ n, Integrable (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) μ := by
  intro n
  have hStrong :
      StronglyMeasurable
        (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) :=
    (U.infiniteRealizedHellingerEnvelopeProcess_stronglyAdapted_prefixFiltration
      π ω pstar B n).mono
        ((infinitePrefixMathlibFiltration (A := A) (O := O)).le n)
  refine Integrable.of_bound hStrong.aestronglyMeasurable (C : ℝ) ?_
  filter_upwards [hBound n] with ξ hξ
  exact_mod_cast hξ

theorem infiniteRealizedObserverFiberHellingerEnvelopeProcess_integrable_of_ae_enorm_bound
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    {C : ℝ≥0}
    (hBound :
      ∀ n, ∀ᵐ ξ ∂μ,
        ‖U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n ξ‖ₑ ≤
          (C : ℝ≥0∞)) :
    ∀ n, Integrable (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n) μ := by
  intro n
  have hStrong :
      StronglyMeasurable
        (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n) :=
    (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess_stronglyAdapted_prefixFiltration
      π ω pstar n).mono
        ((infinitePrefixMathlibFiltration (A := A) (O := O)).le n)
  refine Integrable.of_bound hStrong.aestronglyMeasurable (C : ℝ) ?_
  filter_upwards [hBound n] with ξ hξ
  exact_mod_cast hξ

theorem infiniteRealizedObserverFiberHellingerEnvelopeProcess_martingale_of_condExp_succ_of_bound
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsFiniteMeasure μ]
    {C : ℝ≥0}
    (hBound :
      ∀ n, ∀ᵐ ξ ∂μ,
        ‖U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n ξ‖ₑ ≤
          (C : ℝ≥0∞))
    (hCondExp :
      ∀ n,
        U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n =ᵐ[μ]
          μ[U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar (n + 1) |
            infinitePrefixMathlibFiltration (A := A) (O := O) n]) :
    Martingale (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar)
      (infinitePrefixMathlibFiltration (A := A) (O := O)) μ := by
  exact U.infiniteRealizedObserverFiberHellingerEnvelopeProcess_martingale_of_condExp_succ
    π ω pstar
    (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess_integrable_of_ae_enorm_bound
      π ω pstar hBound)
    hCondExp

theorem infiniteRealizedHellingerEnvelopeProcess_l1_bounded_of_ae_enorm_bound
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (B : StepBhattacharyyaScore A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsProbabilityMeasure μ]
    {C : ℝ≥0∞}
    (hBound :
      ∀ n, ∀ᵐ ξ ∂μ,
        ‖U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ξ‖ₑ ≤ C) :
    ∀ n,
      eLpNorm (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) 1 μ ≤ C := by
  intro n
  have h := eLpNorm_le_of_ae_enorm_bound
    (p := (1 : ℝ≥0∞)) (μ := μ) (hBound n)
  simpa using h

theorem infiniteRealizedObserverFiberHellingerEnvelopeProcess_l1_bounded_of_ae_enorm_bound
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsProbabilityMeasure μ]
    {C : ℝ≥0∞}
    (hBound :
      ∀ n, ∀ᵐ ξ ∂μ,
        ‖U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n ξ‖ₑ ≤ C) :
    ∀ n,
      eLpNorm (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n) 1 μ ≤ C := by
  intro n
  have h := eLpNorm_le_of_ae_enorm_bound
    (p := (1 : ℝ≥0∞)) (μ := μ) (hBound n)
  simpa using h

theorem infiniteRealizedObserverFiberHellingerConvergenceSpine_of_condExp_succ
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsProbabilityMeasure μ]
    {C : ℝ≥0}
    (hCondExp :
      ∀ n,
        U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n =ᵐ[μ]
          μ[U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar (n + 1) |
            infinitePrefixMathlibFiltration (A := A) (O := O) n])
    (hBound :
      ∀ n, ∀ᵐ ξ ∂μ,
        ‖U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar n ξ‖ₑ ≤
          (C : ℝ≥0∞))
    (hS_diverges :
      ∀ᵐ ξ ∂μ,
        Tendsto
          (fun n =>
            U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess
              π ω pstar n ξ)
          atTop atTop) :
    HellingerConvergenceSpine μ
      (infinitePrefixMathlibFiltration (A := A) (O := O))
      (U.infiniteRealizedResidualOddsProcess π ω pstar)
      (U.infiniteRealizedObserverFiberHellingerEnvelopeProcess π ω pstar)
      (U.infiniteRealizedObserverFiberCumulativeBhattacharyyaSeparationProcess π ω pstar)
      C := by
  refine HellingerConvergenceSpine.of_processes
    (U.ae_infiniteRealizedResidualOddsProcess_nonneg π ω pstar)
    ?_ ?_ hS_diverges
  · exact U.infiniteRealizedObserverFiberHellingerEnvelopeProcess_martingale_of_condExp_succ_of_bound
      π ω pstar hBound hCondExp
  · exact U.infiniteRealizedObserverFiberHellingerEnvelopeProcess_l1_bounded_of_ae_enorm_bound
      π ω pstar hBound

/--
Construct the true-law Hellinger convergence spine from the true-law
conditional-expectation identity, envelope bound, true-law multiplier ceiling,
and realized policy support.
-/
theorem infiniteRealizedObserverFiberTrueLawHellingerConvergenceSpine_of_condExp_affinityCeiling
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O)
    (penv : U.Program)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    {μ : Measure (InfiniteTrajectory A O)} [IsProbabilityMeasure μ]
    {C : ℝ≥0} {κ : ℝ}
    (hCondExp :
      ∀ n,
        U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar n =ᵐ[μ]
          μ[U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
              π penv ω pstar (n + 1) |
            infinitePrefixMathlibFiltration (A := A) (O := O) n])
    (hBound :
      ∀ n, ∀ᵐ ξ ∂μ,
        ‖U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess
            π penv ω pstar n ξ‖ₑ ≤
          (C : ℝ≥0∞))
    (hCeiling :
      InfiniteHasObserverFiberTrueLawHellingerAffinityCeilingOnPolicySupport
        U π penv ω pstar μ κ)
    (hRealizedSupport : InfiniteHasRealizedPolicySupportAtAllTimes π μ) :
    HellingerConvergenceSpine μ
      (infinitePrefixMathlibFiltration (A := A) (O := O))
      (U.infiniteRealizedResidualOddsProcess π ω pstar)
      (U.infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess π penv ω pstar)
      (U.infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess
        π penv ω pstar)
      C := by
  let B := U.observerFiberTrueLawStepHellingerScore π penv ω pstar
  have hBoundGeneric :
      ∀ n, ∀ᵐ ξ ∂μ,
        ‖U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n ξ‖ₑ ≤
          (C : ℝ≥0∞) := by
    simpa [B, infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
      infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
      infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess,
      infiniteRealizedHellingerEnvelopeProcess]
      using hBound
  have hCondExpGeneric :
      ∀ n,
        U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n =ᵐ[μ]
          μ[U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B (n + 1) |
            infinitePrefixMathlibFiltration (A := A) (O := O) n] := by
    simpa [B, infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
      infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
      infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess,
      infiniteRealizedHellingerEnvelopeProcess]
      using hCondExp
  have hIntegrable :
      ∀ n, Integrable (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) μ :=
    U.infiniteRealizedHellingerEnvelopeProcess_integrable_of_ae_enorm_bound
      π ω pstar B hBoundGeneric
  have hM :
      Martingale (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B)
        (infinitePrefixMathlibFiltration (A := A) (O := O)) μ :=
    U.infiniteRealizedHellingerEnvelopeProcess_martingale_of_condExp_succ
      π ω pstar B hIntegrable hCondExpGeneric
  have hBdd :
      ∀ n,
        eLpNorm (U.infiniteRealizedHellingerEnvelopeProcess π ω pstar B n) 1 μ ≤
          (C : ℝ≥0∞) :=
    U.infiniteRealizedHellingerEnvelopeProcess_l1_bounded_of_ae_enorm_bound
      π ω pstar B hBoundGeneric
  simpa [B, infiniteRealizedObserverFiberTrueLawHellingerEnvelopeProcess,
    infiniteRealizedObserverFiberTrueLawCumulativeHellingerSeparationProcess,
    infiniteRealizedObserverFiberTrueLawHellingerSeparationProcess,
    infiniteRealizedHellingerEnvelopeProcess] using
    U.hellingerConvergenceSpine_of_infiniteObserverFiberTrueLawHellinger_affinityCeiling_policySupport
      π penv ω pstar hM hBdd hCeiling hRealizedSupport

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
          exact mul_le_mul_right (ih (Nat.le_of_succ_le hN)) _
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
