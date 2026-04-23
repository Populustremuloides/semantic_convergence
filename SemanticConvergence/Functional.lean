import Mathlib.InformationTheory.KullbackLeibler.KLFun
import SemanticConvergence.Hierarchy
import SemanticConvergence.ConcreteBelief
import SemanticConvergence.ConcreteSemantic
import SemanticConvergence.ConcreteFunctional

namespace SemanticConvergence

universe u v

noncomputable section CountablePaperFunctional

open Classical
open CountableConcrete
open CountableConcrete.CountablePrefixMachine
open InformationTheory

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]
[DecidableEq A] [BEq A] [LawfulBEq A]

/-- Convert a rational into `ℝ≥0∞` for the countable action-side penalties. -/
def ratToENNReal (q : Rat) : ENNReal :=
  ENNReal.ofReal q

/-- Finite-list sum of `ℝ≥0∞` weights. -/
def listSumENNReal {α : Type u} (xs : List α) (f : α → ENNReal) : ENNReal :=
  xs.foldr (fun x acc => f x + acc) 0

theorem listSumENNReal_nil {α : Type u} (f : α → ENNReal) :
    listSumENNReal [] f = 0 :=
  rfl

theorem listSumENNReal_cons {α : Type u} (x : α) (xs : List α) (f : α → ENNReal) :
    listSumENNReal (x :: xs) f = f x + listSumENNReal xs f :=
  rfl

theorem listSumENNReal_eq_zero_iff {α : Type u} (xs : List α) (f : α → ENNReal) :
    listSumENNReal xs f = 0 ↔ ∀ x, x ∈ xs → f x = 0 := by
  induction xs with
  | nil =>
      simp [listSumENNReal]
  | cons x xs ih =>
      constructor
      · intro h y hy
        have hsplit : f x = 0 ∧ listSumENNReal xs f = 0 := by
          simpa [listSumENNReal_cons] using (add_eq_zero.mp h)
        simp at hy
        rcases hy with rfl | hy
        · exact hsplit.1
        · exact (ih.mp hsplit.2) y hy
      · intro h
        have hx : f x = 0 := h x (by simp)
        have hxs : ∀ y, y ∈ xs → f y = 0 := by
          intro y hy
          exact h y (by simp [hy])
        have htail : listSumENNReal xs f = 0 := ih.mpr hxs
        simp [listSumENNReal_cons, hx, htail]

theorem listSumENNReal_ne_top {α : Type u} {xs : List α} {f : α → ENNReal}
    (hfin : ∀ x, x ∈ xs → f x ≠ ⊤) :
    listSumENNReal xs f ≠ ⊤ := by
  induction xs with
  | nil =>
      simp [listSumENNReal]
  | cons x xs ih =>
      rw [listSumENNReal_cons]
      rw [ENNReal.add_ne_top]
      exact ⟨hfin x (by simp), ih (fun y hy => hfin y (by simp [hy]))⟩

/-- Finite-list minimizer witness for `ℝ≥0∞`-valued objectives. -/
def MinimizesOnListENNReal {α : Type u} (xs : List α) (f : α → ENNReal) (x : α) : Prop :=
  x ∈ xs ∧ ∀ y, y ∈ xs → f x ≤ f y

theorem exists_minimizerOnListENNReal {α : Type u}
    (xs : List α) (f : α → ENNReal) (hxs : xs ≠ []) :
    ∃ x, MinimizesOnListENNReal xs f x := by
  induction xs with
  | nil =>
      contradiction
  | cons x xs ih =>
      by_cases htail : xs = []
      · refine ⟨x, ?_⟩
        constructor
        · simp
        · intro y hy
          simp [htail] at hy
          rcases hy with rfl
          exact le_rfl
      · rcases ih htail with ⟨x', hx'⟩
        by_cases hle : f x ≤ f x'
        · refine ⟨x, ?_⟩
          constructor
          · simp
          · intro y hy
            simp at hy
            rcases hy with rfl | hy
            · exact le_rfl
            · exact le_trans hle (hx'.2 y hy)
        · have hx'le : f x' ≤ f x := le_of_not_ge hle
          refine ⟨x', ?_⟩
          constructor
          · simp [hx'.1]
          · intro y hy
            simp at hy
            rcases hy with rfl | hy
            · exact hx'le
            · exact hx'.2 y hy

/-- Countable `argmin` on a nonempty finite list. -/
noncomputable def argminOnListENNReal {α : Type u}
    (xs : List α) (f : α → ENNReal) (hxs : xs ≠ []) : α :=
  Classical.choose (exists_minimizerOnListENNReal xs f hxs)

theorem argminOnListENNReal_spec {α : Type u}
    (xs : List α) (f : α → ENNReal) (hxs : xs ≠ []) :
    MinimizesOnListENNReal xs f (argminOnListENNReal xs f hxs) :=
  Classical.choose_spec (exists_minimizerOnListENNReal xs f hxs)

/-- Countable posterior-weight agreement on the enumerable machine domain. -/
def samePosteriorWeights
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) : Prop :=
  ∀ p, q p = U.posteriorWeight π t h p

/--
Pointwise generalized KL term against an unnormalized posterior weight. This is the scalar
`r * klFun (q / r)` with the standard `r = 0` convention and an infinite penalty for an
infinite proposed weight.
-/
def posteriorWeightKLDivergenceTerm (q r : ENNReal) : ENNReal :=
  if q = (⊤ : ENNReal) then
    (⊤ : ENNReal)
  else if r = 0 then
    if q = 0 then 0 else (⊤ : ENNReal)
  else
    r * ENNReal.ofReal (klFun ((q / r).toReal))

/-- Countable posterior weights are always finite. -/
theorem posteriorWeight_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (p : U.Program) :
    U.posteriorWeight π t h p ≠ (⊤ : ENNReal) := by
  unfold CountablePrefixMachine.posteriorWeight
    CountablePrefixMachine.universalWeight
    CountablePrefixMachine.likelihood
    codeWeightENNReal
  refine ENNReal.mul_ne_top ?_ ?_
  · simp
  · exact (CountableConcrete.histPMF π (U.programSemantics p) t).apply_ne_top h

/--
The generalized KL term vanishes exactly at equality whenever the reference weight is finite.
-/
theorem posteriorWeightKLDivergenceTerm_eq_zero_iff
    {q r : ENNReal} (hrTop : r ≠ (⊤ : ENNReal)) :
    posteriorWeightKLDivergenceTerm q r = 0 ↔ q = r := by
  by_cases hqTop : q = (⊤ : ENNReal)
  · subst hqTop
    have hTopEq : ¬ ((⊤ : ENNReal) = r) := by
      simpa [eq_comm] using hrTop
    simp [posteriorWeightKLDivergenceTerm, hTopEq]
  · by_cases hrZero : r = 0
    · subst hrZero
      by_cases hqZero : q = 0
      · simp [posteriorWeightKLDivergenceTerm, hqZero]
      · simp [posteriorWeightKLDivergenceTerm, hqTop, hqZero]
    · constructor
      · intro hZero
        have hMulZero :
            r * ENNReal.ofReal (klFun ((q / r).toReal)) = 0 := by
          simpa [posteriorWeightKLDivergenceTerm, hqTop, hrZero] using hZero
        have hTermZero :
            ENNReal.ofReal (klFun ((q / r).toReal)) = 0 := by
          rw [mul_eq_zero] at hMulZero
          exact hMulZero.resolve_left hrZero
        have hKlNonneg : 0 ≤ klFun ((q / r).toReal) :=
          klFun_nonneg ENNReal.toReal_nonneg
        have hKlZero : klFun ((q / r).toReal) = 0 := by
          exact le_antisymm (ENNReal.ofReal_eq_zero.mp hTermZero) hKlNonneg
        have hRatioReal : (q / r).toReal = 1 :=
          (klFun_eq_zero_iff ENNReal.toReal_nonneg).mp hKlZero
        have hRatio : q / r = 1 :=
          (ENNReal.toReal_eq_one_iff (q / r)).mp hRatioReal
        exact (ENNReal.div_eq_one_iff hrZero hrTop).mp hRatio
      · intro hqr
        subst q
        have hRatio : r / r = 1 :=
          (ENNReal.div_eq_one_iff hrZero hrTop).2 rfl
        calc
          posteriorWeightKLDivergenceTerm r r
              = r * ENNReal.ofReal (klFun ((r / r).toReal)) := by
                  simp [posteriorWeightKLDivergenceTerm, hrTop, hrZero]
          _ = r * 0 := by
                rw [hRatio, ENNReal.toReal_one, klFun_one, ENNReal.ofReal_zero]
          _ = 0 := by simp

/--
Countable algorithmic free energy as the generalized KL / I-divergence from the proposed
belief weights `q` to the unnormalized Bayes numerator `posteriorWeight`.
-/
def def_afe
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) : ENNReal :=
  ∑' p : U.Program, posteriorWeightKLDivergenceTerm (q p) (U.posteriorWeight π t h p)

theorem posteriorWeight_samePosteriorWeights
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) :
    samePosteriorWeights U π t h (fun p => U.posteriorWeight π t h p) := by
  intro p
  rfl

/--
Zero generalized KL against the posterior weights forces pointwise posterior-weight agreement.
-/
theorem samePosteriorWeights_of_def_afe_eq_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hZero : def_afe U π t h q = 0) :
    samePosteriorWeights U π t h q := by
  have hTerms :
      ∀ p : U.Program,
        posteriorWeightKLDivergenceTerm (q p) (U.posteriorWeight π t h p) = 0 := by
    exact ENNReal.tsum_eq_zero.mp (by simpa [def_afe] using hZero)
  intro p
  exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (posteriorWeight_ne_top U π t h p)).mp (hTerms p)

/-- Zero AFE is exactly posterior-weight agreement. -/
theorem def_afe_eq_zero_iff_samePosteriorWeights
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) :
    def_afe U π t h q = 0 ↔ samePosteriorWeights U π t h q := by
  constructor
  · exact samePosteriorWeights_of_def_afe_eq_zero U π t h q
  · intro hq
    rw [def_afe, ENNReal.tsum_eq_zero]
    intro p
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
        (posteriorWeight_ne_top U π t h p)).2 (hq p)

/-- Countable belief-side admissibility range. -/
def BeliefAdmissible (ω : Observer (CountableEncodedProgram A O)) : Prop :=
  behavioralObserver (A := A) (O := O) ≼ω ω

/-- Countable action-side admissibility range. -/
def ActionAdmissible (ω : Observer (CountableEncodedProgram A O)) : Prop :=
  ω ≼ω behavioralObserver (A := A) (O := O)

/-- Countable programs in the `ω`-fiber of `pstar`, viewed on the enumerable machine domain. -/
def goalDialedTarget
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    PredSet U.Program :=
  U.observerFiber ω pstar

/-- Countable observer fiber viewed directly on encoded programs. -/
def encodedObserverFiber
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    PredSet (CountableEncodedProgram A O) :=
  fun p => ω.view p = ω.view pstar

/-- Countable behavioral-fiber weight under the current posterior scaffold. -/
def behavioralFiberMass
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.observerFiberPosteriorWeight π t h (behavioralObserver (A := A) (O := O)) pstar

/-- Ratio of behavioral-fiber posterior weights for two targets. -/
def posteriorRatio
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (p₁ p₂ : CountableEncodedProgram A O) : ENNReal :=
  let num := behavioralFiberMass (A := A) (O := O) U π t h p₁
  let den := behavioralFiberMass (A := A) (O := O) U π t h p₂
  if den = 0 then 0 else num / den

/-- Countable goal-dialed convergence proxy. -/
def goalDialConverges
    (ω : Observer (CountableEncodedProgram A O))
    (_pstar : CountableEncodedProgram A O) : Prop :=
  BeliefAdmissible (A := A) (O := O) ω

/-- Finite-list reference weight induced by code-length prior on `ω`-classes. -/
def observerClassReferenceWeightOnTargets
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  listSumENNReal targets (fun p =>
    if ω.view p = ω.view pstar then
      CountableConcrete.CountablePrefixMachine.codeWeightENNReal p.code
    else 0)

theorem observerClassReferenceWeightOnTargets_ne_top
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    observerClassReferenceWeightOnTargets (A := A) (O := O) ω targets pstar ≠ ⊤ := by
  unfold observerClassReferenceWeightOnTargets
  refine listSumENNReal_ne_top ?_
  intro p hp
  by_cases hView : ω.view p = ω.view pstar
  · simp [hView, CountableConcrete.CountablePrefixMachine.codeWeightENNReal]
  · simp [hView]

/-- Finite-list class score entering the paper-facing countable two-observer functional. -/
def observerClassScore
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  min (1 : ENNReal) (U.semanticSeparation π t h ω pstar)

/--
Finite-list Gibbs weight on a target class: the target-list reference weight multiplied by
the exponentiated capped score.
-/
def observerClassGibbsWeightOnTargets
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  observerClassReferenceWeightOnTargets (A := A) (O := O) ω targets pstar *
    ENNReal.ofReal (Real.exp (observerClassScore U π t h ω pstar).toReal)

theorem observerClassGibbsWeightOnTargets_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) :
    observerClassGibbsWeightOnTargets U π t h ω targets pstar ≠ ⊤ := by
  unfold observerClassGibbsWeightOnTargets
  refine ENNReal.mul_ne_top ?_ ?_
  · exact observerClassReferenceWeightOnTargets_ne_top
      (A := A) (O := O) ω targets pstar
  · simp

/-- Agreement of two target-weight assignments on the designated finite target list. -/
def agreesWithOnTargets
    (targets : List (CountableEncodedProgram A O))
    (ν₁ ν₂ : CountableEncodedProgram A O → ENNReal) : Prop :=
  ∀ p, p ∈ targets → ν₁ p = ν₂ p

/-- Lean wrapper for `def:bhat-omega` on the countable functional stack. -/
def def_bhat_omega
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  observerClassScore U π t h ω pstar

/--
Lean wrapper for `def:raw-two-observer-functional` on the countable functional stack.

This is the per-target Gibbs-mismatch term entering the finite-list paper-facing
two-observer functional: the proposed class weight at `pstar` is compared against the
finite-list Gibbs weight built from the code-length reference mass and the capped
semantic score.
-/
def def_raw_two_observer_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (_ωB ωA : Observer (CountableEncodedProgram A O))
    (q : U.Program → ENNReal)
    (ν : CountableEncodedProgram A O → ENNReal)
    (targets : List (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  let _ := q
  posteriorWeightKLDivergenceTerm (ν pstar)
    (observerClassGibbsWeightOnTargets U π t h ωA targets pstar)

/--
Lean wrapper for `def:two-observer-functional` on the countable functional stack.

The belief-side term is the algorithmic free energy `def_afe`; the action-side term is
the finite-list Gibbs mismatch against the target-class weights induced by the code prior
and the capped semantic scores.
-/
def def_two_observer_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (q : U.Program → ENNReal)
    (ν : CountableEncodedProgram A O → ENNReal)
    (targets : List (CountableEncodedProgram A O)) : ENNReal :=
  def_afe U π t h q +
    listSumENNReal targets
      (fun pstar => def_raw_two_observer_functional U π t h ωB ωA q ν targets pstar)

/--
Countable kernel-score scaffold on the explicit finite target-action chart. On the current
countable substrate this reuses the capped target score uniformly across the action chart;
the joint class-action structure is carried by the kernel law itself.
-/
def kernelActionScoreOnTargets
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) (_a : A) : ENNReal :=
  observerClassScore U π t h ω pstar

/-- Reference mass on a finite target-action chart induced by `\bar w^{\omega_A} ⊗ \lambda`. -/
def countableKernelReferenceWeightOnTargets
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) : ENNReal :=
  observerClassReferenceWeightOnTargets (A := A) (O := O) ω targets pstar *
    ratToENNReal (refLaw.mass a)

theorem countableKernelReferenceWeightOnTargets_ne_top
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) :
    countableKernelReferenceWeightOnTargets (A := A) (O := O) ω targets refLaw pstar a ≠ ⊤ := by
  unfold countableKernelReferenceWeightOnTargets
  refine ENNReal.mul_ne_top ?_ ?_
  · exact observerClassReferenceWeightOnTargets_ne_top
      (A := A) (O := O) ω targets pstar
  · simp [ratToENNReal]

/--
Finite-chart Gibbs weight for the kernel lift: target-class reference mass times reference
action mass, tilted by the capped target score.
-/
def countableKernelGibbsWeightOnTargets
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) : ENNReal :=
  countableKernelReferenceWeightOnTargets (A := A) (O := O) ω targets refLaw pstar a *
    ENNReal.ofReal (Real.exp (kernelActionScoreOnTargets U π t h ω pstar a).toReal)

theorem countableKernelGibbsWeightOnTargets_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) :
    countableKernelGibbsWeightOnTargets U π t h ω targets refLaw pstar a ≠ ⊤ := by
  unfold countableKernelGibbsWeightOnTargets
  refine ENNReal.mul_ne_top ?_ ?_
  · exact countableKernelReferenceWeightOnTargets_ne_top
      (A := A) (O := O) ω targets refLaw pstar a
  · simp

/-- Agreement of two joint target-action weights on the designated finite chart. -/
def agreesWithOnTargetActions
    (targets : List (CountableEncodedProgram A O))
    (actions : List A)
    (κ₁ κ₂ : CountableEncodedProgram A O → A → ENNReal) : Prop :=
  ∀ p, p ∈ targets → ∀ a, a ∈ actions → κ₁ p a = κ₂ p a

/--
Per-chart Gibbs-mismatch term entering the kernel lift: the proposed joint class-action
weight at `(pstar, a)` is compared against the finite-chart Gibbs kernel.
-/
def def_raw_kernel_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (_ωB ωA : Observer (CountableEncodedProgram A O))
    (q : U.Program → ENNReal)
    (κ : CountableEncodedProgram A O → A → ENNReal)
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) : ENNReal :=
  let _ := q
  posteriorWeightKLDivergenceTerm (κ pstar a)
    (countableKernelGibbsWeightOnTargets U π t h ωA targets refLaw pstar a)

/-- Lean wrapper for `def:kernel-functional` on the countable functional stack. -/
def def_kernel_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (q : U.Program → ENNReal)
    (targets : List (CountableEncodedProgram A O))
    (actions : List A)
    (κ : CountableEncodedProgram A O → A → ENNReal)
    (refLaw : ActionLaw A) : ENNReal :=
  def_afe U π t h q +
    listSumENNReal targets
      (fun pstar =>
        listSumENNReal actions
          (fun a => def_raw_kernel_functional U π t h ωB ωA q κ targets refLaw pstar a))

/-- Lean wrapper for `def:meeting-point-shorthand` on the countable functional stack. -/
def def_meeting_point_shorthand
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (q : U.Program → ENNReal)
    (ν : CountableEncodedProgram A O → ENNReal)
    (targets : List (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O)
    (actions : List A)
    (κ : CountableEncodedProgram A O → A → ENNReal)
    (refLaw : ActionLaw A) :
    ENNReal × ENNReal × ENNReal :=
  (def_bhat_omega U π t h ωA pstar,
   def_two_observer_functional U π t h ωB ωA q ν targets,
   def_kernel_functional U π t h ωB ωA q targets actions κ refLaw)

/-- Lean wrapper for `prop:belief-invariance-above` on the countable functional stack. -/
theorem prop_belief_invariance_above
    {ωB : Observer (CountableEncodedProgram A O)}
    (hAbove : BeliefAdmissible (A := A) (O := O) ωB)
    {p q : CountableEncodedProgram A O}
    (hSame : ωB.view p = ωB.view q) :
    (behavioralObserver (A := A) (O := O)).view p =
      (behavioralObserver (A := A) (O := O)).view q := by
  rcases hAbove with ⟨f, hf⟩
  simpa [Function.comp, hf] using congrArg f hSame

/-- Lean wrapper for `cor:twins-frozen-ratio` on the countable functional stack. -/
theorem cor_twins_frozen_ratio
    {p₁ p₂ : CountableEncodedProgram A O}
    (hTwin :
      (behavioralObserver (A := A) (O := O)).view p₁ =
        (behavioralObserver (A := A) (O := O)).view p₂) :
    encodedObserverFiber (A := A) (O := O) (behavioralObserver (A := A) (O := O)) p₁ =
      encodedObserverFiber (A := A) (O := O) (behavioralObserver (A := A) (O := O)) p₂ := by
  funext r
  simp [encodedObserverFiber, hTwin]

/-- Lean wrapper for `cor:canonical-pair` on the countable functional stack. -/
theorem cor_canonical_pair :
    BeliefAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) ∧
    ActionAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) := by
  constructor
  · exact observerRefines_refl _
  · exact observerRefines_refl _

/-- Lean wrapper for `prop:goal-dialed` on the countable functional stack. -/
theorem prop_goal_dialed
    {ωA : Observer (CountableEncodedProgram A O)}
    {pstar : CountableEncodedProgram A O}
    (hRef : BeliefAdmissible (A := A) (O := O) ωA) :
    goalDialConverges (A := A) (O := O) ωA pstar :=
  hRef

/--
Lean wrapper for `prop:two-observer-minimizer` on the countable functional stack.

This is the exact finite-list minimizer characterization currently carried by the Lean
tree: zero functional value occurs exactly at the Bayes/Gibbs posterior weights together
with the finite-list Gibbs class weights induced by the code prior and the capped
semantic score.
-/
theorem prop_two_observer_minimizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O)) :
    def_two_observer_functional U π t h ωB ωA
      (fun p => U.posteriorWeight π t h p)
      (observerClassGibbsWeightOnTargets U π t h ωA targets)
      targets = 0 ∧
    ∀ q ν,
      def_two_observer_functional U π t h ωB ωA q ν targets = 0 ↔
        samePosteriorWeights U π t h q ∧
        agreesWithOnTargets targets ν
          (observerClassGibbsWeightOnTargets U π t h ωA targets) := by
  constructor
  · have hAFE0 :
        def_afe U π t h (fun p => U.posteriorWeight π t h p) = 0 :=
      (def_afe_eq_zero_iff_samePosteriorWeights U π t h
        (fun p => U.posteriorWeight π t h p)).2
          (posteriorWeight_samePosteriorWeights U π t h)
    have hRaw0 :
        listSumENNReal targets
          (fun pstar =>
            def_raw_two_observer_functional U π t h ωB ωA
              (fun p => U.posteriorWeight π t h p)
              (observerClassGibbsWeightOnTargets U π t h ωA targets)
              targets pstar) = 0 := by
      refine (listSumENNReal_eq_zero_iff targets ?_).2 ?_
      intro p hp
      exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
          (observerClassGibbsWeightOnTargets_ne_top U π t h ωA targets p)).2 rfl
    simpa [def_two_observer_functional, hAFE0, hRaw0]
  · intro q ν
    constructor
    · intro hZero
      have hParts :
          def_afe U π t h q = 0 ∧
            listSumENNReal targets
              (fun pstar =>
                def_raw_two_observer_functional U π t h ωB ωA q ν targets pstar) = 0 := by
        simpa [def_two_observer_functional] using (add_eq_zero.mp hZero)
      refine ⟨samePosteriorWeights_of_def_afe_eq_zero U π t h q hParts.1, ?_⟩
      intro p hp
      have hTermZero :=
        (listSumENNReal_eq_zero_iff targets
          (fun pstar => def_raw_two_observer_functional U π t h ωB ωA q ν targets pstar)).mp
            hParts.2 p hp
      exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
          (observerClassGibbsWeightOnTargets_ne_top U π t h ωA targets p)).mp
            (by simpa [def_raw_two_observer_functional] using hTermZero)
    · rintro ⟨hq, hν⟩
      have hAFE0 : def_afe U π t h q = 0 :=
        (def_afe_eq_zero_iff_samePosteriorWeights U π t h q).2 hq
      have hRaw0 :
          listSumENNReal targets
            (fun pstar =>
              def_raw_two_observer_functional U π t h ωB ωA q ν targets pstar) = 0 := by
        refine (listSumENNReal_eq_zero_iff targets ?_).2 ?_
        intro p hp
        exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
            (observerClassGibbsWeightOnTargets_ne_top U π t h ωA targets p)).2
              (hν p hp)
      simpa [def_two_observer_functional, hAFE0, hRaw0]

/-- Lean wrapper for `prop:kernel-functional-minimizer` on the countable functional stack. -/
theorem prop_kernel_functional_minimizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (actions : List A)
    (refLaw : ActionLaw A) :
    def_kernel_functional U π t h ωB ωA
      (fun p => U.posteriorWeight π t h p)
      targets actions
      (countableKernelGibbsWeightOnTargets U π t h ωA targets refLaw)
      refLaw = 0 ∧
    ∀ q κ,
      def_kernel_functional U π t h ωB ωA q targets actions κ refLaw = 0 ↔
        samePosteriorWeights U π t h q ∧
        agreesWithOnTargetActions targets actions κ
          (countableKernelGibbsWeightOnTargets U π t h ωA targets refLaw) := by
  constructor
  · have hAFE0 :
        def_afe U π t h (fun p => U.posteriorWeight π t h p) = 0 :=
      (def_afe_eq_zero_iff_samePosteriorWeights U π t h
        (fun p => U.posteriorWeight π t h p)).2
          (posteriorWeight_samePosteriorWeights U π t h)
    have hKernel0 :
        listSumENNReal targets
          (fun pstar =>
            listSumENNReal actions
                  (fun a =>
                    def_raw_kernel_functional U π t h ωB ωA
                      (fun p => U.posteriorWeight π t h p)
                      (countableKernelGibbsWeightOnTargets U π t h ωA targets refLaw)
                      targets refLaw pstar a)) = 0 := by
      refine (listSumENNReal_eq_zero_iff targets ?_).2 ?_
      intro p hp
      refine (listSumENNReal_eq_zero_iff actions ?_).2 ?_
      intro a ha
      exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
        (countableKernelGibbsWeightOnTargets_ne_top U π t h ωA targets refLaw p a)).2 rfl
    simpa [def_kernel_functional, hAFE0, hKernel0]
  · intro q κ
    constructor
    · intro hZero
      have hParts :
          def_afe U π t h q = 0 ∧
            listSumENNReal targets
              (fun pstar =>
                listSumENNReal actions
                  (fun a =>
                    def_raw_kernel_functional U π t h ωB ωA q κ
                      targets refLaw pstar a)) = 0 := by
        simpa [def_kernel_functional] using (add_eq_zero.mp hZero)
      refine ⟨samePosteriorWeights_of_def_afe_eq_zero U π t h q hParts.1, ?_⟩
      intro p hp a ha
      have hpZero :=
        (listSumENNReal_eq_zero_iff targets
          (fun pstar =>
            listSumENNReal actions
              (fun a =>
                def_raw_kernel_functional U π t h ωB ωA q κ
                  targets refLaw pstar a))).mp hParts.2 p hp
      have hpaZero :=
        (listSumENNReal_eq_zero_iff actions
          (fun a =>
            def_raw_kernel_functional U π t h ωB ωA q κ
              targets refLaw p a)).mp hpZero a ha
      exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
          (countableKernelGibbsWeightOnTargets_ne_top U π t h ωA targets refLaw p a)).mp
            (by simpa [def_raw_kernel_functional] using hpaZero)
    · rintro ⟨hq, hκ⟩
      have hAFE0 : def_afe U π t h q = 0 :=
        (def_afe_eq_zero_iff_samePosteriorWeights U π t h q).2 hq
      have hKernel0 :
          listSumENNReal targets
            (fun pstar =>
              listSumENNReal actions
                (fun a =>
                  def_raw_kernel_functional U π t h ωB ωA q κ
                    targets refLaw pstar a)) = 0 := by
        refine (listSumENNReal_eq_zero_iff targets ?_).2 ?_
        intro p hp
        refine (listSumENNReal_eq_zero_iff actions ?_).2 ?_
        intro a ha
        exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
            (countableKernelGibbsWeightOnTargets_ne_top U π t h ωA targets refLaw p a)).2
              (hκ p hp a ha)
      simpa [def_kernel_functional, hAFE0, hKernel0]

/-- Lean wrapper for `prop:kernel-functional-minimizer-compact` on the countable functional stack. -/
theorem prop_kernel_functional_minimizer_compact
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A) :
    let actionChart := refLaw.support.eraseDups
    def_kernel_functional U π t h ωB ωA
      (fun p => U.posteriorWeight π t h p)
      targets actionChart
      (countableKernelGibbsWeightOnTargets U π t h ωA targets refLaw)
      refLaw = 0 ∧
    ∀ q κ,
      def_kernel_functional U π t h ωB ωA q targets actionChart κ refLaw = 0 ↔
        samePosteriorWeights U π t h q ∧
        agreesWithOnTargetActions targets actionChart κ
          (countableKernelGibbsWeightOnTargets U π t h ωA targets refLaw) := by
  simpa using
    (prop_kernel_functional_minimizer U π t h ωB ωA targets refLaw.support.eraseDups refLaw)

/-- Lean wrapper for `prop:belief-illtyped-below` on the countable functional stack. -/
theorem prop_belief_illtyped_below
    {ωB : Observer (CountableEncodedProgram A O)}
    {pstar : CountableEncodedProgram A O}
    (_hBelow : ActionAdmissible (A := A) (O := O) ωB)
    (hNotAbove : ¬ BeliefAdmissible (A := A) (O := O) ωB) :
    ¬ goalDialConverges (A := A) (O := O) ωB pstar :=
  hNotAbove

/-- Lean wrapper for `prop:action-cap` on the countable functional stack. -/
theorem prop_action_cap
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) :
    countableKernelGibbsWeightOnTargets U π t h ωA targets refLaw pstar a ≤
      countableKernelReferenceWeightOnTargets (A := A) (O := O) ωA targets refLaw pstar a *
        ENNReal.ofReal (Real.exp 1) := by
  have hScoreLe : kernelActionScoreOnTargets U π t h ωA pstar a ≤ 1 := by
    unfold kernelActionScoreOnTargets observerClassScore
    exact min_le_left _ _
  unfold countableKernelGibbsWeightOnTargets
  have hExp :
      ENNReal.ofReal (Real.exp (kernelActionScoreOnTargets U π t h ωA pstar a).toReal) ≤
        ENNReal.ofReal (Real.exp 1) := by
    exact ENNReal.ofReal_le_ofReal (by
      exact Real.exp_le_exp.mpr (by
        exact ENNReal.toReal_mono (by simp) hScoreLe))
  exact mul_le_mul_of_nonneg_left hExp bot_le

/-- Lean wrapper for `thm:meeting-point` on the countable functional stack. -/
theorem thm_meeting_point :
    BeliefAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) ∧
    ActionAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) := by
  exact cor_canonical_pair (A := A) (O := O)

end CountablePaperFunctional

end SemanticConvergence
