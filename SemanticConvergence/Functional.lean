import Mathlib.InformationTheory.KullbackLeibler.KLFun
import SemanticConvergence.Hierarchy
import SemanticConvergence.ConcreteBelief
import SemanticConvergence.ConcreteSemantic
import SemanticConvergence.ConcreteFunctional

/-
NOTE [variational-core exactness]

The canonical variational declarations in this file are under an exactness overhaul. The frozen
paper-to-Lean target map and representation choice are recorded in
`variational_core_exactness_lock.md`. Until that rewrite lands, the current posterior-weight
divergence scaffolds here should not be treated as an exact match for the manuscript's Definition 6,
Definition 9, or Definition 10 objects.
-/

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
Legacy countable algorithmic free energy as the generalized KL / I-divergence from the proposed
belief weights `q` to the unnormalized Bayes numerator `posteriorWeight`.

This is retained temporarily so the existing action-side countable scaffold can keep compiling
while the canonical `def_afe` is rebuilt to match the paper's normalized-prior variational object.
-/
def def_afe_legacy
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

/-- Zero legacy posterior-weight divergence forces pointwise posterior-weight agreement. -/
theorem samePosteriorWeights_of_def_afe_eq_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hZero : def_afe_legacy U π t h q = 0) :
    samePosteriorWeights U π t h q := by
  have hTerms :
      ∀ p : U.Program,
        posteriorWeightKLDivergenceTerm (q p) (U.posteriorWeight π t h p) = 0 := by
    exact ENNReal.tsum_eq_zero.mp (by simpa [def_afe_legacy] using hZero)
  intro p
  exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (posteriorWeight_ne_top U π t h p)).mp (hTerms p)

/-- Zero legacy posterior-weight divergence is exactly posterior-weight agreement. -/
theorem def_afe_eq_zero_iff_samePosteriorWeights
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) :
    def_afe_legacy U π t h q = 0 ↔ samePosteriorWeights U π t h q := by
  constructor
  · exact samePosteriorWeights_of_def_afe_eq_zero U π t h q
  · intro hq
    rw [def_afe_legacy, ENNReal.tsum_eq_zero]
    intro p
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
        (posteriorWeight_ne_top U π t h p)).2 (hq p)

/-- Total raw universal-prior mass on the enumerable machine domain. -/
def universalPriorMass
    (U : CountablePrefixMachine A O) : ENNReal :=
  ∑' p : U.Program, U.universalWeight p

/-- Normalized universal prior from Definition 6 of the manuscript. -/
def def_universal_prior
    (U : CountablePrefixMachine A O)
    (p : U.Program) : ENNReal :=
  U.universalWeight p / universalPriorMass U

/-- Bayes evidence under the normalized universal prior. -/
def bayesEvidence
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) : ENNReal :=
  ∑' p : U.Program, def_universal_prior U p * U.likelihood π t h p

/-- Bayes/Gibbs posterior under the normalized universal prior. -/
def bayesPosterior
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (p : U.Program) : ENNReal :=
  def_universal_prior U p * U.likelihood π t h p / bayesEvidence U π t h

/-- Countable history-fit loss `L_t(p; h_t) = -log μ_p(o_{1:t} | a_{1:t})`. -/
def historyFitLoss
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (p : U.Program) : Real :=
  -Real.log (U.likelihood π t h p).toReal

/-- Pointwise expected-loss contribution of a proposed posterior weight. -/
def historyFitLossContribution
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (p : U.Program) : Real :=
  if hq : q p = 0 then
    0
  else
    (q p).toReal * historyFitLoss U π t h p

/-- Pointwise KL contribution against the normalized universal prior. -/
def priorKLDivergenceContribution
    (U : CountablePrefixMachine A O)
    (q : U.Program → ENNReal)
    (p : U.Program) : Real :=
  if hq : q p = 0 then
    0
  else
    (q p).toReal * Real.log ((q p / def_universal_prior U p).toReal)

/-- Pointwise KL contribution against the Bayes/Gibbs posterior. -/
def posteriorKLDivergenceContribution
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (p : U.Program) : Real :=
  if hq : q p = 0 then
    0
  else
    (q p).toReal * Real.log ((q p / bayesPosterior U π t h p).toReal)

/-- Generalized KL / I-divergence gap against the Bayes/Gibbs posterior. -/
def posteriorIGapContribution
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (p : U.Program) : ENNReal :=
  posteriorWeightKLDivergenceTerm (q p) (bayesPosterior U π t h p)

/-- `E_q[L_t]` from Definition 6 of the manuscript. -/
def expectedHistoryFitLoss
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) : Real :=
  ∑' p : U.Program, historyFitLossContribution U π t h q p

/-- `KL(q || w)` against the normalized universal prior. -/
def priorKLDivergence
    (U : CountablePrefixMachine A O)
    (q : U.Program → ENNReal) : Real :=
  ∑' p : U.Program, priorKLDivergenceContribution U q p

/-- `KL(q || q_t^*(· | h_t))` in the manuscript's variational identity. -/
def posteriorKLDivergence
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) : Real :=
  ∑' p : U.Program, posteriorKLDivergenceContribution U π t h q p

/-- Generalized KL / I-divergence to the Bayes/Gibbs posterior. -/
def posteriorIGap
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) : ENNReal :=
  ∑' p : U.Program, posteriorIGapContribution U π t h q p

/-- The evidence penalty `-log ξ̄(o_{1:t} | a_{1:t})`. -/
def negativeLogBayesEvidence
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O) : Real :=
  -Real.log (bayesEvidence U π t h).toReal

/--
Countable algorithmic free energy from Definition 6 of the manuscript:
`F_t[q; h_t] = E_q[L_t] + KL(q || w)`.
-/
def def_afe
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) : Real :=
  expectedHistoryFitLoss U π t h q + priorKLDivergence U q

/-- Admissible countable posteriors for the exact belief-side variational theorems. -/
structure BeliefAdmissibleAt
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal) : Prop where
  normalized : ∑' p : U.Program, q p = 1
  priorMass_ne_zero : universalPriorMass U ≠ 0
  priorMass_ne_top : universalPriorMass U ≠ ⊤
  evidence_pos : 0 < bayesEvidence U π t h
  vanishes_on_zero_likelihood :
    ∀ p : U.Program, U.likelihood π t h p = 0 → q p = 0
  summable_expectedHistoryFitLoss :
    Summable (fun p : U.Program => historyFitLossContribution U π t h q p)
  summable_priorKLDivergence :
    Summable (fun p : U.Program => priorKLDivergenceContribution U q p)
  summable_posteriorKLDivergence :
    Summable (fun p : U.Program => posteriorKLDivergenceContribution U π t h q p)

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

/-- Finite-list target score retained for the legacy chart-based action scaffold. -/
def observerClassScoreOnTargets
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
    ENNReal.ofReal (Real.exp (observerClassScoreOnTargets U π t h ω pstar).toReal)

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

/-- Legacy finite-target wrapper for `def:bhat-omega`. -/
def def_bhat_omega_legacy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  observerClassScoreOnTargets U π t h ω pstar

/--
Lean wrapper for `def:raw-two-observer-functional` on the countable functional stack.

This is the per-target Gibbs-mismatch term entering the finite-list paper-facing
two-observer functional: the proposed class weight at `pstar` is compared against the
finite-list Gibbs weight built from the code-length reference mass and the capped
semantic score.
-/
def def_raw_two_observer_functional_legacy
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

The belief-side term is the legacy posterior-weight scaffold `def_afe_legacy`; the action-side term is
the finite-list Gibbs mismatch against the target-class weights induced by the code prior
and the capped semantic scores.
-/
def def_two_observer_functional_legacy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (q : U.Program → ENNReal)
    (ν : CountableEncodedProgram A O → ENNReal)
    (targets : List (CountableEncodedProgram A O)) : ENNReal :=
  def_afe_legacy U π t h q +
    listSumENNReal targets
      (fun pstar => def_raw_two_observer_functional_legacy U π t h ωB ωA q ν targets pstar)

/-- Pushforward universal-prior mass of an `ω`-class on the countable machine domain. -/
def observerClassPriorWeight
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (c : ω.Ω) : ENNReal :=
  ∑' p : U.Program, if ω.view (U.toEncodedProgram p) = c then def_universal_prior U p else 0

/-- A chosen countable machine representative for a nonempty `ω`-class. -/
noncomputable def observerClassRepresentative
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (c : ω.Ω) : Option U.Program :=
  if hClass : ∃ p : U.Program, ω.view (U.toEncodedProgram p) = c then
    some (Classical.choose hClass)
  else
    none

/--
Exact class score `G_t^{ω_A}(c; h_t)` on the countable observer codomain, implemented by choosing
any machine representative of `c` and using the class-invariance of `semanticSeparation`.
Absent classes are assigned score `0`.
-/
noncomputable def observerClassScore
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (c : ω.Ω) : Real :=
  if hClass : ∃ p : U.Program, ω.view (U.toEncodedProgram p) = c then
    (min (1 : ENNReal)
      (U.semanticSeparation π t h ω (U.toEncodedProgram (Classical.choose hClass)))).toReal
  else
    0

/-- Class-score contribution `ν(c) G(c)` entering the exact two-observer functional. -/
def observerClassExpectedScoreContribution
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (ν : ω.Ω → ENNReal)
    (c : ω.Ω) : Real :=
  (ν c).toReal * observerClassScore U π t h ω c

/-- Exact expected class score `E_{C ∼ ν}[G_t^{ω_A}(C; h_t)]`. -/
def observerClassExpectedScore
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (ν : ω.Ω → ENNReal) : Real :=
  ∑' c : ω.Ω, observerClassExpectedScoreContribution U π t h ω ν c

/-- Pointwise KL contribution against the pushed-forward class prior `\bar w^{ω}`. -/
def observerClassPriorKLDivergenceContribution
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (ν : ω.Ω → ENNReal)
    (c : ω.Ω) : Real :=
  if hν : ν c = 0 then
    0
  else
    (ν c).toReal * Real.log ((ν c / observerClassPriorWeight U ω c).toReal)

/-- Exact class-side regularizer `KL(ν || \bar w^{ω})`. -/
def observerClassPriorKLDivergence
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (ν : ω.Ω → ENNReal) : Real :=
  ∑' c : ω.Ω, observerClassPriorKLDivergenceContribution U ω ν c

/-- Unnormalized Gibbs weight on an observer class. -/
def observerClassGibbsWeight
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (c : ω.Ω) : ENNReal :=
  observerClassPriorWeight U ω c *
    ENNReal.ofReal (Real.exp ((β / γ) * observerClassScore U π t h ω c))

/-- Gibbs normalizing constant for the exact countable two-observer functional. -/
def observerClassGibbsPartition
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real) : ENNReal :=
  ∑' c : ω.Ω, observerClassGibbsWeight U π t h ω β γ c

/-- Exact Gibbs class law from Proposition 8 of the manuscript. -/
def observerClassGibbsLaw
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (c : ω.Ω) : ENNReal :=
  observerClassGibbsWeight U π t h ω β γ c /
    observerClassGibbsPartition U π t h ω β γ

/-- Generalized discrete I-gap against the exact Gibbs class law. -/
def observerClassGibbsIGapContribution
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (ν : ω.Ω → ENNReal)
    (c : ω.Ω) : ENNReal :=
  posteriorWeightKLDivergenceTerm (ν c) (observerClassGibbsLaw U π t h ω β γ c)

/-- Total generalized I-gap to the exact Gibbs class law. -/
def observerClassGibbsIGap
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (ν : ω.Ω → ENNReal) : ENNReal :=
  ∑' c : ω.Ω, observerClassGibbsIGapContribution U π t h ω β γ ν c

/-- Admissible observer-class laws for the exact countable two-observer variational theorem. -/
structure ObserverClassAdmissibleAt
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (ν : ω.Ω → ENNReal) : Prop where
  normalized : ∑' c : ω.Ω, ν c = 1
  vanishes_on_zero_prior :
    ∀ c : ω.Ω, observerClassPriorWeight U ω c = 0 → ν c = 0
  summable_expectedScore :
    Summable (fun c : ω.Ω => observerClassExpectedScoreContribution U π t h ω ν c)
  summable_priorKLDivergence :
    Summable (fun c : ω.Ω => observerClassPriorKLDivergenceContribution U ω ν c)

/-- Exact wrapper for `def:bhat-omega` on the countable functional stack. -/
def def_bhat_omega
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (pstar : CountableEncodedProgram A O) : Real :=
  observerClassScore U π t h ω (ω.view pstar)

/--
Exact raw policy-coupled scaffold from Definition 9 of the manuscript, expressed against an
explicit class-targeting law `νπ` on `ω_A`-classes.
-/
def def_raw_two_observer_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (_ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : Real)
    (q : U.Program → ENNReal)
    (νπ : ωA.Ω → ENNReal) : Real :=
  def_afe U π t h q
    - β * observerClassExpectedScore U π t h ωA νπ
    + γ * observerClassPriorKLDivergence U ωA νπ

/--
Exact two-observer variational functional from Definition 10 of the manuscript.
-/
def def_two_observer_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (_ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : Real)
    (q : U.Program → ENNReal)
    (ν : ωA.Ω → ENNReal) : Real :=
  def_afe U π t h q
    - β * observerClassExpectedScore U π t h ωA ν
    + γ * observerClassPriorKLDivergence U ωA ν

private theorem def_universal_prior_tsum_eq_one_of_admissible
    (U : CountablePrefixMachine A O)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q) :
    ∑' p : U.Program, def_universal_prior U p = 1 := by
  calc
    ∑' p : U.Program, def_universal_prior U p
        = ∑' p : U.Program, U.universalWeight p / universalPriorMass U := by
            simp [def_universal_prior]
    _ = (∑' p : U.Program, U.universalWeight p) * (universalPriorMass U)⁻¹ := by
          simpa [div_eq_mul_inv] using
            (ENNReal.tsum_mul_right
              (f := fun p : U.Program => U.universalWeight p)
              (a := (universalPriorMass U)⁻¹))
    _ = (∑' p : U.Program, U.universalWeight p) / universalPriorMass U := by
          simp [div_eq_mul_inv]
    _ = 1 := ENNReal.div_self hq.priorMass_ne_zero hq.priorMass_ne_top

private theorem def_universal_prior_ne_top_of_admissible
    (U : CountablePrefixMachine A O)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    def_universal_prior U p ≠ ⊤ := by
  have hle : def_universal_prior U p ≤ 1 := by
    calc
      def_universal_prior U p ≤ ∑' r : U.Program, def_universal_prior U r := ENNReal.le_tsum p
      _ = 1 := def_universal_prior_tsum_eq_one_of_admissible U hq
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

private theorem universalWeight_ne_zero_of_countable
    (U : CountablePrefixMachine A O)
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

private theorem def_universal_prior_pos_of_admissible
    (U : CountablePrefixMachine A O)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    0 < def_universal_prior U p := by
  unfold def_universal_prior
  exact ENNReal.div_pos (universalWeight_ne_zero_of_countable U p) hq.priorMass_ne_top

theorem observerClassPriorWeight_le_one
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (c : ω.Ω) :
    observerClassPriorWeight U ω c ≤ 1 := by
  have hPoint :
      ∀ p : U.Program,
        (if ω.view (U.toEncodedProgram p) = c then def_universal_prior U p else 0) ≤
          def_universal_prior U p := by
    intro p
    by_cases hView : ω.view (U.toEncodedProgram p) = c
    · simp [hView]
    · simp [hView]
  calc
    observerClassPriorWeight U ω c
        = ∑' p : U.Program,
            if ω.view (U.toEncodedProgram p) = c then def_universal_prior U p else 0 := rfl
    _ ≤ ∑' p : U.Program, def_universal_prior U p := ENNReal.tsum_le_tsum hPoint
    _ = 1 := def_universal_prior_tsum_eq_one_of_admissible U hq

theorem observerClassPriorWeight_ne_top
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (c : ω.Ω) :
    observerClassPriorWeight U ω c ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt (observerClassPriorWeight_le_one U ω hq c) ENNReal.one_lt_top)

theorem observerClassPriorWeight_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q) :
    ∑' c : ω.Ω, observerClassPriorWeight U ω c = 1 := by
  calc
    ∑' c : ω.Ω, observerClassPriorWeight U ω c
        = ∑' p : U.Program, ∑' c : ω.Ω,
            if ω.view (U.toEncodedProgram p) = c then def_universal_prior U p else 0 := by
              unfold observerClassPriorWeight
              rw [ENNReal.tsum_comm]
    _ = ∑' p : U.Program, def_universal_prior U p := by
          apply tsum_congr
          intro p
          classical
          let fp : ω.Ω → ENNReal :=
            fun c => if c = ω.view (U.toEncodedProgram p) then def_universal_prior U p else 0
          have hsingle : ∑' c : ω.Ω, fp c = def_universal_prior U p := by
            simpa [fp] using
              (tsum_eq_single (ω.view (U.toEncodedProgram p))
                (fun c hc => by simp [fp, hc]))
          calc
            (∑' c : ω.Ω, if ω.view (U.toEncodedProgram p) = c then def_universal_prior U p else 0)
                = (∑' c : ω.Ω, fp c) := by
                    apply tsum_congr
                    intro c
                    by_cases hc : c = ω.view (U.toEncodedProgram p)
                    · simp [fp, hc, eq_comm]
                    · simp [fp, hc, eq_comm]
            _ = def_universal_prior U p := hsingle
    _ = 1 := def_universal_prior_tsum_eq_one_of_admissible U hq

theorem observerClassPriorWeight_pos_of_exists
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {c : ω.Ω}
    (hClass : ∃ p : U.Program, ω.view (U.toEncodedProgram p) = c) :
    0 < observerClassPriorWeight U ω c := by
  rcases hClass with ⟨p, hp⟩
  have hterm :
      def_universal_prior U p ≤ observerClassPriorWeight U ω c := by
    unfold observerClassPriorWeight
    simpa [hp] using
      (ENNReal.le_tsum p
        (f := fun p : U.Program =>
          if ω.view (U.toEncodedProgram p) = c then def_universal_prior U p else 0))
  exact lt_of_lt_of_le (def_universal_prior_pos_of_admissible U hq p) hterm

theorem observerClassScore_eq_of_rep
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    {c : ω.Ω} {p : U.Program}
    (hp : ω.view (U.toEncodedProgram p) = c) :
    observerClassScore U π t h ω c =
      (min (1 : ENNReal) (U.semanticSeparation π t h ω (U.toEncodedProgram p))).toReal := by
  classical
  unfold observerClassScore
  have hClass : ∃ q : U.Program, ω.view (U.toEncodedProgram q) = c := ⟨p, hp⟩
  simp [hClass]
  have hView :
      ω.view (U.toEncodedProgram (Classical.choose hClass)) =
        ω.view (U.toEncodedProgram p) := by
    rw [Classical.choose_spec hClass, hp]
  have hSep :=
    U.semanticSeparation_eq_of_sameView π t h ω hView
  simpa [hSep]

theorem observerClassScore_nonneg
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (c : ω.Ω) :
    0 ≤ observerClassScore U π t h ω c := by
  classical
  by_cases hClass : ∃ p : U.Program, ω.view (U.toEncodedProgram p) = c
  · simp [observerClassScore, hClass]
  · simp [observerClassScore, hClass]

theorem observerClassScore_le_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (c : ω.Ω) :
    observerClassScore U π t h ω c ≤ 1 := by
  classical
  by_cases hClass : ∃ p : U.Program, ω.view (U.toEncodedProgram p) = c
  · have hle :
        min (1 : ENNReal)
          (U.semanticSeparation π t h ω (U.toEncodedProgram (Classical.choose hClass))) ≤ 1 :=
        min_le_left _ _
    rw [observerClassScore, dif_pos hClass]
    simpa using (ENNReal.toReal_le_toReal (by simp) (by simp)).2 hle
  · simp [observerClassScore, hClass]

private theorem observerClassLaw_ne_top_of_admissible
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    {ν : ω.Ω → ENNReal}
    (hν : ObserverClassAdmissibleAt U π t h ω ν)
    (c : ω.Ω) :
    ν c ≠ ⊤ := by
  have hle : ν c ≤ 1 := by
    calc
      ν c ≤ ∑' d : ω.Ω, ν d := ENNReal.le_tsum c
      _ = 1 := hν.normalized
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

private theorem observerClassLaw_toReal_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    {ν : ω.Ω → ENNReal}
    (hν : ObserverClassAdmissibleAt U π t h ω ν) :
    ∑' c : ω.Ω, (ν c).toReal = 1 := by
  calc
    ∑' c : ω.Ω, (ν c).toReal = (∑' c : ω.Ω, ν c).toReal := by
      exact (ENNReal.tsum_toReal_eq
        (fun c => observerClassLaw_ne_top_of_admissible U π t h ω hν c)).symm
    _ = 1 := by simpa [hν.normalized]

private theorem observerClassGibbsWeight_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (c : ω.Ω) :
    observerClassGibbsWeight U π t h ω β γ c ≠ ⊤ := by
  unfold observerClassGibbsWeight
  refine ENNReal.mul_ne_top ?_ ?_
  · exact observerClassPriorWeight_ne_top U ω hq c
  · simp

private theorem observerClassGibbsWeight_ge_prior
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (c : ω.Ω) :
    observerClassPriorWeight U ω c ≤ observerClassGibbsWeight U π t h ω β γ c := by
  have hExp : (1 : Real) ≤ Real.exp ((β / γ) * observerClassScore U π t h ω c) := by
    apply Real.one_le_exp
    exact mul_nonneg (div_nonneg hβ hγ.le) (observerClassScore_nonneg U π t h ω c)
  have hExpENN : (1 : ENNReal) ≤
      ENNReal.ofReal (Real.exp ((β / γ) * observerClassScore U π t h ω c)) := by
    simpa using ENNReal.ofReal_le_ofReal hExp
  calc
    observerClassPriorWeight U ω c
        = observerClassPriorWeight U ω c * 1 := by simp
    _ ≤ observerClassPriorWeight U ω c *
          ENNReal.ofReal (Real.exp ((β / γ) * observerClassScore U π t h ω c)) := by
            exact mul_le_mul_left' hExpENN _
    _ = observerClassGibbsWeight U π t h ω β γ c := by
          simp [observerClassGibbsWeight]

private theorem observerClassGibbsWeight_le_scaled_prior
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (c : ω.Ω) :
    observerClassGibbsWeight U π t h ω β γ c ≤
      observerClassPriorWeight U ω c * ENNReal.ofReal (Real.exp (β / γ)) := by
  have hScaleNonneg : 0 ≤ β / γ := div_nonneg hβ hγ.le
  have hMulLe : (β / γ) * observerClassScore U π t h ω c ≤ β / γ := by
    nlinarith [hScaleNonneg, observerClassScore_nonneg U π t h ω c,
      observerClassScore_le_one U π t h ω c]
  have hExpLe :
      Real.exp ((β / γ) * observerClassScore U π t h ω c) ≤ Real.exp (β / γ) :=
    Real.exp_le_exp.mpr hMulLe
  have hExpENN :
      ENNReal.ofReal (Real.exp ((β / γ) * observerClassScore U π t h ω c)) ≤
        ENNReal.ofReal (Real.exp (β / γ)) := ENNReal.ofReal_le_ofReal hExpLe
  unfold observerClassGibbsWeight
  exact mul_le_mul_left' hExpENN _

private theorem observerClassGibbsPartition_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    observerClassGibbsPartition U π t h ω β γ ≠ ⊤ := by
  have hle :
      observerClassGibbsPartition U π t h ω β γ ≤
        ENNReal.ofReal (Real.exp (β / γ)) := by
    calc
      observerClassGibbsPartition U π t h ω β γ
          = ∑' c : ω.Ω, observerClassGibbsWeight U π t h ω β γ c := rfl
      _ ≤ ∑' c : ω.Ω,
            observerClassPriorWeight U ω c * ENNReal.ofReal (Real.exp (β / γ)) :=
          ENNReal.tsum_le_tsum
            (fun c => observerClassGibbsWeight_le_scaled_prior U π t h ω β γ hβ hγ c)
      _ = (∑' c : ω.Ω, observerClassPriorWeight U ω c) *
            ENNReal.ofReal (Real.exp (β / γ)) := by
            simpa using
              (ENNReal.tsum_mul_right
                (f := fun c : ω.Ω => observerClassPriorWeight U ω c)
                (a := ENNReal.ofReal (Real.exp (β / γ))))
      _ = ENNReal.ofReal (Real.exp (β / γ)) := by
            rw [observerClassPriorWeight_tsum_eq_one U ω hq, one_mul]
  exact ne_of_lt (lt_of_le_of_lt hle (by simp))

private theorem observerClassGibbsPartition_pos
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    0 < observerClassGibbsPartition U π t h ω β γ := by
  have hOneLe :
      1 ≤ observerClassGibbsPartition U π t h ω β γ := by
    calc
      1 = ∑' c : ω.Ω, observerClassPriorWeight U ω c := by
            rw [observerClassPriorWeight_tsum_eq_one U ω hq]
      _ ≤ ∑' c : ω.Ω, observerClassGibbsWeight U π t h ω β γ c :=
          ENNReal.tsum_le_tsum
            (fun c => observerClassGibbsWeight_ge_prior U π t h ω β γ hβ hγ c)
      _ = observerClassGibbsPartition U π t h ω β γ := rfl
  exact lt_of_lt_of_le (by simp) hOneLe

private theorem observerClassGibbsPartition_ne_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    observerClassGibbsPartition U π t h ω β γ ≠ 0 :=
  (observerClassGibbsPartition_pos U π t h ω β γ hq hβ hγ).ne'

private theorem observerClassGibbsLaw_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (c : ω.Ω) :
    observerClassGibbsLaw U π t h ω β γ c ≠ ⊤ := by
  exact ENNReal.div_ne_top
    (observerClassGibbsWeight_ne_top U π t h ω β γ hq c)
    (observerClassGibbsPartition_ne_zero U π t h ω β γ hq hβ hγ)

private theorem observerClassGibbsLaw_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    ∑' c : ω.Ω, observerClassGibbsLaw U π t h ω β γ c = 1 := by
  calc
    ∑' c : ω.Ω, observerClassGibbsLaw U π t h ω β γ c
        = ∑' c : ω.Ω,
            observerClassGibbsWeight U π t h ω β γ c /
              observerClassGibbsPartition U π t h ω β γ := rfl
    _ = (∑' c : ω.Ω, observerClassGibbsWeight U π t h ω β γ c) /
          observerClassGibbsPartition U π t h ω β γ := by
            simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ = observerClassGibbsPartition U π t h ω β γ /
          observerClassGibbsPartition U π t h ω β γ := by
            rw [observerClassGibbsPartition]
    _ = 1 := ENNReal.div_self
          (observerClassGibbsPartition_ne_zero U π t h ω β γ hq hβ hγ)
          (observerClassGibbsPartition_ne_top U π t h ω β γ hq hβ hγ)

private theorem observerClassGibbsLaw_toReal_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    ∑' c : ω.Ω, (observerClassGibbsLaw U π t h ω β γ c).toReal = 1 := by
  calc
    ∑' c : ω.Ω, (observerClassGibbsLaw U π t h ω β γ c).toReal
        = (∑' c : ω.Ω, observerClassGibbsLaw U π t h ω β γ c).toReal := by
            exact (ENNReal.tsum_toReal_eq
              (fun c => observerClassGibbsLaw_ne_top U π t h ω β γ hq hβ hγ c)).symm
    _ = 1 := by
          simpa [observerClassGibbsLaw_tsum_eq_one U π t h ω β γ hq hβ hγ]

private theorem observerClassGibbsLaw_eq_zero_of_zero_prior
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    {c : ω.Ω}
    (hPrior : observerClassPriorWeight U ω c = 0) :
    observerClassGibbsLaw U π t h ω β γ c = 0 := by
  unfold observerClassGibbsLaw observerClassGibbsWeight
  simp [hPrior]

private theorem observerClassGibbsLaw_ne_zero_of_prior_ne_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    {c : ω.Ω}
    (hPrior : observerClassPriorWeight U ω c ≠ 0) :
    observerClassGibbsLaw U π t h ω β γ c ≠ 0 := by
  have hWeight : observerClassGibbsWeight U π t h ω β γ c ≠ 0 := by
    unfold observerClassGibbsWeight
    refine mul_ne_zero hPrior ?_
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  intro hZero
  have := (ENNReal.div_eq_zero_iff).mp hZero
  exact this.elim hWeight
    (fun hTop =>
      (observerClassGibbsPartition_ne_top U π t h ω β γ hq hβ hγ) hTop)

private theorem observerClassGibbsLaw_eq_zero_iff_prior_eq_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (c : ω.Ω) :
    observerClassGibbsLaw U π t h ω β γ c = 0 ↔
      observerClassPriorWeight U ω c = 0 := by
  constructor
  · intro hZero
    by_contra hPrior
    exact
      (observerClassGibbsLaw_ne_zero_of_prior_ne_zero U π t h ω β γ hq hβ hγ hPrior)
        hZero
  · exact observerClassGibbsLaw_eq_zero_of_zero_prior U π t h ω β γ hq hβ hγ

private theorem observerClassGibbsIGapContribution_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {ν : ω.Ω → ENNReal}
    (hν : ObserverClassAdmissibleAt U π t h ω ν)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (c : ω.Ω) :
    observerClassGibbsIGapContribution U π t h ω β γ ν c ≠ ⊤ := by
  unfold observerClassGibbsIGapContribution
  have hνTop : ν c ≠ ⊤ := observerClassLaw_ne_top_of_admissible U π t h ω hν c
  by_cases hLaw : observerClassGibbsLaw U π t h ω β γ c = 0
  · have hPrior : observerClassPriorWeight U ω c = 0 :=
      (observerClassGibbsLaw_eq_zero_iff_prior_eq_zero U π t h ω β γ hq hβ hγ c).mp hLaw
    have hνZero : ν c = 0 := hν.vanishes_on_zero_prior c hPrior
    simp [posteriorWeightKLDivergenceTerm, hνTop, hLaw, hνZero]
  · simpa [posteriorWeightKLDivergenceTerm, hνTop, hLaw] using
      (ENNReal.mul_ne_top
        (observerClassGibbsLaw_ne_top U π t h ω β γ hq hβ hγ c)
        (by simp : ENNReal.ofReal
          (InformationTheory.klFun ((ν c / observerClassGibbsLaw U π t h ω β γ c).toReal))
            ≠ ⊤))

/--
Zero generalized class-side I-gap occurs exactly at the exact Gibbs class law on the admissible
observer-class domain.
-/
theorem observerClassGibbsIGap_eq_zero_iff
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {ν : ω.Ω → ENNReal}
    (hν : ObserverClassAdmissibleAt U π t h ω ν)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    observerClassGibbsIGap U π t h ω β γ ν = 0 ↔
      ∀ c : ω.Ω, ν c = observerClassGibbsLaw U π t h ω β γ c := by
  constructor
  · intro hGap c
    have hTerm : observerClassGibbsIGapContribution U π t h ω β γ ν c = 0 := by
      exact (ENNReal.tsum_eq_zero.mp (by simpa [observerClassGibbsIGap] using hGap)) c
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (observerClassGibbsLaw_ne_top U π t h ω β γ hq hβ hγ c)).mp hTerm
  · intro hEq
    rw [observerClassGibbsIGap, ENNReal.tsum_eq_zero]
    intro c
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (observerClassGibbsLaw_ne_top U π t h ω β γ hq hβ hγ c)).2 (hEq c)

private theorem observerClassGibbsIGap_term_identity
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {ν : ω.Ω → ENNReal}
    (hν : ObserverClassAdmissibleAt U π t h ω ν)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (c : ω.Ω) :
    (observerClassGibbsIGapContribution U π t h ω β γ ν c).toReal =
      observerClassPriorKLDivergenceContribution U ω ν c
        - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c
        + (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal
        + (observerClassGibbsLaw U π t h ω β γ c).toReal
        - (ν c).toReal := by
  by_cases hνc : ν c = 0
  · by_cases hLaw : observerClassGibbsLaw U π t h ω β γ c = 0
    · simp [observerClassGibbsIGapContribution, posteriorWeightKLDivergenceTerm,
        observerClassPriorKLDivergenceContribution, observerClassExpectedScoreContribution,
        hνc, hLaw]
    · have hLawPos : 0 < (observerClassGibbsLaw U π t h ω β γ c).toReal := by
        exact ENNReal.toReal_pos hLaw
          (observerClassGibbsLaw_ne_top U π t h ω β γ hq hβ hγ c)
      simp [observerClassGibbsIGapContribution, posteriorWeightKLDivergenceTerm,
        observerClassPriorKLDivergenceContribution, observerClassExpectedScoreContribution,
        hνc, hLaw, InformationTheory.klFun_zero, hLawPos.ne']
  · have hνPos : 0 < (ν c).toReal := by
      exact ENNReal.toReal_pos hνc (observerClassLaw_ne_top_of_admissible U π t h ω hν c)
    have hPrior : observerClassPriorWeight U ω c ≠ 0 := by
      intro hPriorZero
      exact hνc (hν.vanishes_on_zero_prior c hPriorZero)
    have hPriorPos : 0 < (observerClassPriorWeight U ω c).toReal := by
      exact ENNReal.toReal_pos hPrior (observerClassPriorWeight_ne_top U ω hq c)
    have hLaw : observerClassGibbsLaw U π t h ω β γ c ≠ 0 :=
      observerClassGibbsLaw_ne_zero_of_prior_ne_zero U π t h ω β γ hq hβ hγ hPrior
    have hLawPos : 0 < (observerClassGibbsLaw U π t h ω β γ c).toReal := by
      exact ENNReal.toReal_pos hLaw
        (observerClassGibbsLaw_ne_top U π t h ω β γ hq hβ hγ c)
    have hPartPos : 0 < (observerClassGibbsPartition U π t h ω β γ).toReal := by
      exact ENNReal.toReal_pos
        (observerClassGibbsPartition_ne_zero U π t h ω β γ hq hβ hγ)
        (observerClassGibbsPartition_ne_top U π t h ω β γ hq hβ hγ)
    have hIGapToReal :
        (observerClassGibbsIGapContribution U π t h ω β γ ν c).toReal =
          (observerClassGibbsLaw U π t h ω β γ c).toReal *
            InformationTheory.klFun
              ((ν c / observerClassGibbsLaw U π t h ω β γ c).toReal) := by
      unfold observerClassGibbsIGapContribution posteriorWeightKLDivergenceTerm
      rw [if_neg (observerClassLaw_ne_top_of_admissible U π t h ω hν c), if_neg hLaw,
        ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (InformationTheory.klFun_nonneg ENNReal.toReal_nonneg)]
    have hRatioLaw :
        (ν c / observerClassGibbsLaw U π t h ω β γ c).toReal =
          (ν c).toReal / (observerClassGibbsLaw U π t h ω β γ c).toReal := by
      rw [ENNReal.toReal_div]
    have hLogPriorRatio :
        Real.log ((ν c / observerClassPriorWeight U ω c).toReal) =
          Real.log (ν c).toReal - Real.log (observerClassPriorWeight U ω c).toReal := by
      rw [ENNReal.toReal_div, Real.log_div hνPos.ne' hPriorPos.ne']
    have hLawToReal :
        (observerClassGibbsLaw U π t h ω β γ c).toReal =
          (observerClassPriorWeight U ω c).toReal *
            Real.exp ((β / γ) * observerClassScore U π t h ω c) /
            (observerClassGibbsPartition U π t h ω β γ).toReal := by
      calc
        (observerClassGibbsLaw U π t h ω β γ c).toReal
            = ((observerClassPriorWeight U ω c *
                  ENNReal.ofReal (Real.exp ((β / γ) * observerClassScore U π t h ω c))) /
                observerClassGibbsPartition U π t h ω β γ).toReal := by
                  rfl
        _ = ((observerClassPriorWeight U ω c).toReal *
              (ENNReal.ofReal (Real.exp ((β / γ) * observerClassScore U π t h ω c))).toReal) /
              (observerClassGibbsPartition U π t h ω β γ).toReal := by
                rw [ENNReal.toReal_div, ENNReal.toReal_mul]
        _ = (observerClassPriorWeight U ω c).toReal *
              Real.exp ((β / γ) * observerClassScore U π t h ω c) /
              (observerClassGibbsPartition U π t h ω β γ).toReal := by
                have hExpNonneg : 0 ≤ Real.exp ((β / γ) * observerClassScore U π t h ω c) := by
                  positivity
                rw [ENNReal.toReal_ofReal hExpNonneg]
    have hLogLaw :
        Real.log (observerClassGibbsLaw U π t h ω β γ c).toReal =
          Real.log (observerClassPriorWeight U ω c).toReal +
            (β / γ) * observerClassScore U π t h ω c
            - Real.log (observerClassGibbsPartition U π t h ω β γ).toReal := by
      rw [hLawToReal, Real.log_div (mul_pos hPriorPos (Real.exp_pos _)).ne' hPartPos.ne',
        Real.log_mul hPriorPos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hLogLawRatio :
        Real.log ((ν c / observerClassGibbsLaw U π t h ω β γ c).toReal) =
          Real.log ((ν c / observerClassPriorWeight U ω c).toReal)
            - (β / γ) * observerClassScore U π t h ω c
            + Real.log (observerClassGibbsPartition U π t h ω β γ).toReal := by
      rw [ENNReal.toReal_div, Real.log_div hνPos.ne' hLawPos.ne', hLogPriorRatio, hLogLaw]
      ring
    calc
      (observerClassGibbsIGapContribution U π t h ω β γ ν c).toReal
          = (observerClassGibbsLaw U π t h ω β γ c).toReal *
              InformationTheory.klFun
                ((ν c / observerClassGibbsLaw U π t h ω β γ c).toReal) := hIGapToReal
      _ = (observerClassGibbsLaw U π t h ω β γ c).toReal *
            (((ν c / observerClassGibbsLaw U π t h ω β γ c).toReal) *
              Real.log ((ν c / observerClassGibbsLaw U π t h ω β γ c).toReal)
              + 1 - (ν c / observerClassGibbsLaw U π t h ω β γ c).toReal) := by
              rw [InformationTheory.klFun_apply]
      _ = (ν c).toReal *
            Real.log ((ν c / observerClassGibbsLaw U π t h ω β γ c).toReal)
            + (observerClassGibbsLaw U π t h ω β γ c).toReal - (ν c).toReal := by
              rw [hRatioLaw]
              field_simp [hLawPos.ne']
      _ = (ν c).toReal *
            (Real.log ((ν c / observerClassPriorWeight U ω c).toReal)
              - (β / γ) * observerClassScore U π t h ω c
              + Real.log (observerClassGibbsPartition U π t h ω β γ).toReal)
            + (observerClassGibbsLaw U π t h ω β γ c).toReal - (ν c).toReal := by
              rw [hLogLawRatio]
      _ = observerClassPriorKLDivergenceContribution U ω ν c
            - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c
            + (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal
            + (observerClassGibbsLaw U π t h ω β γ c).toReal - (ν c).toReal := by
              simp [observerClassPriorKLDivergenceContribution,
                observerClassExpectedScoreContribution, hνc]
              ring

/--
Exact class-side Gibbs variational identity:
`γ D_I(ν || ν_G) = γ KL(ν || \bar w^ω) - β E_ν[G] + γ log Z_G`.
-/
theorem observerClassGibbs_variational_igap
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {ν : ω.Ω → ENNReal}
    (hν : ObserverClassAdmissibleAt U π t h ω ν)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    γ * (observerClassGibbsIGap U π t h ω β γ ν).toReal =
      γ * observerClassPriorKLDivergence U ω ν
        - β * observerClassExpectedScore U π t h ω ν
        + γ * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal := by
  have hLawSummable :
      Summable (fun c : ω.Ω => (observerClassGibbsLaw U π t h ω β γ c).toReal) := by
    exact ENNReal.summable_toReal (by
      simpa [observerClassGibbsLaw_tsum_eq_one U π t h ω β γ hq hβ hγ])
  have hνSummable :
      Summable (fun c : ω.Ω => (ν c).toReal) := by
    exact ENNReal.summable_toReal (by simpa [hν.normalized])
  have hConstSummable :
      Summable (fun c : ω.Ω =>
        (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal) := by
    exact hνSummable.mul_right _
  have hGapSummable :
      Summable (fun c : ω.Ω => (observerClassGibbsIGapContribution U π t h ω β γ ν c).toReal) := by
    have hRhs :
        Summable
          (fun c : ω.Ω =>
            observerClassPriorKLDivergenceContribution U ω ν c
              - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c
              + (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal
              + (observerClassGibbsLaw U π t h ω β γ c).toReal
              - (ν c).toReal) := by
      exact ((hν.summable_priorKLDivergence.sub
        (hν.summable_expectedScore.mul_left (β / γ))).add hConstSummable).add hLawSummable |>.sub hνSummable
    exact hRhs.congr
      (fun c => (observerClassGibbsIGap_term_identity U π t h ω β γ hq hν hβ hγ c).symm)
  have hGapToReal :
      (observerClassGibbsIGap U π t h ω β γ ν).toReal =
        ∑' c : ω.Ω, (observerClassGibbsIGapContribution U π t h ω β γ ν c).toReal := by
    rw [observerClassGibbsIGap]
    exact ENNReal.tsum_toReal_eq
      (fun c => observerClassGibbsIGapContribution_ne_top U π t h ω β γ hq hν hβ hγ c)
  have hABSumm :
      Summable
        (fun c : ω.Ω =>
          observerClassPriorKLDivergenceContribution U ω ν c
            - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c) := by
    exact hν.summable_priorKLDivergence.sub
      (hν.summable_expectedScore.mul_left (β / γ))
  have hDeltaSumm :
      Summable
        (fun c : ω.Ω =>
          (observerClassGibbsLaw U π t h ω β γ c).toReal - (ν c).toReal) := by
    exact hLawSummable.sub hνSummable
  have hASum :
      ∑' c : ω.Ω,
        (observerClassPriorKLDivergenceContribution U ω ν c
          - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c)
        =
          observerClassPriorKLDivergence U ω ν
            - (β / γ) * observerClassExpectedScore U π t h ω ν := by
    have hScoreMul :
        ∑' b : ω.Ω, (β / γ) * observerClassExpectedScoreContribution U π t h ω ν b =
          (β / γ) * ∑' b : ω.Ω, observerClassExpectedScoreContribution U π t h ω ν b := by
      simpa using (hν.summable_expectedScore.tsum_mul_left (β / γ))
    rw [hν.summable_priorKLDivergence.tsum_sub
      (hν.summable_expectedScore.mul_left (β / γ))]
    rw [hScoreMul]
    simp [observerClassPriorKLDivergence, observerClassExpectedScore]
  have hConst :
      ∑' c : ω.Ω,
        (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal
        =
          Real.log (observerClassGibbsPartition U π t h ω β γ).toReal := by
    rw [hνSummable.tsum_mul_right, observerClassLaw_toReal_tsum_eq_one U π t h ω hν]
    ring
  have hDelta :
      ∑' c : ω.Ω,
        ((observerClassGibbsLaw U π t h ω β γ c).toReal - (ν c).toReal) = 0 := by
    rw [Summable.tsum_sub hLawSummable hνSummable,
      observerClassGibbsLaw_toReal_tsum_eq_one U π t h ω β γ hq hβ hγ,
      observerClassLaw_toReal_tsum_eq_one U π t h ω hν]
    ring
  have hGapIdentity :
      (observerClassGibbsIGap U π t h ω β γ ν).toReal =
        observerClassPriorKLDivergence U ω ν
          - (β / γ) * observerClassExpectedScore U π t h ω ν
          + Real.log (observerClassGibbsPartition U π t h ω β γ).toReal := by
    calc
      (observerClassGibbsIGap U π t h ω β γ ν).toReal
          = ∑' c : ω.Ω, (observerClassGibbsIGapContribution U π t h ω β γ ν c).toReal := by
              rw [hGapToReal]
      _ = ∑' c : ω.Ω,
            (observerClassPriorKLDivergenceContribution U ω ν c
              - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c
              + (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal
              + (observerClassGibbsLaw U π t h ω β γ c).toReal
              - (ν c).toReal) := by
                apply tsum_congr
                intro c
                exact observerClassGibbsIGap_term_identity U π t h ω β γ hq hν hβ hγ c
      _ = ∑' c : ω.Ω,
            ((observerClassPriorKLDivergenceContribution U ω ν c
              - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c)
              + ((ν c).toReal
                  * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal)
              + ((observerClassGibbsLaw U π t h ω β γ c).toReal - (ν c).toReal)) := by
                apply tsum_congr
                intro c
                ring
      _ = (∑' c : ω.Ω,
            (observerClassPriorKLDivergenceContribution U ω ν c
              - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c))
            + (∑' c : ω.Ω,
                (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal)
            + (∑' c : ω.Ω,
                ((observerClassGibbsLaw U π t h ω β γ c).toReal - (ν c).toReal)) := by
              rw [((hABSumm.add hConstSummable).tsum_add hDeltaSumm)]
              rw [hABSumm.tsum_add hConstSummable]
      _ = observerClassPriorKLDivergence U ω ν
            - (β / γ) * observerClassExpectedScore U π t h ω ν
            + Real.log (observerClassGibbsPartition U π t h ω β γ).toReal := by
              rw [hASum, hConst, hDelta]
              ring
  calc
    γ * (observerClassGibbsIGap U π t h ω β γ ν).toReal
        = γ *
            (observerClassPriorKLDivergence U ω ν
              - (β / γ) * observerClassExpectedScore U π t h ω ν
              + Real.log (observerClassGibbsPartition U π t h ω β γ).toReal) := by
                rw [hGapIdentity]
    _ = γ * observerClassPriorKLDivergence U ω ν
          - β * observerClassExpectedScore U π t h ω ν
          + γ * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal := by
            field_simp [hγ.ne']

theorem observerClassGibbsIGap_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {ν : ω.Ω → ENNReal}
    (hν : ObserverClassAdmissibleAt U π t h ω ν)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    observerClassGibbsIGap U π t h ω β γ ν ≠ ⊤ := by
  have hLawSummable :
      Summable (fun c : ω.Ω => (observerClassGibbsLaw U π t h ω β γ c).toReal) := by
    exact ENNReal.summable_toReal (by
      simpa [observerClassGibbsLaw_tsum_eq_one U π t h ω β γ hq hβ hγ])
  have hνSummable :
      Summable (fun c : ω.Ω => (ν c).toReal) := by
    exact ENNReal.summable_toReal (by simpa [hν.normalized])
  have hConstSummable :
      Summable (fun c : ω.Ω =>
        (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal) := by
    exact hνSummable.mul_right _
  have hGapSummable :
      Summable (fun c : ω.Ω => (observerClassGibbsIGapContribution U π t h ω β γ ν c).toReal) := by
    have hRhs :
        Summable
          (fun c : ω.Ω =>
            observerClassPriorKLDivergenceContribution U ω ν c
              - (β / γ) * observerClassExpectedScoreContribution U π t h ω ν c
              + (ν c).toReal * Real.log (observerClassGibbsPartition U π t h ω β γ).toReal
              + (observerClassGibbsLaw U π t h ω β γ c).toReal
              - (ν c).toReal) := by
      exact ((hν.summable_priorKLDivergence.sub
        (hν.summable_expectedScore.mul_left (β / γ))).add hConstSummable).add hLawSummable |>.sub hνSummable
    exact hRhs.congr
      (fun c => (observerClassGibbsIGap_term_identity U π t h ω β γ hq hν hβ hγ c).symm)
  have hEq :
      observerClassGibbsIGap U π t h ω β γ ν =
        ∑' c : ω.Ω, ENNReal.ofReal
          ((observerClassGibbsIGapContribution U π t h ω β γ ν c).toReal) := by
    rw [observerClassGibbsIGap]
    apply tsum_congr
    intro c
    rw [ENNReal.ofReal_toReal
      (observerClassGibbsIGapContribution_ne_top U π t h ω β γ hq hν hβ hγ c)]
  rw [hEq]
  exact hGapSummable.tsum_ofReal_ne_top

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
  observerClassScoreOnTargets U π t h ω pstar

/-- Reference mass on a finite target-action chart induced by `\bar w^{\omega_A} ⊗ \lambda`. -/
def countableKernelReferenceWeightOnTargets_legacy
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
    countableKernelReferenceWeightOnTargets_legacy (A := A) (O := O) ω targets refLaw pstar a ≠ ⊤ := by
  unfold countableKernelReferenceWeightOnTargets_legacy
  refine ENNReal.mul_ne_top ?_ ?_
  · exact observerClassReferenceWeightOnTargets_ne_top
      (A := A) (O := O) ω targets pstar
  · simp [ratToENNReal]

/--
Finite-chart Gibbs weight for the kernel lift: target-class reference mass times reference
action mass, tilted by the capped target score.
-/
def countableKernelGibbsWeightOnTargets_legacy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) : ENNReal :=
  countableKernelReferenceWeightOnTargets_legacy (A := A) (O := O) ω targets refLaw pstar a *
    ENNReal.ofReal (Real.exp (kernelActionScoreOnTargets U π t h ω pstar a).toReal)

theorem countableKernelGibbsWeightOnTargets_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) :
    countableKernelGibbsWeightOnTargets_legacy U π t h ω targets refLaw pstar a ≠ ⊤ := by
  unfold countableKernelGibbsWeightOnTargets_legacy
  refine ENNReal.mul_ne_top ?_ ?_
  · exact countableKernelReferenceWeightOnTargets_ne_top
      (A := A) (O := O) ω targets refLaw pstar a
  · simp

/-- Agreement of two joint target-action weights on the designated finite chart. -/
def agreesWithOnTargetActions_legacy
    (targets : List (CountableEncodedProgram A O))
    (actions : List A)
    (κ₁ κ₂ : CountableEncodedProgram A O → A → ENNReal) : Prop :=
  ∀ p, p ∈ targets → ∀ a, a ∈ actions → κ₁ p a = κ₂ p a

/--
Per-chart Gibbs-mismatch term entering the kernel lift: the proposed joint class-action
weight at `(pstar, a)` is compared against the finite-chart Gibbs kernel.
-/
def def_raw_kernel_functional_legacy
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
    (countableKernelGibbsWeightOnTargets_legacy U π t h ωA targets refLaw pstar a)

/-- Lean wrapper for `def:kernel-functional` on the countable functional stack. -/
def def_kernel_functional_legacy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (q : U.Program → ENNReal)
    (targets : List (CountableEncodedProgram A O))
    (actions : List A)
    (κ : CountableEncodedProgram A O → A → ENNReal)
    (refLaw : ActionLaw A) : ENNReal :=
  def_afe_legacy U π t h q +
    listSumENNReal targets
      (fun pstar =>
        listSumENNReal actions
          (fun a => def_raw_kernel_functional_legacy U π t h ωB ωA q κ targets refLaw pstar a))

/-- Lean wrapper for `def:meeting-point-shorthand` on the countable functional stack. -/
def def_meeting_point_shorthand_legacy
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
  (def_bhat_omega_legacy U π t h ωA pstar,
   def_two_observer_functional_legacy U π t h ωB ωA q ν targets,
   def_kernel_functional_legacy U π t h ωB ωA q targets actions κ refLaw)

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
theorem prop_two_observer_minimizer_legacy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O)) :
    def_two_observer_functional_legacy U π t h ωB ωA
      (fun p => U.posteriorWeight π t h p)
      (observerClassGibbsWeightOnTargets U π t h ωA targets)
      targets = 0 ∧
    ∀ q ν,
      def_two_observer_functional_legacy U π t h ωB ωA q ν targets = 0 ↔
        samePosteriorWeights U π t h q ∧
        agreesWithOnTargets targets ν
          (observerClassGibbsWeightOnTargets U π t h ωA targets) := by
  constructor
  · have hAFE0 :
        def_afe_legacy U π t h (fun p => U.posteriorWeight π t h p) = 0 :=
      (def_afe_eq_zero_iff_samePosteriorWeights U π t h
        (fun p => U.posteriorWeight π t h p)).2
          (posteriorWeight_samePosteriorWeights U π t h)
    have hRaw0 :
        listSumENNReal targets
          (fun pstar =>
            def_raw_two_observer_functional_legacy U π t h ωB ωA
              (fun p => U.posteriorWeight π t h p)
              (observerClassGibbsWeightOnTargets U π t h ωA targets)
              targets pstar) = 0 := by
      refine (listSumENNReal_eq_zero_iff targets ?_).2 ?_
      intro p hp
      exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
          (observerClassGibbsWeightOnTargets_ne_top U π t h ωA targets p)).2 rfl
    simpa [def_two_observer_functional_legacy, hAFE0, hRaw0]
  · intro q ν
    constructor
    · intro hZero
      have hParts :
          def_afe_legacy U π t h q = 0 ∧
            listSumENNReal targets
              (fun pstar =>
                def_raw_two_observer_functional_legacy U π t h ωB ωA q ν targets pstar) = 0 := by
        simpa [def_two_observer_functional_legacy] using (add_eq_zero.mp hZero)
      refine ⟨samePosteriorWeights_of_def_afe_eq_zero U π t h q hParts.1, ?_⟩
      intro p hp
      have hTermZero :=
        (listSumENNReal_eq_zero_iff targets
          (fun pstar => def_raw_two_observer_functional_legacy U π t h ωB ωA q ν targets pstar)).mp
            hParts.2 p hp
      exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
          (observerClassGibbsWeightOnTargets_ne_top U π t h ωA targets p)).mp
            (by simpa [def_raw_two_observer_functional_legacy] using hTermZero)
    · rintro ⟨hq, hν⟩
      have hAFE0 : def_afe_legacy U π t h q = 0 :=
        (def_afe_eq_zero_iff_samePosteriorWeights U π t h q).2 hq
      have hRaw0 :
          listSumENNReal targets
            (fun pstar =>
              def_raw_two_observer_functional_legacy U π t h ωB ωA q ν targets pstar) = 0 := by
        refine (listSumENNReal_eq_zero_iff targets ?_).2 ?_
        intro p hp
        exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
            (observerClassGibbsWeightOnTargets_ne_top U π t h ωA targets p)).2
              (hν p hp)
      simpa [def_two_observer_functional_legacy, hAFE0, hRaw0]

/-- Lean wrapper for `prop:kernel-functional-minimizer` on the countable functional stack. -/
theorem prop_kernel_functional_minimizer_legacy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (actions : List A)
    (refLaw : ActionLaw A) :
    def_kernel_functional_legacy U π t h ωB ωA
      (fun p => U.posteriorWeight π t h p)
      targets actions
      (countableKernelGibbsWeightOnTargets_legacy U π t h ωA targets refLaw)
      refLaw = 0 ∧
    ∀ q κ,
      def_kernel_functional_legacy U π t h ωB ωA q targets actions κ refLaw = 0 ↔
        samePosteriorWeights U π t h q ∧
        agreesWithOnTargetActions_legacy targets actions κ
          (countableKernelGibbsWeightOnTargets_legacy U π t h ωA targets refLaw) := by
  constructor
  · have hAFE0 :
        def_afe_legacy U π t h (fun p => U.posteriorWeight π t h p) = 0 :=
      (def_afe_eq_zero_iff_samePosteriorWeights U π t h
        (fun p => U.posteriorWeight π t h p)).2
          (posteriorWeight_samePosteriorWeights U π t h)
    have hKernel0 :
        listSumENNReal targets
          (fun pstar =>
            listSumENNReal actions
                  (fun a =>
                    def_raw_kernel_functional_legacy U π t h ωB ωA
                      (fun p => U.posteriorWeight π t h p)
                      (countableKernelGibbsWeightOnTargets_legacy U π t h ωA targets refLaw)
                      targets refLaw pstar a)) = 0 := by
      refine (listSumENNReal_eq_zero_iff targets ?_).2 ?_
      intro p hp
      refine (listSumENNReal_eq_zero_iff actions ?_).2 ?_
      intro a ha
      exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
        (countableKernelGibbsWeightOnTargets_ne_top U π t h ωA targets refLaw p a)).2 rfl
    simpa [def_kernel_functional_legacy, hAFE0, hKernel0]
  · intro q κ
    constructor
    · intro hZero
      have hParts :
          def_afe_legacy U π t h q = 0 ∧
            listSumENNReal targets
              (fun pstar =>
                listSumENNReal actions
                  (fun a =>
                    def_raw_kernel_functional_legacy U π t h ωB ωA q κ
                      targets refLaw pstar a)) = 0 := by
        simpa [def_kernel_functional_legacy] using (add_eq_zero.mp hZero)
      refine ⟨samePosteriorWeights_of_def_afe_eq_zero U π t h q hParts.1, ?_⟩
      intro p hp a ha
      have hpZero :=
        (listSumENNReal_eq_zero_iff targets
          (fun pstar =>
            listSumENNReal actions
              (fun a =>
                def_raw_kernel_functional_legacy U π t h ωB ωA q κ
                  targets refLaw pstar a))).mp hParts.2 p hp
      have hpaZero :=
        (listSumENNReal_eq_zero_iff actions
          (fun a =>
            def_raw_kernel_functional_legacy U π t h ωB ωA q κ
              targets refLaw p a)).mp hpZero a ha
      exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
          (countableKernelGibbsWeightOnTargets_ne_top U π t h ωA targets refLaw p a)).mp
            (by simpa [def_raw_kernel_functional_legacy] using hpaZero)
    · rintro ⟨hq, hκ⟩
      have hAFE0 : def_afe_legacy U π t h q = 0 :=
        (def_afe_eq_zero_iff_samePosteriorWeights U π t h q).2 hq
      have hKernel0 :
          listSumENNReal targets
            (fun pstar =>
              listSumENNReal actions
                (fun a =>
                  def_raw_kernel_functional_legacy U π t h ωB ωA q κ
                    targets refLaw pstar a)) = 0 := by
        refine (listSumENNReal_eq_zero_iff targets ?_).2 ?_
        intro p hp
        refine (listSumENNReal_eq_zero_iff actions ?_).2 ?_
        intro a ha
        exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
            (countableKernelGibbsWeightOnTargets_ne_top U π t h ωA targets refLaw p a)).2
              (hκ p hp a ha)
      simpa [def_kernel_functional_legacy, hAFE0, hKernel0]

/-- Lean wrapper for `prop:kernel-functional-minimizer-compact` on the countable functional stack. -/
theorem prop_kernel_functional_minimizer_compact_legacy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A) :
    let actionChart := refLaw.support.eraseDups
    def_kernel_functional_legacy U π t h ωB ωA
      (fun p => U.posteriorWeight π t h p)
      targets actionChart
      (countableKernelGibbsWeightOnTargets_legacy U π t h ωA targets refLaw)
      refLaw = 0 ∧
    ∀ q κ,
      def_kernel_functional_legacy U π t h ωB ωA q targets actionChart κ refLaw = 0 ↔
        samePosteriorWeights U π t h q ∧
        agreesWithOnTargetActions_legacy targets actionChart κ
          (countableKernelGibbsWeightOnTargets_legacy U π t h ωA targets refLaw) := by
  simpa using
    (prop_kernel_functional_minimizer_legacy U π t h ωB ωA targets refLaw.support.eraseDups refLaw)

/-- Lean wrapper for `prop:belief-illtyped-below` on the countable functional stack. -/
theorem prop_belief_illtyped_below
    {ωB : Observer (CountableEncodedProgram A O)}
    {pstar : CountableEncodedProgram A O}
    (_hBelow : ActionAdmissible (A := A) (O := O) ωB)
    (hNotAbove : ¬ BeliefAdmissible (A := A) (O := O) ωB) :
    ¬ goalDialConverges (A := A) (O := O) ωB pstar :=
  hNotAbove

/-- Lean wrapper for `prop:action-cap` on the countable functional stack. -/
theorem prop_action_cap_legacy
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωA : Observer (CountableEncodedProgram A O))
    (targets : List (CountableEncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : CountableEncodedProgram A O) (a : A) :
    countableKernelGibbsWeightOnTargets_legacy U π t h ωA targets refLaw pstar a ≤
      countableKernelReferenceWeightOnTargets_legacy (A := A) (O := O) ωA targets refLaw pstar a *
        ENNReal.ofReal (Real.exp 1) := by
  have hScoreLe : kernelActionScoreOnTargets U π t h ωA pstar a ≤ 1 := by
    unfold kernelActionScoreOnTargets observerClassScoreOnTargets
    exact min_le_left _ _
  unfold countableKernelGibbsWeightOnTargets_legacy
  have hExp :
      ENNReal.ofReal (Real.exp (kernelActionScoreOnTargets U π t h ωA pstar a).toReal) ≤
        ENNReal.ofReal (Real.exp 1) := by
    exact ENNReal.ofReal_le_ofReal (by
      exact Real.exp_le_exp.mpr (by
        exact ENNReal.toReal_mono (by simp) hScoreLe))
  exact mul_le_mul_of_nonneg_left hExp bot_le

section ExactKernelVariational

variable (A)

/--
Possibly sparse finite-action reference law `λ` for the exact kernel lift.

This is the right admissibility surface for constrained Gibbs rules: the
reference law is normalized and nonnegative, but may assign zero mass to
actions outside a feasible/safe set.
-/
structure KernelReferenceLawMassAdmissible
    [Fintype A] (refLaw : ActionLaw A) : Prop where
  normalized : (∑ a : A, ratToENNReal (refLaw.mass a)) = 1
  nonneg : ∀ a : A, 0 ≤ refLaw.mass a

/-- Full-support finite-action reference law retained for unrestricted Gibbs/no-go results. -/
structure KernelReferenceLawAdmissible
    [Fintype A] (refLaw : ActionLaw A) : Prop where
  normalized : (∑ a : A, ratToENNReal (refLaw.mass a)) = 1
  nonneg : ∀ a : A, 0 ≤ refLaw.mass a
  full_support : ∀ a : A, refLaw.mass a ≠ 0

variable {A}

namespace KernelReferenceLawAdmissible

omit [Encodable A] [DecidableEq A] [BEq A] [LawfulBEq A] in
/-- A full-support reference is, in particular, a possibly sparse admissible reference. -/
theorem toMassAdmissible
    [Fintype A] {refLaw : ActionLaw A}
    (href : KernelReferenceLawAdmissible (A := A) refLaw) :
    KernelReferenceLawMassAdmissible (A := A) refLaw :=
  ⟨href.normalized, href.nonneg⟩

end KernelReferenceLawAdmissible

/-- Exact product reference mass `(\\bar w^{ω_A} \\otimes λ)(c,a)`. -/
def kernelReferenceWeight
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (refLaw : ActionLaw A)
    (c : ω.Ω) (a : A) : ENNReal :=
  observerClassPriorWeight U ω c * ratToENNReal (refLaw.mass a)

/-- Exact capped class-action score `\\bar B_t^{ω_A}(c,a;h_t)` supplied to the kernel lift. -/
abbrev KernelScore
    (ω : Observer (CountableEncodedProgram A O)) : Type _ :=
  ω.Ω → A → Real

/-- Exact expected kernel score contribution `(κ(c,a)) \\bar B(c,a)`. -/
def kernelExpectedScoreContribution
    {ω : Observer (CountableEncodedProgram A O)}
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (Bbar : KernelScore (A := A) (O := O) ω)
    (κ : ω.Ω → A → ENNReal)
    (ca : ω.Ω × A) : Real :=
  (κ ca.1 ca.2).toReal * Bbar ca.1 ca.2

/-- Exact expected kernel score `E_{(C,A)∼κ}[\\bar B_t^{ω_A}(C,A;h_t)]`. -/
def kernelExpectedScore
    {ω : Observer (CountableEncodedProgram A O)}
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (Bbar : KernelScore (A := A) (O := O) ω)
    (κ : ω.Ω → A → ENNReal) : Real :=
  ∑' ca : ω.Ω × A, kernelExpectedScoreContribution Bbar κ ca

/-- Pointwise KL contribution against the exact product reference law `\\bar w^{ω_A} ⊗ λ`. -/
def kernelPriorKLDivergenceContribution
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (refLaw : ActionLaw A)
    (κ : ω.Ω → A → ENNReal)
    (ca : ω.Ω × A) : Real :=
  if hκ : κ ca.1 ca.2 = 0 then
    0
  else
    (κ ca.1 ca.2).toReal *
      Real.log ((κ ca.1 ca.2 / kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal)

/-- Exact regularizer `KL(κ || \\bar w^{ω_A} ⊗ λ)`. -/
def kernelPriorKLDivergence
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (refLaw : ActionLaw A)
    (κ : ω.Ω → A → ENNReal) : Real :=
  ∑' ca : ω.Ω × A, kernelPriorKLDivergenceContribution U ω refLaw κ ca

/-- Admissible exact kernel laws on `C^{ω_A} × A`. -/
structure KernelLawAdmissibleAt
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (refLaw : ActionLaw A)
    (κ : ω.Ω → A → ENNReal) : Prop where
  normalized : ∑' ca : ω.Ω × A, κ ca.1 ca.2 = 1
  vanishes_on_zero_reference :
    ∀ c : ω.Ω, ∀ a : A, kernelReferenceWeight U ω refLaw c a = 0 → κ c a = 0
  summable_priorKLDivergence :
    Summable (fun ca : ω.Ω × A => kernelPriorKLDivergenceContribution U ω refLaw κ ca)

private theorem kernelLaw_ne_top_of_admissible
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (refLaw : ActionLaw A)
    {κ : ω.Ω → A → ENNReal}
    (hκ : KernelLawAdmissibleAt U ω refLaw κ)
    (ca : ω.Ω × A) :
    κ ca.1 ca.2 ≠ ⊤ := by
  have hle : κ ca.1 ca.2 ≤ 1 := by
    calc
      κ ca.1 ca.2 ≤ ∑' x : ω.Ω × A, κ x.1 x.2 := ENNReal.le_tsum ca
      _ = 1 := hκ.normalized
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

private theorem kernelLaw_toReal_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (refLaw : ActionLaw A)
    {κ : ω.Ω → A → ENNReal}
    (hκ : KernelLawAdmissibleAt U ω refLaw κ) :
    ∑' ca : ω.Ω × A, (κ ca.1 ca.2).toReal = 1 := by
  calc
    ∑' ca : ω.Ω × A, (κ ca.1 ca.2).toReal
        = (∑' ca : ω.Ω × A, κ ca.1 ca.2).toReal := by
            exact (ENNReal.tsum_toReal_eq
              (fun ca => kernelLaw_ne_top_of_admissible U ω refLaw hκ ca)).symm
    _ = 1 := by simpa [hκ.normalized]

theorem kernelReferenceWeight_ne_top
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (refLaw : ActionLaw A)
    (c : ω.Ω) (a : A) :
    kernelReferenceWeight U ω refLaw c a ≠ ⊤ := by
  unfold kernelReferenceWeight
  refine ENNReal.mul_ne_top ?_ ?_
  · exact observerClassPriorWeight_ne_top U ω hq c
  · simp [ratToENNReal]

private theorem kernelReferenceWeight_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw) :
    ∑' ca : ω.Ω × A, kernelReferenceWeight U ω refLaw ca.1 ca.2 = 1 := by
  rw [ENNReal.tsum_prod]
  calc
    ∑' c : ω.Ω, ∑' a : A, kernelReferenceWeight U ω refLaw c a
        = ∑' c : ω.Ω, observerClassPriorWeight U ω c * (∑ a : A, ratToENNReal (refLaw.mass a)) := by
            apply tsum_congr
            intro c
            rw [tsum_fintype]
            simp [kernelReferenceWeight, Finset.mul_sum]
    _ = ∑' c : ω.Ω, observerClassPriorWeight U ω c := by
          simp [href.normalized]
    _ = 1 := observerClassPriorWeight_tsum_eq_one U ω hq

/-- Exact Gibbs weight on the joint class-action domain. -/
def kernelGibbsWeight
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (c : ω.Ω) (a : A) : ENNReal :=
  kernelReferenceWeight U ω refLaw c a *
    ENNReal.ofReal (Real.exp ((β / γ) * Bbar c a))

/-- Exact Gibbs partition function on `C^{ω_A} × A`. -/
def kernelGibbsPartition
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A) : ENNReal :=
  ∑' ca : ω.Ω × A, kernelGibbsWeight U ω β γ Bbar refLaw ca.1 ca.2

/-- Exact Gibbs kernel law from the manuscript's kernel variational proposition. -/
def kernelGibbsLaw
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (c : ω.Ω) (a : A) : ENNReal :=
  kernelGibbsWeight U ω β γ Bbar refLaw c a /
    kernelGibbsPartition U ω β γ Bbar refLaw

/-- Exact generalized I-gap against the Gibbs kernel. -/
def kernelGibbsIGapContribution
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (κ : ω.Ω → A → ENNReal)
    (ca : ω.Ω × A) : ENNReal :=
  posteriorWeightKLDivergenceTerm (κ ca.1 ca.2)
    (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2)

/-- Total exact generalized I-gap to the Gibbs kernel. -/
def kernelGibbsIGap
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (κ : ω.Ω → A → ENNReal) : ENNReal :=
  ∑' ca : ω.Ω × A, kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca

private theorem kernelGibbsWeight_ne_top
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (refLaw : ActionLaw A)
    (c : ω.Ω) (a : A) :
    kernelGibbsWeight U ω β γ Bbar refLaw c a ≠ ⊤ := by
  unfold kernelGibbsWeight
  refine ENNReal.mul_ne_top ?_ ?_
  · exact kernelReferenceWeight_ne_top U ω hq refLaw c a
  · simp

private theorem kernelGibbsWeight_ge_reference
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (refLaw : ActionLaw A)
    (c : ω.Ω) (a : A) :
    kernelReferenceWeight U ω refLaw c a ≤ kernelGibbsWeight U ω β γ Bbar refLaw c a := by
  have hExp : (1 : Real) ≤ Real.exp ((β / γ) * Bbar c a) := by
    apply Real.one_le_exp
    exact mul_nonneg (div_nonneg hβ hγ.le) (hBbar_nonneg c a)
  have hExpENN : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp ((β / γ) * Bbar c a)) := by
    simpa using ENNReal.ofReal_le_ofReal hExp
  calc
    kernelReferenceWeight U ω refLaw c a
        = kernelReferenceWeight U ω refLaw c a * 1 := by simp
    _ ≤ kernelReferenceWeight U ω refLaw c a *
          ENNReal.ofReal (Real.exp ((β / γ) * Bbar c a)) := by
            exact mul_le_mul_left' hExpENN _
    _ = kernelGibbsWeight U ω β γ Bbar refLaw c a := by
          simp [kernelGibbsWeight]

private theorem kernelGibbsWeight_le_scaled_reference
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (refLaw : ActionLaw A)
    (c : ω.Ω) (a : A) :
    kernelGibbsWeight U ω β γ Bbar refLaw c a ≤
      kernelReferenceWeight U ω refLaw c a * ENNReal.ofReal (Real.exp (β / γ)) := by
  have hScaleNonneg : 0 ≤ β / γ := div_nonneg hβ hγ.le
  have hMulLe : (β / γ) * Bbar c a ≤ β / γ := by
    nlinarith [hScaleNonneg, hBbar_nonneg c a, hBbar_le_one c a]
  have hExpLe :
      Real.exp ((β / γ) * Bbar c a) ≤ Real.exp (β / γ) := Real.exp_le_exp.mpr hMulLe
  have hExpENN :
      ENNReal.ofReal (Real.exp ((β / γ) * Bbar c a)) ≤
        ENNReal.ofReal (Real.exp (β / γ)) := ENNReal.ofReal_le_ofReal hExpLe
  unfold kernelGibbsWeight
  exact mul_le_mul_left' hExpENN _

private theorem kernelGibbsPartition_ne_top
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    kernelGibbsPartition U ω β γ Bbar refLaw ≠ ⊤ := by
  have hle :
      kernelGibbsPartition U ω β γ Bbar refLaw ≤ ENNReal.ofReal (Real.exp (β / γ)) := by
    calc
      kernelGibbsPartition U ω β γ Bbar refLaw
          = ∑' ca : ω.Ω × A, kernelGibbsWeight U ω β γ Bbar refLaw ca.1 ca.2 := rfl
      _ ≤ ∑' ca : ω.Ω × A,
            kernelReferenceWeight U ω refLaw ca.1 ca.2 * ENNReal.ofReal (Real.exp (β / γ)) :=
          ENNReal.tsum_le_tsum
            (fun ca => kernelGibbsWeight_le_scaled_reference U ω β γ Bbar
              hBbar_nonneg hBbar_le_one hβ hγ refLaw ca.1 ca.2)
      _ = (∑' ca : ω.Ω × A, kernelReferenceWeight U ω refLaw ca.1 ca.2) *
            ENNReal.ofReal (Real.exp (β / γ)) := by
              simpa using
                (ENNReal.tsum_mul_right
                  (f := fun ca : ω.Ω × A => kernelReferenceWeight U ω refLaw ca.1 ca.2)
                  (a := ENNReal.ofReal (Real.exp (β / γ))))
      _ = ENNReal.ofReal (Real.exp (β / γ)) := by
            rw [kernelReferenceWeight_tsum_eq_one U ω hq href, one_mul]
  exact ne_of_lt (lt_of_le_of_lt hle (by simp))

private theorem kernelGibbsPartition_pos
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    0 < kernelGibbsPartition U ω β γ Bbar refLaw := by
  have hOneLe :
      1 ≤ kernelGibbsPartition U ω β γ Bbar refLaw := by
    calc
      1 = ∑' ca : ω.Ω × A, kernelReferenceWeight U ω refLaw ca.1 ca.2 := by
            rw [kernelReferenceWeight_tsum_eq_one U ω hq href]
      _ ≤ ∑' ca : ω.Ω × A, kernelGibbsWeight U ω β γ Bbar refLaw ca.1 ca.2 :=
          ENNReal.tsum_le_tsum
            (fun ca => kernelGibbsWeight_ge_reference U ω β γ Bbar
              hBbar_nonneg hβ hγ refLaw ca.1 ca.2)
      _ = kernelGibbsPartition U ω β γ Bbar refLaw := rfl
  exact lt_of_lt_of_le (by simp) hOneLe

private theorem kernelGibbsPartition_ne_zero
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    kernelGibbsPartition U ω β γ Bbar refLaw ≠ 0 :=
  (kernelGibbsPartition_pos U ω β γ Bbar hBbar_nonneg hq href hβ hγ).ne'

private theorem kernelGibbsLaw_ne_top
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (ca : ω.Ω × A) :
    kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2 ≠ ⊤ := by
  exact ENNReal.div_ne_top
    (kernelGibbsWeight_ne_top U ω β γ Bbar hq refLaw ca.1 ca.2)
    (kernelGibbsPartition_ne_zero U ω β γ Bbar hBbar_nonneg hq href hβ hγ)

private theorem kernelGibbsLaw_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    ∑' ca : ω.Ω × A, kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2 = 1 := by
  calc
    ∑' ca : ω.Ω × A, kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2
        = ∑' ca : ω.Ω × A,
            kernelGibbsWeight U ω β γ Bbar refLaw ca.1 ca.2 /
              kernelGibbsPartition U ω β γ Bbar refLaw := rfl
    _ = (∑' ca : ω.Ω × A, kernelGibbsWeight U ω β γ Bbar refLaw ca.1 ca.2) /
          kernelGibbsPartition U ω β γ Bbar refLaw := by
            simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ = 1 := by
          unfold kernelGibbsPartition
          exact ENNReal.div_self
            (kernelGibbsPartition_ne_zero U ω β γ Bbar hBbar_nonneg hq href hβ hγ)
            (kernelGibbsPartition_ne_top U ω β γ Bbar hBbar_nonneg hBbar_le_one hq href hβ hγ)

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/--
The product reference is nonzero at every action in a nonzero-prior observer class
under the current full-support reference-law hypothesis.
-/
theorem kernelReferenceWeight_ne_zero_of_prior_ne_zero_fullSupport
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawAdmissible (A := A) refLaw)
    {c : ω.Ω} {a : A}
    (hPrior : observerClassPriorWeight U ω c ≠ 0) :
    kernelReferenceWeight U ω refLaw c a ≠ 0 := by
  unfold kernelReferenceWeight
  refine mul_ne_zero hPrior ?_
  have hMassPosRat : (0 : Rat) < refLaw.mass a := by
    exact lt_of_le_of_ne (href.nonneg a) (by simpa [eq_comm] using href.full_support a)
  have hMassPosReal : (0 : ℝ) < refLaw.mass a := by
    exact_mod_cast hMassPosRat
  exact ENNReal.ofReal_ne_zero_iff.mpr hMassPosReal

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/-- Gibbs inherits zero support from the product reference. -/
theorem kernelGibbsLaw_eq_zero_of_kernelReferenceWeight_eq_zero
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    {c : ω.Ω} {a : A}
    (hRef : kernelReferenceWeight U ω refLaw c a = 0) :
    kernelGibbsLaw U ω β γ Bbar refLaw c a = 0 := by
  simp [kernelGibbsLaw, kernelGibbsWeight, hRef]

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/-- Gibbs assigns zero mass to every action with zero reference mass. -/
theorem kernelGibbsLaw_eq_zero_of_refLaw_mass_eq_zero
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    {c : ω.Ω} {a : A}
    (hMass : refLaw.mass a = 0) :
    kernelGibbsLaw U ω β γ Bbar refLaw c a = 0 := by
  apply kernelGibbsLaw_eq_zero_of_kernelReferenceWeight_eq_zero
  simp [kernelReferenceWeight, ratToENNReal, hMass]

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/-- Nonzero Gibbs mass at `(c,a)` forces nonzero reference mass on `a`. -/
theorem kernelGibbsLaw_ne_zero_refLaw_mass_ne_zero
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    {c : ω.Ω} {a : A}
    (hLaw : kernelGibbsLaw U ω β γ Bbar refLaw c a ≠ 0) :
    refLaw.mass a ≠ 0 := by
  intro hMass
  exact hLaw
    (kernelGibbsLaw_eq_zero_of_refLaw_mass_eq_zero
      U ω β γ Bbar refLaw hMass)

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/--
Sparse-reference support inheritance: if the reference law only supports actions
with property `Safe`, then the Gibbs law also only supports such actions.
-/
theorem kernelGibbsLaw_support_subset_refLaw_action_property
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (Safe : A → Prop)
    (hRefSafe : ∀ a : A, refLaw.mass a ≠ 0 → Safe a)
    {c : ω.Ω} {a : A}
    (hLaw : kernelGibbsLaw U ω β γ Bbar refLaw c a ≠ 0) :
    Safe a :=
  hRefSafe a
    (kernelGibbsLaw_ne_zero_refLaw_mass_ne_zero
      U ω β γ Bbar refLaw hLaw)

/-- Action marginal of the exact Gibbs kernel on `C^{ω_A} × A`. -/
def kernelGibbsActionMarginal
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (a : A) : ENNReal :=
  ∑' c : ω.Ω, kernelGibbsLaw U ω β γ Bbar refLaw c a

/-- Action marginal of an arbitrary exact kernel law on `C^{ω_A} × A`. -/
def kernelLawActionMarginal
    {ω : Observer (CountableEncodedProgram A O)}
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (κ : ω.Ω → A → ENNReal)
    (a : A) : ENNReal :=
  ∑' c : ω.Ω, κ c a

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/-- Pointwise equality with the Gibbs kernel identifies action marginals. -/
theorem kernelLawActionMarginal_eq_kernelGibbsActionMarginal_of_eq
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (κ : ω.Ω → A → ENNReal)
    (hEq :
      ∀ c : ω.Ω, ∀ a : A,
        κ c a = kernelGibbsLaw U ω β γ Bbar refLaw c a)
    (a : A) :
    kernelLawActionMarginal κ a =
      kernelGibbsActionMarginal U ω β γ Bbar refLaw a := by
  unfold kernelLawActionMarginal kernelGibbsActionMarginal
  exact tsum_congr (fun c => hEq c a)

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/-- The Gibbs action marginal assigns zero mass to actions outside the reference support. -/
theorem kernelGibbsActionMarginal_eq_zero_of_refLaw_mass_eq_zero
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    {a : A}
    (hMass : refLaw.mass a = 0) :
    kernelGibbsActionMarginal U ω β γ Bbar refLaw a = 0 := by
  unfold kernelGibbsActionMarginal
  simp [kernelGibbsLaw_eq_zero_of_refLaw_mass_eq_zero
    U ω β γ Bbar refLaw hMass]

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/-- Nonzero Gibbs action marginal mass forces nonzero reference mass on that action. -/
theorem kernelGibbsActionMarginal_ne_zero_refLaw_mass_ne_zero
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    {a : A}
    (hMarg : kernelGibbsActionMarginal U ω β γ Bbar refLaw a ≠ 0) :
    refLaw.mass a ≠ 0 := by
  intro hMass
  exact hMarg
    (kernelGibbsActionMarginal_eq_zero_of_refLaw_mass_eq_zero
      U ω β γ Bbar refLaw hMass)

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/--
Sparse-reference support inheritance for the Gibbs action marginal: if the
reference law only supports actions with property `Safe`, then the action
marginal also only supports such actions.
-/
theorem kernelGibbsActionMarginal_support_subset_refLaw_action_property
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (Safe : A → Prop)
    (hRefSafe : ∀ a : A, refLaw.mass a ≠ 0 → Safe a)
    {a : A}
    (hMarg : kernelGibbsActionMarginal U ω β γ Bbar refLaw a ≠ 0) :
    Safe a :=
  hRefSafe a
    (kernelGibbsActionMarginal_ne_zero_refLaw_mass_ne_zero
      U ω β γ Bbar refLaw hMarg)

omit [Encodable A] [Encodable O] [DecidableEq A] [BEq A] [LawfulBEq A] in
/--
Optimizer support inheritance: if an admissible kernel law is pointwise the
Gibbs kernel, then its action marginal inherits any action property supported
by the sparse reference law.
-/
theorem kernelLawActionMarginal_support_subset_refLaw_action_property_of_eq_gibbs
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    (refLaw : ActionLaw A)
    (κ : ω.Ω → A → ENNReal)
    (hEq :
      ∀ c : ω.Ω, ∀ a : A,
        κ c a = kernelGibbsLaw U ω β γ Bbar refLaw c a)
    (Safe : A → Prop)
    (hRefSafe : ∀ a : A, refLaw.mass a ≠ 0 → Safe a)
    {a : A}
    (hMarg : kernelLawActionMarginal κ a ≠ 0) :
    Safe a := by
  have hGibbsMarg :
      kernelGibbsActionMarginal U ω β γ Bbar refLaw a ≠ 0 := by
    have hMargEq :=
      kernelLawActionMarginal_eq_kernelGibbsActionMarginal_of_eq
        U ω β γ Bbar refLaw κ hEq a
    simpa [hMargEq] using hMarg
  exact
    kernelGibbsActionMarginal_support_subset_refLaw_action_property
      U ω β γ Bbar refLaw Safe hRefSafe hGibbsMarg

/-- The exact Gibbs action marginal is normalized whenever the joint Gibbs law is. -/
theorem kernelGibbsActionMarginal_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    ∑' a : A, kernelGibbsActionMarginal U ω β γ Bbar refLaw a = 1 := by
  calc
    ∑' a : A, kernelGibbsActionMarginal U ω β γ Bbar refLaw a
        = ∑' a : A, ∑' c : ω.Ω, kernelGibbsLaw U ω β γ Bbar refLaw c a := rfl
    _ = ∑' c : ω.Ω, ∑' a : A, kernelGibbsLaw U ω β γ Bbar refLaw c a := by
          rw [ENNReal.tsum_comm]
    _ = ∑' ca : ω.Ω × A, kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2 := by
          rw [ENNReal.tsum_prod]
    _ = 1 :=
          kernelGibbsLaw_tsum_eq_one U ω β γ Bbar hq href
            hBbar_nonneg hBbar_le_one hβ hγ

/--
Conversely, at finite positive partition, Gibbs has nonzero mass wherever the
product reference is nonzero. The exponential tilt cannot remove support.
-/
theorem kernelGibbsLaw_ne_zero_of_kernelReferenceWeight_ne_zero
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    {c : ω.Ω} {a : A}
    (hRef : kernelReferenceWeight U ω refLaw c a ≠ 0) :
    kernelGibbsLaw U ω β γ Bbar refLaw c a ≠ 0 := by
  have hWeight : kernelGibbsWeight U ω β γ Bbar refLaw c a ≠ 0 := by
    unfold kernelGibbsWeight
    refine mul_ne_zero hRef ?_
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  intro hLaw
  have hZeroOrTop := (ENNReal.div_eq_zero_iff).mp hLaw
  exact hZeroOrTop.elim hWeight
    (fun hTop =>
      (kernelGibbsPartition_ne_top U ω β γ Bbar hBbar_nonneg hBbar_le_one hq href hβ hγ)
        hTop)

/--
With the current full-support reference law, finite-temperature Gibbs gives
nonzero mass to every action in every nonzero-prior observer class.
-/
theorem kernelGibbsLaw_ne_zero_of_prior_ne_zero_fullSupport
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawAdmissible (A := A) refLaw)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    {c : ω.Ω} {a : A}
    (hPrior : observerClassPriorWeight U ω c ≠ 0) :
    kernelGibbsLaw U ω β γ Bbar refLaw c a ≠ 0 := by
  exact
    kernelGibbsLaw_ne_zero_of_kernelReferenceWeight_ne_zero
      U ω β γ Bbar hq href.toMassAdmissible hBbar_nonneg hBbar_le_one hβ hγ
      (kernelReferenceWeight_ne_zero_of_prior_ne_zero_fullSupport
        U ω href hPrior)

/--
No-go support lemma: if a full-support finite-temperature Gibbs law only supports
actions satisfying `Safe`, then every action must satisfy `Safe` in each
nonzero-prior observer class.

This is the formal obstruction for deriving a hard Hellinger-safe support
property from an unrestricted soft Gibbs rule.
-/
theorem kernelGibbs_fullSupport_forces_action_property
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawAdmissible (A := A) refLaw)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (Safe : A → Prop)
    (hSupportSafe :
      ∀ c : ω.Ω, ∀ a : A,
        kernelGibbsLaw U ω β γ Bbar refLaw c a ≠ 0 → Safe a)
    {c : ω.Ω}
    (hPrior : observerClassPriorWeight U ω c ≠ 0) :
    ∀ a : A, Safe a := by
  intro a
  exact hSupportSafe c a
    (kernelGibbsLaw_ne_zero_of_prior_ne_zero_fullSupport
      U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ hPrior)

/--
Contrapositive form of the no-go lemma: under the current full-support reference,
a single unsafe action rules out any claim that Gibbs support is contained in
`Safe`, provided some observer class has nonzero prior.
-/
theorem kernelGibbs_fullSupport_no_go_of_unsafe_action
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawAdmissible (A := A) refLaw)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (Safe : A → Prop)
    {c : ω.Ω} {a : A}
    (hPrior : observerClassPriorWeight U ω c ≠ 0)
    (hUnsafe : ¬ Safe a) :
    ¬ ∀ c : ω.Ω, ∀ a : A,
        kernelGibbsLaw U ω β γ Bbar refLaw c a ≠ 0 → Safe a := by
  intro hSupportSafe
  exact hUnsafe
    (kernelGibbs_fullSupport_forces_action_property
      U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ Safe hSupportSafe hPrior a)

private theorem kernelGibbsIGapContribution_ne_top
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    {κ : ω.Ω → A → ENNReal}
    (hκ : KernelLawAdmissibleAt U ω refLaw κ)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (ca : ω.Ω × A) :
    kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca ≠ ⊤ := by
  unfold kernelGibbsIGapContribution
  have hκTop : κ ca.1 ca.2 ≠ ⊤ := kernelLaw_ne_top_of_admissible U ω refLaw hκ ca
  by_cases hLaw : kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2 = 0
  · have hRefZero :
        kernelReferenceWeight U ω refLaw ca.1 ca.2 = 0 := by
          by_contra hRefNonzero
          have hWeightNonzero : kernelGibbsWeight U ω β γ Bbar refLaw ca.1 ca.2 ≠ 0 := by
            unfold kernelGibbsWeight
            refine mul_ne_zero hRefNonzero ?_
            exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
          have := (ENNReal.div_eq_zero_iff).mp hLaw
          exact this.elim hWeightNonzero
            (fun hTop =>
              (kernelGibbsPartition_ne_top U ω β γ Bbar hBbar_nonneg hBbar_le_one hq href hβ hγ) hTop)
    have hκZero : κ ca.1 ca.2 = 0 := hκ.vanishes_on_zero_reference ca.1 ca.2 hRefZero
    simpa [posteriorWeightKLDivergenceTerm, hκTop, hLaw, hκZero]
  · have hMulNeTop :
        kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2 *
          ENNReal.ofReal
            (InformationTheory.klFun
              ((κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal)) ≠ ⊤ := by
        exact ENNReal.mul_ne_top
          (kernelGibbsLaw_ne_top U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ ca)
          (by simp)
    simpa [posteriorWeightKLDivergenceTerm, hκTop, hLaw] using hMulNeTop

theorem kernelGibbsIGap_eq_zero_iff
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    {κ : ω.Ω → A → ENNReal}
    (hκ : KernelLawAdmissibleAt U ω refLaw κ)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    kernelGibbsIGap U ω β γ Bbar refLaw κ = 0 ↔
      ∀ c : ω.Ω, ∀ a : A, κ c a = kernelGibbsLaw U ω β γ Bbar refLaw c a := by
  constructor
  · intro hGap c a
    have hTerm : kernelGibbsIGapContribution U ω β γ Bbar refLaw κ (c, a) = 0 := by
      exact (ENNReal.tsum_eq_zero.mp (by simpa [kernelGibbsIGap] using hGap)) (c, a)
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (kernelGibbsLaw_ne_top U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ (c, a))).mp hTerm
  · intro hEq
    rw [kernelGibbsIGap, ENNReal.tsum_eq_zero]
    intro ca
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (kernelGibbsLaw_ne_top U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ ca)).2
        (hEq ca.1 ca.2)

private theorem kernelGibbsIGap_term_identity
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    {κ : ω.Ω → A → ENNReal}
    (hκ : KernelLawAdmissibleAt U ω refLaw κ)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (ca : ω.Ω × A) :
    (kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal =
      kernelPriorKLDivergenceContribution U ω refLaw κ ca
        - (β / γ) * kernelExpectedScoreContribution Bbar κ ca
        + (κ ca.1 ca.2).toReal * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal
        + (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
        - (κ ca.1 ca.2).toReal := by
  by_cases hκca : κ ca.1 ca.2 = 0
  · by_cases hLaw : kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2 = 0
    · simp [kernelGibbsIGapContribution, posteriorWeightKLDivergenceTerm,
        kernelPriorKLDivergenceContribution, kernelExpectedScoreContribution, hκca, hLaw]
    · have hLawPos : 0 < (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal := by
        exact ENNReal.toReal_pos hLaw
          (kernelGibbsLaw_ne_top U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ ca)
      simp [kernelGibbsIGapContribution, posteriorWeightKLDivergenceTerm,
        kernelPriorKLDivergenceContribution, kernelExpectedScoreContribution,
        hκca, hLaw, InformationTheory.klFun_zero]
  · have hκPos : 0 < (κ ca.1 ca.2).toReal := by
      exact ENNReal.toReal_pos hκca (kernelLaw_ne_top_of_admissible U ω refLaw hκ ca)
    have hRef : kernelReferenceWeight U ω refLaw ca.1 ca.2 ≠ 0 := by
      intro hRefZero
      exact hκca (hκ.vanishes_on_zero_reference ca.1 ca.2 hRefZero)
    have hRefPos : 0 < (kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal := by
      exact ENNReal.toReal_pos hRef (kernelReferenceWeight_ne_top U ω hq refLaw ca.1 ca.2)
    have hLaw : kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2 ≠ 0 := by
      intro hLaw
      have hWeight : kernelGibbsWeight U ω β γ Bbar refLaw ca.1 ca.2 ≠ 0 := by
        unfold kernelGibbsWeight
        refine mul_ne_zero hRef ?_
        exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
      have := (ENNReal.div_eq_zero_iff).mp hLaw
      exact this.elim hWeight
        (fun hTop =>
          (kernelGibbsPartition_ne_top U ω β γ Bbar hBbar_nonneg hBbar_le_one hq href hβ hγ) hTop)
    have hLawPos : 0 < (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal := by
      exact ENNReal.toReal_pos hLaw
        (kernelGibbsLaw_ne_top U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ ca)
    have hPartPos : 0 < (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
      exact ENNReal.toReal_pos
        (kernelGibbsPartition_ne_zero U ω β γ Bbar hBbar_nonneg hq href hβ hγ)
        (kernelGibbsPartition_ne_top U ω β γ Bbar hBbar_nonneg hBbar_le_one hq href hβ hγ)
    have hIGapToReal :
        (kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal =
          (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal *
            InformationTheory.klFun
              ((κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal) := by
      unfold kernelGibbsIGapContribution posteriorWeightKLDivergenceTerm
      rw [if_neg (kernelLaw_ne_top_of_admissible U ω refLaw hκ ca), if_neg hLaw,
        ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (InformationTheory.klFun_nonneg ENNReal.toReal_nonneg)]
    have hRatioLaw :
        (κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal =
          (κ ca.1 ca.2).toReal / (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal := by
      rw [ENNReal.toReal_div]
    have hLogRefRatio :
        Real.log ((κ ca.1 ca.2 / kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal) =
          Real.log (κ ca.1 ca.2).toReal -
            Real.log (kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal := by
      rw [ENNReal.toReal_div, Real.log_div hκPos.ne' hRefPos.ne']
    have hLawToReal :
        (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal =
          (kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal *
            Real.exp ((β / γ) * Bbar ca.1 ca.2) /
            (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
      calc
        (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
            = ((kernelReferenceWeight U ω refLaw ca.1 ca.2 *
                  ENNReal.ofReal (Real.exp ((β / γ) * Bbar ca.1 ca.2))) /
                kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
                  rfl
        _ = ((kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal *
              (ENNReal.ofReal (Real.exp ((β / γ) * Bbar ca.1 ca.2))).toReal) /
              (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
                rw [ENNReal.toReal_div, ENNReal.toReal_mul]
        _ = (kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal *
              Real.exp ((β / γ) * Bbar ca.1 ca.2) /
              (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
                have hExpNonneg : 0 ≤ Real.exp ((β / γ) * Bbar ca.1 ca.2) := by positivity
                rw [ENNReal.toReal_ofReal hExpNonneg]
    have hLogLaw :
        Real.log (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal =
          Real.log (kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal +
            (β / γ) * Bbar ca.1 ca.2
            - Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
      rw [hLawToReal, Real.log_div (mul_pos hRefPos (Real.exp_pos _)).ne' hPartPos.ne',
        Real.log_mul hRefPos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hLogLawRatio :
        Real.log
            ((κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal) =
          Real.log ((κ ca.1 ca.2 / kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal)
            - (β / γ) * Bbar ca.1 ca.2
            + Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
      rw [ENNReal.toReal_div, Real.log_div hκPos.ne' hLawPos.ne', hLogRefRatio, hLogLaw]
      ring
    calc
      (kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal
          = (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal *
              InformationTheory.klFun
                ((κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal) :=
            hIGapToReal
      _ = (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal *
            (((κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal) *
              Real.log
                ((κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal)
              + 1 - (κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal) := by
              rw [InformationTheory.klFun_apply]
      _ = (κ ca.1 ca.2).toReal *
            Real.log
              ((κ ca.1 ca.2 / kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal)
            + (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
            - (κ ca.1 ca.2).toReal := by
              rw [hRatioLaw]
              field_simp [hLawPos.ne']
      _ = (κ ca.1 ca.2).toReal *
            (Real.log ((κ ca.1 ca.2 / kernelReferenceWeight U ω refLaw ca.1 ca.2).toReal)
              - (β / γ) * Bbar ca.1 ca.2
              + Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal)
            + (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
            - (κ ca.1 ca.2).toReal := by
              rw [hLogLawRatio]
      _ = kernelPriorKLDivergenceContribution U ω refLaw κ ca
            - (β / γ) * kernelExpectedScoreContribution Bbar κ ca
            + (κ ca.1 ca.2).toReal * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal
            + (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
            - (κ ca.1 ca.2).toReal := by
              simp [kernelPriorKLDivergenceContribution, kernelExpectedScoreContribution, hκca]
              ring

/--
Exact product-domain Gibbs variational identity for the kernel lift:
`γ D_I(κ || κ_G) = γ KL(κ || \\bar w^{ω_A} ⊗ λ) - β E_κ[B̄] + γ log Z_{ker}`.
-/
theorem kernelGibbs_variational_igap
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    {κ : ω.Ω → A → ENNReal}
    (hκ : KernelLawAdmissibleAt U ω refLaw κ)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    γ * (kernelGibbsIGap U ω β γ Bbar refLaw κ).toReal =
      γ * kernelPriorKLDivergence U ω refLaw κ
        - β * kernelExpectedScore Bbar κ
        + γ * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
  have hκSummable : Summable (fun ca : ω.Ω × A => (κ ca.1 ca.2).toReal) := by
    exact ENNReal.summable_toReal (by simpa [hκ.normalized])
  have hScoreSummable :
      Summable (fun ca : ω.Ω × A => kernelExpectedScoreContribution Bbar κ ca) := by
    refine Summable.of_nonneg_of_le
      (fun ca => mul_nonneg ENNReal.toReal_nonneg (hBbar_nonneg ca.1 ca.2))
      (fun ca => ?_) hκSummable
    calc
      kernelExpectedScoreContribution Bbar κ ca
          = (κ ca.1 ca.2).toReal * Bbar ca.1 ca.2 := rfl
      _ ≤ (κ ca.1 ca.2).toReal * 1 := by
            gcongr
            exact hBbar_le_one ca.1 ca.2
      _ = (κ ca.1 ca.2).toReal := by ring
  have hLawSummable :
      Summable (fun ca : ω.Ω × A => (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal) := by
    exact ENNReal.summable_toReal (by
      simpa [kernelGibbsLaw_tsum_eq_one U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ])
  have hConstSummable :
      Summable (fun ca : ω.Ω × A =>
        (κ ca.1 ca.2).toReal * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal) := by
    exact hκSummable.mul_right _
  have hGapSummable :
      Summable (fun ca : ω.Ω × A => (kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal) := by
    have hRhs :
        Summable
          (fun ca : ω.Ω × A =>
            kernelPriorKLDivergenceContribution U ω refLaw κ ca
              - (β / γ) * kernelExpectedScoreContribution Bbar κ ca
              + (κ ca.1 ca.2).toReal
                  * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal
              + (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
              - (κ ca.1 ca.2).toReal) := by
      exact ((hκ.summable_priorKLDivergence.sub
        (hScoreSummable.mul_left (β / γ))).add hConstSummable).add hLawSummable |>.sub hκSummable
    exact hRhs.congr
      (fun ca => (kernelGibbsIGap_term_identity U ω β γ Bbar hq href hκ
        hBbar_nonneg hBbar_le_one hβ hγ ca).symm)
  have hGapToReal :
      (kernelGibbsIGap U ω β γ Bbar refLaw κ).toReal =
        ∑' ca : ω.Ω × A, (kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal := by
    rw [kernelGibbsIGap]
    exact ENNReal.tsum_toReal_eq
      (fun ca => kernelGibbsIGapContribution_ne_top U ω β γ Bbar hq href hκ
        hBbar_nonneg hBbar_le_one hβ hγ ca)
  have hABSumm :
      Summable
        (fun ca : ω.Ω × A =>
          kernelPriorKLDivergenceContribution U ω refLaw κ ca
            - (β / γ) * kernelExpectedScoreContribution Bbar κ ca) := by
    exact hκ.summable_priorKLDivergence.sub (hScoreSummable.mul_left (β / γ))
  have hDeltaSumm :
      Summable
        (fun ca : ω.Ω × A =>
          (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal - (κ ca.1 ca.2).toReal) := by
    exact hLawSummable.sub hκSummable
  have hASum :
      ∑' ca : ω.Ω × A,
        (kernelPriorKLDivergenceContribution U ω refLaw κ ca
          - (β / γ) * kernelExpectedScoreContribution Bbar κ ca)
        =
          kernelPriorKLDivergence U ω refLaw κ
            - (β / γ) * kernelExpectedScore Bbar κ := by
    have hScoreMul :
        ∑' b : ω.Ω × A, (β / γ) * kernelExpectedScoreContribution Bbar κ b =
          (β / γ) * ∑' b : ω.Ω × A, kernelExpectedScoreContribution Bbar κ b := by
      simpa using (hScoreSummable.tsum_mul_left (β / γ))
    rw [hκ.summable_priorKLDivergence.tsum_sub (hScoreSummable.mul_left (β / γ))]
    rw [hScoreMul]
    simp [kernelPriorKLDivergence, kernelExpectedScore]
  have hConst :
      ∑' ca : ω.Ω × A,
        (κ ca.1 ca.2).toReal * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal
        =
          Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
    rw [hκSummable.tsum_mul_right, kernelLaw_toReal_tsum_eq_one U ω refLaw hκ]
    ring
  have hDelta :
      ∑' ca : ω.Ω × A,
        ((kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal - (κ ca.1 ca.2).toReal) = 0 := by
    have hLawToRealOne :
        ∑' ca : ω.Ω × A, (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal = 1 := by
      calc
        ∑' ca : ω.Ω × A, (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
            = (∑' ca : ω.Ω × A, kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal := by
                exact (ENNReal.tsum_toReal_eq
                  (fun ca => kernelGibbsLaw_ne_top U ω β γ Bbar hq href
                    hBbar_nonneg hBbar_le_one hβ hγ ca)).symm
        _ = 1 := by
              simpa [kernelGibbsLaw_tsum_eq_one U ω β γ Bbar hq href
                hBbar_nonneg hBbar_le_one hβ hγ]
    rw [Summable.tsum_sub hLawSummable hκSummable, hLawToRealOne,
      kernelLaw_toReal_tsum_eq_one U ω refLaw hκ]
    ring
  have hGapIdentity :
      (kernelGibbsIGap U ω β γ Bbar refLaw κ).toReal =
        kernelPriorKLDivergence U ω refLaw κ
          - (β / γ) * kernelExpectedScore Bbar κ
          + Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
    calc
      (kernelGibbsIGap U ω β γ Bbar refLaw κ).toReal
          = ∑' ca : ω.Ω × A,
              (kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal := by
                rw [hGapToReal]
      _ = ∑' ca : ω.Ω × A,
            (kernelPriorKLDivergenceContribution U ω refLaw κ ca
              - (β / γ) * kernelExpectedScoreContribution Bbar κ ca
              + (κ ca.1 ca.2).toReal
                  * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal
              + (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
              - (κ ca.1 ca.2).toReal) := by
                apply tsum_congr
                intro ca
                exact kernelGibbsIGap_term_identity U ω β γ Bbar hq href hκ
                  hBbar_nonneg hBbar_le_one hβ hγ ca
      _ = ∑' ca : ω.Ω × A,
            ((kernelPriorKLDivergenceContribution U ω refLaw κ ca
              - (β / γ) * kernelExpectedScoreContribution Bbar κ ca)
              + ((κ ca.1 ca.2).toReal
                  * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal)
              + ((kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
                  - (κ ca.1 ca.2).toReal)) := by
                apply tsum_congr
                intro ca
                ring
      _ = (∑' ca : ω.Ω × A,
            (kernelPriorKLDivergenceContribution U ω refLaw κ ca
              - (β / γ) * kernelExpectedScoreContribution Bbar κ ca))
            + (∑' ca : ω.Ω × A,
                (κ ca.1 ca.2).toReal
                  * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal)
            + (∑' ca : ω.Ω × A,
                ((kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
                  - (κ ca.1 ca.2).toReal)) := by
                rw [((hABSumm.add hConstSummable).tsum_add hDeltaSumm)]
                rw [hABSumm.tsum_add hConstSummable]
      _ = kernelPriorKLDivergence U ω refLaw κ
            - (β / γ) * kernelExpectedScore Bbar κ
            + Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
              rw [hASum, hConst, hDelta]
              ring
  calc
    γ * (kernelGibbsIGap U ω β γ Bbar refLaw κ).toReal
        = γ *
            (kernelPriorKLDivergence U ω refLaw κ
              - (β / γ) * kernelExpectedScore Bbar κ
              + Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal) := by
                rw [hGapIdentity]
    _ = γ * kernelPriorKLDivergence U ω refLaw κ
          - β * kernelExpectedScore Bbar κ
          + γ * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal := by
            field_simp [hγ.ne']

theorem kernelGibbsIGap_ne_top
    (U : CountablePrefixMachine A O)
    (ω : Observer (CountableEncodedProgram A O))
    [Encodable ω.Ω] [DecidableEq ω.Ω] [Fintype A]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ω)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    {refLaw : ActionLaw A}
    (href : KernelReferenceLawMassAdmissible (A := A) refLaw)
    {κ : ω.Ω → A → ENNReal}
    (hκ : KernelLawAdmissibleAt U ω refLaw κ)
    (hBbar_nonneg : ∀ c : ω.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ω.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    kernelGibbsIGap U ω β γ Bbar refLaw κ ≠ ⊤ := by
  have hGapSummable :
      Summable (fun ca : ω.Ω × A => (kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal) := by
    have hId := kernelGibbs_variational_igap U ω β γ Bbar hq href hκ
      hBbar_nonneg hBbar_le_one hβ hγ
    have hκSummable : Summable (fun ca : ω.Ω × A => (kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal) := by
      have hRhs :
          Summable (fun ca : ω.Ω × A =>
            kernelPriorKLDivergenceContribution U ω refLaw κ ca
              - (β / γ) * kernelExpectedScoreContribution Bbar κ ca
              + (κ ca.1 ca.2).toReal * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal
              + (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal
              - (κ ca.1 ca.2).toReal) := by
        have hκMassSummable : Summable (fun ca : ω.Ω × A => (κ ca.1 ca.2).toReal) := by
          exact ENNReal.summable_toReal (by simpa [hκ.normalized])
        have hScoreSummable :
            Summable (fun ca : ω.Ω × A => kernelExpectedScoreContribution Bbar κ ca) := by
          refine Summable.of_nonneg_of_le
            (fun ca => mul_nonneg ENNReal.toReal_nonneg (hBbar_nonneg ca.1 ca.2))
            (fun ca => ?_) hκMassSummable
          calc
            kernelExpectedScoreContribution Bbar κ ca
                = (κ ca.1 ca.2).toReal * Bbar ca.1 ca.2 := rfl
            _ ≤ (κ ca.1 ca.2).toReal * 1 := by
                  gcongr
                  exact hBbar_le_one ca.1 ca.2
            _ = (κ ca.1 ca.2).toReal := by ring
        have hLawSummable :
            Summable (fun ca : ω.Ω × A => (kernelGibbsLaw U ω β γ Bbar refLaw ca.1 ca.2).toReal) := by
          exact ENNReal.summable_toReal (by
            simpa [kernelGibbsLaw_tsum_eq_one U ω β γ Bbar hq href hBbar_nonneg hBbar_le_one hβ hγ])
        have hConstSummable :
            Summable (fun ca : ω.Ω × A =>
              (κ ca.1 ca.2).toReal * Real.log (kernelGibbsPartition U ω β γ Bbar refLaw).toReal) := by
          exact hκMassSummable.mul_right _
        exact ((hκ.summable_priorKLDivergence.sub
          (hScoreSummable.mul_left (β / γ))).add hConstSummable).add hLawSummable |>.sub hκMassSummable
      exact hRhs.congr
        (fun ca => (kernelGibbsIGap_term_identity U ω β γ Bbar hq href hκ
          hBbar_nonneg hBbar_le_one hβ hγ ca).symm)
    exact hκSummable
  have hEq :
      kernelGibbsIGap U ω β γ Bbar refLaw κ =
        ∑' ca : ω.Ω × A, ENNReal.ofReal
          ((kernelGibbsIGapContribution U ω β γ Bbar refLaw κ ca).toReal) := by
    rw [kernelGibbsIGap]
    apply tsum_congr
    intro ca
    rw [ENNReal.ofReal_toReal
      (kernelGibbsIGapContribution_ne_top U ω β γ Bbar hq href hκ
        hBbar_nonneg hBbar_le_one hβ hγ ca)]
  rw [hEq]
  exact hGapSummable.tsum_ofReal_ne_top

/-- Exact per-pair Gibbs mismatch term used by the canonical kernel lift. -/
def def_raw_kernel_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (_ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ωA)
    (refLaw : ActionLaw A)
    (κ : ωA.Ω → A → ENNReal)
    (c : ωA.Ω) (a : A) : ENNReal :=
  let _ := π
  let _ := t
  let _ := h
  posteriorWeightKLDivergenceTerm (κ c a)
    (kernelGibbsLaw U ωA β γ Bbar refLaw c a)

/-- Exact kernel lift from the manuscript: `F_t[q;h_t] - β E_κ[B̄] + γ KL(κ || \\bar w^{ω_A} ⊗ λ)`. -/
def def_kernel_functional
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (_ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ωA)
    (q : U.Program → ENNReal)
    (κ : ωA.Ω → A → ENNReal)
    (refLaw : ActionLaw A) : Real :=
  def_afe U π t h q
    - β * kernelExpectedScore Bbar κ
    + γ * kernelPriorKLDivergence U ωA refLaw κ

/-- Meeting-point specialization with the exact kernel lift on the countable stack. -/
def def_meeting_point_shorthand
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ωA)
    (q : U.Program → ENNReal)
    (ν : ωA.Ω → ENNReal)
    (pstar : CountableEncodedProgram A O)
    (κ : ωA.Ω → A → ENNReal)
    (refLaw : ActionLaw A) :
    Real × Real × Real :=
  (def_bhat_omega U π t h ωA pstar,
   def_two_observer_functional U π t h ωB ωA β γ q ν,
   def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw)

/-- Exact Gibbs-kernel action cap: the bounded score contributes at most `exp (β / γ)`. -/
theorem prop_action_cap
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : Real)
    (Bbar : KernelScore (A := A) (O := O) ωA)
    (hBbar_nonneg : ∀ c : ωA.Ω, ∀ a : A, 0 ≤ Bbar c a)
    (hBbar_le_one : ∀ c : ωA.Ω, ∀ a : A, Bbar c a ≤ 1)
    (hβ : 0 ≤ β) (hγ : 0 < γ)
    (refLaw : ActionLaw A)
    (c : ωA.Ω) (a : A) :
    kernelGibbsWeight U ωA β γ Bbar refLaw c a ≤
      kernelReferenceWeight U ωA refLaw c a * ENNReal.ofReal (Real.exp (β / γ)) := by
  let _ := π
  let _ := t
  let _ := h
  exact kernelGibbsWeight_le_scaled_reference U ωA β γ Bbar
    hBbar_nonneg hBbar_le_one hβ hγ refLaw c a

end ExactKernelVariational

/-- Lean wrapper for `thm:meeting-point` on the countable functional stack. -/
theorem thm_meeting_point :
    BeliefAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) ∧
    ActionAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) := by
  exact cor_canonical_pair (A := A) (O := O)

end CountablePaperFunctional

end SemanticConvergence
