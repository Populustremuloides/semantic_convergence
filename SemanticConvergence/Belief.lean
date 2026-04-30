import SemanticConvergence.Functional
import SemanticConvergence.DiscreteConvexDuality
import SemanticConvergence.ConcreteBelief
import SemanticConvergence.CompactKernel

/-
NOTE [variational-core exactness]

`lem_variational` and `lem_kl_necessity` are governed by the exactness lock in
`variational_core_exactness_lock.md`. The canonical `lem_kl_necessity` declaration below is the
countable discrete convex-duality theorem; posterior-gap zero characterizations are kept under
explicit helper names.
-/

namespace SemanticConvergence

universe u v w x

noncomputable section CountablePaperBelief

open Classical
open CountableConcrete
open CountableConcrete.CountablePrefixMachine
open InformationTheory
open MeasureTheory

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

/-- Countable class-prior weight scaffold. -/
def classPriorWeight
    (U : CountablePrefixMachine A O)
    (C : PredSet U.Program) : ENNReal :=
  ∑' p : U.Program, if C p then def_universal_prior U p else 0

/-- Lean wrapper for `lem:prior-invariance` on the countable prefix-machine stack. -/
theorem lem_prior_invariance
    (U : CountablePrefixMachine A O)
    (p : U.Program) :
    def_universal_prior U p = U.universalWeight p / universalPriorMass U := by
  rfl

/-- Lean wrapper for `lem:prior-necessity` on the countable prefix-machine stack. -/
theorem lem_prior_necessity
    (U : CountablePrefixMachine A O)
    (C : PredSet U.Program) :
    classPriorWeight U C =
      ∑' p : U.Program, if C p then def_universal_prior U p else 0 := by
  rfl

private theorem q_ne_top_of_admissible
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    q p ≠ ⊤ := by
  have hle : q p ≤ 1 := by
    calc
      q p ≤ ∑' r : U.Program, q r := ENNReal.le_tsum p
      _ = 1 := hq.normalized
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

private theorem q_toReal_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q) :
    ∑' p : U.Program, (q p).toReal = 1 := by
  calc
    ∑' p : U.Program, (q p).toReal = (∑' p : U.Program, q p).toReal := by
      exact (ENNReal.tsum_toReal_eq (fun p => q_ne_top_of_admissible U π t h hq p)).symm
    _ = 1 := by simpa [hq.normalized]

private theorem universalWeight_ne_zero
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

private theorem def_universal_prior_tsum_eq_one
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

private theorem def_universal_prior_ne_top
    (U : CountablePrefixMachine A O)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    def_universal_prior U p ≠ ⊤ := by
  have hle : def_universal_prior U p ≤ 1 := by
    calc
      def_universal_prior U p ≤ ∑' r : U.Program, def_universal_prior U r := ENNReal.le_tsum p
      _ = 1 := def_universal_prior_tsum_eq_one U hq
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

private theorem def_universal_prior_pos
    (U : CountablePrefixMachine A O)
    {π : CountablePolicy A O} {t : Nat} {h : CountHist A O}
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    0 < def_universal_prior U p := by
  unfold def_universal_prior
  exact ENNReal.div_pos (universalWeight_ne_zero U p) hq.priorMass_ne_top

private theorem bayesEvidence_le_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q) :
    bayesEvidence U π t h ≤ 1 := by
  have hPoint :
      ∀ p : U.Program,
        def_universal_prior U p * U.likelihood π t h p ≤ def_universal_prior U p := by
    intro p
    calc
      def_universal_prior U p * U.likelihood π t h p
          ≤ def_universal_prior U p * 1 := by
              gcongr
              exact (CountableConcrete.histPMF π (U.programSemantics p) t).coe_le_one h
      _ = def_universal_prior U p := by simp
  calc
    bayesEvidence U π t h = ∑' p : U.Program, def_universal_prior U p * U.likelihood π t h p := rfl
    _ ≤ ∑' p : U.Program, def_universal_prior U p := ENNReal.tsum_le_tsum hPoint
    _ = 1 := def_universal_prior_tsum_eq_one U hq

private theorem bayesEvidence_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q) :
    bayesEvidence U π t h ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt (bayesEvidence_le_one U π t h hq) ENNReal.one_lt_top)

private theorem bayesPosterior_tsum_eq_one
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q) :
    ∑' p : U.Program, bayesPosterior U π t h p = 1 := by
  calc
    ∑' p : U.Program, bayesPosterior U π t h p
        = ∑' p : U.Program,
            (def_universal_prior U p * U.likelihood π t h p) / bayesEvidence U π t h := by
              simp [bayesPosterior]
    _ = (∑' p : U.Program, def_universal_prior U p * U.likelihood π t h p) *
          (bayesEvidence U π t h)⁻¹ := by
            simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ = (∑' p : U.Program, def_universal_prior U p * U.likelihood π t h p) /
          bayesEvidence U π t h := by simp [div_eq_mul_inv]
    _ = 1 := by
          unfold bayesEvidence
          exact ENNReal.div_self (ne_of_gt hq.evidence_pos) (bayesEvidence_ne_top U π t h hq)

private theorem bayesPosterior_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    bayesPosterior U π t h p ≠ ⊤ := by
  have hle : bayesPosterior U π t h p ≤ 1 := by
    calc
      bayesPosterior U π t h p ≤ ∑' r : U.Program, bayesPosterior U π t h r := ENNReal.le_tsum p
      _ = 1 := bayesPosterior_tsum_eq_one U π t h hq
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

private theorem posteriorIGap_eq_zero_iff
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q) :
    posteriorIGap U π t h q = 0 ↔ ∀ p : U.Program, q p = bayesPosterior U π t h p := by
  constructor
  · intro hGap p
    have hTerm :
        posteriorIGapContribution U π t h q p = 0 := by
      exact (ENNReal.tsum_eq_zero.mp (by simpa [posteriorIGap] using hGap)) p
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (bayesPosterior_ne_top U π t h hq p)).mp hTerm
  · intro hEq
    rw [posteriorIGap, ENNReal.tsum_eq_zero]
    intro p
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (bayesPosterior_ne_top U π t h hq p)).2 (hEq p)

private theorem variational_term_identity
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    historyFitLossContribution U π t h q p +
      priorKLDivergenceContribution U q p =
      posteriorKLDivergenceContribution U π t h q p +
        (q p).toReal * negativeLogBayesEvidence U π t h := by
  by_cases hqp : q p = 0
  · simp [historyFitLossContribution, priorKLDivergenceContribution,
      posteriorKLDivergenceContribution, negativeLogBayesEvidence, hqp]
  · have hqPos : 0 < (q p).toReal := by
      exact ENNReal.toReal_pos hqp (q_ne_top_of_admissible U π t h hq p)
    have hLikeNeZero : U.likelihood π t h p ≠ 0 := by
      intro hZero
      exact hqp (hq.vanishes_on_zero_likelihood p hZero)
    have hLikePos : 0 < (U.likelihood π t h p).toReal := by
      exact ENNReal.toReal_pos hLikeNeZero
        ((CountableConcrete.histPMF π (U.programSemantics p) t).apply_ne_top h)
    have hPriorPos : 0 < (def_universal_prior U p).toReal := by
      exact ENNReal.toReal_pos (def_universal_prior_pos U hq p).ne'
        (def_universal_prior_ne_top U hq p)
    have hEvidencePos : 0 < (bayesEvidence U π t h).toReal := by
      exact ENNReal.toReal_pos hq.evidence_pos.ne' (bayesEvidence_ne_top U π t h hq)
    have hPosteriorToReal :
        (bayesPosterior U π t h p).toReal =
          (def_universal_prior U p).toReal * (U.likelihood π t h p).toReal /
            (bayesEvidence U π t h).toReal := by
      simp [bayesPosterior, ENNReal.toReal_mul, ENNReal.toReal_div]
    have hPosteriorPos : 0 < (bayesPosterior U π t h p).toReal := by
      rw [hPosteriorToReal]
      positivity
    have hLogPrior :
        Real.log ((q p / def_universal_prior U p).toReal) =
          Real.log (q p).toReal - Real.log (def_universal_prior U p).toReal := by
      rw [ENNReal.toReal_div, Real.log_div hqPos.ne' hPriorPos.ne']
    have hLogPosterior :
        Real.log ((q p / bayesPosterior U π t h p).toReal) =
          Real.log (q p).toReal - Real.log (bayesPosterior U π t h p).toReal := by
      rw [ENNReal.toReal_div, Real.log_div hqPos.ne' hPosteriorPos.ne']
    have hLogPosteriorWeight :
        Real.log (bayesPosterior U π t h p).toReal =
          Real.log (def_universal_prior U p).toReal +
            Real.log (U.likelihood π t h p).toReal -
            Real.log (bayesEvidence U π t h).toReal := by
      rw [hPosteriorToReal, Real.log_div (by positivity) hEvidencePos.ne',
        Real.log_mul hPriorPos.ne' hLikePos.ne']
    have hInside :
        -Real.log (U.likelihood π t h p).toReal +
            Real.log ((q p / def_universal_prior U p).toReal) =
          Real.log ((q p / bayesPosterior U π t h p).toReal) +
            negativeLogBayesEvidence U π t h := by
      rw [negativeLogBayesEvidence, hLogPrior, hLogPosterior, hLogPosteriorWeight]
      ring
    calc
      historyFitLossContribution U π t h q p +
          priorKLDivergenceContribution U q p
          =
            (q p).toReal * (-Real.log (U.likelihood π t h p).toReal) +
              (q p).toReal * Real.log ((q p / def_universal_prior U p).toReal) := by
                simp [historyFitLossContribution, priorKLDivergenceContribution,
                  historyFitLoss, hqp]
      _ = (q p).toReal *
            (-Real.log (U.likelihood π t h p).toReal +
              Real.log ((q p / def_universal_prior U p).toReal)) := by ring
      _ = (q p).toReal *
            (Real.log ((q p / bayesPosterior U π t h p).toReal) +
              negativeLogBayesEvidence U π t h) := by rw [hInside]
      _ = posteriorKLDivergenceContribution U π t h q p +
            (q p).toReal * negativeLogBayesEvidence U π t h := by
              simp [posteriorKLDivergenceContribution, hqp]
              ring

/-- Lean wrapper for `lem:variational` on the countable posterior stack. -/
theorem lem_variational
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q) :
    def_afe U π t h q =
      posteriorKLDivergence U π t h q + negativeLogBayesEvidence U π t h := by
  have hqSummableToReal : Summable (fun p : U.Program => (q p).toReal) := by
    exact ENNReal.summable_toReal (by simpa [hq.normalized])
  have hConstSummable :
      Summable (fun p : U.Program =>
        (q p).toReal * negativeLogBayesEvidence U π t h) := by
    exact hqSummableToReal.mul_right _
  calc
    def_afe U π t h q
        = ∑' p : U.Program,
            (historyFitLossContribution U π t h q p +
              priorKLDivergenceContribution U q p) := by
              unfold def_afe expectedHistoryFitLoss priorKLDivergence
              exact (hq.summable_expectedHistoryFitLoss.tsum_add
                hq.summable_priorKLDivergence).symm
    _ = ∑' p : U.Program,
          (posteriorKLDivergenceContribution U π t h q p +
            (q p).toReal * negativeLogBayesEvidence U π t h) := by
              apply tsum_congr
              intro p
              exact variational_term_identity U π t h q hq p
    _ = posteriorKLDivergence U π t h q +
          ∑' p : U.Program, (q p).toReal * negativeLogBayesEvidence U π t h := by
            unfold posteriorKLDivergence
            rw [hq.summable_posteriorKLDivergence.tsum_add hConstSummable]
    _ = posteriorKLDivergence U π t h q + negativeLogBayesEvidence U π t h := by
      rw [hqSummableToReal.tsum_mul_right]
      simp [q_toReal_tsum_eq_one U π t h hq]

private theorem likelihood_eq_zero_of_bayesPosterior_eq_zero
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program)
    (hPost : bayesPosterior U π t h p = 0) :
    U.likelihood π t h p = 0 := by
  by_contra hLike
  have hLikePos : 0 < (U.likelihood π t h p).toReal := by
    exact ENNReal.toReal_pos hLike
      ((CountableConcrete.histPMF π (U.programSemantics p) t).apply_ne_top h)
  have hPriorPos : 0 < (def_universal_prior U p).toReal := by
    exact ENNReal.toReal_pos (def_universal_prior_pos U hq p).ne'
      (def_universal_prior_ne_top U hq p)
  have hEvidencePos : 0 < (bayesEvidence U π t h).toReal := by
    exact ENNReal.toReal_pos hq.evidence_pos.ne' (bayesEvidence_ne_top U π t h hq)
  have hPosteriorToReal :
      (bayesPosterior U π t h p).toReal =
        (def_universal_prior U p).toReal * (U.likelihood π t h p).toReal /
          (bayesEvidence U π t h).toReal := by
    simp [bayesPosterior, ENNReal.toReal_mul, ENNReal.toReal_div]
  have hPostPos : 0 < (bayesPosterior U π t h p).toReal := by
    rw [hPosteriorToReal]
    positivity
  exact hPostPos.ne' (by simpa [hPost])

private theorem posteriorIGapContribution_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {q : U.Program → ENNReal}
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    posteriorIGapContribution U π t h q p ≠ ⊤ := by
  unfold posteriorIGapContribution posteriorWeightKLDivergenceTerm
  have hqTop : q p ≠ ⊤ := q_ne_top_of_admissible U π t h hq p
  by_cases hPost : bayesPosterior U π t h p = 0
  · have hLike : U.likelihood π t h p = 0 :=
      likelihood_eq_zero_of_bayesPosterior_eq_zero U π t h hq p hPost
    have hqZero : q p = 0 := hq.vanishes_on_zero_likelihood p hLike
    simp [hPost, hqZero]
  · simpa [hqTop, hPost] using
      (ENNReal.mul_ne_top
        (bayesPosterior_ne_top U π t h hq p)
        (by simp : ENNReal.ofReal (InformationTheory.klFun
          ((q p / bayesPosterior U π t h p).toReal)) ≠ ⊤))

private theorem posteriorIGap_term_identity
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q)
    (p : U.Program) :
    (posteriorIGapContribution U π t h q p).toReal =
      posteriorKLDivergenceContribution U π t h q p +
        (bayesPosterior U π t h p).toReal - (q p).toReal := by
  by_cases hqp : q p = 0
  · by_cases hPost : bayesPosterior U π t h p = 0
    · simp [posteriorIGapContribution, posteriorWeightKLDivergenceTerm,
        posteriorKLDivergenceContribution, hqp, hPost]
    · have hPostPos : 0 < (bayesPosterior U π t h p).toReal := by
        exact ENNReal.toReal_pos hPost (bayesPosterior_ne_top U π t h hq p)
      simp [posteriorIGapContribution, posteriorWeightKLDivergenceTerm,
        posteriorKLDivergenceContribution, hqp, hPost, InformationTheory.klFun_zero]
  · have hqPos : 0 < (q p).toReal := by
      exact ENNReal.toReal_pos hqp (q_ne_top_of_admissible U π t h hq p)
    have hqTop : q p ≠ ⊤ := q_ne_top_of_admissible U π t h hq p
    have hPost : bayesPosterior U π t h p ≠ 0 := by
      intro hPost
      have hLike := likelihood_eq_zero_of_bayesPosterior_eq_zero U π t h hq p hPost
      exact hqp (hq.vanishes_on_zero_likelihood p hLike)
    have hPostPos : 0 < (bayesPosterior U π t h p).toReal := by
      exact ENNReal.toReal_pos hPost (bayesPosterior_ne_top U π t h hq p)
    have hIGapToReal :
        (posteriorIGapContribution U π t h q p).toReal =
          (bayesPosterior U π t h p).toReal *
            InformationTheory.klFun ((q p / bayesPosterior U π t h p).toReal) := by
      unfold posteriorIGapContribution posteriorWeightKLDivergenceTerm
      rw [if_neg hqTop, if_neg hPost, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (InformationTheory.klFun_nonneg (by positivity))]
    have hRatio :
        (q p / bayesPosterior U π t h p).toReal =
          (q p).toReal / (bayesPosterior U π t h p).toReal := by
      rw [ENNReal.toReal_div]
    calc
      (posteriorIGapContribution U π t h q p).toReal
          = (bayesPosterior U π t h p).toReal *
              InformationTheory.klFun ((q p / bayesPosterior U π t h p).toReal) := hIGapToReal
      _ = (bayesPosterior U π t h p).toReal *
            (((q p / bayesPosterior U π t h p).toReal) *
              Real.log ((q p / bayesPosterior U π t h p).toReal) + 1 -
              (q p / bayesPosterior U π t h p).toReal) := by
                rw [InformationTheory.klFun_apply]
      _ = (q p).toReal *
            Real.log ((q p / bayesPosterior U π t h p).toReal) +
              (bayesPosterior U π t h p).toReal - (q p).toReal := by
                rw [hRatio]
                field_simp [hPostPos.ne']
      _ = posteriorKLDivergenceContribution U π t h q p +
            (bayesPosterior U π t h p).toReal - (q p).toReal := by
              simp [posteriorKLDivergenceContribution, hqp]

theorem posteriorIGap_ne_top
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q) :
    posteriorIGap U π t h q ≠ ⊤ := by
  have hPosteriorSummable :
      Summable (fun p : U.Program => (bayesPosterior U π t h p).toReal) := by
    exact ENNReal.summable_toReal (by
      simpa [bayesPosterior_tsum_eq_one U π t h hq])
  have hQSummable :
      Summable (fun p : U.Program => (q p).toReal) := by
    exact ENNReal.summable_toReal (by simpa [hq.normalized])
  have hGapSummable :
      Summable (fun p : U.Program => (posteriorIGapContribution U π t h q p).toReal) := by
    have hRhs :
        Summable
          (fun p : U.Program =>
            posteriorKLDivergenceContribution U π t h q p +
              (bayesPosterior U π t h p).toReal - (q p).toReal) := by
      exact (hq.summable_posteriorKLDivergence.add hPosteriorSummable).sub hQSummable
    exact hRhs.congr (fun p => (posteriorIGap_term_identity U π t h q hq p).symm)
  have hEq :
      posteriorIGap U π t h q =
        ∑' p : U.Program, ENNReal.ofReal ((posteriorIGapContribution U π t h q p).toReal) := by
    rw [posteriorIGap]
    apply tsum_congr
    intro p
    rw [ENNReal.ofReal_toReal (posteriorIGapContribution_ne_top U π t h hq p)]
  rw [hEq]
  exact hGapSummable.tsum_ofReal_ne_top

/--
Exact posterior-gap form of the variational identity: on the admissible domain,
`F_t[q; h_t] = D_I(q || q_t^*) - log ξ̄(o_{1:t} | a_{1:t})`, where the Lean posterior gap
`posteriorIGap` is the generalized discrete I-divergence to the Bayes/Gibbs posterior.
-/
theorem lem_variational_igap
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q) :
    def_afe U π t h q =
      (posteriorIGap U π t h q).toReal + negativeLogBayesEvidence U π t h := by
  have hPosteriorSummable :
      Summable (fun p : U.Program => (bayesPosterior U π t h p).toReal) := by
    exact ENNReal.summable_toReal (by
      simpa [bayesPosterior_tsum_eq_one U π t h hq])
  have hQSummable :
      Summable (fun p : U.Program => (q p).toReal) := by
    exact ENNReal.summable_toReal (by simpa [hq.normalized])
  have hGapSummable :
      Summable (fun p : U.Program => (posteriorIGapContribution U π t h q p).toReal) := by
    have hRhs :
        Summable
          (fun p : U.Program =>
            posteriorKLDivergenceContribution U π t h q p +
              (bayesPosterior U π t h p).toReal - (q p).toReal) := by
      exact (hq.summable_posteriorKLDivergence.add hPosteriorSummable).sub
        hQSummable
    refine Summable.congr hRhs ?_
    intro p
    symm
    exact posteriorIGap_term_identity U π t h q hq p
  have hGapToReal :
      (posteriorIGap U π t h q).toReal =
        ∑' p : U.Program, (posteriorIGapContribution U π t h q p).toReal := by
    rw [posteriorIGap]
    exact ENNReal.tsum_toReal_eq (fun p => posteriorIGapContribution_ne_top U π t h hq p)
  have hPosteriorKLTsum :
      posteriorKLDivergence U π t h q =
        ∑' p : U.Program, (posteriorIGapContribution U π t h q p).toReal := by
    have hPosteriorToReal :
        ∑' p : U.Program, (bayesPosterior U π t h p).toReal = 1 := by
      calc
        ∑' p : U.Program, (bayesPosterior U π t h p).toReal
            = (∑' p : U.Program, bayesPosterior U π t h p).toReal := by
                exact (ENNReal.tsum_toReal_eq (fun p => bayesPosterior_ne_top U π t h hq p)).symm
        _ = 1 := by simpa [bayesPosterior_tsum_eq_one U π t h hq]
    have hZero :
        ∑' p : U.Program, ((bayesPosterior U π t h p).toReal - (q p).toReal) = 0 := by
      rw [Summable.tsum_sub hPosteriorSummable hQSummable, hPosteriorToReal,
        q_toReal_tsum_eq_one U π t h hq]
      ring
    calc
      posteriorKLDivergence U π t h q
          = posteriorKLDivergence U π t h q + 0 := by ring
      _ = posteriorKLDivergence U π t h q +
            ∑' p : U.Program, ((bayesPosterior U π t h p).toReal - (q p).toReal) := by
              rw [hZero]
      _ = ∑' p : U.Program,
            (posteriorKLDivergenceContribution U π t h q p +
              ((bayesPosterior U π t h p).toReal - (q p).toReal)) := by
              unfold posteriorKLDivergence
              rw [hq.summable_posteriorKLDivergence.tsum_add
                (hPosteriorSummable.sub hQSummable)]
      _ = ∑' p : U.Program, (posteriorIGapContribution U π t h q p).toReal := by
            apply tsum_congr
            intro p
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (posteriorIGap_term_identity U π t h q hq p).symm
  calc
    def_afe U π t h q
        = posteriorKLDivergence U π t h q + negativeLogBayesEvidence U π t h :=
          lem_variational U π t h q hq
    _ = (∑' p : U.Program, (posteriorIGapContribution U π t h q p).toReal)
          + negativeLogBayesEvidence U π t h := by rw [hPosteriorKLTsum]
    _ = (posteriorIGap U π t h q).toReal + negativeLogBayesEvidence U π t h := by
          rw [← hGapToReal]

/--
Lean wrapper for `lem:kl-necessity`.

On the countable simplex, any extended divergence satisfying the exact bounded-loss variational
formula against a reference law `w` agrees with the honest discrete KL divergence `KL(. || w)` on
every normalized belief. The proof delegates the truncation and lower-semicontinuity argument to
`DiscreteConvexDuality.exactBoundedLossFormula_eq_kl`; this declaration is the canonical
paper-facing theorem name used by the manifest.

The framework's `ExactBoundedLossFormula` hypothesis is non-vacuous: it is satisfied by KL
itself, as certified by `genericWeightKLDivergence_satisfies_ExactBoundedLossFormula` in
`DiscreteConvexDuality.lean`. The four predicate hypotheses on the simplex-restricted KL
(`ProperOnSimplex`, `ConvexOnSimplex`, `OffSimplexTop`, `SequentialLowerSemicontinuousOnSimplex`)
are standard for the discrete simplex but require additional bridging work to formalize on this
substrate; see `genericWeightKLDivergence_self_instantiation` in `DiscreteConvexDuality.lean`
for the corollary that combines them with the bounded-loss-formula instantiation to recover
the trivial self-identity `KL = KL`. See `lean_open_issues.md` (G2) for the current status.
-/
theorem lem_kl_necessity
    {P : Type u} [Encodable P]
    (D : ExtendedDivergence P)
    (w q : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hProper : ProperOnSimplex D)
    (hConvex : ConvexOnSimplex D)
    (hOffSimplex : OffSimplexTop D)
    (hSeq : SequentialLowerSemicontinuousOnSimplex D)
    (hExact : ExactBoundedLossFormula D w) :
    D q = genericWeightKLDivergenceEReal q w := by
  have hLower :
      genericWeightKLDivergenceEReal q w ≤ D q :=
    exactBoundedLossFormula_ge_kl D w hw hExact q hq
  have hEquality :
      D q = genericWeightKLDivergenceEReal q w :=
    exactBoundedLossFormula_eq_kl D w q hw hq hProper hConvex hOffSimplex hSeq hExact
  have hUpper :
      D q ≤ genericWeightKLDivergenceEReal q w := by
    exact le_of_eq hEquality
  exact le_antisymm hUpper hLower

/--
Correctly named helper for the countable belief stack: vanishing posterior I-gap forces exact
Bayes/Gibbs posterior agreement pointwise. This is a posterior-specific zero-gap fact, not the
manuscript's convex-duality KL-necessity theorem.
-/
theorem lem_posterior_gap_necessity
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q) :
    posteriorIGap U π t h q = 0 ↔
      ∀ p : U.Program, q p = bayesPosterior U π t h p := by
  constructor
  · intro hGap p
    have hTerm :
        posteriorIGapContribution U π t h q p = 0 := by
      exact (ENNReal.tsum_eq_zero.mp (by simpa [posteriorIGap] using hGap)) p
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (bayesPosterior_ne_top U π t h hq p)).mp hTerm
  · intro hEq
    rw [posteriorIGap, ENNReal.tsum_eq_zero]
    intro p
    exact (posteriorWeightKLDivergenceTerm_eq_zero_iff
      (bayesPosterior_ne_top U π t h hq p)).2 (hEq p)

/--
Lean wrapper for `prop:two-observer-minimizer` on the exact countable variational stack.

The two-observer functional decomposes into the Bayes evidence term, the Gibbs partition
correction, and two nonnegative generalized I-gaps. Equality with the minimum constant therefore
holds exactly at the Bayes posterior and the Gibbs class law.
-/
theorem prop_two_observer_minimizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω]
    (β γ : Real)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q)
    (ν : ωA.Ω → ENNReal)
    (hν : ObserverClassAdmissibleAt U π t h ωA ν)
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    def_two_observer_functional U π t h ωB ωA β γ q ν
      =
        negativeLogBayesEvidence U π t h
          - γ * Real.log (observerClassGibbsPartition U π t h ωA β γ).toReal
          + (posteriorIGap U π t h q).toReal
          + γ * (observerClassGibbsIGap U π t h ωA β γ ν).toReal
      ∧
    (negativeLogBayesEvidence U π t h
        - γ * Real.log (observerClassGibbsPartition U π t h ωA β γ).toReal)
      ≤ def_two_observer_functional U π t h ωB ωA β γ q ν
      ∧
    (def_two_observer_functional U π t h ωB ωA β γ q ν
        =
          negativeLogBayesEvidence U π t h
            - γ * Real.log (observerClassGibbsPartition U π t h ωA β γ).toReal
      ↔
        (∀ p : U.Program, q p = bayesPosterior U π t h p)
          ∧
        (∀ c : ωA.Ω, ν c = observerClassGibbsLaw U π t h ωA β γ c)) := by
  let zLog : Real := Real.log (observerClassGibbsPartition U π t h ωA β γ).toReal
  let minVal : Real := negativeLogBayesEvidence U π t h - γ * zLog
  have hClassShift :
      - β * observerClassExpectedScore U π t h ωA ν
        + γ * observerClassPriorKLDivergence U ωA ν
      =
        γ * (observerClassGibbsIGap U π t h ωA β γ ν).toReal
          - γ * zLog := by
    have hShift :=
      congrArg (fun x => x - γ * zLog)
        (observerClassGibbs_variational_igap U π t h ωA β γ hq hν hβ hγ)
    simpa [zLog, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hShift.symm
  have hExact :
      def_two_observer_functional U π t h ωB ωA β γ q ν
        = minVal
          + (posteriorIGap U π t h q).toReal
          + γ * (observerClassGibbsIGap U π t h ωA β γ ν).toReal := by
    calc
      def_two_observer_functional U π t h ωB ωA β γ q ν
          = def_afe U π t h q
              - β * observerClassExpectedScore U π t h ωA ν
              + γ * observerClassPriorKLDivergence U ωA ν := rfl
      _ = ((posteriorIGap U π t h q).toReal + negativeLogBayesEvidence U π t h)
            + (- β * observerClassExpectedScore U π t h ωA ν
                + γ * observerClassPriorKLDivergence U ωA ν) := by
              rw [lem_variational_igap U π t h q hq]
              ring
      _ = ((posteriorIGap U π t h q).toReal + negativeLogBayesEvidence U π t h)
            + (γ * (observerClassGibbsIGap U π t h ωA β γ ν).toReal - γ * zLog) := by
              rw [hClassShift]
      _ = minVal
            + (posteriorIGap U π t h q).toReal
            + γ * (observerClassGibbsIGap U π t h ωA β γ ν).toReal := by
              simp [minVal, zLog]
              ring
  have hPosteriorGapNonneg : 0 ≤ (posteriorIGap U π t h q).toReal := by
    exact ENNReal.toReal_nonneg
  have hClassGapNonneg :
      0 ≤ γ * (observerClassGibbsIGap U π t h ωA β γ ν).toReal := by
    exact mul_nonneg hγ.le ENNReal.toReal_nonneg
  have hLower : minVal ≤ def_two_observer_functional U π t h ωB ωA β γ q ν := by
    rw [hExact]
    linarith
  have hEqIff :
      def_two_observer_functional U π t h ωB ωA β γ q ν = minVal
        ↔
          (∀ p : U.Program, q p = bayesPosterior U π t h p)
            ∧
          (∀ c : ωA.Ω, ν c = observerClassGibbsLaw U π t h ωA β γ c) := by
    constructor
    · intro hMin
      rw [hExact] at hMin
      have hPosteriorGapZeroToReal : (posteriorIGap U π t h q).toReal = 0 := by
        linarith
      have hClassGapMulZero :
          γ * (observerClassGibbsIGap U π t h ωA β γ ν).toReal = 0 := by
        linarith
      have hPosteriorGapZero : posteriorIGap U π t h q = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (posteriorIGap U π t h q)).mp
          hPosteriorGapZeroToReal with hZero | hTop
        · exact hZero
        · exact False.elim ((posteriorIGap_ne_top U π t h q hq) hTop)
      have hClassGapZeroToReal :
          (observerClassGibbsIGap U π t h ωA β γ ν).toReal = 0 := by
        exact (mul_eq_zero.mp hClassGapMulZero).resolve_left hγ.ne'
      have hClassGapZero : observerClassGibbsIGap U π t h ωA β γ ν = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff
          (observerClassGibbsIGap U π t h ωA β γ ν)).mp hClassGapZeroToReal with hZero | hTop
        · exact hZero
        · exact False.elim
            ((observerClassGibbsIGap_ne_top U π t h ωA β γ hq hν hβ hγ) hTop)
      exact ⟨(lem_posterior_gap_necessity U π t h q hq).mp hPosteriorGapZero,
        (observerClassGibbsIGap_eq_zero_iff U π t h ωA β γ hq hν hβ hγ).mp hClassGapZero⟩
    · rintro ⟨hqEq, hνEq⟩
      have hPosteriorGapZero : posteriorIGap U π t h q = 0 :=
        (lem_posterior_gap_necessity U π t h q hq).mpr hqEq
      have hClassGapZero : observerClassGibbsIGap U π t h ωA β γ ν = 0 :=
        (observerClassGibbsIGap_eq_zero_iff U π t h ωA β γ hq hν hβ hγ).mpr hνEq
      rw [hExact, hPosteriorGapZero, hClassGapZero]
      simp [minVal]
  refine ⟨?_, hLower, ?_⟩
  · simpa [minVal, zLog] using hExact
  · simpa [minVal, zLog] using hEqIff

/--
Lean wrapper for `prop:kernel-functional-minimizer` on the exact countable variational stack.

The kernel lift decomposes into the Bayes evidence term, the kernel Gibbs partition correction, and
two nonnegative generalized I-gaps. Equality with the minimum constant therefore holds exactly at
the Bayes posterior and the Gibbs kernel on `C^{ω_A} × A`.
-/
theorem prop_kernel_functional_minimizer
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω] [Fintype A]
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
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw
      =
        negativeLogBayesEvidence U π t h
          - γ * Real.log (kernelGibbsPartition U ωA β γ Bbar refLaw).toReal
          + (posteriorIGap U π t h q).toReal
          + γ * (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal
      ∧
    (negativeLogBayesEvidence U π t h
        - γ * Real.log (kernelGibbsPartition U ωA β γ Bbar refLaw).toReal)
      ≤ def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw
      ∧
    (def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw
        =
          negativeLogBayesEvidence U π t h
            - γ * Real.log (kernelGibbsPartition U ωA β γ Bbar refLaw).toReal
      ↔
        (∀ p : U.Program, q p = bayesPosterior U π t h p)
          ∧
        (∀ c : ωA.Ω, ∀ a : A, κ c a = kernelGibbsLaw U ωA β γ Bbar refLaw c a)) := by
  let zLog : Real := Real.log (kernelGibbsPartition U ωA β γ Bbar refLaw).toReal
  let minVal : Real := negativeLogBayesEvidence U π t h - γ * zLog
  have hKernelShift :
      - β * kernelExpectedScore Bbar κ
        + γ * kernelPriorKLDivergence U ωA refLaw κ
      =
        γ * (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal
          - γ * zLog := by
    have hShift :=
      congrArg (fun x => x - γ * zLog)
        (kernelGibbs_variational_igap U ωA β γ Bbar hq href hκ
          hBbar_nonneg hBbar_le_one hβ hγ)
    simpa [zLog, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hShift.symm
  have hExact :
      def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw
        = minVal
          + (posteriorIGap U π t h q).toReal
          + γ * (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal := by
    calc
      def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw
          = def_afe U π t h q
              - β * kernelExpectedScore Bbar κ
              + γ * kernelPriorKLDivergence U ωA refLaw κ := rfl
      _ = ((posteriorIGap U π t h q).toReal + negativeLogBayesEvidence U π t h)
            + (- β * kernelExpectedScore Bbar κ
                + γ * kernelPriorKLDivergence U ωA refLaw κ) := by
              rw [lem_variational_igap U π t h q hq]
              ring
      _ = ((posteriorIGap U π t h q).toReal + negativeLogBayesEvidence U π t h)
            + (γ * (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal - γ * zLog) := by
              rw [hKernelShift]
      _ = minVal
            + (posteriorIGap U π t h q).toReal
            + γ * (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal := by
              simp [minVal, zLog]
              ring
  have hPosteriorGapNonneg : 0 ≤ (posteriorIGap U π t h q).toReal := by
    exact ENNReal.toReal_nonneg
  have hKernelGapNonneg :
      0 ≤ γ * (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal := by
    exact mul_nonneg hγ.le ENNReal.toReal_nonneg
  have hLower :
      minVal ≤ def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw := by
    rw [hExact]
    linarith
  have hEqIff :
      def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw = minVal
        ↔
          (∀ p : U.Program, q p = bayesPosterior U π t h p)
            ∧
          (∀ c : ωA.Ω, ∀ a : A, κ c a = kernelGibbsLaw U ωA β γ Bbar refLaw c a) := by
    constructor
    · intro hMin
      rw [hExact] at hMin
      have hPosteriorGapZeroToReal : (posteriorIGap U π t h q).toReal = 0 := by
        linarith
      have hKernelGapMulZero :
          γ * (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal = 0 := by
        linarith
      have hPosteriorGapZero : posteriorIGap U π t h q = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (posteriorIGap U π t h q)).mp
          hPosteriorGapZeroToReal with hZero | hTop
        · exact hZero
        · exact False.elim ((posteriorIGap_ne_top U π t h q hq) hTop)
      have hKernelGapZeroToReal :
          (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal = 0 := by
        exact (mul_eq_zero.mp hKernelGapMulZero).resolve_left hγ.ne'
      have hKernelGapZero : kernelGibbsIGap U ωA β γ Bbar refLaw κ = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff
          (kernelGibbsIGap U ωA β γ Bbar refLaw κ)).mp hKernelGapZeroToReal with hZero | hTop
        · exact hZero
        · exact False.elim
            ((kernelGibbsIGap_ne_top U ωA β γ Bbar hq href hκ
              hBbar_nonneg hBbar_le_one hβ hγ) hTop)
      exact ⟨(lem_posterior_gap_necessity U π t h q hq).mp hPosteriorGapZero,
        (kernelGibbsIGap_eq_zero_iff U ωA β γ Bbar hq href hκ
          hBbar_nonneg hBbar_le_one hβ hγ).mp hKernelGapZero⟩
    · rintro ⟨hqEq, hκEq⟩
      have hPosteriorGapZero : posteriorIGap U π t h q = 0 :=
        (lem_posterior_gap_necessity U π t h q hq).mpr hqEq
      have hKernelGapZero : kernelGibbsIGap U ωA β γ Bbar refLaw κ = 0 :=
        (kernelGibbsIGap_eq_zero_iff U ωA β γ Bbar hq href hκ
          hBbar_nonneg hBbar_le_one hβ hγ).mpr hκEq
      rw [hExact, hPosteriorGapZero, hKernelGapZero]
      simp [minVal]
  refine ⟨?_, hLower, ?_⟩
  · simpa [minVal, zLog] using hExact
  · simpa [minVal, zLog] using hEqIff

/--
Exact finite-action specialization of the kernel minimizer.

This is a useful finite-action chart, but it is not the manuscript's compact
Borel-action proposition. The public compact proposition is
`prop_kernel_functional_minimizer_compact` below, which uses the
measure-theoretic compact-kernel setup.
-/
theorem prop_kernel_functional_minimizer_finiteAction
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ωB ωA : Observer (CountableEncodedProgram A O))
    [Encodable ωA.Ω] [DecidableEq ωA.Ω] [Fintype A]
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
    (hβ : 0 ≤ β) (hγ : 0 < γ) :
    def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw
      =
        negativeLogBayesEvidence U π t h
          - γ * Real.log (kernelGibbsPartition U ωA β γ Bbar refLaw).toReal
          + (posteriorIGap U π t h q).toReal
          + γ * (kernelGibbsIGap U ωA β γ Bbar refLaw κ).toReal
      ∧
    (negativeLogBayesEvidence U π t h
        - γ * Real.log (kernelGibbsPartition U ωA β γ Bbar refLaw).toReal)
      ≤ def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw
      ∧
    (def_kernel_functional U π t h ωB ωA β γ Bbar q κ refLaw
        =
          negativeLogBayesEvidence U π t h
            - γ * Real.log (kernelGibbsPartition U ωA β γ Bbar refLaw).toReal
      ↔
        (∀ p : U.Program, q p = bayesPosterior U π t h p)
          ∧
        (∀ c : ωA.Ω, ∀ a : A, κ c a = kernelGibbsLaw U ωA β γ Bbar refLaw c a)) := by
  obtain ⟨hExact, hLower, hEqIff⟩ :=
    prop_kernel_functional_minimizer U π t h ωB ωA β γ Bbar
      hBbar_nonneg hBbar_le_one q hq refLaw href κ hκ hβ hγ
  exact ⟨hExact, hLower, hEqIff⟩

/--
Extended-valued measure-theoretic compact-kernel lift of the repaired belief
functional.

This is the manuscript object before restricting to the finite-KL chart. The
kernel contribution is `CompactKernel.kernelObjectiveEReal`, so non-dominated
laws remain at `⊤` rather than being projected through `ENNReal.toReal`.
-/
def def_compact_kernel_functional_measureEReal
    {C : Type w} {X : Type x} [MeasurableSpace C] [MeasurableSpace X]
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (β γ : Real)
    (B : CompactKernel.BoundedKernelScore C X)
    (q : U.Program → ENNReal)
    (κ ref : Measure (C × X)) : EReal :=
  (def_afe U π t h q : EReal) + CompactKernel.kernelObjectiveEReal β γ B κ ref

/--
The combined compact-kernel functional inherits the kernel layer's honest
extended-value behavior: if the candidate law is not dominated by the reference,
then the objective is `⊤`.
-/
theorem def_compact_kernel_functional_measureEReal_eq_top_of_not_ac
    {C : Type w} {X : Type x} [MeasurableSpace C] [MeasurableSpace X]
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    {β γ : Real} (hγ : 0 < γ)
    (B : CompactKernel.BoundedKernelScore C X)
    (q : U.Program → ENNReal)
    {κ ref : Measure (C × X)} (hκref : ¬ κ ≪ ref) :
    def_compact_kernel_functional_measureEReal U π t h β γ B q κ ref = ⊤ := by
  unfold def_compact_kernel_functional_measureEReal
  rw [CompactKernel.kernelObjectiveEReal_eq_top_of_not_ac hγ B hκref,
    EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]

/--
Finite-chart view of the measure-theoretic compact-kernel lift of the repaired
belief functional.

This is the paper's compact kernel objective on the finite-value admissible
domain: the exact belief-side AFE plus the compact measure-theoretic kernel
part `-β Eκ[B] + γ KL(κ || ref)`. The corresponding extended-valued kernel
part, including the non-dominated `+∞` branch, remains exposed in
`def_compact_kernel_functional_measureEReal`.
-/
def def_compact_kernel_functional_measure
    {C : Type w} {X : Type x} [MeasurableSpace C] [MeasurableSpace X]
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (β γ : Real)
    (B : CompactKernel.BoundedKernelScore C X)
    (q : U.Program → ENNReal)
    (κ ref : Measure (C × X)) : Real :=
  def_afe U π t h q + CompactKernel.kernelObjectiveReal β γ B κ ref

/--
Combined compact-kernel minimizer theorem on the measure-theoretic admissible
domain.

The theorem separates the two independent exact variational gaps:

* the belief gap `posteriorIGap(q || q_t*)`, supplied by the repaired
  `lem_variational_igap`;
* the compact kernel gap `KL(κ || κ_G)`, supplied by
  `CompactKernel.kernelObjectiveReal_gibbs_gap`.

Consequently the unique global minimizer on the product admissible domain is
the Bayes posterior together with the normalized compact Gibbs kernel.
-/
theorem prop_compact_kernel_functional_minimizer_measure
    {C : Type w} {X : Type x} [MeasurableSpace C] [MeasurableSpace X]
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (β γ : Real) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : CompactKernel.BoundedKernelScore C X)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q)
    (κ ref : Measure (C × X))
    [IsProbabilityMeasure κ] [IsProbabilityMeasure ref]
    (hκref : κ ≪ ref)
    (hllr : Integrable (llr κ ref) κ) :
    def_compact_kernel_functional_measure U π t h β γ B q κ ref
      =
        negativeLogBayesEvidence U π t h
          - γ * Real.log (CompactKernel.partition ref β γ B).toReal
          + (posteriorIGap U π t h q).toReal
          + γ * (CompactKernel.kernelKL κ
              (CompactKernel.gibbsMeasure ref β γ B)).toReal
      ∧
    (negativeLogBayesEvidence U π t h
        - γ * Real.log (CompactKernel.partition ref β γ B).toReal)
      ≤ def_compact_kernel_functional_measure U π t h β γ B q κ ref
      ∧
    (def_compact_kernel_functional_measure U π t h β γ B q κ ref
        =
          negativeLogBayesEvidence U π t h
            - γ * Real.log (CompactKernel.partition ref β γ B).toReal
      ↔
        (∀ p : U.Program, q p = bayesPosterior U π t h p)
          ∧
        κ = CompactKernel.gibbsMeasure ref β γ B) := by
  letI : IsProbabilityMeasure (CompactKernel.gibbsMeasure ref β γ B) :=
    CompactKernel.gibbsMeasure_isProbabilityMeasure ref hβ hγ B
  let zLog : Real := Real.log (CompactKernel.partition ref β γ B).toReal
  let minVal : Real := negativeLogBayesEvidence U π t h - γ * zLog
  have hKernelDecomp :=
    CompactKernel.kernelObjectiveReal_decomposition κ ref hβ hγ B hκref hllr
  have hExact :
      def_compact_kernel_functional_measure U π t h β γ B q κ ref
        = minVal
          + (posteriorIGap U π t h q).toReal
          + γ * (CompactKernel.kernelKL κ
              (CompactKernel.gibbsMeasure ref β γ B)).toReal := by
    calc
      def_compact_kernel_functional_measure U π t h β γ B q κ ref
          = def_afe U π t h q + CompactKernel.kernelObjectiveReal β γ B κ ref := rfl
      _ = ((posteriorIGap U π t h q).toReal + negativeLogBayesEvidence U π t h)
            + (-γ * zLog
                + γ * (CompactKernel.kernelKL κ
                    (CompactKernel.gibbsMeasure ref β γ B)).toReal) := by
              rw [lem_variational_igap U π t h q hq, hKernelDecomp]
      _ = minVal
            + (posteriorIGap U π t h q).toReal
            + γ * (CompactKernel.kernelKL κ
                (CompactKernel.gibbsMeasure ref β γ B)).toReal := by
              simp [minVal, zLog]
              ring
  have hPosteriorGapNonneg : 0 ≤ (posteriorIGap U π t h q).toReal := by
    exact ENNReal.toReal_nonneg
  have hKernelGapNonneg :
      0 ≤ γ * (CompactKernel.kernelKL κ
          (CompactKernel.gibbsMeasure ref β γ B)).toReal := by
    exact mul_nonneg hγ.le
      (CompactKernel.kernelKL_toReal_nonneg κ
        (CompactKernel.gibbsMeasure ref β γ B))
  have hLower :
      minVal ≤ def_compact_kernel_functional_measure U π t h β γ B q κ ref := by
    rw [hExact]
    linarith
  have hEqIff :
      def_compact_kernel_functional_measure U π t h β γ B q κ ref = minVal
        ↔
          (∀ p : U.Program, q p = bayesPosterior U π t h p)
            ∧
          κ = CompactKernel.gibbsMeasure ref β γ B := by
    constructor
    · intro hMin
      rw [hExact] at hMin
      have hPosteriorGapZeroToReal : (posteriorIGap U π t h q).toReal = 0 := by
        linarith
      have hKernelGapMulZero :
          γ * (CompactKernel.kernelKL κ
            (CompactKernel.gibbsMeasure ref β γ B)).toReal = 0 := by
        linarith
      have hPosteriorGapZero : posteriorIGap U π t h q = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (posteriorIGap U π t h q)).mp
          hPosteriorGapZeroToReal with hZero | hTop
        · exact hZero
        · exact False.elim ((posteriorIGap_ne_top U π t h q hq) hTop)
      have hKernelGapZeroToReal :
          (CompactKernel.kernelKL κ
            (CompactKernel.gibbsMeasure ref β γ B)).toReal = 0 := by
        exact (mul_eq_zero.mp hKernelGapMulZero).resolve_left hγ.ne'
      have hKernelKLFinite :
          CompactKernel.kernelKL κ
            (CompactKernel.gibbsMeasure ref β γ B) ≠ ⊤ :=
        CompactKernel.kernelKL_gibbs_ne_top_of_reference κ ref hβ hγ B hκref hllr
      exact ⟨
        (lem_posterior_gap_necessity U π t h q hq).mp hPosteriorGapZero,
        (CompactKernel.kernelKL_toReal_eq_zero_iff_eq_of_ne_top κ
          (CompactKernel.gibbsMeasure ref β γ B) hKernelKLFinite).mp
          hKernelGapZeroToReal⟩
    · rintro ⟨hqEq, hκEq⟩
      have hPosteriorGapZero : posteriorIGap U π t h q = 0 :=
        (lem_posterior_gap_necessity U π t h q hq).mpr hqEq
      have hKernelGapZero :
          CompactKernel.kernelKL κ (CompactKernel.gibbsMeasure ref β γ B) = 0 := by
        rw [hκEq, CompactKernel.kernelKL, klDiv_self]
      rw [hExact, hPosteriorGapZero, hKernelGapZero]
      simp [minVal]
  refine ⟨?_, hLower, ?_⟩
  · simpa [minVal, zLog] using hExact
  · simpa [minVal, zLog] using hEqIff

/--
Lean wrapper for `prop:kernel-functional-minimizer-compact` on the
measure-theoretic compact-action surface.

The public compact theorem is no longer the finite-action chart. It is stated
for a compact/Borel action space with a full-support action reference law, an
explicit class reference law, and the product reference
`CompactKernel.Setup.reference S = S.classRef.prod S.actionRef`.
-/
theorem prop_kernel_functional_minimizer_compact
    {C : Type w} {X : Type x}
    [MeasurableSpace C] [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (S : CompactKernel.Setup C X)
    (β γ : Real) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (B : CompactKernel.BoundedKernelScore C X)
    (q : U.Program → ENNReal)
    (hq : BeliefAdmissibleAt U π t h q)
    (κ : Measure (C × X))
    [IsProbabilityMeasure κ]
    (hκref : κ ≪ S.reference)
    (hllr : Integrable (llr κ S.reference) κ) :
    def_compact_kernel_functional_measure U π t h β γ B q κ S.reference
      =
        negativeLogBayesEvidence U π t h
          - γ * Real.log (CompactKernel.partition S.reference β γ B).toReal
          + (posteriorIGap U π t h q).toReal
          + γ * (CompactKernel.kernelKL κ
              (CompactKernel.gibbsMeasure S.reference β γ B)).toReal
      ∧
    (negativeLogBayesEvidence U π t h
        - γ * Real.log (CompactKernel.partition S.reference β γ B).toReal)
      ≤ def_compact_kernel_functional_measure U π t h β γ B q κ S.reference
      ∧
    (def_compact_kernel_functional_measure U π t h β γ B q κ S.reference
        =
          negativeLogBayesEvidence U π t h
            - γ * Real.log (CompactKernel.partition S.reference β γ B).toReal
      ↔
        (∀ p : U.Program, q p = bayesPosterior U π t h p)
          ∧
        κ = CompactKernel.gibbsMeasure S.reference β γ B) := by
  letI : IsProbabilityMeasure S.reference := S.reference_isProbability
  exact
    prop_compact_kernel_functional_minimizer_measure U π t h β γ hβ hγ B q hq
      κ S.reference hκref hllr

/-- Lean wrapper for `lem:merging` on the countable posterior stack. -/
theorem lem_merging
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberPosteriorWeight π t h ω p =
      U.observerFiberPosteriorWeight π t h ω q := by
  simpa using U.observerFiberPosteriorWeight_eq_of_sameView π t h ω hView

end CountablePaperBelief

end SemanticConvergence
