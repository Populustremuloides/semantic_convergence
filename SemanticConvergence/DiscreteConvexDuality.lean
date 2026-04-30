import Mathlib

/-!
# Discrete convex duality for the variational-core overhaul

This module isolates the generic countable Gibbs / KL algebra used by
`SemanticConvergence.lem_kl_necessity`.

The central result is `exactBoundedLossFormula_eq_kl`: on the countable simplex, an extended
divergence satisfying the exact bounded-loss Gibbs variational formula and sequential lower
semicontinuity agrees with the honest discrete KL divergence. The proper/convex/off-simplex
hypotheses are carried in the theorem surface to match the manuscript's natural convex class.
-/

namespace SemanticConvergence

universe u

noncomputable section

open Classical Filter Topology

section DiscreteKLDuality

variable {P : Type u} [Encodable P]

/-- Normalized countable probability weights on a countable type. -/
def ProbabilityWeight (μ : P → ENNReal) : Prop :=
  ∑' p : P, μ p = 1

/-- Bounded loss profiles on a countable type. -/
def BoundedLossProfile (L : P → Real) : Prop :=
  ∃ B : Real, 0 ≤ B ∧ ∀ p : P, |L p| ≤ B

/-- Extended-value divergence functionals on the countable simplex. -/
abbrev ExtendedDivergence (P : Type u) := (P → ENNReal) → EReal

/--
Countable-simplex `ℓ¹` distance on normalized weight functions, used as the sequential
lower-semicontinuity notion for the direct discrete duality theorem.
-/
def genericWeightL1Dist
    (q r : P → ENNReal) : Real :=
  ∑' p : P, |(q p).toReal - (r p).toReal|

/-- Properness of an extended divergence on the countable simplex. -/
def ProperOnSimplex
    (D : ExtendedDivergence P) : Prop :=
  ∃ q : P → ENNReal, ProbabilityWeight q ∧ D q ≠ ⊤ ∧ D q ≠ ⊥

/-- Off-simplex `+∞` extension semantics for a countable divergence. -/
def OffSimplexTop
    (D : ExtendedDivergence P) : Prop :=
  ∀ q : P → ENNReal, ¬ ProbabilityWeight q → D q = ⊤

/--
Sequential lower semicontinuity on the countable simplex, specialized to the `ℓ¹` distance on
unbundled discrete probability weights.
-/
def SequentialLowerSemicontinuousOnSimplex
    (D : ExtendedDivergence P) : Prop :=
  ∀ (q : P → ENNReal) (qs : Nat → P → ENNReal),
    ProbabilityWeight q → (∀ n : Nat, ProbabilityWeight (qs n)) →
    Tendsto (fun n : Nat => genericWeightL1Dist (qs n) q) atTop (𝓝 0) →
      ∀ y : Real, (y : EReal) < D q → ∀ᶠ n : Nat in atTop, (y : EReal) < D (qs n)

/-- Pointwise expected-loss contribution for a proposed countable belief `q`. -/
def genericLossContribution
    (q : P → ENNReal) (L : P → Real)
    (p : P) : Real :=
  (q p).toReal * L p

/-- Expected loss of a countable belief `q` against a loss profile `L`. -/
def genericExpectedLoss
    (q : P → ENNReal) (L : P → Real) : Real :=
  ∑' p : P, genericLossContribution q L p

/-- Extended-real view of the expected loss. -/
def genericExpectedLossEReal
    (q : P → ENNReal) (L : P → Real) : EReal :=
  (genericExpectedLoss q L : EReal)

/--
Expected reward of a countable belief against a bounded reward profile, defined as the negation of
the expected loss of the corresponding negated profile.
-/
def genericExpectedReward
    (q : P → ENNReal) (f : P → Real) : Real :=
  -genericExpectedLoss q (fun p => -f p)

/-- Extended-real view of the expected reward. -/
def genericExpectedRewardEReal
    (q : P → ENNReal) (f : P → Real) : EReal :=
  (genericExpectedReward q f : EReal)

/-- Pointwise KL contribution against a reference weight `w`. -/
def genericWeightKLDivergenceContribution
    (q w : P → ENNReal)
    (p : P) : Real :=
  if hq : q p = 0 then
    0
  else
    (q p).toReal * Real.log ((q p / w p).toReal)

/--
Honest nonnegative pointwise divergence term on nonnegative weights.

This is the discrete `r * klFun(q / r)` scalar with the standard `r = 0` convention and an
infinite penalty for positive mass placed outside the reference support. On the simplex, its total
agrees with the usual discrete KL divergence whenever that KL value is finite.
-/
def genericWeightKLDivergenceTerm
    (q r : ENNReal) : ENNReal :=
  if hqTop : q = (⊤ : ENNReal) then
    (⊤ : ENNReal)
  else if hrZero : r = 0 then
    if hqZero : q = 0 then 0 else (⊤ : ENNReal)
  else
    r * ENNReal.ofReal (InformationTheory.klFun ((q / r).toReal))

/-- Honest nonnegative total of the discrete KL/I-divergence on the countable simplex. -/
def genericWeightKLDivergenceInf
    (q w : P → ENNReal) : ENNReal :=
  ∑' p : P, genericWeightKLDivergenceTerm (q p) (w p)

/-- `KL(q || w)` on the countable discrete simplex, expressed as a `tsum` of pointwise terms. -/
def genericWeightKLDivergence
    (q w : P → ENNReal) : Real :=
  ∑' p : P, genericWeightKLDivergenceContribution q w p

/-- Extended-real view of the discrete KL term. -/
def genericWeightKLDivergenceEReal
    (q w : P → ENNReal) : EReal :=
  (genericWeightKLDivergenceInf q w : EReal)

/-- Extended-real variational value for a candidate divergence `D`. -/
def genericVariationalValue
    (D : ExtendedDivergence P)
    (q : P → ENNReal) (L : P → Real) : EReal :=
  genericExpectedLossEReal q L + D q

/-- Unnormalized Gibbs weight induced by a bounded loss profile. -/
def genericGibbsWeight
    (w : P → ENNReal) (L : P → Real)
    (p : P) : ENNReal :=
  w p * ENNReal.ofReal (Real.exp (-L p))

/-- Gibbs normalizing constant induced by a bounded loss profile. -/
def genericGibbsPartition
    (w : P → ENNReal) (L : P → Real) : ENNReal :=
  ∑' p : P, genericGibbsWeight w L p

/-- Log-partition functional `H(f) = log ∑_p w(p) e^{f(p)}` on the countable simplex. -/
def genericLogPartition
    (w : P → ENNReal) (f : P → Real) : Real :=
  Real.log (genericGibbsPartition w (fun p => -f p)).toReal

/-- Gibbs law induced by a bounded loss profile and a reference weight. -/
def genericGibbsLaw
    (w : P → ENNReal) (L : P → Real)
    (p : P) : ENNReal :=
  genericGibbsWeight w L p / genericGibbsPartition w L

/-- Honest nonnegative Gibbs-gap total against the Gibbs law induced by `w` and `L`. -/
def genericGibbsGapInf
    (q w : P → ENNReal) (L : P → Real) : ENNReal :=
  genericWeightKLDivergenceInf q (genericGibbsLaw w L)

/-- Extended-real view of the Gibbs gap. -/
def genericGibbsGapEReal
    (q w : P → ENNReal) (L : P → Real) : EReal :=
  (genericGibbsGapInf q w L : EReal)

/--
Exact bounded-loss variational formula on the countable simplex, expressed as a lower bound plus
arbitrarily sharp `ε`-attainment. This is the direct discrete replacement for the manuscript's
`inf = - log Z` statement.
-/
def ExactBoundedLossFormula
    (D : ExtendedDivergence P)
    (w : P → ENNReal) : Prop :=
  ∀ L : P → Real, BoundedLossProfile L →
    (∀ q : P → ENNReal, ProbabilityWeight q →
      (((-Real.log (genericGibbsPartition w L).toReal : Real) : EReal)) ≤
        genericVariationalValue D q L) ∧
    ∀ ε : Real, 0 < ε →
      ∃ q : P → ENNReal, ProbabilityWeight q ∧
        genericVariationalValue D q L ≤
          (((-Real.log (genericGibbsPartition w L).toReal + ε : Real) : EReal))

/-- Convexity of an extended divergence along pointwise convex combinations on the simplex. -/
def ConvexOnSimplex
    (D : ExtendedDivergence P) : Prop :=
  ∀ (q r : P → ENNReal) (a b : NNReal),
    ProbabilityWeight q → ProbabilityWeight r →
    a + b = (1 : NNReal) →
      D (fun p => ENNReal.ofNNReal a * q p + ENNReal.ofNNReal b * r p)
        ≤ (a : EReal) * D q + (b : EReal) * D r

/-- Bounded singleton reward used for the off-support `D = ⊤` branch. -/
def singletonReward
    (p0 : P) (c : Real) : P → Real :=
  fun p => if p = p0 then c else 0

/--
Truncated log-ratio profile used in the direct countable-simplex duality proof.

On the reference-zero branch we set the profile to `0`; this is harmless on the support-compatible
branch because `q(p) = 0` there as well.
-/
def truncatedLogRatio
    (q w : P → ENNReal) (n : Nat) : P → Real :=
  fun p =>
    if hq : q p = 0 then
      -(n : Real)
    else if hw : w p = 0 then
      0
    else
      max (-(n : Real))
        (min (Real.log ((q p / w p).toReal)) (n : Real))

private theorem genericWeight_ne_top_of_normalized
    {μ : P → ENNReal}
    (hμ : ProbabilityWeight μ)
    (p : P) :
    μ p ≠ ⊤ := by
  have hle : μ p ≤ 1 := by
    calc
      μ p ≤ ∑' r : P, μ r := ENNReal.le_tsum p
      _ = 1 := hμ
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

private theorem genericWeight_toReal_tsum_eq_one
    {μ : P → ENNReal}
    (hμ : ProbabilityWeight μ) :
    ∑' p : P, (μ p).toReal = 1 := by
  calc
    ∑' p : P, (μ p).toReal = (∑' p : P, μ p).toReal := by
      exact (ENNReal.tsum_toReal_eq (fun p => genericWeight_ne_top_of_normalized hμ p)).symm
    _ = 1 := by rw [hμ, ENNReal.toReal_one]

private theorem genericWeightSummable_toReal
    {μ : P → ENNReal}
    (hμ : ProbabilityWeight μ) :
    Summable (fun p : P => (μ p).toReal) := by
  exact ENNReal.summable_toReal (by rw [hμ]; simp)

/--
The honest pointwise divergence term vanishes exactly at equality whenever the reference weight is
finite.
-/
private theorem genericWeightKLDivergenceTerm_eq_zero_iff
    {q r : ENNReal} (hrTop : r ≠ (⊤ : ENNReal)) :
    genericWeightKLDivergenceTerm q r = 0 ↔ q = r := by
  by_cases hqTop : q = (⊤ : ENNReal)
  · subst hqTop
    have hTopEq : ¬ ((⊤ : ENNReal) = r) := by
      simpa [eq_comm] using hrTop
    simp [genericWeightKLDivergenceTerm, hTopEq]
  · by_cases hrZero : r = 0
    · subst hrZero
      by_cases hqZero : q = 0
      · simp [genericWeightKLDivergenceTerm, hqZero]
      · simp [genericWeightKLDivergenceTerm, hqTop, hqZero]
    · constructor
      · intro hZero
        have hMulZero :
            r * ENNReal.ofReal (InformationTheory.klFun ((q / r).toReal)) = 0 := by
          simpa [genericWeightKLDivergenceTerm, hqTop, hrZero] using hZero
        have hTermZero :
            ENNReal.ofReal (InformationTheory.klFun ((q / r).toReal)) = 0 := by
          rw [mul_eq_zero] at hMulZero
          exact hMulZero.resolve_left hrZero
        have hKlNonneg : 0 ≤ InformationTheory.klFun ((q / r).toReal) :=
          InformationTheory.klFun_nonneg ENNReal.toReal_nonneg
        have hKlZero : InformationTheory.klFun ((q / r).toReal) = 0 := by
          exact le_antisymm (ENNReal.ofReal_eq_zero.mp hTermZero) hKlNonneg
        have hRatioReal : (q / r).toReal = 1 :=
          (InformationTheory.klFun_eq_zero_iff ENNReal.toReal_nonneg).mp hKlZero
        have hRatio : q / r = 1 :=
          (ENNReal.toReal_eq_one_iff (q / r)).mp hRatioReal
        exact (ENNReal.div_eq_one_iff hrZero hrTop).mp hRatio
      · intro hqr
        subst q
        have hRatio : r / r = 1 :=
          (ENNReal.div_eq_one_iff hrZero hrTop).2 rfl
        calc
          genericWeightKLDivergenceTerm r r
              = r * ENNReal.ofReal (InformationTheory.klFun ((r / r).toReal)) := by
                  simp [genericWeightKLDivergenceTerm, hrTop, hrZero]
          _ = r * 0 := by
                rw [hRatio, ENNReal.toReal_one, InformationTheory.klFun_one, ENNReal.ofReal_zero]
          _ = 0 := by simp

private theorem genericWeightKLDivergenceTerm_eq_top_of_positive_mass_zero_ref
    {q r : ENNReal}
    (hq : q ≠ 0) (hr : r = 0) :
    genericWeightKLDivergenceTerm q r = ⊤ := by
  by_cases hqTop : q = (⊤ : ENNReal)
  · simp [genericWeightKLDivergenceTerm, hqTop]
  · simp [genericWeightKLDivergenceTerm, hqTop, hr, hq]

private theorem genericWeightKLDivergenceTerm_ne_top_of_supportCompatible
    {q r : ENNReal}
    (hqTop : q ≠ ⊤) (hrTop : r ≠ ⊤)
    (hCompat : q ≠ 0 → r ≠ 0) :
    genericWeightKLDivergenceTerm q r ≠ ⊤ := by
  by_cases hrZero : r = 0
  · have hqZero : q = 0 := by
      exact by_contra fun hqZero => (hCompat hqZero) hrZero
    simp [genericWeightKLDivergenceTerm, hrZero, hqZero]
  · simp [genericWeightKLDivergenceTerm, hqTop, hrZero, hrTop]
    exact ENNReal.mul_ne_top hrTop (by simp)

private theorem genericWeightKLDivergenceContribution_eq_term_toReal_sub
    {q r : ENNReal}
    (hqTop : q ≠ ⊤) (hrTop : r ≠ ⊤)
    (hCompat : q ≠ 0 → r ≠ 0) :
    genericWeightKLDivergenceContribution (fun _ : Unit => q) (fun _ : Unit => r) () =
      (genericWeightKLDivergenceTerm q r).toReal - r.toReal + q.toReal := by
  by_cases hqZero : q = 0
  · by_cases hrZero : r = 0
    · simp [genericWeightKLDivergenceContribution, genericWeightKLDivergenceTerm, hqZero, hrZero]
    · simp [genericWeightKLDivergenceContribution, genericWeightKLDivergenceTerm, hqTop, hqZero,
        hrZero, InformationTheory.klFun_zero]
  · have hrZero : r ≠ 0 := hCompat hqZero
    have hqReal : 0 < q.toReal := ENNReal.toReal_pos hqZero hqTop
    have hrReal : 0 < r.toReal := ENNReal.toReal_pos hrZero hrTop
    have hDivReal : (q / r).toReal = q.toReal / r.toReal := by
      rw [ENNReal.toReal_div]
    have hMulRatio : r.toReal * (q.toReal / r.toReal) = q.toReal := by
      field_simp [hrReal.ne']
    have hTermReal :
        (genericWeightKLDivergenceTerm q r).toReal =
          r.toReal * InformationTheory.klFun ((q / r).toReal) := by
      rw [show genericWeightKLDivergenceTerm q r
            = r * ENNReal.ofReal (InformationTheory.klFun ((q / r).toReal)) by
              simp [genericWeightKLDivergenceTerm, hqTop, hrZero]]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (InformationTheory.klFun_nonneg ENNReal.toReal_nonneg)]
    have hExpand :
        r.toReal * InformationTheory.klFun ((q / r).toReal) - r.toReal + q.toReal =
          q.toReal * Real.log ((q / r).toReal) := by
      let x : Real := (q / r).toReal
      have hxEq : q.toReal = r.toReal * x := by
        simpa [x] using hMulRatio.symm
      calc
        r.toReal * InformationTheory.klFun ((q / r).toReal) - r.toReal + q.toReal
            = r.toReal * (x * Real.log x + 1 - x) - r.toReal + q.toReal := by
                simpa [x] using congrArg (fun y => r.toReal * y - r.toReal + q.toReal)
                  (InformationTheory.klFun_apply ((q / r).toReal))
        _ = r.toReal * x * Real.log x := by
              rw [hxEq]
              ring
        _ = q.toReal * Real.log x := by
              simpa [hxEq] using rfl
        _ = q.toReal * Real.log ((q / r).toReal) := by simp [x]
    calc
      genericWeightKLDivergenceContribution (fun _ : Unit => q) (fun _ : Unit => r) ()
          = q.toReal * Real.log ((q / r).toReal) := by
              simp [genericWeightKLDivergenceContribution, hqZero]
      _ = r.toReal * InformationTheory.klFun ((q / r).toReal) - r.toReal + q.toReal := by
            exact hExpand.symm
      _ = (genericWeightKLDivergenceTerm q r).toReal - r.toReal + q.toReal := by
            rw [hTermReal]

private theorem genericGibbsWeight_eq_zero_iff
    (w : P → ENNReal) (L : P → Real)
    (p : P) :
    genericGibbsWeight w L p = 0 ↔ w p = 0 := by
  unfold genericGibbsWeight
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exfalso
      have hExp : (ENNReal.ofReal (Real.exp (-L p))) ≠ 0 := by
        exact ne_of_gt (by positivity : 0 < ENNReal.ofReal (Real.exp (-L p)))
      exact hExp h
  · intro hw
    exact Or.inl hw

private theorem genericGibbsWeight_ne_zero_of_prior_ne_zero
    (w : P → ENNReal) (L : P → Real)
    (p : P)
    (hw : w p ≠ 0) :
    genericGibbsWeight w L p ≠ 0 := by
  intro hZero
  exact hw ((genericGibbsWeight_eq_zero_iff w L p).mp hZero)

private theorem genericGibbsWeight_ne_top
    (w : P → ENNReal) (L : P → Real)
    (hw : ProbabilityWeight w)
    (p : P) :
    genericGibbsWeight w L p ≠ ⊤ := by
  unfold genericGibbsWeight
  exact ENNReal.mul_ne_top (genericWeight_ne_top_of_normalized hw p) (by simp)

private theorem genericGibbsPartition_ne_zero
    (w : P → ENNReal) (L : P → Real)
    (hw : ProbabilityWeight w) :
    genericGibbsPartition w L ≠ 0 := by
  have hExists : ∃ p : P, w p ≠ 0 := by
    by_contra hNone
    have hZero : ∀ p : P, w p = 0 := by
      intro p
      by_contra hp
      exact hNone ⟨p, hp⟩
    have hTsum : ∑' p : P, w p = 0 := by
      rw [ENNReal.tsum_eq_zero]
      exact hZero
    have : (1 : ENNReal) = 0 := by rw [← hw, hTsum]
    exact one_ne_zero this
  rcases hExists with ⟨p, hp⟩
  intro hZero
  have hTerms : ∀ p : P, genericGibbsWeight w L p = 0 := by
    rw [genericGibbsPartition] at hZero
    exact ENNReal.tsum_eq_zero.mp hZero
  exact (genericGibbsWeight_ne_zero_of_prior_ne_zero w L p hp) (hTerms p)

private theorem genericGibbsPartition_ne_top_of_normalized_gibbs
    (w q : P → ENNReal) (L : P → Real)
    (hq : ProbabilityWeight q)
    (hGibbs : ∀ p : P, q p = genericGibbsLaw w L p) :
    genericGibbsPartition w L ≠ ⊤ := by
  have hp0 : ∃ p : P, q p ≠ 0 := by
    by_contra hNone
    have hZero : ∀ p : P, q p = 0 := by
      intro p
      by_contra hp
      exact hNone ⟨p, hp⟩
    have hTsum : ∑' p : P, q p = 0 := by
      rw [ENNReal.tsum_eq_zero]
      exact hZero
    have : (1 : ENNReal) = 0 := by rw [← hq, hTsum]
    exact one_ne_zero this
  rcases hp0 with ⟨p0, hp0⟩
  intro hTop
  have : q p0 = 0 := by
    rw [hGibbs p0, genericGibbsLaw, hTop]
    simp
  exact hp0 this

private theorem genericSupportCompatible_of_gibbs
    (w q : P → ENNReal) (L : P → Real)
    (hq : ProbabilityWeight q)
    (hGibbs : ∀ p : P, q p = genericGibbsLaw w L p) :
    ∀ p : P, q p ≠ 0 → w p ≠ 0 := by
  intro p hqNonzero hwZero
  have hZtop : genericGibbsPartition w L ≠ ⊤ :=
    genericGibbsPartition_ne_top_of_normalized_gibbs w q L hq hGibbs
  have hLawZero : genericGibbsLaw w L p = 0 := by
    rw [genericGibbsLaw, genericGibbsWeight]
    simp [hwZero, hZtop]
  exact hqNonzero (by rw [hGibbs p]; exact hLawZero)

private theorem genericGibbsPartition_ne_top_of_bounded
    (w : P → ENNReal) (L : P → Real)
    (hw : ProbabilityWeight w)
    (hL : BoundedLossProfile L) :
    genericGibbsPartition w L ≠ ⊤ := by
  rcases hL with ⟨B, hBnonneg, hLbound⟩
  have hPoint :
      ∀ p : P, genericGibbsWeight w L p ≤ ENNReal.ofReal (Real.exp B) * w p := by
    intro p
    unfold genericGibbsWeight
    have hExpBound : ENNReal.ofReal (Real.exp (-L p)) ≤ ENNReal.ofReal (Real.exp B) := by
      have hNegLe : -L p ≤ B := by
        have hBounds := abs_le.mp (hLbound p)
        linarith
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hNegLe)
    calc
      w p * ENNReal.ofReal (Real.exp (-L p))
          ≤ w p * ENNReal.ofReal (Real.exp B) := by
              gcongr
      _ = ENNReal.ofReal (Real.exp B) * w p := by rw [mul_comm]
  have hBounded :
      genericGibbsPartition w L ≤ ENNReal.ofReal (Real.exp B) := by
    calc
      genericGibbsPartition w L
          = ∑' p : P, genericGibbsWeight w L p := rfl
      _ ≤ ∑' p : P, ENNReal.ofReal (Real.exp B) * w p := ENNReal.tsum_le_tsum hPoint
      _ = ENNReal.ofReal (Real.exp B) * ∑' p : P, w p := by
            simpa [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (Real.exp B) := by rw [hw, mul_one]
  exact ne_of_lt (lt_of_le_of_lt hBounded ENNReal.coe_lt_top)

private theorem genericGibbsLaw_normalized
    (w : P → ENNReal) (L : P → Real)
    (hw : ProbabilityWeight w)
    (hL : BoundedLossProfile L) :
    ProbabilityWeight (genericGibbsLaw w L) := by
  have hZne : genericGibbsPartition w L ≠ 0 := genericGibbsPartition_ne_zero w L hw
  have hZtop : genericGibbsPartition w L ≠ ⊤ := genericGibbsPartition_ne_top_of_bounded w L hw hL
  calc
    ∑' p : P, genericGibbsLaw w L p
        = ∑' p : P, genericGibbsWeight w L p / genericGibbsPartition w L := by
            simp [genericGibbsLaw]
    _ = (∑' p : P, genericGibbsWeight w L p) / genericGibbsPartition w L := by
          simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ = 1 := by
          unfold genericGibbsPartition
          exact ENNReal.div_self hZne hZtop

private theorem genericGibbsLaw_ne_top
    (w : P → ENNReal) (L : P → Real)
    (hw : ProbabilityWeight w)
    (hL : BoundedLossProfile L)
    (p : P) :
    genericGibbsLaw w L p ≠ ⊤ :=
  genericWeight_ne_top_of_normalized (genericGibbsLaw_normalized w L hw hL) p

private theorem genericGibbsLaw_eq_zero_iff
    (w : P → ENNReal) (L : P → Real)
    (hw : ProbabilityWeight w)
    (hL : BoundedLossProfile L)
    (p : P) :
    genericGibbsLaw w L p = 0 ↔ w p = 0 := by
  have hZtop : genericGibbsPartition w L ≠ ⊤ :=
    genericGibbsPartition_ne_top_of_bounded w L hw hL
  rw [genericGibbsLaw, ENNReal.div_eq_zero_iff, or_iff_left hZtop]
  exact genericGibbsWeight_eq_zero_iff w L p

private theorem genericExpectedLossSummable_of_bounded
    (q : P → ENNReal) (L : P → Real)
    (hq : ProbabilityWeight q)
    (hL : BoundedLossProfile L) :
    Summable (fun p : P => genericLossContribution q L p) := by
  rcases hL with ⟨B, hBnonneg, hLbound⟩
  have hqSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hBound :
      ∀ p : P, ‖genericLossContribution q L p‖ ≤ B * (q p).toReal := by
    intro p
    dsimp [genericLossContribution]
    have hqNonneg : 0 ≤ (q p).toReal := ENNReal.toReal_nonneg
    calc
      ‖(q p).toReal * L p‖ = ‖(q p).toReal‖ * ‖L p‖ := norm_mul _ _
      _ = (q p).toReal * |L p| := by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hqNonneg]
      _ ≤ (q p).toReal * B := by
            gcongr
            exact hLbound p
      _ = B * (q p).toReal := by ring
  exact Summable.of_norm_bounded (g := fun p : P => B * (q p).toReal) (hqSummable.mul_left B) hBound

private theorem boundedLossProfile_neg
    {L : P → Real}
    (hL : BoundedLossProfile L) :
    BoundedLossProfile (fun p => -L p) := by
  rcases hL with ⟨B, hBnonneg, hLbound⟩
  refine ⟨B, hBnonneg, ?_⟩
  intro p
  simpa [abs_neg] using hLbound p

private theorem boundedLossProfile_singletonReward
    (p0 : P) (c : Real) :
    BoundedLossProfile (singletonReward p0 c) := by
  refine ⟨|c|, abs_nonneg c, ?_⟩
  intro p
  unfold singletonReward
  by_cases hp : p = p0
  · simp [hp]
  · simp [hp]

private theorem boundedLossProfile_truncatedLogRatio
    (q w : P → ENNReal) (n : Nat) :
    BoundedLossProfile (truncatedLogRatio q w n) := by
  refine ⟨n, by exact_mod_cast Nat.zero_le n, ?_⟩
  intro p
  unfold truncatedLogRatio
  by_cases hq : q p = 0
  · simp [hq]
  · by_cases hw : w p = 0
    · simp [hq, hw]
    · have hLower : -(n : Real) ≤
        max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) :=
        le_max_left _ _
      have hUpper :
          max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) ≤ n := by
        exact max_le_iff.mpr ⟨by linarith, min_le_right _ _⟩
      have hAbs : |max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real))| ≤ n := by
        exact abs_le.mpr ⟨hLower, hUpper⟩
      simpa [hq, hw] using hAbs

private theorem truncatedLogRatio_eventually_eq_log
    (q w : P → ENNReal)
    (p : P)
    (hq : q p ≠ 0)
    (hw : w p ≠ 0) :
    ∀ᶠ n : Nat in atTop,
      truncatedLogRatio q w n p = Real.log ((q p / w p).toReal) := by
  let x : Real := Real.log ((q p / w p).toReal)
  obtain ⟨N, hN⟩ : ∃ N : Nat, |x| < N := exists_nat_gt |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hN' : |x| < (n : Real) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hLower : -(n : Real) < x := by
    calc
      -(n : Real) < -|x| := by linarith
      _ ≤ x := neg_abs_le x
  have hUpper : x < (n : Real) := by
    calc
      x ≤ |x| := le_abs_self x
      _ < (n : Real) := hN'
  have hMin : min x (n : Real) = x := min_eq_left (le_of_lt hUpper)
  have hMax : max (-(n : Real)) (min x (n : Real)) = x := by
    rw [hMin, max_eq_right (le_of_lt hLower)]
  have hBody :
      max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) =
        Real.log ((q p / w p).toReal) := by
    simpa [x] using hMax
  simpa [truncatedLogRatio, hq, hw] using hBody

private theorem genericGibbsWeight_truncatedLogRatio_toReal_eq_q
    (q w : P → ENNReal)
    (n : Nat)
    (p : P)
    (hq : q p ≠ 0)
    (hw : w p ≠ 0)
    (hqTop : q p ≠ ⊤)
    (hwTop : w p ≠ ⊤)
    (htr :
      truncatedLogRatio q w n p = Real.log ((q p / w p).toReal)) :
    (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal = (q p).toReal := by
  have hloss : -(fun x => -truncatedLogRatio q w n x) p = truncatedLogRatio q w n p := by
    simp
  have hDivToReal : (q p / w p).toReal = (q p).toReal / (w p).toReal := by
    rw [ENNReal.toReal_div]
  have hwRealPos : 0 < (w p).toReal := ENNReal.toReal_pos hw hwTop
  calc
    (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
        = (w p).toReal * Real.exp (truncatedLogRatio q w n p) := by
            unfold genericGibbsWeight
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), hloss]
    _ = (w p).toReal * Real.exp (Real.log ((q p / w p).toReal)) := by rw [htr]
    _ = (w p).toReal * ((q p / w p).toReal) := by
          rw [Real.exp_log (ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hq, hwTop⟩)
            (ENNReal.div_ne_top hqTop hw))]
    _ = (w p).toReal * ((q p).toReal / (w p).toReal) := by rw [hDivToReal]
    _ = (q p).toReal := by
          field_simp [hwRealPos.ne']

private theorem genericGibbsWeight_truncatedLogRatio_toReal_le_q_add_w
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (n : Nat)
    (p : P) :
    (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
      ≤ (q p).toReal + (w p).toReal := by
  have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
  have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
  have hExpToReal :
      (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
        = (w p).toReal * Real.exp (truncatedLogRatio q w n p) := by
    have hloss : -(fun x => -truncatedLogRatio q w n x) p = truncatedLogRatio q w n p := by
      simp
    unfold genericGibbsWeight
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), hloss]
  by_cases hqZero : q p = 0
  · rw [hExpToReal]
    have htr : truncatedLogRatio q w n p = -(n : Real) := by
      simpa [truncatedLogRatio, hqZero]
    rw [htr]
    have hExpLe : Real.exp (-(n : Real)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have hqRealNonneg : 0 ≤ (q p).toReal := ENNReal.toReal_nonneg
    calc
      (w p).toReal * Real.exp (-(n : Real))
          ≤ (w p).toReal * 1 := by
              gcongr
      _ ≤ (q p).toReal + (w p).toReal := by
            simp [hqZero, hqRealNonneg]
  · have hwZero : w p ≠ 0 := hCompat p hqZero
    by_cases hLow : Real.log ((q p / w p).toReal) ≤ -(n : Real)
    · rw [hExpToReal]
      have htr : truncatedLogRatio q w n p = -(n : Real) := by
        have hBody : max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) =
            -(n : Real) := by
          exact max_eq_left (le_trans (min_le_left _ _) hLow)
        simpa [truncatedLogRatio, hqZero, hwZero] using hBody
      rw [htr]
      have hExpLe : Real.exp (-(n : Real)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith
      have hqRealNonneg : 0 ≤ (q p).toReal := ENNReal.toReal_nonneg
      calc
        (w p).toReal * Real.exp (-(n : Real))
            ≤ (w p).toReal * 1 := by
                gcongr
        _ ≤ (q p).toReal + (w p).toReal := by
              linarith
    · by_cases hHigh : (n : Real) ≤ Real.log ((q p / w p).toReal)
      · rw [hExpToReal]
        have htr : truncatedLogRatio q w n p = (n : Real) := by
          have hBody : max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) =
              (n : Real) := by
            have hMin : min (Real.log ((q p / w p).toReal)) (n : Real) = (n : Real) :=
              min_eq_right hHigh
            rw [hMin]
            exact max_eq_right (by nlinarith)
          simpa [truncatedLogRatio, hqZero, hwZero] using hBody
        rw [htr]
        have hRatioLower :
            Real.exp (n : Real) ≤ ((q p / w p).toReal) := by
          calc
            Real.exp (n : Real) ≤ Real.exp (Real.log ((q p / w p).toReal)) := by
                gcongr
            _ = ((q p / w p).toReal) := by
                rw [Real.exp_log (ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hqZero, hwTop⟩)
                  (ENNReal.div_ne_top hqTop hwZero))]
        have hDivToReal : (q p / w p).toReal = (q p).toReal / (w p).toReal := by
          rw [ENNReal.toReal_div]
        have hwRealPos : 0 < (w p).toReal := ENNReal.toReal_pos hwZero hwTop
        have hwRealNonneg : 0 ≤ (w p).toReal := ENNReal.toReal_nonneg
        calc
          (w p).toReal * Real.exp (n : Real)
              ≤ (w p).toReal * ((q p / w p).toReal) := by
                  gcongr
          _ = (w p).toReal * ((q p).toReal / (w p).toReal) := by rw [hDivToReal]
          _ = (q p).toReal := by
                field_simp [hwRealPos.ne']
          _ ≤ (q p).toReal + (w p).toReal := by
                linarith
      · have htr :
          truncatedLogRatio q w n p = Real.log ((q p / w p).toReal) := by
            have hLower : -(n : Real) < Real.log ((q p / w p).toReal) := lt_of_not_ge hLow
            have hUpper : Real.log ((q p / w p).toReal) < (n : Real) := lt_of_not_ge hHigh
            have hBody :
                max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) =
                  Real.log ((q p / w p).toReal) := by
              rw [min_eq_left (le_of_lt hUpper), max_eq_right (le_of_lt hLower)]
            simpa [truncatedLogRatio, hqZero, hwZero] using hBody
        rw [genericGibbsWeight_truncatedLogRatio_toReal_eq_q q w n p hqZero hwZero hqTop hwTop htr]
        have hwRealNonneg : 0 ≤ (w p).toReal := ENNReal.toReal_nonneg
        linarith

private theorem genericGibbsWeight_truncatedLogRatio_toReal_tendsto
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (p : P) :
    Tendsto
      (fun n : Nat =>
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal)
      atTop (𝓝 ((q p).toReal)) := by
  by_cases hqZero : q p = 0
  · have hEq :
        (fun n : Nat =>
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal)
          =
        fun n : Nat => (w p).toReal * Real.exp (-(n : Real)) := by
      funext n
      have htr : truncatedLogRatio q w n p = -(n : Real) := by
        simpa [truncatedLogRatio, hqZero]
      have hloss : -(fun x => -truncatedLogRatio q w n x) p = truncatedLogRatio q w n p := by
        simp
      unfold genericGibbsWeight
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), hloss, htr]
    rw [hEq]
    simpa [hqZero] using
      (tendsto_const_nhds.mul
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop))
  · have hwZero : w p ≠ 0 := hCompat p hqZero
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [truncatedLogRatio_eventually_eq_log q w p hqZero hwZero] with n hn
    rw [genericGibbsWeight_truncatedLogRatio_toReal_eq_q q w n p hqZero hwZero hqTop hwTop hn]

private theorem genericGibbsPartition_truncatedLogRatio_toReal_tendsto_one
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0) :
    Tendsto
      (fun n : Nat =>
        (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
      atTop (𝓝 1) := by
  have hqSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hwSummable : Summable (fun p : P => (w p).toReal) := genericWeightSummable_toReal hw
  have hBoundSummable : Summable (fun p : P => (q p).toReal + (w p).toReal) :=
    hqSummable.add hwSummable
  have hPoint :
      ∀ p : P,
        Tendsto
          (fun n : Nat =>
            (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal)
          atTop (𝓝 ((q p).toReal)) :=
    genericGibbsWeight_truncatedLogRatio_toReal_tendsto q w hq hw hCompat
  have hBound :
      ∀ᶠ n : Nat in atTop,
        ∀ p : P,
          ‖(genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal‖
            ≤ (q p).toReal + (w p).toReal := by
    refine Filter.Eventually.of_forall ?_
    intro n p
    have hLe :=
      genericGibbsWeight_truncatedLogRatio_toReal_le_q_add_w q w hq hw hCompat n p
    have hNonneg :
        0 ≤ (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal :=
      ENNReal.toReal_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hNonneg] using hLe
  have hTsum :
      Tendsto
        (fun n : Nat =>
          ∑' p : P, (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal)
        atTop (𝓝 (∑' p : P, (q p).toReal)) := by
    exact tendsto_tsum_of_dominated_convergence hBoundSummable hPoint hBound
  have hEq :
      (fun n : Nat =>
        (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        =
      (fun n : Nat =>
        ∑' p : P, (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal) := by
    funext n
    unfold genericGibbsPartition
    exact ENNReal.tsum_toReal_eq (fun p =>
      genericGibbsWeight_ne_top w (fun x => -truncatedLogRatio q w n x) hw p)
  rw [hEq]
  simpa [genericWeight_toReal_tsum_eq_one hq] using hTsum

private theorem genericLogPartition_truncatedLogRatio_tendsto_zero
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0) :
    Tendsto
      (fun n : Nat => genericLogPartition w (truncatedLogRatio q w n))
      atTop (𝓝 0) := by
  have hPart :
      Tendsto
        (fun n : Nat =>
          (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 1) :=
    genericGibbsPartition_truncatedLogRatio_toReal_tendsto_one q w hq hw hCompat
  have hLog :
      Tendsto
        (fun n : Nat =>
          Real.log (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 (Real.log 1)) :=
    (Real.continuousAt_log one_ne_zero).tendsto.comp hPart
  simpa [genericLogPartition] using hLog

private theorem truncatedRewardContribution_tendsto
    (q w : P → ENNReal)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (p : P) :
    Tendsto
      (fun n : Nat => (q p).toReal * truncatedLogRatio q w n p)
      atTop (𝓝 (genericWeightKLDivergenceContribution q w p)) := by
  by_cases hqZero : q p = 0
  · have hEq :
      (fun n : Nat => (q p).toReal * truncatedLogRatio q w n p) = fun _ : Nat => 0 := by
      funext n
      simp [hqZero]
    rw [hEq]
    simpa [genericWeightKLDivergenceContribution, hqZero] using tendsto_const_nhds
  · have hwZero : w p ≠ 0 := hCompat p hqZero
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [truncatedLogRatio_eventually_eq_log q w p hqZero hwZero] with n hn
    simp [genericWeightKLDivergenceContribution, hqZero, hn]

private theorem truncatedRewardContribution_norm_le
    (q w : P → ENNReal)
    (p : P)
    (n : Nat)
    (hCompat : q p ≠ 0 → w p ≠ 0)
    (hqTop : q p ≠ ⊤)
    (hwTop : w p ≠ ⊤) :
    ‖(q p).toReal * truncatedLogRatio q w n p‖
      ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
          + (q p).toReal
          + Real.exp (-1) * (w p).toReal := by
  have hqRealNonneg : 0 ≤ (q p).toReal := ENNReal.toReal_nonneg
  have hwRealNonneg : 0 ≤ (w p).toReal := ENNReal.toReal_nonneg
  have hTermNonneg : 0 ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal := ENNReal.toReal_nonneg
  by_cases hqZero : q p = 0
  · have hRhsNonneg :
      0 ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
            + (q p).toReal
            + Real.exp (-1) * (w p).toReal := by
      positivity
    simpa [hqZero] using hRhsNonneg
  · have hwZero : w p ≠ 0 := hCompat hqZero
    let r : Real := (q p / w p).toReal
    have hrPos : 0 < r := by
      unfold r
      exact ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hqZero, hwTop⟩)
        (ENNReal.div_ne_top hqTop hwZero)
    have hwRealPos : 0 < (w p).toReal := ENNReal.toReal_pos hwZero hwTop
    have hDivToReal : r = (q p).toReal / (w p).toReal := by
      unfold r
      rw [ENNReal.toReal_div]
    by_cases hlog : 0 ≤ Real.log r
    · have hClampNonneg :
        0 ≤ max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) := by
        have hMinNonneg :
            0 ≤ min (Real.log ((q p / w p).toReal)) (n : Real) := by
          refine le_min ?_ ?_
          · simpa [r] using hlog
          · exact_mod_cast Nat.zero_le n
        exact le_trans hMinNonneg (le_max_right _ _)
      have hClampLe :
          max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real))
            ≤ Real.log ((q p / w p).toReal) := by
        refine max_le_iff.mpr ⟨?_, min_le_left _ _⟩
        have hlogNonneg' : 0 ≤ Real.log ((q p / w p).toReal) := by simpa [r] using hlog
        nlinarith
      have htrNonneg : 0 ≤ truncatedLogRatio q w n p := by
        simpa [truncatedLogRatio, hqZero, hwZero] using hClampNonneg
      have htrLe : truncatedLogRatio q w n p ≤ Real.log ((q p / w p).toReal) := by
        simpa [truncatedLogRatio, hqZero, hwZero] using hClampLe
      have hAbsEq :
          ‖(q p).toReal * truncatedLogRatio q w n p‖
            = (q p).toReal * truncatedLogRatio q w n p := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg hqRealNonneg htrNonneg
      have hTermId :
          (q p).toReal * Real.log ((q p / w p).toReal)
            = (genericWeightKLDivergenceTerm (q p) (w p)).toReal
                - (w p).toReal + (q p).toReal := by
        simpa [genericWeightKLDivergenceContribution, hqZero] using
          (genericWeightKLDivergenceContribution_eq_term_toReal_sub
            (q := q p) (r := w p) hqTop hwTop hCompat)
      calc
        ‖(q p).toReal * truncatedLogRatio q w n p‖
            = (q p).toReal * truncatedLogRatio q w n p := hAbsEq
        _ ≤ (q p).toReal * Real.log ((q p / w p).toReal) := by
              gcongr
        _ = (genericWeightKLDivergenceTerm (q p) (w p)).toReal
              - (w p).toReal + (q p).toReal := hTermId
        _ ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
              + (q p).toReal + Real.exp (-1) * (w p).toReal := by
              have hExpwNonneg : 0 ≤ Real.exp (-1) * (w p).toReal := by positivity
              linarith
    · have hlogNeg : Real.log r < 0 := lt_of_not_ge hlog
      have hClampNonpos :
          max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) ≤ 0 := by
        refine max_le_iff.mpr ⟨?_, ?_⟩
        · nlinarith
        · exact le_trans (min_le_left _ _) (by simpa [r] using hlogNeg.le)
      have hClampGe :
          Real.log ((q p / w p).toReal)
            ≤ max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) := by
        have hMinEq :
            min (Real.log ((q p / w p).toReal)) (n : Real)
              = Real.log ((q p / w p).toReal) := by
          apply min_eq_left
          have hLogLeZero : Real.log ((q p / w p).toReal) ≤ 0 := by simpa [r] using hlogNeg.le
          have hnNonneg : 0 ≤ (n : Real) := by exact_mod_cast Nat.zero_le n
          linarith
        rw [hMinEq]
        exact le_max_right _ _
      have htrNonpos : truncatedLogRatio q w n p ≤ 0 := by
        simpa [truncatedLogRatio, hqZero, hwZero] using hClampNonpos
      have htrGe : Real.log ((q p / w p).toReal) ≤ truncatedLogRatio q w n p := by
        simpa [truncatedLogRatio, hqZero, hwZero] using hClampGe
      have hAbsEq :
          ‖(q p).toReal * truncatedLogRatio q w n p‖
            = -((q p).toReal * truncatedLogRatio q w n p) := by
        rw [Real.norm_eq_abs, abs_of_nonpos]
        exact mul_nonpos_of_nonneg_of_nonpos hqRealNonneg htrNonpos
      have hNegMulLogBound : r * (-Real.log r) ≤ Real.exp (-1) := by
        simpa [mul_comm, mul_left_comm, mul_assoc, Real.exp_log hrPos] using
          (Real.mul_exp_neg_le_exp_neg_one (-Real.log r))
      have hScale :
          (q p).toReal * (-Real.log r) = (w p).toReal * (r * (-Real.log r)) := by
        rw [hDivToReal]
        field_simp [hwRealPos.ne']
      calc
        ‖(q p).toReal * truncatedLogRatio q w n p‖
            = (q p).toReal * (-truncatedLogRatio q w n p) := by
                rw [hAbsEq]
                ring_nf
        _ ≤ (q p).toReal * (-Real.log r) := by
              have hNegTruncLe : -truncatedLogRatio q w n p ≤ -Real.log r := by
                linarith
              gcongr
        _ = (w p).toReal * (r * (-Real.log r)) := hScale
        _ ≤ (w p).toReal * Real.exp (-1) := by
              gcongr
        _ ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
              + (q p).toReal + Real.exp (-1) * (w p).toReal := by
              have hBaseNonneg :
                  0 ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal + (q p).toReal := by
                positivity
              rw [mul_comm]
              linarith

private theorem exactBoundedLossFormula_nonneg
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (q : P → ENNReal)
    (hq : ProbabilityWeight q) :
    (0 : EReal) ≤ D q := by
  have hPart : genericGibbsPartition w (fun _ : P => 0) = 1 := by
    unfold genericGibbsPartition genericGibbsWeight
    simpa [hw]
  have hZeroBound := (hExact (fun _ : P => 0) ⟨0, le_rfl, by simp⟩).1 q hq
  simpa [genericVariationalValue, genericExpectedLossEReal, genericExpectedLoss,
    genericLossContribution, hPart] using hZeroBound

private theorem exactBoundedLossFormula_ne_bot
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (q : P → ENNReal)
    (hq : ProbabilityWeight q) :
    D q ≠ ⊥ := by
  exact ne_of_gt (lt_of_lt_of_le (by simp : (⊥ : EReal) < 0)
    (exactBoundedLossFormula_nonneg D w hw hExact q hq))

private theorem exactBoundedLossFormula_reward_lower_bound
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (f : P → Real)
    (hf : BoundedLossProfile f)
    (q : P → ENNReal)
    (hq : ProbabilityWeight q) :
    ((genericExpectedReward q f - genericLogPartition w f : Real) : EReal) ≤ D q := by
  have hBase :=
    (hExact (fun p => -f p) (boundedLossProfile_neg hf)).1 q hq
  have hAdd := add_le_add_left hBase (genericExpectedRewardEReal q f)
  have hCancel :
      ((genericExpectedLoss q (fun p => -f p) : Real) : EReal)
        + ((-genericExpectedLoss q (fun p => -f p) : Real) : EReal) = 0 := by
    change (((genericExpectedLoss q (fun p => -f p)) + (-genericExpectedLoss q (fun p => -f p)) : Real) : EReal) = 0
    ring_nf
    simp
  have hD_ne_bot : D q ≠ ⊥ := exactBoundedLossFormula_ne_bot D w hw hExact q hq
  calc
    ((genericExpectedReward q f - genericLogPartition w f : Real) : EReal)
        = genericExpectedRewardEReal q f
            + (((-Real.log (genericGibbsPartition w (fun p => -f p)).toReal : Real) : EReal)) := by
              simp [genericExpectedRewardEReal, genericExpectedReward, genericLogPartition, add_comm,
                add_left_comm, add_assoc, sub_eq_add_neg]
    _ ≤ genericExpectedRewardEReal q f
          + genericVariationalValue D q (fun p => -f p) := by
            simpa [add_comm, add_left_comm, add_assoc] using hAdd
    _ = D q := by
          unfold genericExpectedRewardEReal genericExpectedReward genericVariationalValue
          simpa [genericExpectedLossEReal, add_assoc, add_left_comm, add_comm, hD_ne_bot] using
            congrArg (fun x : EReal => x + D q) hCancel

private theorem genericExpectedReward_eq_tsum
    (q : P → ENNReal) (f : P → Real)
    (hq : ProbabilityWeight q)
    (hf : BoundedLossProfile f) :
    genericExpectedReward q f = ∑' p : P, (q p).toReal * f p := by
  unfold genericExpectedReward genericExpectedLoss genericLossContribution
  have hSummable :
      Summable (fun p : P => (q p).toReal * ((fun p => -f p) p)) :=
    genericExpectedLossSummable_of_bounded q (fun p => -f p) hq (boundedLossProfile_neg hf)
  calc
    -(∑' p : P, (q p).toReal * ((fun p => -f p) p))
        = ∑' p : P, -((q p).toReal * ((fun p => -f p) p)) := by
            simpa using (tsum_neg (f := fun p : P => (q p).toReal * ((fun p => -f p) p))).symm
    _ = ∑' p : P, (q p).toReal * f p := by
          apply tsum_congr
          intro p
          ring

/--
Pointwise lower-approximation term used in the direct discrete duality proof.

The total sum of these contributions is `E_q[f_n] + 1 - Z_n`, where `f_n` is the bounded truncated
log-ratio profile and `Z_n = ∑_p w(p) e^{f_n(p)}`. Since `1 - Z_n ≤ -log Z_n`, this total is
uniformly bounded above by `D q` under the exact bounded-loss variational formula.
-/
def truncatedDualContribution
    (q w : P → ENNReal) (n : Nat) (p : P) : Real :=
  (q p).toReal * truncatedLogRatio q w n p
    + (w p).toReal
    - (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal

/-- Finite-support truncation of the bounded log-ratio reward on a chosen finite set. -/
def finsetTruncatedReward
    (s : Finset P)
    (q w : P → ENNReal) (n : Nat) : P → Real :=
  fun p => if p ∈ s then truncatedLogRatio q w n p else 0

private theorem boundedLossProfile_finsetTruncatedReward
    (s : Finset P)
    (q w : P → ENNReal) (n : Nat) :
    BoundedLossProfile (finsetTruncatedReward s q w n) := by
  rcases boundedLossProfile_truncatedLogRatio q w n with ⟨B, hB, hAbs⟩
  refine ⟨B, hB, ?_⟩
  intro p
  unfold finsetTruncatedReward
  by_cases hp : p ∈ s
  · simpa [hp] using hAbs p
  · simpa [hp] using hB

private theorem truncatedDualContributionSummable
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (n : Nat) :
    Summable (fun p : P => truncatedDualContribution q w n p) := by
  have hBounded : BoundedLossProfile (truncatedLogRatio q w n) :=
    boundedLossProfile_truncatedLogRatio q w n
  have hQSummable :
      Summable (fun p : P => (q p).toReal * truncatedLogRatio q w n p) := by
    simpa using genericExpectedLossSummable_of_bounded q (truncatedLogRatio q w n) hq hBounded
  have hWSummable : Summable (fun p : P => (w p).toReal) :=
    genericWeightSummable_toReal hw
  have hPartTop :
      genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ ⊤ :=
    genericGibbsPartition_ne_top_of_bounded w (fun x => -truncatedLogRatio q w n x) hw
      (boundedLossProfile_neg hBounded)
  have hWeightSummable :
      Summable (fun p : P =>
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal) :=
    ENNReal.summable_toReal hPartTop
  have hAux :
      Summable (fun p : P =>
        (q p).toReal * truncatedLogRatio q w n p + (w p).toReal) :=
    hQSummable.add hWSummable
  refine hAux.sub ?_
  simpa using hWeightSummable

private theorem tsum_truncatedDualContribution_eq
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (n : Nat) :
    ∑' p : P, truncatedDualContribution q w n p
      =
        genericExpectedReward q (truncatedLogRatio q w n)
          + 1
          - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal := by
  have hBounded : BoundedLossProfile (truncatedLogRatio q w n) :=
    boundedLossProfile_truncatedLogRatio q w n
  have hSummable := truncatedDualContributionSummable q w hq hw n
  have hQSummable :
      Summable (fun p : P => (q p).toReal * truncatedLogRatio q w n p) := by
    simpa using genericExpectedLossSummable_of_bounded q (truncatedLogRatio q w n) hq hBounded
  have hWSummable : Summable (fun p : P => (w p).toReal) :=
    genericWeightSummable_toReal hw
  have hPartTop :
      genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ ⊤ :=
    genericGibbsPartition_ne_top_of_bounded w (fun x => -truncatedLogRatio q w n x) hw
      (boundedLossProfile_neg hBounded)
  have hWeightNeTop :
      ∀ p : P, genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p ≠ ⊤ := by
    intro p
    exact genericGibbsWeight_ne_top w (fun x => -truncatedLogRatio q w n x) hw p
  have hWeightSummable :
      Summable (fun p : P =>
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal) :=
    ENNReal.summable_toReal hPartTop
  calc
    ∑' p : P, truncatedDualContribution q w n p
        = ∑' p : P,
            ((q p).toReal * truncatedLogRatio q w n p
              + (w p).toReal
              - (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal) := by
              rfl
    _ = (∑' p : P, ((q p).toReal * truncatedLogRatio q w n p + (w p).toReal))
          - ∑' p : P,
              (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal := by
            exact Summable.tsum_sub
              (hQSummable.add hWSummable)
              hWeightSummable
    _ = ((∑' p : P, (q p).toReal * truncatedLogRatio q w n p)
            + ∑' p : P, (w p).toReal)
          - ∑' p : P,
              (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal := by
            rw [Summable.tsum_add hQSummable hWSummable]
    _ = genericExpectedReward q (truncatedLogRatio q w n)
          + 1
          - ∑' p : P,
              (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal := by
            rw [genericExpectedReward_eq_tsum q (truncatedLogRatio q w n) hq hBounded,
              genericWeight_toReal_tsum_eq_one hw]
    _ = genericExpectedReward q (truncatedLogRatio q w n)
          + 1
          - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal := by
            congr 1
            rw [show (∑' p : P,
                (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal)
                  = (∑' p : P, genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal by
                    exact (ENNReal.tsum_toReal_eq hWeightNeTop).symm]
            rfl

private theorem truncatedDualContribution_total_le_divergence
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (q : P → ENNReal)
    (hq : ProbabilityWeight q)
    (n : Nat) :
    (((∑' p : P, truncatedDualContribution q w n p) : Real) : EReal) ≤ D q := by
  have hBounded : BoundedLossProfile (truncatedLogRatio q w n) :=
    boundedLossProfile_truncatedLogRatio q w n
  have hReward :=
    exactBoundedLossFormula_reward_lower_bound D w hw hExact
      (truncatedLogRatio q w n) hBounded q hq
  have hReward' :
      ((genericExpectedReward q (truncatedLogRatio q w n)
          - Real.log (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal : Real) :
        EReal) ≤ D q := by
    simpa [genericLogPartition] using hReward
  have hZne :
      genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ 0 :=
    genericGibbsPartition_ne_zero w (fun x => -truncatedLogRatio q w n x) hw
  have hZtop :
      genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ ⊤ :=
    genericGibbsPartition_ne_top_of_bounded w (fun x => -truncatedLogRatio q w n x) hw
      (boundedLossProfile_neg hBounded)
  have hZpos : 0 < (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal :=
    ENNReal.toReal_pos hZne hZtop
  have hLog :
      ((genericExpectedReward q (truncatedLogRatio q w n)
          + 1
          - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal : Real) : EReal)
        ≤ D q := by
    have hReal :
        genericExpectedReward q (truncatedLogRatio q w n)
            + 1
            - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal
          ≤
        genericExpectedReward q (truncatedLogRatio q w n)
            - Real.log (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal := by
      have hIneq : 1 - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal
          ≤ -Real.log (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal := by
        have hLogLe := Real.log_le_sub_one_of_pos hZpos
        linarith
      linarith
    have hReal' :
        (((genericExpectedReward q (truncatedLogRatio q w n)
            + 1
            - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal : Real) :
          EReal))
          ≤
        (((genericExpectedReward q (truncatedLogRatio q w n)
            - Real.log (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal :
          Real) : EReal)) := by
      exact_mod_cast hReal
    exact hReal'.trans hReward'
  rw [tsum_truncatedDualContribution_eq q w hq hw n]
  exact hLog

private theorem genericExpectedReward_finsetTruncatedReward
    (s : Finset P)
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (n : Nat) :
    genericExpectedReward q (finsetTruncatedReward s q w n)
      = Finset.sum s (fun p => (q p).toReal * truncatedLogRatio q w n p) := by
  have hBounded : BoundedLossProfile (finsetTruncatedReward s q w n) :=
    boundedLossProfile_finsetTruncatedReward s q w n
  rw [genericExpectedReward_eq_tsum q (finsetTruncatedReward s q w n) hq hBounded]
  rw [tsum_eq_sum fun p hp => ?_]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [finsetTruncatedReward, hp]
  · simp [finsetTruncatedReward, hp]

private theorem genericExpectedReward_singletonReward
    (q : P → ENNReal)
    (p0 : P) (c : Real) :
    genericExpectedReward q (singletonReward p0 c) = (q p0).toReal * c := by
  unfold genericExpectedReward genericExpectedLoss genericLossContribution singletonReward
  have hTerm :
      (fun p : P => (q p).toReal * ((fun p => -(if p = p0 then c else 0)) p))
        = (fun p : P => -if p = p0 then (q p).toReal * c else 0) := by
    funext p
    by_cases hp : p = p0
    · simp [hp]
    · simp [hp]
  have hSeries :
      (∑' p : P, -if p = p0 then (q p).toReal * c else 0)
        = -((q p0).toReal * c) := by
    rw [tsum_eq_single p0]
    · simp
    · intro p hp
      simp [hp]
  rw [hTerm, hSeries]
  simp

private theorem genericLogPartition_singletonReward_of_zero_ref
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (p0 : P) (c : Real)
    (hw0 : w p0 = 0) :
    genericLogPartition w (singletonReward p0 c) = 0 := by
  have hPart :
      genericGibbsPartition w (fun p => -singletonReward p0 c p) = 1 := by
    unfold genericGibbsPartition
    apply calc
      ∑' p : P, genericGibbsWeight w (fun p => -singletonReward p0 c p) p
          = ∑' p : P, w p := by
              apply tsum_congr
              intro p
              unfold genericGibbsWeight singletonReward
              by_cases hp : p = p0
              · subst hp
                simp [hw0]
              · simp [hp]
      _ = 1 := hw
  unfold genericLogPartition
  simp [hPart]

/--
If a normalized law places positive mass where the reference prior is zero, then the bounded-loss
variational formula forces the candidate divergence to take the value `⊤` there.
-/
theorem exactBoundedLossFormula_eq_top_of_positive_mass_zero_ref
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (q : P → ENNReal)
    (hq : ProbabilityWeight q)
    (p0 : P)
    (hq0 : q p0 ≠ 0)
    (hw0 : w p0 = 0) :
    D q = ⊤ := by
  by_contra hDtop
  have hD_ne_bot : D q ≠ ⊥ := exactBoundedLossFormula_ne_bot D w hw hExact q hq
  have hq0RealPos : 0 < (q p0).toReal := ENNReal.toReal_pos hq0 (genericWeight_ne_top_of_normalized hq p0)
  have hLower :
      ∀ n : Nat,
        (((n : Real) * (q p0).toReal : Real) : EReal) ≤ D q := by
    intro n
    have hReward :=
      exactBoundedLossFormula_reward_lower_bound D w hw hExact
        (singletonReward p0 (n : Real))
        (boundedLossProfile_singletonReward p0 (n : Real)) q hq
    simpa [genericExpectedReward_singletonReward, genericLogPartition_singletonReward_of_zero_ref
      w hw p0 (n : Real) hw0, mul_comm, mul_left_comm, mul_assoc] using hReward
  have hUpperReal :
      ∀ n : Nat, (n : Real) * (q p0).toReal ≤ (D q).toReal := by
    intro n
    have := hLower n
    have hco : D q = ((D q).toReal : EReal) := (EReal.coe_toReal hDtop hD_ne_bot).symm
    rw [hco] at this
    exact_mod_cast (EReal.coe_le_coe_iff.mp this)
  obtain ⟨n, hn⟩ : ∃ n : Nat, (D q).toReal / (q p0).toReal < n := exists_nat_gt ((D q).toReal / (q p0).toReal)
  have hMul : (D q).toReal < (n : Real) * (q p0).toReal := by
    have := (div_lt_iff₀ hq0RealPos).mp hn
    simpa [mul_comm] using this
  exact (not_lt_of_ge (hUpperReal n)) hMul

private theorem genericWeightKLDivergenceContribution_eq_term_toReal_sub_point
    {q r : ENNReal}
    (hqTop : q ≠ ⊤) (hrTop : r ≠ ⊤)
    (hCompat : q ≠ 0 → r ≠ 0) :
    (if hq : q = 0 then 0 else q.toReal * Real.log ((q / r).toReal))
      = (genericWeightKLDivergenceTerm q r).toReal - r.toReal + q.toReal := by
  simpa [genericWeightKLDivergenceContribution] using
    (genericWeightKLDivergenceContribution_eq_term_toReal_sub (q := q) (r := r) hqTop hrTop hCompat)

private theorem truncatedDualContribution_tendsto_term
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (p : P) :
    Tendsto
      (fun n : Nat => truncatedDualContribution q w n p)
      atTop (𝓝 ((genericWeightKLDivergenceTerm (q p) (w p)).toReal)) := by
  have hReward :
      Tendsto
        (fun n : Nat => (q p).toReal * truncatedLogRatio q w n p)
        atTop (𝓝 (genericWeightKLDivergenceContribution q w p)) :=
    truncatedRewardContribution_tendsto q w hCompat p
  have hWeight :
      Tendsto
        (fun n : Nat =>
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal)
        atTop (𝓝 ((q p).toReal)) :=
    genericGibbsWeight_truncatedLogRatio_toReal_tendsto q w hq hw hCompat p
  have hTotal :
      Tendsto
        (fun n : Nat =>
          (q p).toReal * truncatedLogRatio q w n p
            + (w p).toReal
            - (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal)
        atTop
        (𝓝 (genericWeightKLDivergenceContribution q w p + (w p).toReal - (q p).toReal)) := by
    have hConstW : Tendsto (fun _ : Nat => (w p).toReal) atTop (𝓝 ((w p).toReal)) :=
      tendsto_const_nhds
    have hAdd :
        Tendsto
          (fun n : Nat =>
            (q p).toReal * truncatedLogRatio q w n p + (w p).toReal)
          atTop
          (𝓝 (genericWeightKLDivergenceContribution q w p + (w p).toReal)) :=
      hReward.add hConstW
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hAdd.sub hWeight
  have hId :
      genericWeightKLDivergenceContribution q w p + (w p).toReal - (q p).toReal =
        (genericWeightKLDivergenceTerm (q p) (w p)).toReal := by
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
    have hPoint :=
      genericWeightKLDivergenceContribution_eq_term_toReal_sub_point
        (q := q p) (r := w p) hqTop hwTop (hCompat p)
    unfold genericWeightKLDivergenceContribution
    rw [hPoint]
    ring
  simpa [truncatedDualContribution, hId] using hTotal

private theorem finset_sum_truncatedDualContribution_tendsto_term
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (s : Finset P) :
    Tendsto
      (fun n : Nat => s.sum (fun p => truncatedDualContribution q w n p))
      atTop (𝓝 (s.sum (fun p => (genericWeightKLDivergenceTerm (q p) (w p)).toReal))) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert p s hp hs =>
      simpa [Finset.sum_insert, hp] using
        (truncatedDualContribution_tendsto_term q w hq hw hCompat p).add hs

private theorem truncatedLogRatio_mem_segment_zero_log
    (q w : P → ENNReal)
    (p : P) (n : Nat)
    (hq : q p ≠ 0)
    (hw : w p ≠ 0) :
    min 0 (Real.log ((q p / w p).toReal)) ≤ truncatedLogRatio q w n p ∧
      truncatedLogRatio q w n p ≤ max 0 (Real.log ((q p / w p).toReal)) := by
  let l : Real := Real.log ((q p / w p).toReal)
  by_cases hl : 0 ≤ l
  · have hLower :
        0 ≤ max (-(n : Real)) (min l (n : Real)) := by
      have hMinNonneg : 0 ≤ min l (n : Real) := by
        refine le_min hl ?_
        exact_mod_cast Nat.zero_le n
      exact le_trans hMinNonneg (le_max_right _ _)
    have hUpper :
        max (-(n : Real)) (min l (n : Real)) ≤ l := by
      refine max_le_iff.mpr ⟨?_, min_le_left _ _⟩
      have hnNonneg : 0 ≤ (n : Real) := by exact_mod_cast Nat.zero_le n
      linarith
    constructor
    · rw [min_eq_left hl]
      simpa [l, truncatedLogRatio, hq, hw] using hLower
    · rw [max_eq_right hl]
      simpa [l, truncatedLogRatio, hq, hw] using hUpper
  · have hl' : l ≤ 0 := le_of_lt (lt_of_not_ge hl)
    have hLower :
        l ≤ max (-(n : Real)) (min l (n : Real)) := by
      have hnNonneg : 0 ≤ (n : Real) := by exact_mod_cast Nat.zero_le n
      have : l ≤ min l (n : Real) := by
        exact le_min le_rfl (by linarith)
      exact le_trans this (le_max_right _ _)
    have hUpper :
        max (-(n : Real)) (min l (n : Real)) ≤ 0 := by
      refine max_le_iff.mpr ⟨?_, ?_⟩
      · nlinarith
      · exact le_trans (min_le_left _ _) hl'
    constructor
    · rw [min_eq_right hl']
      simpa [l, truncatedLogRatio, hq, hw] using hLower
    · rw [max_eq_left hl']
      simpa [l, truncatedLogRatio, hq, hw] using hUpper

private theorem exp_le_one_add_mul_on_segment_log
    {r g : Real}
    (hr : 0 < r)
    (hg : min 0 (Real.log r) ≤ g ∧ g ≤ max 0 (Real.log r)) :
    Real.exp g ≤ 1 + r * g := by
  by_cases hlog : Real.log r = 0
  · have hgZero : g = 0 := by
      have hgLower : 0 ≤ g := by simpa [hlog] using hg.1
      have hgUpper : g ≤ 0 := by simpa [hlog] using hg.2
      linarith
    simp [hgZero]
  · let t : Real := g / Real.log r
    have hLogPosOrNeg : 0 < Real.log r ∨ Real.log r < 0 := by
      have hlog' : 0 ≠ Real.log r := by simpa [eq_comm] using hlog
      exact lt_or_gt_of_ne hlog'
    have htBounds : 0 ≤ t ∧ t ≤ 1 := by
      rcases hLogPosOrNeg with hLogPos | hLogNeg
      · have hgLower : 0 ≤ g := by
          have : min 0 (Real.log r) = 0 := min_eq_left hLogPos.le
          simpa [this] using hg.1
        have hgUpper : g ≤ Real.log r := by
          have : max 0 (Real.log r) = Real.log r := max_eq_right hLogPos.le
          simpa [this] using hg.2
        constructor
        · exact div_nonneg hgLower hLogPos.le
        · exact (div_le_one₀ hLogPos).2 hgUpper
      · have hgLower : Real.log r ≤ g := by
          have : min 0 (Real.log r) = Real.log r := min_eq_right hLogNeg.le
          simpa [this] using hg.1
        have hgUpper : g ≤ 0 := by
          have : max 0 (Real.log r) = 0 := max_eq_left hLogNeg.le
          simpa [this] using hg.2
        constructor
        · rw [div_nonneg_iff]
          right
          exact ⟨hgUpper, hLogNeg.le⟩
        · exact (div_le_one_of_neg hLogNeg).2 hgLower
    have htNonneg : 0 ≤ t := htBounds.1
    have htLeOne : t ≤ 1 := htBounds.2
    have hExpSecant :
        Real.exp g ≤ (1 - t) * Real.exp 0 + t * Real.exp (Real.log r) := by
      have hComb : (1 - t) * 0 + t * Real.log r = g := by
        have hgEq : t * Real.log r = g := by
          unfold t
          field_simp [hlog]
        simpa [hgEq]
      calc
        Real.exp g = Real.exp ((1 - t) * 0 + t * Real.log r) := by rw [hComb]
        _ ≤ (1 - t) * Real.exp 0 + t * Real.exp (Real.log r) :=
          convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (Real.log r))
            (by linarith) htNonneg (by ring)
    have hKlNonneg : 0 ≤ InformationTheory.klFun r :=
      InformationTheory.klFun_nonneg hr.le
    have hLogBound : r - 1 ≤ r * Real.log r := by
      have hEval := InformationTheory.klFun_apply r
      linarith
    have hSecantLe :
        (1 - t) * Real.exp 0 + t * Real.exp (Real.log r) ≤ 1 + r * g := by
      have hMul : t * (r - 1) ≤ t * (r * Real.log r) := by
        gcongr
      have hgEq : g = t * Real.log r := by
        unfold t
        field_simp [hlog]
      rw [Real.exp_zero, Real.exp_log hr]
      calc
        (1 - t) * 1 + t * r = 1 + t * (r - 1) := by ring
        _ ≤ 1 + t * (r * Real.log r) := by linarith
        _ = 1 + r * g := by rw [hgEq]; ring
    exact hExpSecant.trans hSecantLe

private theorem klFun_ge_sq_sqrt_sub_one
    {x : Real}
    (hx : 0 ≤ x) :
    (Real.sqrt x - 1) ^ 2 ≤ InformationTheory.klFun x := by
  let y : Real := Real.sqrt x
  have hy : 0 ≤ y := by
    unfold y
    exact Real.sqrt_nonneg _
  have hySq : y ^ 2 = x := by
    unfold y
    exact Real.sq_sqrt hx
  have hlogSq :
      Real.log (y ^ 2) = 2 * Real.log y := by
    by_cases hyZero : y = 0
    · simp [hyZero]
    · rw [sq, Real.log_mul hyZero hyZero]
      ring
  have hId :
      (y - 1) ^ 2 + 2 * y * InformationTheory.klFun y =
        InformationTheory.klFun x := by
    calc
      (y - 1) ^ 2 + 2 * y * InformationTheory.klFun y
          = y ^ 2 * Real.log (y ^ 2) + 1 - y ^ 2 := by
              rw [InformationTheory.klFun_apply, hlogSq]
              ring
      _ = InformationTheory.klFun (y ^ 2) := by
            rw [InformationTheory.klFun_apply]
      _ = InformationTheory.klFun x := by rw [hySq]
  have hNonneg :
      0 ≤ 2 * y * InformationTheory.klFun y := by
    have hKlNonneg : 0 ≤ InformationTheory.klFun y :=
      InformationTheory.klFun_nonneg hy
    nlinarith
  calc
    (Real.sqrt x - 1) ^ 2 = (y - 1) ^ 2 := by simp [y]
    _ ≤ (y - 1) ^ 2 + 2 * y * InformationTheory.klFun y := by nlinarith
    _ = InformationTheory.klFun x := hId

private theorem sq_sqrt_sub_le_genericWeightKLDivergenceTerm_toReal
    {q r : ENNReal}
    (hqTop : q ≠ ⊤)
    (hrTop : r ≠ ⊤)
    (hCompat : q ≠ 0 → r ≠ 0) :
    (Real.sqrt q.toReal - Real.sqrt r.toReal) ^ 2 ≤
      (genericWeightKLDivergenceTerm q r).toReal := by
  have hqRealNonneg : 0 ≤ q.toReal := ENNReal.toReal_nonneg
  have hrRealNonneg : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  by_cases hqZero : q = 0
  · by_cases hrZero : r = 0
    · simp [genericWeightKLDivergenceTerm, hqZero, hrZero]
    · have hTerm :
        (genericWeightKLDivergenceTerm q r).toReal = r.toReal := by
          subst q
          simp [genericWeightKLDivergenceTerm, hrZero, InformationTheory.klFun_zero]
      have hLeft : (Real.sqrt q.toReal - Real.sqrt r.toReal) ^ 2 = r.toReal := by
        rw [hqZero, ENNReal.toReal_zero, Real.sqrt_zero]
        ring_nf
        rw [Real.sq_sqrt hrRealNonneg]
      exact le_of_eq (by simpa [hTerm] using hLeft)
  · have hrZero : r ≠ 0 := hCompat hqZero
    let x : Real := (q / r).toReal
    have hxNonneg : 0 ≤ x := by
      unfold x
      exact ENNReal.toReal_nonneg
    have hrRealPos : 0 < r.toReal := ENNReal.toReal_pos hrZero hrTop
    have hqReal :
        q.toReal = r.toReal * x := by
      unfold x
      rw [ENNReal.toReal_div]
      field_simp [hrRealPos.ne']
    have hSqrt :
        Real.sqrt q.toReal = Real.sqrt r.toReal * Real.sqrt x := by
      rw [hqReal, Real.sqrt_mul hrRealNonneg]
    have hTerm :
        (genericWeightKLDivergenceTerm q r).toReal =
          r.toReal * InformationTheory.klFun x := by
      unfold x
      rw [show genericWeightKLDivergenceTerm q r
            = r * ENNReal.ofReal (InformationTheory.klFun ((q / r).toReal)) by
              simp [genericWeightKLDivergenceTerm, hqTop, hrZero]]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (InformationTheory.klFun_nonneg ENNReal.toReal_nonneg)]
    calc
      (Real.sqrt q.toReal - Real.sqrt r.toReal) ^ 2
          = (Real.sqrt r.toReal * (Real.sqrt x - 1)) ^ 2 := by
              rw [hSqrt]
              ring
      _ = (Real.sqrt r.toReal) ^ 2 * (Real.sqrt x - 1) ^ 2 := by ring
      _ = r.toReal * (Real.sqrt x - 1) ^ 2 := by
            rw [Real.sq_sqrt hrRealNonneg]
      _ ≤ r.toReal * InformationTheory.klFun x := by
            gcongr
            exact klFun_ge_sq_sqrt_sub_one hxNonneg
      _ = (genericWeightKLDivergenceTerm q r).toReal := hTerm.symm

private theorem truncatedDualContribution_nonneg
    (q w : P → ENNReal)
    (p : P) (n : Nat)
    (hCompat : q p ≠ 0 → w p ≠ 0)
    (hqTop : q p ≠ ⊤)
    (hwTop : w p ≠ ⊤) :
    0 ≤ truncatedDualContribution q w n p := by
  by_cases hqZero : q p = 0
  · have htr : truncatedLogRatio q w n p = -(n : Real) := by
      simpa [truncatedLogRatio, hqZero]
    have hWeightEq :
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal =
          (w p).toReal * Real.exp (-(n : Real)) := by
      have hloss : -(fun x => -truncatedLogRatio q w n x) p = truncatedLogRatio q w n p := by
        simp
      rw [htr] at hloss
      unfold genericGibbsWeight
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), hloss]
    have hExpLe : Real.exp (-(n : Real)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    unfold truncatedDualContribution
    rw [htr, hWeightEq]
    have hwRealNonneg : 0 ≤ (w p).toReal := ENNReal.toReal_nonneg
    have hNonneg :
        0 ≤ (w p).toReal - (w p).toReal * Real.exp (-(n : Real)) := by
      nlinarith
    simpa [hqZero, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hNonneg
  · have hwZero : w p ≠ 0 := hCompat hqZero
    let r : Real := (q p / w p).toReal
    let g : Real := truncatedLogRatio q w n p
    have hrPos : 0 < r := by
      unfold r
      exact ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hqZero, hwTop⟩)
        (ENNReal.div_ne_top hqTop hwZero)
    have hgSeg :
        min 0 (Real.log r) ≤ g ∧ g ≤ max 0 (Real.log r) := by
      simpa [r, g] using truncatedLogRatio_mem_segment_zero_log q w p n hqZero hwZero
    have hExpLe : Real.exp g ≤ 1 + r * g :=
      exp_le_one_add_mul_on_segment_log hrPos hgSeg
    have hDivToReal : r = (q p).toReal / (w p).toReal := by
      unfold r
      rw [ENNReal.toReal_div]
    have hwRealPos : 0 < (w p).toReal := ENNReal.toReal_pos hwZero hwTop
    have hWeightEq :
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal =
          (w p).toReal * Real.exp g := by
      have hloss : -(fun x => -truncatedLogRatio q w n x) p = truncatedLogRatio q w n p := by
        simp
      unfold g
      unfold genericGibbsWeight
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), hloss]
    have hWeightLe :
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
          ≤ (w p).toReal + (q p).toReal * g := by
      rw [hWeightEq]
      calc
        (w p).toReal * Real.exp g ≤ (w p).toReal * (1 + r * g) := by
          gcongr
        _ = (w p).toReal + (q p).toReal * g := by
          rw [hDivToReal]
          field_simp [hwRealPos.ne']
    unfold truncatedDualContribution
    linarith

private theorem genericWeightKLDivergenceSummable_of_finite
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0) :
    Summable (fun p : P => genericWeightKLDivergenceContribution q w p) := by
  have hTermSummable : Summable (fun p : P => (genericWeightKLDivergenceTerm (q p) (w p)).toReal) :=
    ENNReal.summable_toReal hFinite
  have hqSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hwSummable : Summable (fun p : P => (w p).toReal) := genericWeightSummable_toReal hw
  have hAux : Summable (fun p : P =>
      (genericWeightKLDivergenceTerm (q p) (w p)).toReal - (w p).toReal + (q p).toReal) :=
    (hTermSummable.sub hwSummable).add hqSummable
  refine hAux.congr ?_
  intro p
  have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
  have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
  symm
  exact genericWeightKLDivergenceContribution_eq_term_toReal_sub_point hqTop hwTop (hCompat p)

private theorem genericWeightKLDivergenceEReal_eq_of_finite
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0) :
    genericWeightKLDivergenceEReal q w = (genericWeightKLDivergence q w : EReal) := by
  have hTermNeTop :
      ∀ p : P, genericWeightKLDivergenceTerm (q p) (w p) ≠ ⊤ := by
    intro p
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
    exact genericWeightKLDivergenceTerm_ne_top_of_supportCompatible hqTop hwTop (hCompat p)
  have hKLSummable :
      Summable (fun p : P => genericWeightKLDivergenceContribution q w p) :=
    genericWeightKLDivergenceSummable_of_finite q w hq hw hFinite hCompat
  have hDiffSummable : Summable (fun p : P => (w p).toReal - (q p).toReal) :=
    (genericWeightSummable_toReal hw).sub (genericWeightSummable_toReal hq)
  have hToRealEq :
      (genericWeightKLDivergenceInf q w).toReal = genericWeightKLDivergence q w := by
    calc
      (genericWeightKLDivergenceInf q w).toReal
          = ∑' p : P, (genericWeightKLDivergenceTerm (q p) (w p)).toReal := by
              unfold genericWeightKLDivergenceInf
              exact ENNReal.tsum_toReal_eq hTermNeTop
      _ = ∑' p : P,
            (genericWeightKLDivergenceContribution q w p + ((w p).toReal - (q p).toReal)) := by
            apply tsum_congr
            intro p
            have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
            have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
            unfold genericWeightKLDivergenceContribution
            rw [genericWeightKLDivergenceContribution_eq_term_toReal_sub_point hqTop hwTop
              (hCompat p)]
            ring
      _ = genericWeightKLDivergence q w + ∑' p : P, ((w p).toReal - (q p).toReal) := by
            unfold genericWeightKLDivergence
            exact hKLSummable.tsum_add hDiffSummable
      _ = genericWeightKLDivergence q w + ((∑' p : P, (w p).toReal) - ∑' p : P, (q p).toReal) := by
            rw [Summable.tsum_sub (genericWeightSummable_toReal hw) (genericWeightSummable_toReal hq)]
      _ = genericWeightKLDivergence q w + (1 - 1) := by
            rw [genericWeight_toReal_tsum_eq_one hw, genericWeight_toReal_tsum_eq_one hq]
      _ = genericWeightKLDivergence q w := by ring
  calc
    genericWeightKLDivergenceEReal q w = ((genericWeightKLDivergenceInf q w).toReal : EReal) := by
      unfold genericWeightKLDivergenceEReal
      rw [← EReal.coe_ennreal_toReal hFinite]
    _ = (genericWeightKLDivergence q w : EReal) := by simp [hToRealEq]

private theorem genericWeightKLDivergenceEReal_eq_of_summable
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (hKLSummable : Summable (fun p : P => genericWeightKLDivergenceContribution q w p)) :
    genericWeightKLDivergenceEReal q w = (genericWeightKLDivergence q w : EReal) := by
  have hTermNeTop :
      ∀ p : P, genericWeightKLDivergenceTerm (q p) (w p) ≠ ⊤ := by
    intro p
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
    exact genericWeightKLDivergenceTerm_ne_top_of_supportCompatible hqTop hwTop (hCompat p)
  have hqSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hwSummable : Summable (fun p : P => (w p).toReal) := genericWeightSummable_toReal hw
  have hTermToRealSummable : Summable (fun p : P => (genericWeightKLDivergenceTerm (q p) (w p)).toReal) := by
    have hDiffSummable : Summable (fun p : P => (w p).toReal - (q p).toReal) :=
      hwSummable.sub hqSummable
    have hAux : Summable (fun p : P =>
        genericWeightKLDivergenceContribution q w p + ((w p).toReal - (q p).toReal)) :=
      hKLSummable.add hDiffSummable
    refine hAux.congr ?_
    intro p
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
    symm
    unfold genericWeightKLDivergenceContribution
    rw [genericWeightKLDivergenceContribution_eq_term_toReal_sub_point hqTop hwTop (hCompat p)]
    ring
  have hFinite : genericWeightKLDivergenceInf q w ≠ ⊤ := by
    have hOfRealTop :
        ∑' p : P, ENNReal.ofReal ((genericWeightKLDivergenceTerm (q p) (w p)).toReal) ≠ ⊤ :=
      hTermToRealSummable.tsum_ofReal_ne_top
    have hSeries :
        genericWeightKLDivergenceInf q w =
          ∑' p : P, ENNReal.ofReal ((genericWeightKLDivergenceTerm (q p) (w p)).toReal) := by
      unfold genericWeightKLDivergenceInf
      apply tsum_congr
      intro p
      rw [ENNReal.ofReal_toReal (hTermNeTop p)]
    simpa [hSeries] using hOfRealTop
  exact genericWeightKLDivergenceEReal_eq_of_finite q w hq hw hFinite hCompat

private theorem genericWeightKLDivergenceInf_eq_top_of_positive_mass_zero_ref
    (q w : P → ENNReal)
    (p : P)
    (hq : q p ≠ 0)
    (hw : w p = 0) :
    genericWeightKLDivergenceInf q w = ⊤ := by
  apply top_unique
  calc
    ⊤ = genericWeightKLDivergenceTerm (q p) (w p) := by
          simpa [hw] using
            (genericWeightKLDivergenceTerm_eq_top_of_positive_mass_zero_ref
              (q := q p) (r := w p) hq hw).symm
    _ ≤ ∑' r : P, genericWeightKLDivergenceTerm (q r) (w r) := ENNReal.le_tsum p

private theorem exists_large_finset_of_genericWeightKLDivergenceInf_eq_top
    (q w : P → ENNReal)
    (hInfTop : genericWeightKLDivergenceInf q w = ⊤)
    (r : ENNReal)
    (hr : r < ⊤) :
    ∃ s : Finset P, r < s.sum (fun p => genericWeightKLDivergenceTerm (q p) (w p)) := by
  have hlt :
      r < ⨆ s : Finset P, s.sum (fun p => genericWeightKLDivergenceTerm (q p) (w p)) := by
    calc
      r < ⊤ := hr
      _ = genericWeightKLDivergenceInf q w := hInfTop.symm
      _ = ⨆ s : Finset P, s.sum (fun p => genericWeightKLDivergenceTerm (q p) (w p)) := by
            rw [genericWeightKLDivergenceInf, ENNReal.tsum_eq_iSup_sum]
  simpa [lt_iSup_iff] using hlt

private theorem finset_sum_genericWeightKLDivergenceTerm_ne_top_of_supportCompatible
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (s : Finset P) :
    s.sum (fun p => genericWeightKLDivergenceTerm (q p) (w p)) ≠ ⊤ := by
  simpa using (ENNReal.sum_ne_top.2 fun p hp =>
    genericWeightKLDivergenceTerm_ne_top_of_supportCompatible
      (genericWeight_ne_top_of_normalized hq p)
      (genericWeight_ne_top_of_normalized hw p)
      (hCompat p))

private theorem exists_large_finset_of_genericWeightKLDivergenceTerm_toReal_of_top_supportCompatible
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (hInfTop : genericWeightKLDivergenceInf q w = ⊤)
    (R : Real)
    (hR : 0 ≤ R) :
    ∃ s : Finset P, R < s.sum (fun p => (genericWeightKLDivergenceTerm (q p) (w p)).toReal) := by
  obtain ⟨s, hs⟩ :=
    exists_large_finset_of_genericWeightKLDivergenceInf_eq_top q w hInfTop (ENNReal.ofReal R)
      (by simp)
  have hSumNeTop :
      s.sum (fun p => genericWeightKLDivergenceTerm (q p) (w p)) ≠ ⊤ :=
    finset_sum_genericWeightKLDivergenceTerm_ne_top_of_supportCompatible q w hq hw hCompat s
  have hsReal :
      R < (s.sum (fun p => genericWeightKLDivergenceTerm (q p) (w p))).toReal := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal hR hSumNeTop).mp hs
  refine ⟨s, ?_⟩
  rw [ENNReal.toReal_sum (s := s) (f := fun p => genericWeightKLDivergenceTerm (q p) (w p))
    (fun p hp =>
      genericWeightKLDivergenceTerm_ne_top_of_supportCompatible
        (genericWeight_ne_top_of_normalized hq p)
        (genericWeight_ne_top_of_normalized hw p)
        (hCompat p))] at hsReal
  exact hsReal

private theorem genericSupportCompatible_of_finite
    (q w : P → ENNReal)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    ∀ p : P, q p ≠ 0 → w p ≠ 0 := by
  intro p hq hp
  exact hFinite (genericWeightKLDivergenceInf_eq_top_of_positive_mass_zero_ref q w p hq hp)

private theorem genericExpectedReward_truncatedLogRatio_tendsto_kl_of_finite
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    Tendsto
      (fun n : Nat => genericExpectedReward q (truncatedLogRatio q w n))
      atTop (𝓝 (genericWeightKLDivergence q w)) := by
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 := genericSupportCompatible_of_finite q w hFinite
  have hqSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hwSummable : Summable (fun p : P => (w p).toReal) := genericWeightSummable_toReal hw
  have hTermSummable :
      Summable (fun p : P => (genericWeightKLDivergenceTerm (q p) (w p)).toReal) :=
    ENNReal.summable_toReal hFinite
  have hBoundSummable :
      Summable
        (fun p : P =>
          (genericWeightKLDivergenceTerm (q p) (w p)).toReal
            + (q p).toReal
            + Real.exp (-1) * (w p).toReal) := by
    exact (hTermSummable.add hqSummable).add (hwSummable.mul_left (Real.exp (-1)))
  have hPoint :
      ∀ p : P,
        Tendsto
          (fun n : Nat => (q p).toReal * truncatedLogRatio q w n p)
          atTop (𝓝 (genericWeightKLDivergenceContribution q w p)) :=
    truncatedRewardContribution_tendsto q w hCompat
  have hBound :
      ∀ᶠ n : Nat in atTop,
        ∀ p : P,
          ‖(q p).toReal * truncatedLogRatio q w n p‖
            ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
                + (q p).toReal
                + Real.exp (-1) * (w p).toReal := by
    refine Filter.Eventually.of_forall ?_
    intro n p
    exact truncatedRewardContribution_norm_le q w p n
      (hCompat p)
      (genericWeight_ne_top_of_normalized hq p)
      (genericWeight_ne_top_of_normalized hw p)
  have hTsum :
      Tendsto
        (fun n : Nat => ∑' p : P, (q p).toReal * truncatedLogRatio q w n p)
        atTop (𝓝 (∑' p : P, genericWeightKLDivergenceContribution q w p)) := by
    exact tendsto_tsum_of_dominated_convergence hBoundSummable hPoint hBound
  have hEq :
      (fun n : Nat => genericExpectedReward q (truncatedLogRatio q w n))
        =
      (fun n : Nat => ∑' p : P, (q p).toReal * truncatedLogRatio q w n p) := by
    funext n
    rw [genericExpectedReward_eq_tsum q (truncatedLogRatio q w n) hq
      (boundedLossProfile_truncatedLogRatio q w n)]
  rw [hEq]
  simpa [genericWeightKLDivergence] using hTsum

private theorem exactBoundedLossFormula_ge_kl_of_finite
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (q : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    genericWeightKLDivergenceEReal q w ≤ D q := by
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 := genericSupportCompatible_of_finite q w hFinite
  have hReward :
      Tendsto
        (fun n : Nat => genericExpectedReward q (truncatedLogRatio q w n))
        atTop (𝓝 (genericWeightKLDivergence q w)) :=
    genericExpectedReward_truncatedLogRatio_tendsto_kl_of_finite q w hq hw hFinite
  have hPart :
      Tendsto
        (fun n : Nat =>
          (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 1) :=
    genericGibbsPartition_truncatedLogRatio_toReal_tendsto_one q w hq hw hCompat
  have hConstOne : Tendsto (fun _ : Nat => (1 : Real)) atTop (𝓝 1) := tendsto_const_nhds
  have hTail :
      Tendsto
        (fun n : Nat =>
          (1 : Real) - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 0) := by
    simpa using (hConstOne.sub hPart)
  have hTotal :
      Tendsto
        (fun n : Nat =>
          genericExpectedReward q (truncatedLogRatio q w n)
            + 1
            - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 (genericWeightKLDivergence q w)) := by
    have hAdd :
        Tendsto
          (fun n : Nat =>
            genericExpectedReward q (truncatedLogRatio q w n)
              + ((1 : Real) - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal))
          atTop (𝓝 (genericWeightKLDivergence q w + 0)) :=
      hReward.add hTail
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hAdd
  have hSeqLe :
      ∀ n : Nat,
        (((genericExpectedReward q (truncatedLogRatio q w n)
            + 1
            - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal : Real) :
          EReal))
          ≤ D q := by
    intro n
    simpa [tsum_truncatedDualContribution_eq q w hq hw n] using
      truncatedDualContribution_total_le_divergence D w hw hExact q hq n
  have hTotalEReal :
      Tendsto
        (fun n : Nat =>
          (((genericExpectedReward q (truncatedLogRatio q w n)
              + 1
              - (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal : Real) :
            EReal)))
        atTop (𝓝 ((genericWeightKLDivergence q w : Real) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hTotal
  have hLe :
      ((genericWeightKLDivergence q w : Real) : EReal) ≤ D q := by
    exact le_of_tendsto hTotalEReal (Filter.Eventually.of_forall hSeqLe)
  have hKLEReal :
      genericWeightKLDivergenceEReal q w = (genericWeightKLDivergence q w : EReal) :=
    genericWeightKLDivergenceEReal_eq_of_finite q w hq hw hFinite hCompat
  simpa [hKLEReal] using hLe

private theorem exactBoundedLossFormula_eq_top_of_supportCompatible_infinite
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (q : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (hInfTop : genericWeightKLDivergenceInf q w = ⊤) :
    D q = ⊤ := by
  by_contra hD_ne_top
  have hD_ne_bot : D q ≠ ⊥ := exactBoundedLossFormula_ne_bot D w hw hExact q hq
  have hD_nonneg : (0 : EReal) ≤ D q := exactBoundedLossFormula_nonneg D w hw hExact q hq
  let R : Real := (D q).toReal + 1
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    linarith [EReal.toReal_nonneg hD_nonneg]
  obtain ⟨s, hsLarge⟩ :=
    exists_large_finset_of_genericWeightKLDivergenceTerm_toReal_of_top_supportCompatible
      q w hq hw hCompat hInfTop R hRnonneg
  have hTendsto :=
    finset_sum_truncatedDualContribution_tendsto_term q w hq hw hCompat s
  have hEventuallyLarge :
      ∀ᶠ n : Nat in atTop, R < s.sum (fun p => truncatedDualContribution q w n p) := by
    have hMem :
        Set.Ioi R ∈
          𝓝 (s.sum (fun p => (genericWeightKLDivergenceTerm (q p) (w p)).toReal)) :=
      Ioi_mem_nhds hsLarge
    exact hTendsto hMem
  rcases Filter.eventually_atTop.1 hEventuallyLarge with ⟨N, hN⟩
  have hLargeN : R < s.sum (fun p => truncatedDualContribution q w N p) := hN N le_rfl
  have hUpperN :
      s.sum (fun p => truncatedDualContribution q w N p) ≤ (D q).toReal := by
    have hFinLeTsum :
        s.sum (fun p => truncatedDualContribution q w N p)
          ≤ ∑' p : P, truncatedDualContribution q w N p := by
      exact Summable.sum_le_tsum s
        (fun p hp =>
          truncatedDualContribution_nonneg q w p N (hCompat p)
            (genericWeight_ne_top_of_normalized hq p)
            (genericWeight_ne_top_of_normalized hw p))
        (truncatedDualContributionSummable q w hq hw N)
    have hTsumLe :
        ((((∑' p : P, truncatedDualContribution q w N p) : Real) : EReal)) ≤ D q :=
      truncatedDualContribution_total_le_divergence D w hw hExact q hq N
    have hTsumLeReal :
        (∑' p : P, truncatedDualContribution q w N p) ≤ (D q).toReal := by
      rw [(EReal.coe_toReal hD_ne_top hD_ne_bot).symm] at hTsumLe
      exact EReal.coe_le_coe_iff.mp hTsumLe
    exact hFinLeTsum.trans hTsumLeReal
  have hUpperNR : s.sum (fun p => truncatedDualContribution q w N p) ≤ R := by
    dsimp [R]
    linarith
  have : ¬ R < s.sum (fun p => truncatedDualContribution q w N p) := not_lt_of_ge hUpperNR
  exact this hLargeN

/--
Any divergence satisfying the exact bounded-loss variational formula dominates the honest discrete
KL term pointwise on the countable simplex.

This is the `D ≥ KL` half of the manuscript's convex-duality argument. The proof handles all three
branches honestly:
- finite KL, via the truncated-reward limit argument
- infinite KL from off-support positive mass, forcing `D q = ⊤`
- infinite KL with support compatibility, forcing `D q = ⊤` by the finite-subset truncation
  contradiction proved above
-/
theorem exactBoundedLossFormula_ge_kl
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (q : P → ENNReal)
    (hq : ProbabilityWeight q) :
    genericWeightKLDivergenceEReal q w ≤ D q := by
  by_cases hFinite : genericWeightKLDivergenceInf q w ≠ ⊤
  · exact exactBoundedLossFormula_ge_kl_of_finite D w hw hExact q hq hFinite
  · have hInfTop : genericWeightKLDivergenceInf q w = ⊤ := not_ne_iff.mp hFinite
    by_cases hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0
    · have hDTop :
          D q = ⊤ :=
        exactBoundedLossFormula_eq_top_of_supportCompatible_infinite
          D w hw hExact q hq hCompat hInfTop
      simp [genericWeightKLDivergenceEReal, hInfTop, hDTop]
    · push_neg at hCompat
      rcases hCompat with ⟨p, hqp, hwp⟩
      have hDTop :
          D q = ⊤ :=
        exactBoundedLossFormula_eq_top_of_positive_mass_zero_ref
          D w hw hExact q hq p hqp hwp
      simp [genericWeightKLDivergenceEReal, hInfTop, hDTop]

private theorem finset_sum_abs_toReal_sub_le_two_sqrt_sum_term
    (q r : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hr : ProbabilityWeight r)
    (hFinite : genericWeightKLDivergenceInf q r ≠ ⊤)
    (s : Finset P) :
    s.sum (fun p => |(q p).toReal - (r p).toReal|) ≤
      2 * Real.sqrt (s.sum (fun p => (genericWeightKLDivergenceTerm (q p) (r p)).toReal)) := by
  let aq : P → Real := fun p => (q p).toReal
  let ar : P → Real := fun p => (r p).toReal
  have hCompat : ∀ p : P, q p ≠ 0 → r p ≠ 0 := genericSupportCompatible_of_finite q r hFinite
  have hPoint :
      ∀ p : P,
        |aq p - ar p| =
          |Real.sqrt (aq p) - Real.sqrt (ar p)| * (Real.sqrt (aq p) + Real.sqrt (ar p)) := by
    intro p
    have haq : 0 ≤ aq p := by unfold aq; exact ENNReal.toReal_nonneg
    have har : 0 ≤ ar p := by unfold ar; exact ENNReal.toReal_nonneg
    have hId :
        aq p - ar p =
          (Real.sqrt (aq p) - Real.sqrt (ar p)) * (Real.sqrt (aq p) + Real.sqrt (ar p)) := by
      unfold aq ar
      rw [sub_eq_add_neg]
      ring_nf
      rw [Real.sq_sqrt (ENNReal.toReal_nonneg), Real.sq_sqrt (ENNReal.toReal_nonneg)]
    have hsumNonneg : 0 ≤ Real.sqrt (aq p) + Real.sqrt (ar p) := by
      exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc
      |aq p - ar p|
          = |(Real.sqrt (aq p) - Real.sqrt (ar p)) *
              (Real.sqrt (aq p) + Real.sqrt (ar p))| := by rw [hId]
      _ = |Real.sqrt (aq p) - Real.sqrt (ar p)| *
            |Real.sqrt (aq p) + Real.sqrt (ar p)| := by rw [abs_mul]
      _ = |Real.sqrt (aq p) - Real.sqrt (ar p)| *
            (Real.sqrt (aq p) + Real.sqrt (ar p)) := by
              rw [abs_of_nonneg hsumNonneg]
  have hFirstSq :
      ∑ p ∈ s, (|Real.sqrt (aq p) - Real.sqrt (ar p)|) ^ 2 ≤
        ∑ p ∈ s, (genericWeightKLDivergenceTerm (q p) (r p)).toReal := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    have hrTop : r p ≠ ⊤ := genericWeight_ne_top_of_normalized hr p
    have hHell :
        (Real.sqrt (aq p) - Real.sqrt (ar p)) ^ 2 ≤
          (genericWeightKLDivergenceTerm (q p) (r p)).toReal := by
      unfold aq ar
      exact sq_sqrt_sub_le_genericWeightKLDivergenceTerm_toReal hqTop hrTop (hCompat p)
    simpa [sq_abs] using hHell
  have hQPartial :
      s.sum (fun p => aq p) ≤ 1 := by
    have hqSummable : Summable (fun p : P => aq p) := by
      unfold aq
      exact genericWeightSummable_toReal hq
    calc
      s.sum (fun p => aq p) ≤ ∑' p : P, aq p := by
        exact hqSummable.sum_le_tsum _ (by intro p hp; exact ENNReal.toReal_nonneg)
      _ = 1 := by
            unfold aq
            exact genericWeight_toReal_tsum_eq_one hq
  have hRPartial :
      s.sum (fun p => ar p) ≤ 1 := by
    have hrSummable : Summable (fun p : P => ar p) := by
      unfold ar
      exact genericWeightSummable_toReal hr
    calc
      s.sum (fun p => ar p) ≤ ∑' p : P, ar p := by
        exact hrSummable.sum_le_tsum _ (by intro p hp; exact ENNReal.toReal_nonneg)
      _ = 1 := by
            unfold ar
            exact genericWeight_toReal_tsum_eq_one hr
  have hSecondSq :
      ∑ p ∈ s, (Real.sqrt (aq p) + Real.sqrt (ar p)) ^ 2 ≤ 4 := by
    calc
      ∑ p ∈ s, (Real.sqrt (aq p) + Real.sqrt (ar p)) ^ 2
          ≤ ∑ p ∈ s, 2 * (aq p + ar p) := by
              refine Finset.sum_le_sum ?_
              intro p hp
              have haq : 0 ≤ aq p := by unfold aq; exact ENNReal.toReal_nonneg
              have har : 0 ≤ ar p := by unfold ar; exact ENNReal.toReal_nonneg
              have hAMGM :
                  2 * Real.sqrt (aq p) * Real.sqrt (ar p) ≤ aq p + ar p := by
                have hSqNonneg :
                    0 ≤ (Real.sqrt (aq p) - Real.sqrt (ar p)) ^ 2 := by
                  exact sq_nonneg _
                have hSqExpand :
                    (Real.sqrt (aq p) - Real.sqrt (ar p)) ^ 2 =
                      aq p + ar p - 2 * Real.sqrt (aq p) * Real.sqrt (ar p) := by
                  calc
                    (Real.sqrt (aq p) - Real.sqrt (ar p)) ^ 2
                        = (Real.sqrt (aq p)) ^ 2 + (Real.sqrt (ar p)) ^ 2 -
                            2 * Real.sqrt (aq p) * Real.sqrt (ar p) := by
                              ring
                    _ = aq p + ar p - 2 * Real.sqrt (aq p) * Real.sqrt (ar p) := by
                          rw [Real.sq_sqrt haq, Real.sq_sqrt har]
                nlinarith [hSqNonneg, hSqExpand]
              calc
                (Real.sqrt (aq p) + Real.sqrt (ar p)) ^ 2
                    = (Real.sqrt (aq p)) ^ 2 + (Real.sqrt (ar p)) ^ 2 +
                        2 * Real.sqrt (aq p) * Real.sqrt (ar p) := by
                          ring
                _ = aq p + ar p + 2 * Real.sqrt (aq p) * Real.sqrt (ar p) := by
                      rw [Real.sq_sqrt haq, Real.sq_sqrt har]
                _ ≤ aq p + ar p + (aq p + ar p) := by linarith
                _ = 2 * (aq p + ar p) := by ring
      _ = ∑ p ∈ s, (2 * aq p + 2 * ar p) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            ring
      _ = (∑ p ∈ s, 2 * aq p) + (∑ p ∈ s, 2 * ar p) := by
            rw [Finset.sum_add_distrib]
      _ = 2 * s.sum (fun p => aq p) + 2 * s.sum (fun p => ar p) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * (s.sum (fun p => aq p) + s.sum (fun p => ar p)) := by ring
      _ ≤ 2 * (1 + 1) := by gcongr
      _ = 4 := by ring
  have hFirstSqrt :
      Real.sqrt (∑ p ∈ s, (|Real.sqrt (aq p) - Real.sqrt (ar p)|) ^ 2) ≤
        Real.sqrt (∑ p ∈ s, (genericWeightKLDivergenceTerm (q p) (r p)).toReal) := by
    exact Real.sqrt_le_sqrt hFirstSq
  have hSecondSqrt :
      Real.sqrt (∑ p ∈ s, (Real.sqrt (aq p) + Real.sqrt (ar p)) ^ 2) ≤ 2 := by
    have h' :
        Real.sqrt (∑ p ∈ s, (Real.sqrt (aq p) + Real.sqrt (ar p)) ^ 2) ≤ Real.sqrt 4 :=
      Real.sqrt_le_sqrt hSecondSq
    have hsqrt4 : Real.sqrt 4 = 2 := by norm_num
    simpa [hsqrt4] using h'
  calc
    s.sum (fun p => |(q p).toReal - (r p).toReal|)
        = ∑ p ∈ s,
            |Real.sqrt (aq p) - Real.sqrt (ar p)| *
              (Real.sqrt (aq p) + Real.sqrt (ar p)) := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                simpa using hPoint p
    _ ≤
        Real.sqrt (∑ p ∈ s, (|Real.sqrt (aq p) - Real.sqrt (ar p)|) ^ 2) *
          Real.sqrt (∑ p ∈ s, (Real.sqrt (aq p) + Real.sqrt (ar p)) ^ 2) := by
            simpa using
              Real.sum_mul_le_sqrt_mul_sqrt s
                (fun p => |Real.sqrt (aq p) - Real.sqrt (ar p)|)
                (fun p => Real.sqrt (aq p) + Real.sqrt (ar p))
    _ ≤ Real.sqrt (∑ p ∈ s, (genericWeightKLDivergenceTerm (q p) (r p)).toReal) * 2 := by
          gcongr
    _ = 2 * Real.sqrt (∑ p ∈ s, (genericWeightKLDivergenceTerm (q p) (r p)).toReal) := by
          ring

private theorem genericWeightL1Dist_le_two_sqrt_of_finite
    (q r : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hr : ProbabilityWeight r)
    (hFinite : genericWeightKLDivergenceInf q r ≠ ⊤) :
    genericWeightL1Dist q r ≤
      2 * Real.sqrt (genericWeightKLDivergence q r) := by
  let a : P → NNReal := fun p => ⟨|(q p).toReal - (r p).toReal|, abs_nonneg _⟩
  have hCompat : ∀ p : P, q p ≠ 0 → r p ≠ 0 := genericSupportCompatible_of_finite q r hFinite
  have hTermNeTop :
      ∀ p : P, genericWeightKLDivergenceTerm (q p) (r p) ≠ ⊤ := by
    intro p
    exact genericWeightKLDivergenceTerm_ne_top_of_supportCompatible
      (genericWeight_ne_top_of_normalized hq p)
      (genericWeight_ne_top_of_normalized hr p)
      (hCompat p)
  have hPartialTermLe :
      ∀ s : Finset P,
        s.sum (fun p => (genericWeightKLDivergenceTerm (q p) (r p)).toReal) ≤
          (genericWeightKLDivergenceInf q r).toReal := by
    intro s
    have hSumLe :
        s.sum (fun p => genericWeightKLDivergenceTerm (q p) (r p))
          ≤ genericWeightKLDivergenceInf q r := by
      unfold genericWeightKLDivergenceInf
      exact ENNReal.sum_le_tsum s
    have hToRealSum :
        (s.sum (fun p => genericWeightKLDivergenceTerm (q p) (r p))).toReal =
          s.sum (fun p => (genericWeightKLDivergenceTerm (q p) (r p)).toReal) := by
      simpa using
        (ENNReal.toReal_sum (s := s)
          (f := fun p => genericWeightKLDivergenceTerm (q p) (r p))
          (fun p hp => hTermNeTop p))
    calc
      s.sum (fun p => (genericWeightKLDivergenceTerm (q p) (r p)).toReal)
          = (s.sum (fun p => genericWeightKLDivergenceTerm (q p) (r p))).toReal := by
              symm
              exact hToRealSum
      _ ≤ (genericWeightKLDivergenceInf q r).toReal := by
            exact ENNReal.toReal_mono hFinite hSumLe
  have hPartialAbsLe :
      ∀ s : Finset P,
        s.sum (fun p => (a p : Real)) ≤
          2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal) := by
    intro s
    calc
      s.sum (fun p => (a p : Real))
          = s.sum (fun p => |(q p).toReal - (r p).toReal|) := by simp [a]
      _ ≤ 2 * Real.sqrt (s.sum (fun p => (genericWeightKLDivergenceTerm (q p) (r p)).toReal)) :=
            finset_sum_abs_toReal_sub_le_two_sqrt_sum_term q r hq hr hFinite s
      _ ≤ 2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal) := by
            gcongr
            exact hPartialTermLe s
  have hTsumLe :
      ∑' p : P, (a p : ENNReal) ≤
        ENNReal.ofReal (2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal)) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le ?_
    intro s
    have hs :
        s.sum (fun p => (a p : Real)) ≤
          2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal) :=
      hPartialAbsLe s
    have hsumEq :
        (∑ p ∈ s, (a p : ENNReal)) =
          ENNReal.ofReal (∑ p ∈ s, (a p : Real)) := by
      symm
      simpa using
        (ENNReal.ofReal_sum_of_nonneg
          (s := s) (f := fun p => (a p : Real)) (fun p hp => (a p).2))
    have hsENN :
        (∑ p ∈ s, (a p : ENNReal)) ≤
          ENNReal.ofReal (2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal)) := by
      have hsENN' :
          ENNReal.ofReal (∑ p ∈ s, (a p : Real)) ≤
            ENNReal.ofReal (2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal)) :=
        ENNReal.ofReal_le_ofReal hs
      simpa [hsumEq] using hsENN'
    simpa using hsENN
  have hTsumNeTop :
      ∑' p : P, (a p : ENNReal) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hTsumLe ENNReal.ofReal_lt_top)
  have hSummableAReal : Summable (fun p : P => (a p : Real)) :=
    (ENNReal.tsum_coe_ne_top_iff_summable_coe).1 hTsumNeTop
  have hSummableA : Summable a :=
    (NNReal.summable_coe).1 hSummableAReal
  have hRealEq :
      (genericWeightKLDivergenceInf q r).toReal = genericWeightKLDivergence q r := by
    have hEReal :
        genericWeightKLDivergenceEReal q r = (genericWeightKLDivergence q r : EReal) :=
      genericWeightKLDivergenceEReal_eq_of_finite q r hq hr hFinite hCompat
    unfold genericWeightKLDivergenceEReal at hEReal
    rw [← EReal.coe_ennreal_toReal hFinite] at hEReal
    exact EReal.coe_injective hEReal
  have hTsumLeENN :
      ((∑' p : P, a p : NNReal) : ENNReal) ≤
        ENNReal.ofReal (2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal)) := by
    simpa [ENNReal.coe_tsum hSummableA] using hTsumLe
  have hRealLe :
      ((∑' p : P, a p : NNReal) : Real) ≤
        2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal) := by
    have hRealLe' :
        (((∑' p : P, a p : NNReal) : ENNReal)).toReal ≤
          (ENNReal.ofReal (2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal))).toReal := by
      exact
        (ENNReal.toReal_le_toReal (by simp) ENNReal.ofReal_ne_top).2 hTsumLeENN
    simpa [ENNReal.toReal_ofReal, Real.sqrt_nonneg] using hRealLe'
  have hL1Eq :
      genericWeightL1Dist q r = ((∑' p : P, a p : NNReal) : Real) := by
    unfold genericWeightL1Dist
    calc
      ∑' p : P, |(q p).toReal - (r p).toReal|
          = ∑' p : P, ((a p : NNReal) : Real) := by
              apply tsum_congr
              intro p
              simp [a]
      _ = ((∑' p : P, a p : NNReal) : Real) := by
            rw [NNReal.coe_tsum]
  calc
    genericWeightL1Dist q r = ((∑' p : P, a p : NNReal) : Real) := hL1Eq
    _ ≤ 2 * Real.sqrt ((genericWeightKLDivergenceInf q r).toReal) := hRealLe
    _ = 2 * Real.sqrt (genericWeightKLDivergence q r) := by simp [hRealEq]

private theorem genericExpectedReward_lipschitz_of_bounded
    (q r : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hr : ProbabilityWeight r)
    (f : P → Real)
    (hf : BoundedLossProfile f) :
    |genericExpectedReward q f - genericExpectedReward r f|
      ≤ (Classical.choose hf) * genericWeightL1Dist q r := by
  let B : Real := Classical.choose hf
  have hB_nonneg : 0 ≤ B := (Classical.choose_spec hf).1
  have hB_bound : ∀ p : P, |f p| ≤ B := (Classical.choose_spec hf).2
  have hqMassSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hrMassSummable : Summable (fun p : P => (r p).toReal) := genericWeightSummable_toReal hr
  have hAbsDiffSummable : Summable (fun p : P => |(q p).toReal - (r p).toReal|) := by
    refine Summable.of_nonneg_of_le
      (f := fun p : P => (q p).toReal + (r p).toReal)
      (g := fun p : P => |(q p).toReal - (r p).toReal|)
      (fun p => abs_nonneg _)
      (fun p => by
        calc
          |(q p).toReal - (r p).toReal|
              = |(q p).toReal + (-(r p).toReal)| := by ring_nf
          _ ≤ |(q p).toReal| + |-(r p).toReal| := abs_add_le _ _
          _ = (q p).toReal + (r p).toReal := by
                simp [ENNReal.toReal_nonneg])
      (hqMassSummable.add hrMassSummable)
  have hBoundSummable :
      Summable (fun p : P => B * |(q p).toReal - (r p).toReal|) := by
    exact hAbsDiffSummable.mul_left B
  have hqRewardSummable : Summable (fun p : P => (q p).toReal * f p) := by
    have hBase :=
      genericExpectedLossSummable_of_bounded q (fun p => -f p) hq (boundedLossProfile_neg hf)
    refine hBase.neg.congr ?_
    intro p
    unfold genericLossContribution
    ring_nf
  have hrRewardSummable : Summable (fun p : P => (r p).toReal * f p) := by
    have hBase :=
      genericExpectedLossSummable_of_bounded r (fun p => -f p) hr (boundedLossProfile_neg hf)
    refine hBase.neg.congr ?_
    intro p
    unfold genericLossContribution
    ring_nf
  have hDiffSummable :
      Summable (fun p : P => ((q p).toReal - (r p).toReal) * f p) := by
    have hSub := hqRewardSummable.sub hrRewardSummable
    refine hSub.congr ?_
    intro p
    ring
  have hDiffEq :
      genericExpectedReward q f - genericExpectedReward r f
        = ∑' p : P, ((q p).toReal - (r p).toReal) * f p := by
    rw [genericExpectedReward_eq_tsum q f hq hf, genericExpectedReward_eq_tsum r f hr hf]
    calc
      ∑' p : P, (q p).toReal * f p - ∑' p : P, (r p).toReal * f p
          = ∑' p : P, ((q p).toReal * f p - (r p).toReal * f p) := by
              simpa using (hqRewardSummable.tsum_sub hrRewardSummable).symm
      _ = ∑' p : P, ((q p).toReal - (r p).toReal) * f p := by
            apply tsum_congr
            intro p
            ring
  have hBoundPoint :
      ∀ p : P, ‖((q p).toReal - (r p).toReal) * f p‖ ≤ B * |(q p).toReal - (r p).toReal| := by
    intro p
    rw [Real.norm_eq_abs, abs_mul]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hB_bound p) (abs_nonneg ((q p).toReal - (r p).toReal))
  calc
    |genericExpectedReward q f - genericExpectedReward r f|
        = ‖∑' p : P, ((q p).toReal - (r p).toReal) * f p‖ := by
            rw [hDiffEq, Real.norm_eq_abs]
    _ ≤ ∑' p : P, ‖((q p).toReal - (r p).toReal) * f p‖ := by
          exact norm_tsum_le_tsum_norm hDiffSummable.norm
    _ ≤ ∑' p : P, B * |(q p).toReal - (r p).toReal| := by
          exact Summable.tsum_le_tsum (fun p => hBoundPoint p) hDiffSummable.norm hBoundSummable
    _ = B * genericWeightL1Dist q r := by
          rw [genericWeightL1Dist, tsum_mul_left]

private theorem genericExpectedLoss_lipschitz_of_bounded
    (q r : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hr : ProbabilityWeight r)
    (L : P → Real)
    (hL : BoundedLossProfile L) :
    |genericExpectedLoss q L - genericExpectedLoss r L|
      ≤ (Classical.choose hL) * genericWeightL1Dist q r := by
  have hReward :
      |-genericExpectedLoss q L + genericExpectedLoss r L|
        ≤ (Classical.choose hL) * genericWeightL1Dist q r := by
    simpa [genericExpectedReward] using
      genericExpectedReward_lipschitz_of_bounded q r hq hr (fun p => -L p)
        (boundedLossProfile_neg hL)
  have hAbsEq :
      |-genericExpectedLoss q L + genericExpectedLoss r L|
        = |genericExpectedLoss q L - genericExpectedLoss r L| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (abs_neg (genericExpectedLoss q L - genericExpectedLoss r L))
  rw [← hAbsEq]
  exact hReward

/-- Real-valued Gibbs-gap contribution against the Gibbs law induced by `w` and `L`. -/
def genericGibbsGapContribution
    (q w : P → ENNReal) (L : P → Real)
    (p : P) : Real :=
  genericWeightKLDivergenceContribution q (genericGibbsLaw w L) p

/-- Real-valued Gibbs gap on the countable simplex. -/
def genericGibbsGap
    (q w : P → ENNReal) (L : P → Real) : Real :=
  ∑' p : P, genericGibbsGapContribution q w L p

/-- Honest KL variational objective `E_q[L] + KL(q || w)` on the countable simplex. -/
def genericKLVariationalObjective
    (q w : P → ENNReal) (L : P → Real) : EReal :=
  genericExpectedLossEReal q L + genericWeightKLDivergenceEReal q w

private theorem genericGibbsLaw_toReal
    (w : P → ENNReal) (L : P → Real)
    (hw : ProbabilityWeight w)
    (p : P) :
    (genericGibbsLaw w L p).toReal =
      (w p).toReal * Real.exp (-L p) / (genericGibbsPartition w L).toReal := by
  have hZne : genericGibbsPartition w L ≠ 0 := genericGibbsPartition_ne_zero w L hw
  rw [genericGibbsLaw, genericGibbsWeight]
  simp [ENNReal.toReal_mul, ENNReal.toReal_div, Real.exp_nonneg, hZne]

private theorem genericGibbsGapContribution_identity
    (q w : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hL : BoundedLossProfile L)
    (p : P)
    (hqTop : q p ≠ ⊤)
    (hCompat : q p ≠ 0 → w p ≠ 0) :
    genericGibbsGapContribution q w L p =
      genericWeightKLDivergenceContribution q w p
        + genericLossContribution q L p
        + (q p).toReal * Real.log (genericGibbsPartition w L).toReal := by
  have hZne : genericGibbsPartition w L ≠ 0 := genericGibbsPartition_ne_zero w L hw
  have hZtop : genericGibbsPartition w L ≠ ⊤ := genericGibbsPartition_ne_top_of_bounded w L hw hL
  by_cases hqZero : q p = 0
  · simp [genericGibbsGapContribution, genericWeightKLDivergenceContribution, genericLossContribution,
      hqZero]
  · have hwZero : w p ≠ 0 := hCompat hqZero
    have hwpTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
    have hLawZero : genericGibbsLaw w L p ≠ 0 := by
      intro hLawEq
      exact hwZero ((genericGibbsLaw_eq_zero_iff w L hw hL p).mp hLawEq)
    have hRatioW :
        ((q p) / (w p)).toReal = (q p).toReal / (w p).toReal := by
      rw [ENNReal.toReal_div]
    have hRatioLaw :
        ((q p) / (genericGibbsLaw w L p)).toReal =
          (q p).toReal / (genericGibbsLaw w L p).toReal := by
      rw [ENNReal.toReal_div]
    have hLawToReal := genericGibbsLaw_toReal w L hw p
    have hwRealPos : 0 < (w p).toReal := ENNReal.toReal_pos hwZero hwpTop
    have hLawRealPos : 0 < (genericGibbsLaw w L p).toReal := ENNReal.toReal_pos hLawZero
      (genericGibbsLaw_ne_top w L hw hL p)
    have hRatioWPos : 0 < ((q p) / (w p)).toReal := by
      exact ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hqZero, hwpTop⟩) (ENNReal.div_ne_top hqTop hwZero)
    have hZRealPos : 0 < (genericGibbsPartition w L).toReal := ENNReal.toReal_pos hZne hZtop
    have hRatioIdentity :
        ((q p) / (genericGibbsLaw w L p)).toReal =
          ((q p) / (w p)).toReal * (genericGibbsPartition w L).toReal * Real.exp (L p) := by
      rw [hRatioLaw, hRatioW, hLawToReal, div_eq_mul_inv, div_eq_mul_inv, Real.exp_neg]
      field_simp [hwRealPos.ne', hZRealPos.ne', (Real.exp_pos (L p)).ne']
    have hLogIdentity :
        Real.log (((q p) / (genericGibbsLaw w L p)).toReal) =
          Real.log (((q p) / (w p)).toReal) + L p + Real.log (genericGibbsPartition w L).toReal := by
      have hFirstPos : 0 < ((q p) / (w p)).toReal * (genericGibbsPartition w L).toReal := by
        exact mul_pos hRatioWPos hZRealPos
      rw [hRatioIdentity]
      rw [Real.log_mul hFirstPos.ne' (Real.exp_pos _).ne']
      rw [Real.log_mul hRatioWPos.ne' hZRealPos.ne', Real.log_exp]
      ring
    calc
      genericGibbsGapContribution q w L p
          = (q p).toReal * Real.log (((q p) / (genericGibbsLaw w L p)).toReal) := by
              simp [genericGibbsGapContribution, genericWeightKLDivergenceContribution, hqZero]
      _ = (q p).toReal * Real.log (((q p) / (w p)).toReal)
            + (q p).toReal * L p
            + (q p).toReal * Real.log (genericGibbsPartition w L).toReal := by
              rw [hLogIdentity]
              ring
      _ = genericWeightKLDivergenceContribution q w p
            + genericLossContribution q L p
            + (q p).toReal * Real.log (genericGibbsPartition w L).toReal := by
              simp [genericWeightKLDivergenceContribution, genericLossContribution, hqZero]

/--
Exact Gibbs objective identity on the countable simplex: if a candidate law `q` is exactly the
Gibbs law associated with the reference weight `w` and profile `L`, then
`E_q[L] + KL(q || w) = -log Z_L`.
-/
theorem genericExpectedLoss_add_genericWeightKLDivergence_eq_negativeLogPartition
    (w q : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hLossSummable : Summable (fun p : P => genericLossContribution q L p))
    (hKLSummable : Summable (fun p : P => genericWeightKLDivergenceContribution q w p))
    (hGibbs : ∀ p : P, q p = genericGibbsLaw w L p) :
    genericExpectedLoss q L + genericWeightKLDivergence q w =
      -Real.log (genericGibbsPartition w L).toReal := by
  have hZne : genericGibbsPartition w L ≠ 0 :=
    genericGibbsPartition_ne_zero w L hw
  have hZtop : genericGibbsPartition w L ≠ ⊤ :=
    genericGibbsPartition_ne_top_of_normalized_gibbs w q L hq hGibbs
  have hTermIdentity :
      ∀ p : P,
        genericLossContribution q L p + genericWeightKLDivergenceContribution q w p =
          (q p).toReal * (-Real.log (genericGibbsPartition w L).toReal) := by
    intro p
    by_cases hqp : q p = 0
    · simp [genericLossContribution, genericWeightKLDivergenceContribution, hqp]
    · have hqPos : 0 < (q p).toReal := by
        exact ENNReal.toReal_pos hqp (genericWeight_ne_top_of_normalized hq p)
      have hWeightNeZero : genericGibbsWeight w L p ≠ 0 := by
        intro hWeight
        have : q p = 0 := by
          rw [hGibbs p, genericGibbsLaw, hWeight]
          simp
        exact hqp this
      have hwPos : 0 < (w p).toReal := by
        exact ENNReal.toReal_pos
          ((genericGibbsWeight_eq_zero_iff w L p).not.mp hWeightNeZero)
          (genericWeight_ne_top_of_normalized hw p)
      have hGibbsToReal :
          (q p).toReal =
            (w p).toReal * Real.exp (-L p) / (genericGibbsPartition w L).toReal := by
        rw [hGibbs p, genericGibbsLaw, genericGibbsWeight]
        simp [ENNReal.toReal_mul, ENNReal.toReal_div, Real.exp_nonneg]
      have hRatio :
          (q p / w p).toReal =
            Real.exp (-L p) / (genericGibbsPartition w L).toReal := by
        rw [ENNReal.toReal_div, hGibbsToReal]
        field_simp [hwPos.ne']
      have hLogRatio :
          Real.log ((q p / w p).toReal) = -L p - Real.log (genericGibbsPartition w L).toReal := by
        rw [hRatio, Real.log_div (Real.exp_pos (-L p)).ne' (ENNReal.toReal_pos hZne hZtop).ne',
          Real.log_exp]
      calc
        genericLossContribution q L p + genericWeightKLDivergenceContribution q w p
            = (q p).toReal * L p + (q p).toReal * Real.log ((q p / w p).toReal) := by
                simp [genericLossContribution, genericWeightKLDivergenceContribution, hqp]
        _ = (q p).toReal * (L p + Real.log ((q p / w p).toReal)) := by ring
        _ = (q p).toReal * (-Real.log (genericGibbsPartition w L).toReal) := by
              rw [hLogRatio]
              ring
  calc
    genericExpectedLoss q L + genericWeightKLDivergence q w
        = ∑' p : P,
            (genericLossContribution q L p + genericWeightKLDivergenceContribution q w p) := by
              unfold genericExpectedLoss genericWeightKLDivergence
              exact (hLossSummable.tsum_add hKLSummable).symm
    _ = ∑' p : P, (q p).toReal * (-Real.log (genericGibbsPartition w L).toReal) := by
          apply tsum_congr
          intro p
          exact hTermIdentity p
    _ = (∑' p : P, (q p).toReal) * (-Real.log (genericGibbsPartition w L).toReal) := by
          have hqSummable : Summable (fun p : P => (q p).toReal) :=
            ENNReal.summable_toReal (by rw [hq]; simp)
          simpa using
            (_root_.tsum_mul_right
              (f := fun p : P => (q p).toReal)
              (a := -Real.log (genericGibbsPartition w L).toReal))
    _ = -Real.log (genericGibbsPartition w L).toReal := by
          rw [genericWeight_toReal_tsum_eq_one hq]
          ring

/--
Finite-branch Gibbs decomposition for an arbitrary admissible belief `q`.

If the honest discrete KL term against `w` is finite, then the variational objective decomposes
into the Gibbs gap against `genericGibbsLaw w L` plus the constant `-log Z_L`.
-/
theorem genericExpectedLoss_add_genericWeightKLDivergence_eq_genericGibbsGap_sub_logPartition
    (w q : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hL : BoundedLossProfile L)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    genericExpectedLoss q L + genericWeightKLDivergence q w =
      genericGibbsGap q w L - Real.log (genericGibbsPartition w L).toReal := by
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 := genericSupportCompatible_of_finite q w hFinite
  have hLossSummable : Summable (fun p : P => genericLossContribution q L p) :=
    genericExpectedLossSummable_of_bounded q L hq hL
  have hKLSummable : Summable (fun p : P => genericWeightKLDivergenceContribution q w p) :=
    genericWeightKLDivergenceSummable_of_finite q w hq hw hFinite hCompat
  have hQSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hGapSummable :
      Summable (fun p : P => genericGibbsGapContribution q w L p) := by
    have hAux : Summable (fun p : P =>
        genericWeightKLDivergenceContribution q w p
          + genericLossContribution q L p
          + (q p).toReal * Real.log (genericGibbsPartition w L).toReal) := by
      exact (hKLSummable.add hLossSummable).add
        (hQSummable.mul_right (Real.log (genericGibbsPartition w L).toReal))
    refine hAux.congr ?_
    intro p
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    exact (genericGibbsGapContribution_identity q w L hw hL p hqTop (hCompat p)).symm
  have hConstSummable :
      Summable (fun p : P => (q p).toReal * Real.log (genericGibbsPartition w L).toReal) :=
    hQSummable.mul_right (Real.log (genericGibbsPartition w L).toReal)
  have hTermwise :
      ∀ p : P,
        genericLossContribution q L p + genericWeightKLDivergenceContribution q w p =
          genericGibbsGapContribution q w L p
            - (q p).toReal * Real.log (genericGibbsPartition w L).toReal := by
    intro p
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    rw [genericGibbsGapContribution_identity q w L hw hL p hqTop (hCompat p)]
    ring
  calc
    genericExpectedLoss q L + genericWeightKLDivergence q w
        = ∑' p : P,
            (genericGibbsGapContribution q w L p
              - (q p).toReal * Real.log (genericGibbsPartition w L).toReal) := by
              unfold genericExpectedLoss genericWeightKLDivergence
              rw [(hLossSummable.tsum_add hKLSummable).symm]
              apply tsum_congr
              exact hTermwise
    _ = genericGibbsGap q w L - ∑' p : P, (q p).toReal * Real.log (genericGibbsPartition w L).toReal := by
          unfold genericGibbsGap
          rw [Summable.tsum_sub hGapSummable hConstSummable]
    _ = genericGibbsGap q w L - (∑' p : P, (q p).toReal) * Real.log (genericGibbsPartition w L).toReal := by
          congr 1
          simpa using (_root_.tsum_mul_right
            (f := fun p : P => (q p).toReal)
            (a := Real.log (genericGibbsPartition w L).toReal))
    _ = genericGibbsGap q w L - Real.log (genericGibbsPartition w L).toReal := by
          rw [genericWeight_toReal_tsum_eq_one hq]
          ring

/--
Gibbs lower bound for the honest KL variational objective on the countable simplex.

The objective is bounded below by `-log Z_L`, with equality exactly at the Gibbs law. The theorem
handles both branches honestly: if the KL term is infinite, the objective is `⊤`; otherwise the
finite branch reduces to the exact Gibbs-gap decomposition above.
-/
theorem genericKLVariationalObjective_lower_bound
    (w q : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hL : BoundedLossProfile L) :
    ((-Real.log (genericGibbsPartition w L).toReal : Real) : EReal) ≤
      genericKLVariationalObjective q w L := by
  by_cases hFinite : genericWeightKLDivergenceInf q w ≠ ⊤
  · have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 := genericSupportCompatible_of_finite q w hFinite
    have hObjectiveEq :
        genericKLVariationalObjective q w L =
          ((genericExpectedLoss q L + genericWeightKLDivergence q w : Real) : EReal) := by
      unfold genericKLVariationalObjective genericExpectedLossEReal
      rw [genericWeightKLDivergenceEReal_eq_of_finite q w hq hw hFinite hCompat]
      simp
    have hDecomp :
        genericExpectedLoss q L + genericWeightKLDivergence q w =
          genericGibbsGap q w L - Real.log (genericGibbsPartition w L).toReal :=
      genericExpectedLoss_add_genericWeightKLDivergence_eq_genericGibbsGap_sub_logPartition
        w q L hw hq hL hFinite
    have hCompatGap : ∀ p : P, q p ≠ 0 → genericGibbsLaw w L p ≠ 0 := by
      intro p hqp
      intro hLawZero
      exact (hCompat p hqp) ((genericGibbsLaw_eq_zero_iff w L hw hL p).mp hLawZero)
    have hGapSummable :
        Summable (fun p : P => genericGibbsGapContribution q w L p) := by
      have hLossSummable := genericExpectedLossSummable_of_bounded q L hq hL
      have hKLSummable := genericWeightKLDivergenceSummable_of_finite q w hq hw hFinite hCompat
      have hQSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
      have hAux : Summable (fun p : P =>
          genericWeightKLDivergenceContribution q w p
            + genericLossContribution q L p
            + (q p).toReal * Real.log (genericGibbsPartition w L).toReal) := by
        exact (hKLSummable.add hLossSummable).add
          (hQSummable.mul_right (Real.log (genericGibbsPartition w L).toReal))
      refine hAux.congr ?_
      intro p
      have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
      exact (genericGibbsGapContribution_identity q w L hw hL p hqTop (hCompat p)).symm
    have hGapEq :
        genericGibbsGapEReal q w L = (genericGibbsGap q w L : EReal) := by
      exact genericWeightKLDivergenceEReal_eq_of_summable
        q (genericGibbsLaw w L) hq (genericGibbsLaw_normalized w L hw hL) hCompatGap hGapSummable
    have hGapNonneg : (0 : Real) ≤ genericGibbsGap q w L := by
      have : (0 : EReal) ≤ genericGibbsGapEReal q w L := by
        exact EReal.coe_ennreal_nonneg (genericGibbsGapInf q w L)
      simpa [hGapEq] using this
    rw [hObjectiveEq, hDecomp]
    have hRealLe :
        -Real.log (genericGibbsPartition w L).toReal ≤
          genericGibbsGap q w L - Real.log (genericGibbsPartition w L).toReal := by
      linarith
    exact_mod_cast hRealLe
  · have hTop :
        genericKLVariationalObjective q w L = ⊤ := by
      have hInfTop : genericWeightKLDivergenceInf q w = ⊤ := not_ne_iff.mp hFinite
      unfold genericKLVariationalObjective genericExpectedLossEReal genericWeightKLDivergenceEReal
      rw [hInfTop]
      exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
    rw [hTop]
    exact le_top

private theorem genericKLVariationalObjective_eq_gibbsGap_sub_logPartition_of_finite
    (w q : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hL : BoundedLossProfile L)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    genericKLVariationalObjective q w L =
      ((genericGibbsGap q w L - Real.log (genericGibbsPartition w L).toReal : Real) : EReal) := by
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 := genericSupportCompatible_of_finite q w hFinite
  calc
    genericKLVariationalObjective q w L
        = ((genericExpectedLoss q L + genericWeightKLDivergence q w : Real) : EReal) := by
            unfold genericKLVariationalObjective genericExpectedLossEReal
            rw [genericWeightKLDivergenceEReal_eq_of_finite q w hq hw hFinite hCompat]
            simp
    _ = ((genericGibbsGap q w L - Real.log (genericGibbsPartition w L).toReal : Real) : EReal) := by
          congr 1
          exact genericExpectedLoss_add_genericWeightKLDivergence_eq_genericGibbsGap_sub_logPartition
            w q L hw hq hL hFinite

/--
Approximate minimizers supplied by the exact bounded-loss variational formula are also approximate
minimizers for the honest KL variational objective.
-/
theorem exactBoundedLossFormula_has_near_kl_minimizer
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (L : P → Real)
    (hL : BoundedLossProfile L)
    (ε : Real)
    (hε : 0 < ε) :
    ∃ q : P → ENNReal, ProbabilityWeight q ∧
      genericKLVariationalObjective q w L ≤
        (((-Real.log (genericGibbsPartition w L).toReal + ε : Real) : EReal)) := by
  rcases (hExact L hL).2 ε hε with ⟨q, hq, hNear⟩
  refine ⟨q, hq, ?_⟩
  have hKLleD : genericWeightKLDivergenceEReal q w ≤ D q :=
    exactBoundedLossFormula_ge_kl D w hw hExact q hq
  have hObjLe :
      genericKLVariationalObjective q w L ≤ genericVariationalValue D q L := by
    simpa [genericKLVariationalObjective, genericVariationalValue, add_assoc, add_left_comm,
      add_comm] using add_le_add_left hKLleD (genericExpectedLossEReal q L)
  exact hObjLe.trans hNear

/--
The exact bounded-loss variational formula therefore produces arbitrarily small Gibbs-gap
approximate minimizers for every bounded loss profile.
-/
theorem exactBoundedLossFormula_has_near_gibbs_gap_minimizer
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (L : P → Real)
    (hL : BoundedLossProfile L)
    (ε : Real)
    (hε : 0 < ε) :
    ∃ q : P → ENNReal, ProbabilityWeight q ∧ genericGibbsGap q w L ≤ ε := by
  rcases exactBoundedLossFormula_has_near_kl_minimizer D w hw hExact L hL ε hε with
    ⟨q, hq, hNear⟩
  have hFinite : genericWeightKLDivergenceInf q w ≠ ⊤ := by
    intro hInfTop
    have hTop :
        genericKLVariationalObjective q w L = ⊤ := by
      unfold genericKLVariationalObjective genericExpectedLossEReal genericWeightKLDivergenceEReal
      rw [hInfTop]
      exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
    have hTopLe :
        (⊤ : EReal) ≤ (((-Real.log (genericGibbsPartition w L).toReal + ε : Real) : EReal)) := by
      simpa [hTop] using hNear
    exact (not_le_of_gt (EReal.coe_lt_top _)) hTopLe
  refine ⟨q, hq, ?_⟩
  rw [genericKLVariationalObjective_eq_gibbsGap_sub_logPartition_of_finite w q L hw hq hL hFinite]
    at hNear
  have hGapShift :
      genericGibbsGap q w L - Real.log (genericGibbsPartition w L).toReal
        ≤ -Real.log (genericGibbsPartition w L).toReal + ε :=
    EReal.coe_le_coe_iff.mp hNear
  linarith

private theorem genericWeightKLDivergenceInf_ne_top_of_objective_le
    (q w : P → ENNReal)
    (L : P → Real)
    (c : Real)
    (hObj :
      genericKLVariationalObjective q w L ≤ (c : EReal)) :
    genericWeightKLDivergenceInf q w ≠ ⊤ := by
  intro hInfTop
  have hTop :
      genericKLVariationalObjective q w L = ⊤ := by
    unfold genericKLVariationalObjective genericExpectedLossEReal genericWeightKLDivergenceEReal
    rw [hInfTop]
    exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
  have : (⊤ : EReal) ≤ (c : EReal) := by
    simpa [hTop] using hObj
  exact (not_le_of_gt (EReal.coe_lt_top _)) this

private theorem genericGibbsGapSummable_of_finite
    (w q : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hL : BoundedLossProfile L)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    Summable (fun p : P => genericGibbsGapContribution q w L p) := by
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 := genericSupportCompatible_of_finite q w hFinite
  have hLossSummable : Summable (fun p : P => genericLossContribution q L p) :=
    genericExpectedLossSummable_of_bounded q L hq hL
  have hKLSummable :
      Summable (fun p : P => genericWeightKLDivergenceContribution q w p) :=
    genericWeightKLDivergenceSummable_of_finite q w hq hw hFinite hCompat
  have hQSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hAux : Summable (fun p : P =>
      genericWeightKLDivergenceContribution q w p
        + genericLossContribution q L p
        + (q p).toReal * Real.log (genericGibbsPartition w L).toReal) := by
    exact (hKLSummable.add hLossSummable).add
      (hQSummable.mul_right (Real.log (genericGibbsPartition w L).toReal))
  refine hAux.congr ?_
  intro p
  have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
  exact (genericGibbsGapContribution_identity q w L hw hL p hqTop (hCompat p)).symm

private theorem genericGibbsGapEReal_eq_of_finite
    (w q : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hL : BoundedLossProfile L)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    genericGibbsGapEReal q w L = (genericGibbsGap q w L : EReal) := by
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 := genericSupportCompatible_of_finite q w hFinite
  have hCompatGap : ∀ p : P, q p ≠ 0 → genericGibbsLaw w L p ≠ 0 := by
    intro p hqp
    intro hLawZero
    exact (hCompat p hqp) ((genericGibbsLaw_eq_zero_iff w L hw hL p).mp hLawZero)
  exact genericWeightKLDivergenceEReal_eq_of_summable
    q (genericGibbsLaw w L) hq (genericGibbsLaw_normalized w L hw hL) hCompatGap
    (genericGibbsGapSummable_of_finite w q L hw hq hL hFinite)

private theorem genericExpectedLoss_tendsto_of_l1
    (qs : Nat → P → ENNReal)
    (q : P → ENNReal)
    (hqs : ∀ n : Nat, ProbabilityWeight (qs n))
    (hq : ProbabilityWeight q)
    (L : P → Real)
    (hL : BoundedLossProfile L)
    (hDist :
      Tendsto (fun n : Nat => genericWeightL1Dist (qs n) q) atTop (𝓝 0)) :
    Tendsto (fun n : Nat => genericExpectedLoss (qs n) L) atTop (𝓝 (genericExpectedLoss q L)) := by
  let B : Real := Classical.choose hL
  have hB_nonneg : 0 ≤ B := (Classical.choose_spec hL).1
  have hAbsBound :
      ∀ n : Nat,
        |genericExpectedLoss (qs n) L - genericExpectedLoss q L|
          ≤ B * genericWeightL1Dist (qs n) q := by
    intro n
    exact genericExpectedLoss_lipschitz_of_bounded (qs n) q (hqs n) hq L hL
  have hBoundTendsto :
      Tendsto (fun n : Nat => B * genericWeightL1Dist (qs n) q) atTop (𝓝 0) := by
    simpa [hB_nonneg, zero_mul] using (tendsto_const_nhds.mul hDist)
  have hAbsTendsto :
      Tendsto
        (fun n : Nat => |genericExpectedLoss (qs n) L - genericExpectedLoss q L|)
        atTop (𝓝 0) := by
    exact squeeze_zero (fun n => abs_nonneg _) hAbsBound hBoundTendsto
  have hDiffTendsto :
      Tendsto
        (fun n : Nat => genericExpectedLoss (qs n) L - genericExpectedLoss q L)
        atTop (𝓝 0) := by
    simpa using (tendsto_zero_iff_abs_tendsto_zero _).2 hAbsTendsto
  have hAdd :
      Tendsto
        (fun n : Nat =>
          genericExpectedLoss q L + (genericExpectedLoss (qs n) L - genericExpectedLoss q L))
        atTop (𝓝 (genericExpectedLoss q L + 0)) :=
    Tendsto.add tendsto_const_nhds hDiffTendsto
  rw [show
      (fun n : Nat =>
        genericExpectedLoss q L + (genericExpectedLoss (qs n) L - genericExpectedLoss q L))
        = (fun n : Nat => genericExpectedLoss (qs n) L) by
          funext n
          ring] at hAdd
  simpa using hAdd

private theorem ereal_le_coe_of_forall_real_lt
    {x : EReal}
    {b : Real}
    (h : ∀ y : Real, (y : EReal) < x → y ≤ b) :
    x ≤ (b : EReal) := by
  by_contra hxb
  have hlt : ((b : Real) : EReal) < x := lt_of_not_ge hxb
  rcases EReal.exists_rat_btwn_of_lt hlt with ⟨q, hqLeft, hqRight⟩
  have hqLe : (q : Real) ≤ b := h q hqRight
  have hqGt : b < (q : Real) := EReal.coe_lt_coe_iff.mp hqLeft
  exact (not_lt_of_ge hqLe) hqGt

private theorem exactBoundedLossFormula_attains_at_gibbs
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (hSeq : SequentialLowerSemicontinuousOnSimplex D)
    (L : P → Real)
    (hL : BoundedLossProfile L) :
    genericVariationalValue D (genericGibbsLaw w L) L =
      ((-Real.log (genericGibbsPartition w L).toReal : Real) : EReal) := by
  let qStar : P → ENNReal := genericGibbsLaw w L
  let c : Real := -Real.log (genericGibbsPartition w L).toReal
  have hqStar : ProbabilityWeight qStar := genericGibbsLaw_normalized w L hw hL
  have hLower :
      (c : EReal) ≤ genericVariationalValue D qStar L := by
    simpa [qStar, c] using (hExact L hL).1 qStar hqStar
  let ε : Nat → Real := fun n => (1 / ((n : Real) + 1)) ^ 2
  have hεPos : ∀ n : Nat, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hNearExists :
      ∀ n : Nat, ∃ q : P → ENNReal, ProbabilityWeight q ∧
        genericVariationalValue D q L ≤ ((c + ε n : Real) : EReal) := by
    intro n
    rcases (hExact L hL).2 (ε n) (hεPos n) with ⟨q, hq, hqNear⟩
    exact ⟨q, hq, by simpa [c] using hqNear⟩
  choose qs hqsWeight hqsObj using hNearExists
  have hFinite : ∀ n : Nat, genericWeightKLDivergenceInf (qs n) w ≠ ⊤ := by
    intro n
    have hKLleD : genericWeightKLDivergenceEReal (qs n) w ≤ D (qs n) :=
      exactBoundedLossFormula_ge_kl D w hw hExact (qs n) (hqsWeight n)
    have hKLObjLe :
        genericKLVariationalObjective (qs n) w L ≤ genericVariationalValue D (qs n) L := by
      simpa [genericKLVariationalObjective, genericVariationalValue, add_assoc, add_left_comm,
        add_comm] using add_le_add_left hKLleD (genericExpectedLossEReal (qs n) L)
    exact genericWeightKLDivergenceInf_ne_top_of_objective_le (qs n) w L (c + ε n)
      (hKLObjLe.trans (hqsObj n))
  have hGapBound : ∀ n : Nat, genericGibbsGap (qs n) w L ≤ ε n := by
    intro n
    have hKLleD : genericWeightKLDivergenceEReal (qs n) w ≤ D (qs n) :=
      exactBoundedLossFormula_ge_kl D w hw hExact (qs n) (hqsWeight n)
    have hKLObjLe :
        genericKLVariationalObjective (qs n) w L ≤ genericVariationalValue D (qs n) L := by
      simpa [genericKLVariationalObjective, genericVariationalValue, add_assoc, add_left_comm,
        add_comm] using add_le_add_left hKLleD (genericExpectedLossEReal (qs n) L)
    have hObjEq :=
      genericKLVariationalObjective_eq_gibbsGap_sub_logPartition_of_finite
        w (qs n) L hw (hqsWeight n) hL (hFinite n)
    have hObjN := hKLObjLe.trans (hqsObj n)
    rw [hObjEq] at hObjN
    have hShift : genericGibbsGap (qs n) w L - Real.log (genericGibbsPartition w L).toReal
        ≤ c + ε n := EReal.coe_le_coe_iff.mp (by simpa [c] using hObjN)
    linarith
  have hFiniteGap : ∀ n : Nat, genericWeightKLDivergenceInf (qs n) qStar ≠ ⊤ := by
    intro n
    have hGapEq :
        genericGibbsGapEReal (qs n) w L = (genericGibbsGap (qs n) w L : EReal) :=
      genericGibbsGapEReal_eq_of_finite w (qs n) L hw (hqsWeight n) hL (hFinite n)
    intro hTop
    have : ((genericGibbsGap (qs n) w L : Real) : EReal) = ⊤ := by
      simpa [genericGibbsGapEReal, genericGibbsGapInf, qStar, hTop] using hGapEq.symm
    exact EReal.coe_ne_top _ this
  have hDistBound :
      ∀ n : Nat, genericWeightL1Dist (qs n) qStar ≤ 2 * (1 / ((n : Real) + 1)) := by
    intro n
    calc
      genericWeightL1Dist (qs n) qStar
          ≤ 2 * Real.sqrt (genericWeightKLDivergence (qs n) qStar) := by
              exact genericWeightL1Dist_le_two_sqrt_of_finite
                (qs n) qStar (hqsWeight n) hqStar (hFiniteGap n)
      _ = 2 * Real.sqrt (genericGibbsGap (qs n) w L) := by
            rfl
      _ ≤ 2 * Real.sqrt (ε n) := by
            gcongr
            exact hGapBound n
      _ = 2 * (1 / ((n : Real) + 1)) := by
            dsimp [ε]
            have hNonneg : 0 ≤ 1 / ((n : Real) + 1) := by positivity
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hNonneg]
  have hInvTendsto :
      Tendsto (fun n : Nat => 1 / ((n : Real) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hDistTendsto :
      Tendsto (fun n : Nat => genericWeightL1Dist (qs n) qStar) atTop (𝓝 0) := by
    have hBoundTendsto :
        Tendsto (fun n : Nat => 2 * (1 / ((n : Real) + 1))) atTop (𝓝 0) := by
      simpa [zero_mul] using (tendsto_const_nhds.mul hInvTendsto)
    exact squeeze_zero (fun n => by
      unfold genericWeightL1Dist
      exact tsum_nonneg (fun _ => abs_nonneg _)) hDistBound hBoundTendsto
  have hLossTendsto :
      Tendsto (fun n : Nat => genericExpectedLoss (qs n) L)
        atTop (𝓝 (genericExpectedLoss qStar L)) :=
    genericExpectedLoss_tendsto_of_l1 qs qStar hqsWeight hqStar L hL hDistTendsto
  have hEpsTendsto :
      Tendsto ε atTop (𝓝 0) := by
    dsimp [ε]
    simpa [pow_two] using (hInvTendsto.mul hInvTendsto)
  have hDUpper :
      D qStar ≤ ((c - genericExpectedLoss qStar L : Real) : EReal) := by
    apply ereal_le_coe_of_forall_real_lt
    intro y hy
    by_contra hyLe
    let δ : Real := (y + genericExpectedLoss qStar L - c) / 3
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hyEventually : ∀ᶠ n : Nat in atTop, (y : EReal) < D (qs n) :=
      hSeq qStar qs hqStar hqsWeight hDistTendsto y hy
    have hLossEventually :
        ∀ᶠ n : Nat in atTop,
          genericExpectedLoss qStar L - δ < genericExpectedLoss (qs n) L := by
      have hMem : Set.Ioi (genericExpectedLoss qStar L - δ) ∈ 𝓝 (genericExpectedLoss qStar L) := by
        exact Ioi_mem_nhds (by linarith)
      exact hLossTendsto.eventually hMem
    have hEpsEventually : ∀ᶠ n : Nat in atTop, ε n < δ := by
      have hMem : Set.Iio δ ∈ 𝓝 (0 : Real) := Iio_mem_nhds hδ
      exact hEpsTendsto.eventually hMem
    rcases (hyEventually.and (hLossEventually.and hEpsEventually)).exists with
      ⟨n, hyN, hLossN, hEpsN⟩
    have hD_ne_bot : D (qs n) ≠ ⊥ :=
      exactBoundedLossFormula_ne_bot D w hw hExact (qs n) (hqsWeight n)
    have hD_ne_top : D (qs n) ≠ ⊤ := by
      intro hTop
      have hVarTop :
          genericVariationalValue D (qs n) L = ⊤ := by
        unfold genericVariationalValue genericExpectedLossEReal
        simpa [hTop] using EReal.add_top_of_ne_bot (x := ((genericExpectedLoss (qs n) L : Real) : EReal))
          (EReal.coe_ne_bot _)
      have : (⊤ : EReal) ≤ ((c + ε n : Real) : EReal) := by
        simpa [hVarTop] using hqsObj n
      exact (not_le_of_gt (EReal.coe_lt_top _)) this
    have hyReal : y < (D (qs n)).toReal := by
      have hyToReal : (y : EReal) < (((D (qs n)).toReal : Real) : EReal) :=
        lt_of_lt_of_le hyN (EReal.le_coe_toReal hD_ne_top)
      exact EReal.coe_lt_coe_iff.mp hyToReal
    have hVar_ne_bot : genericVariationalValue D (qs n) L ≠ ⊥ := by
      unfold genericVariationalValue genericExpectedLossEReal
      simp [hD_ne_bot]
    have hObjReal :
        genericExpectedLoss (qs n) L + (D (qs n)).toReal ≤ c + ε n := by
      have hObjReal' :
          (genericVariationalValue D (qs n) L).toReal ≤ (c + ε n : Real) := by
        exact EReal.toReal_le_toReal (hqsObj n) hVar_ne_bot (EReal.coe_ne_top _)
      have hObjReal'' :
          ((((genericExpectedLoss (qs n) L : Real) : EReal) + D (qs n)).toReal) ≤ c + ε n := by
        simpa [genericVariationalValue, genericExpectedLossEReal] using hObjReal'
      simpa [EReal.toReal_add, hD_ne_top, hD_ne_bot] using hObjReal''
    have hRealLt :
        genericExpectedLoss (qs n) L + y < c + ε n := by
      linarith
    have hLowerReal : c + 2 * δ < genericExpectedLoss (qs n) L + y := by
      dsimp [δ] at hLossN ⊢
      linarith
    have hUpperReal : genericExpectedLoss (qs n) L + y < c + δ := by
      linarith
    have hContr : c + 2 * δ < c + δ := lt_of_lt_of_le hLowerReal hUpperReal.le
    have : ¬ c + 2 * δ < c + δ := by
      have hLe : c + δ ≤ c + 2 * δ := by linarith
      exact not_lt_of_ge hLe
    exact this hContr
  have hUpper :
      genericVariationalValue D qStar L ≤ (c : EReal) := by
    unfold genericVariationalValue genericExpectedLossEReal
    calc
      ((genericExpectedLoss qStar L : Real) : EReal) + D qStar
          ≤ ((genericExpectedLoss qStar L : Real) : EReal)
              + ((c - genericExpectedLoss qStar L : Real) : EReal) := by
                gcongr
      _ = (((genericExpectedLoss qStar L + (c - genericExpectedLoss qStar L) : Real)) : EReal) := by
            rw [EReal.coe_add]
      _ = (c : EReal) := by
            congr 1
            ring
  exact le_antisymm hUpper hLower

private theorem genericGibbsGapContribution_self_eq_zero
    (w : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hL : BoundedLossProfile L)
    (p : P) :
    genericGibbsGapContribution (genericGibbsLaw w L) w L p = 0 := by
  by_cases hq : genericGibbsLaw w L p = 0
  · simp [genericGibbsGapContribution, genericWeightKLDivergenceContribution, hq]
  · have hqTop : genericGibbsLaw w L p ≠ ⊤ := genericGibbsLaw_ne_top w L hw hL p
    simp [genericGibbsGapContribution, genericWeightKLDivergenceContribution, hq, hqTop,
      ENNReal.div_self hq hqTop, Real.log_one]

private theorem genericWeightKLDivergenceSummable_of_gibbs
    (w : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hL : BoundedLossProfile L) :
    Summable (fun p : P =>
      genericWeightKLDivergenceContribution (genericGibbsLaw w L) w p) := by
  let qStar : P → ENNReal := genericGibbsLaw w L
  have hqStar : ProbabilityWeight qStar := genericGibbsLaw_normalized w L hw hL
  have hCompat : ∀ p : P, qStar p ≠ 0 → w p ≠ 0 := by
    intro p hqp
    exact (genericGibbsLaw_eq_zero_iff w L hw hL p).not.mp hqp
  have hLossSummable : Summable (fun p : P => genericLossContribution qStar L p) :=
    genericExpectedLossSummable_of_bounded qStar L hqStar hL
  have hQSummable : Summable (fun p : P => (qStar p).toReal) := genericWeightSummable_toReal hqStar
  have hConstSummable :
      Summable (fun p : P => (qStar p).toReal * Real.log (genericGibbsPartition w L).toReal) :=
    hQSummable.mul_right (Real.log (genericGibbsPartition w L).toReal)
  have hAux :
      Summable (fun p : P =>
        -(genericLossContribution qStar L p
          + (qStar p).toReal * Real.log (genericGibbsPartition w L).toReal)) := by
    exact (hLossSummable.add hConstSummable).neg
  refine hAux.congr ?_
  intro p
  have hqTop : qStar p ≠ ⊤ := genericGibbsLaw_ne_top w L hw hL p
  have hId :=
    genericGibbsGapContribution_identity qStar w L hw hL p hqTop (hCompat p)
  have hZero : genericGibbsGapContribution qStar w L p = 0 :=
    genericGibbsGapContribution_self_eq_zero w L hw hL p
  linarith

/--
Real-valued helper form of Gibbs-attainment uniqueness.

This is not the final theorem surface for the duality layer. It exists so the extended-value
version below can reduce a finite exact-attainment equality to the already proved discrete KL
identity.
-/
theorem genericRealDivergence_eq_kl_of_exact_gibbs_attainment
    (D : (P → ENNReal) → Real)
    (w q : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hLossSummable : Summable (fun p : P => genericLossContribution q L p))
    (hKLSummable : Summable (fun p : P => genericWeightKLDivergenceContribution q w p))
    (hGibbs : ∀ p : P, q p = genericGibbsLaw w L p)
    (hExact :
      genericExpectedLoss q L + D q =
        -Real.log (genericGibbsPartition w L).toReal) :
    D q = genericWeightKLDivergence q w := by
  have hKL :
      genericExpectedLoss q L + genericWeightKLDivergence q w =
        -Real.log (genericGibbsPartition w L).toReal :=
    genericExpectedLoss_add_genericWeightKLDivergence_eq_negativeLogPartition
      w q L hw hq hLossSummable hKLSummable hGibbs
  linarith

/--
Extended-value Gibbs-attainment uniqueness.

If an extended-value divergence `D` attains the exact Gibbs variational value at a Gibbs law and is
finite there, then it agrees with discrete KL at that law. This is the strongest generic theorem
available before the full discrete Fenchel–Moreau step is formalized.
-/
theorem generic_divergence_eq_kl_of_exact_gibbs_attainment
    (D : ExtendedDivergence P)
    (w q : P → ENNReal)
    (L : P → Real)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (hLossSummable : Summable (fun p : P => genericLossContribution q L p))
    (hKLSummable : Summable (fun p : P => genericWeightKLDivergenceContribution q w p))
    (hGibbs : ∀ p : P, q p = genericGibbsLaw w L p)
    (hD_ne_bot : D q ≠ ⊥)
    (hExact :
      genericVariationalValue D q L =
        ((-Real.log (genericGibbsPartition w L).toReal : Real) : EReal)) :
    D q = genericWeightKLDivergenceEReal q w := by
  have hD_ne_top : D q ≠ ⊤ := by
    intro hTop
    have hLhsTop :
        genericVariationalValue D q L = ⊤ := by
      unfold genericVariationalValue genericExpectedLossEReal
      simpa [hTop] using EReal.add_top_of_ne_bot (x := ((genericExpectedLoss q L : Real) : EReal))
        (EReal.coe_ne_bot _)
    have : (((-Real.log (genericGibbsPartition w L).toReal : Real) : EReal)) = ⊤ := by
      simpa [hExact] using hLhsTop
    exact EReal.coe_ne_top _ this
  have hExactReal :
      genericExpectedLoss q L + (D q).toReal =
        -Real.log (genericGibbsPartition w L).toReal := by
    have hToReal := congrArg EReal.toReal hExact
    simpa [genericVariationalValue, genericExpectedLossEReal, EReal.toReal_add,
      hD_ne_top, hD_ne_bot] using hToReal
  have hReal :
      (D q).toReal = genericWeightKLDivergence q w :=
    genericRealDivergence_eq_kl_of_exact_gibbs_attainment
      (D := fun μ => (D μ).toReal) w q L hw hq hLossSummable hKLSummable hGibbs hExactReal
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 :=
    genericSupportCompatible_of_gibbs w q L hq hGibbs
  have hKLEReal :
      genericWeightKLDivergenceEReal q w = (genericWeightKLDivergence q w : EReal) :=
    genericWeightKLDivergenceEReal_eq_of_summable q w hq hw hCompat hKLSummable
  calc
    D q = ((D q).toReal : EReal) := (EReal.coe_toReal hD_ne_top hD_ne_bot).symm
    _ = (genericWeightKLDivergence q w : EReal) := by simp [hReal]
    _ = genericWeightKLDivergenceEReal q w := by simpa [hKLEReal] using hKLEReal.symm

private theorem exactBoundedLossFormula_eq_kl_at_gibbs
    (D : ExtendedDivergence P)
    (w : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hExact : ExactBoundedLossFormula D w)
    (hSeq : SequentialLowerSemicontinuousOnSimplex D)
    (L : P → Real)
    (hL : BoundedLossProfile L) :
    D (genericGibbsLaw w L) =
      genericWeightKLDivergenceEReal (genericGibbsLaw w L) w := by
  let qStar : P → ENNReal := genericGibbsLaw w L
  have hqStar : ProbabilityWeight qStar := genericGibbsLaw_normalized w L hw hL
  have hLossSummable : Summable (fun p : P => genericLossContribution qStar L p) :=
    genericExpectedLossSummable_of_bounded qStar L hqStar hL
  have hKLSummable :
      Summable (fun p : P => genericWeightKLDivergenceContribution qStar w p) :=
    genericWeightKLDivergenceSummable_of_gibbs w L hw hL
  have hD_ne_bot : D qStar ≠ ⊥ := exactBoundedLossFormula_ne_bot D w hw hExact qStar hqStar
  have hExactAt :
      genericVariationalValue D qStar L =
        ((-Real.log (genericGibbsPartition w L).toReal : Real) : EReal) :=
    exactBoundedLossFormula_attains_at_gibbs D w hw hExact hSeq L hL
  exact generic_divergence_eq_kl_of_exact_gibbs_attainment
    D w qStar L hw hqStar hLossSummable hKLSummable (fun p => rfl) hD_ne_bot hExactAt

private theorem genericGibbsLaw_truncatedLogRatio_toReal_tendsto
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (p : P) :
    Tendsto
      (fun n : Nat =>
        (genericGibbsLaw w (fun x => -truncatedLogRatio q w n x) p).toReal)
      atTop (𝓝 ((q p).toReal)) := by
  have hNum :
      Tendsto
        (fun n : Nat =>
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal)
        atTop (𝓝 ((q p).toReal)) :=
    genericGibbsWeight_truncatedLogRatio_toReal_tendsto q w hq hw hCompat p
  have hDen :
      Tendsto
        (fun n : Nat =>
          (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 1) :=
    genericGibbsPartition_truncatedLogRatio_toReal_tendsto_one q w hq hw hCompat
  have hDenNe :
      ∀ᶠ n : Nat in atTop,
        (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal ≠ 0 := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hZne :
        genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ 0 :=
      genericGibbsPartition_ne_zero w (fun x => -truncatedLogRatio q w n x) hw
    have hZtop :
        genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ ⊤ :=
      genericGibbsPartition_ne_top_of_bounded w (fun x => -truncatedLogRatio q w n x) hw
        (boundedLossProfile_neg (boundedLossProfile_truncatedLogRatio q w n))
    exact ne_of_gt (ENNReal.toReal_pos hZne hZtop)
  have hDiv :
      Tendsto
        (fun n : Nat =>
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
            / (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 ((q p).toReal / 1)) :=
    hNum.div hDen one_ne_zero
  have hEq :
      (fun n : Nat =>
        (genericGibbsLaw w (fun x => -truncatedLogRatio q w n x) p).toReal) =
      (fun n : Nat =>
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
          / (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal) := by
    funext n
    rw [genericGibbsLaw, ENNReal.toReal_div]
  rw [hEq]
  simpa using hDiv

private theorem genericWeightL1Dist_truncatedGibbsLaw_tendsto_zero_of_finite
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    Tendsto
      (fun n : Nat =>
        genericWeightL1Dist (genericGibbsLaw w (fun x => -truncatedLogRatio q w n x)) q)
      atTop (𝓝 0) := by
  let qs : Nat → P → ENNReal := fun n => genericGibbsLaw w (fun x => -truncatedLogRatio q w n x)
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 :=
    genericSupportCompatible_of_finite q w hFinite
  have hqs : ∀ n : Nat, ProbabilityWeight (qs n) := by
    intro n
    dsimp [qs]
    exact genericGibbsLaw_normalized w (fun x => -truncatedLogRatio q w n x) hw
      (boundedLossProfile_neg (boundedLossProfile_truncatedLogRatio q w n))
  have hPoint :
      ∀ p : P,
        Tendsto
          (fun n : Nat => ((qs n p).toReal - (q p).toReal))
          atTop (𝓝 0) := by
    intro p
    dsimp [qs]
    have hSub :
        Tendsto
          (fun n : Nat =>
            (genericGibbsLaw w (fun x => -truncatedLogRatio q w n x) p).toReal - (q p).toReal)
          atTop (𝓝 (((q p).toReal) - (q p).toReal)) :=
      (genericGibbsLaw_truncatedLogRatio_toReal_tendsto q w hq hw hCompat p).sub
        tendsto_const_nhds
    simpa using hSub
  have hPointAbs :
      ∀ p : P,
        Tendsto
          (fun n : Nat => |(qs n p).toReal - (q p).toReal|)
          atTop (𝓝 0) := by
    intro p
    simpa [Real.norm_eq_abs] using (hPoint p).norm
  have hqSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hwSummable : Summable (fun p : P => (w p).toReal) := genericWeightSummable_toReal hw
  have hBoundSummable :
      Summable (fun p : P => 3 * (q p).toReal + 2 * (w p).toReal) := by
    exact (hqSummable.mul_left 3).add (hwSummable.mul_left 2)
  have hPartHalf :
      ∀ᶠ n : Nat in atTop,
        (1 / 2 : Real) <
          (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal := by
    have hPart :
        Tendsto
          (fun n : Nat =>
            (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
          atTop (𝓝 1) :=
      genericGibbsPartition_truncatedLogRatio_toReal_tendsto_one q w hq hw hCompat
    have hMem : Set.Ioi (1 / 2 : Real) ∈ 𝓝 (1 : Real) := by
      exact Ioi_mem_nhds (by norm_num)
    exact hPart.eventually hMem
  have hBound :
      ∀ᶠ n : Nat in atTop,
        ∀ p : P,
          ‖|(qs n p).toReal - (q p).toReal|‖ ≤ 3 * (q p).toReal + 2 * (w p).toReal := by
    filter_upwards [hPartHalf] with n hn p
    have hLawEq :
        (qs n p).toReal =
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
            / (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal := by
      dsimp [qs]
      rw [genericGibbsLaw, ENNReal.toReal_div]
    have hWeightLe :
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
          ≤ (q p).toReal + (w p).toReal :=
      genericGibbsWeight_truncatedLogRatio_toReal_le_q_add_w q w hq hw hCompat n p
    have hLawLe :
        (qs n p).toReal ≤ 2 * ((q p).toReal + (w p).toReal) := by
      rw [hLawEq]
      calc
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal /
            (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal
            ≤
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal / (1 / 2 : Real) := by
              exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg (by norm_num) hn.le
        _ = 2 * (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal := by
              field_simp
        _ ≤ 2 * ((q p).toReal + (w p).toReal) := by
              nlinarith
    have hAbsLe :
        |(qs n p).toReal - (q p).toReal| ≤ (qs n p).toReal + (q p).toReal := by
      simpa [ENNReal.toReal_nonneg] using abs_sub_le (qs n p).toReal 0 (q p).toReal
    have hNonneg :
        0 ≤ 3 * (q p).toReal + 2 * (w p).toReal := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _), abs_of_nonneg hNonneg] using
      calc
      |(qs n p).toReal - (q p).toReal|
          ≤ (qs n p).toReal + (q p).toReal := hAbsLe
      _ ≤ 2 * ((q p).toReal + (w p).toReal) + (q p).toReal := by
            linarith
      _ = 3 * (q p).toReal + 2 * (w p).toReal := by ring
  have hTsum :
      Tendsto
        (fun n : Nat => ∑' p : P, |(qs n p).toReal - (q p).toReal|)
        atTop (𝓝 (∑' p : P, (0 : Real))) :=
    tendsto_tsum_of_dominated_convergence hBoundSummable hPointAbs hBound
  simpa [genericWeightL1Dist, qs] using hTsum

private theorem genericGibbsWeight_truncatedRewardContribution_tendsto
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0)
    (p : P) :
    Tendsto
      (fun n : Nat =>
        (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
          * truncatedLogRatio q w n p)
      atTop (𝓝 (genericWeightKLDivergenceContribution q w p)) := by
  by_cases hqZero : q p = 0
  · have hEq :
        (fun n : Nat =>
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
            * truncatedLogRatio q w n p)
          =
        fun n : Nat => -((w p).toReal * ((n : Real) * Real.exp (-(n : Real)))) := by
        funext n
        have htr : truncatedLogRatio q w n p = -(n : Real) := by
          simpa [truncatedLogRatio, hqZero]
        have hloss : -(fun x => -truncatedLogRatio q w n x) p = truncatedLogRatio q w n p := by
          simp
        calc
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
              * truncatedLogRatio q w n p
              = ((w p).toReal * Real.exp (truncatedLogRatio q w n p))
                  * truncatedLogRatio q w n p := by
                    unfold genericGibbsWeight
                    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), hloss]
          _ = ((w p).toReal * Real.exp (-(n : Real))) * (-(n : Real)) := by rw [htr]
          _ = -((w p).toReal * ((n : Real) * Real.exp (-(n : Real)))) := by ring
    have hExp :
        Tendsto (fun n : Nat => (n : Real) * Real.exp (-(n : Real))) atTop (𝓝 0) := by
        simpa [pow_one] using
          (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_natCast_atTop_atTop
    have hScaled :
        Tendsto
          (fun n : Nat => -((w p).toReal * ((n : Real) * Real.exp (-(n : Real)))))
          atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hExp).neg
    rw [hEq]
    simpa [genericWeightKLDivergenceContribution, hqZero] using hScaled
  · have hwZero : w p ≠ 0 := hCompat p hqZero
    have hqTop : q p ≠ ⊤ := genericWeight_ne_top_of_normalized hq p
    have hwTop : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
    have hEventually :
        ∀ᶠ n : Nat in atTop,
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
              * truncatedLogRatio q w n p =
            genericWeightKLDivergenceContribution q w p := by
      filter_upwards [truncatedLogRatio_eventually_eq_log q w p hqZero hwZero] with n hn
      rw [genericGibbsWeight_truncatedLogRatio_toReal_eq_q q w n p hqZero hwZero hqTop hwTop hn]
      simp [genericWeightKLDivergenceContribution, hqZero, hn]
    exact (tendsto_congr' hEventually).2 tendsto_const_nhds

private theorem genericGibbsWeight_truncatedRewardContribution_norm_le
    (q w : P → ENNReal)
    (p : P)
    (n : Nat)
    (hCompat : q p ≠ 0 → w p ≠ 0)
    (hqTop : q p ≠ ⊤)
    (hwTop : w p ≠ ⊤) :
    ‖(genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
        * truncatedLogRatio q w n p‖
      ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
          + (q p).toReal
          + Real.exp (-1) * (w p).toReal := by
  have hRhsNonneg :
      0 ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
            + (q p).toReal
            + Real.exp (-1) * (w p).toReal := by
    positivity
  have hExpToReal :
      (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
        = (w p).toReal * Real.exp (truncatedLogRatio q w n p) := by
    have hloss : -(fun x => -truncatedLogRatio q w n x) p = truncatedLogRatio q w n p := by
      simp
    unfold genericGibbsWeight
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), hloss]
  by_cases hqZero : q p = 0
  · have htr : truncatedLogRatio q w n p = -(n : Real) := by
      simpa [truncatedLogRatio, hqZero]
    rw [hExpToReal, htr]
    have hMain :
        ‖(w p).toReal * Real.exp (-(n : Real)) * (-(n : Real))‖
          ≤ Real.exp (-1) * (w p).toReal := by
      have hneg : (-(n : Real)) ≤ 0 := by
        exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le n)
      calc
        ‖(w p).toReal * Real.exp (-(n : Real)) * (-(n : Real))‖
            = (w p).toReal * ((n : Real) * Real.exp (-(n : Real))) := by
                rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
                  abs_of_nonneg (Real.exp_nonneg _), abs_of_nonpos hneg]
                ring
        _ ≤ (w p).toReal * Real.exp (-1) := by
              gcongr
              exact Real.mul_exp_neg_le_exp_neg_one (n : Real)
        _ = Real.exp (-1) * (w p).toReal := by ring
    calc
      ‖(w p).toReal * Real.exp (-(n : Real)) * (-(n : Real))‖
          ≤ Real.exp (-1) * (w p).toReal := hMain
      _ ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
            + (q p).toReal
            + Real.exp (-1) * (w p).toReal := by
              have hExtraNonneg :
                  0 ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal + (q p).toReal := by
                positivity
              linarith
  · have hwZero : w p ≠ 0 := hCompat hqZero
    by_cases hLow : Real.log ((q p / w p).toReal) ≤ -(n : Real)
    · rw [hExpToReal]
      have htr : truncatedLogRatio q w n p = -(n : Real) := by
        have hBody :
            max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) = -(n : Real) := by
          exact max_eq_left (le_trans (min_le_left _ _) hLow)
        simpa [truncatedLogRatio, hqZero, hwZero] using hBody
      rw [htr]
      have hMain :
          ‖(w p).toReal * Real.exp (-(n : Real)) * (-(n : Real))‖
            ≤ Real.exp (-1) * (w p).toReal := by
        have hneg : (-(n : Real)) ≤ 0 := by
          exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le n)
        calc
          ‖(w p).toReal * Real.exp (-(n : Real)) * (-(n : Real))‖
              = (w p).toReal * ((n : Real) * Real.exp (-(n : Real))) := by
                  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
                    abs_of_nonneg (Real.exp_nonneg _), abs_of_nonpos hneg]
                  ring
          _ ≤ (w p).toReal * Real.exp (-1) := by
                gcongr
                exact Real.mul_exp_neg_le_exp_neg_one (n : Real)
          _ = Real.exp (-1) * (w p).toReal := by ring
      calc
        ‖(w p).toReal * Real.exp (-(n : Real)) * (-(n : Real))‖
            ≤ Real.exp (-1) * (w p).toReal := hMain
        _ ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
              + (q p).toReal
              + Real.exp (-1) * (w p).toReal := by
                have hExtraNonneg :
                    0 ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal + (q p).toReal := by
                  positivity
                linarith
    · by_cases hHigh : (n : Real) ≤ Real.log ((q p / w p).toReal)
      · have htr : truncatedLogRatio q w n p = (n : Real) := by
          have hBody :
              max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) = (n : Real) := by
            have hMin : min (Real.log ((q p / w p).toReal)) (n : Real) = (n : Real) :=
              min_eq_right hHigh
            rw [hMin]
            exact max_eq_right (by nlinarith)
          simpa [truncatedLogRatio, hqZero, hwZero] using hBody
        rw [hExpToReal, htr]
        have hRatioLower :
            Real.exp (n : Real) ≤ ((q p / w p).toReal) := by
          calc
            Real.exp (n : Real) ≤ Real.exp (Real.log ((q p / w p).toReal)) := by
                gcongr
            _ = ((q p / w p).toReal) := by
                rw [Real.exp_log (ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hqZero, hwTop⟩)
                  (ENNReal.div_ne_top hqTop hwZero))]
        have hDivToReal : (q p / w p).toReal = (q p).toReal / (w p).toReal := by
          rw [ENNReal.toReal_div]
        have hwRealPos : 0 < (w p).toReal := ENNReal.toReal_pos hwZero hwTop
        have hWeightLeQ :
            (w p).toReal * Real.exp (n : Real) ≤ (q p).toReal := by
          calc
            (w p).toReal * Real.exp (n : Real)
                ≤ (w p).toReal * ((q p / w p).toReal) := by
                    gcongr
            _ = (w p).toReal * ((q p).toReal / (w p).toReal) := by rw [hDivToReal]
            _ = (q p).toReal := by
                  field_simp [hwRealPos.ne']
        have hBase :
            |(w p).toReal * Real.exp (n : Real) * (n : Real)|
              ≤ |(q p).toReal * truncatedLogRatio q w n p| := by
          have hNonnegLhs : 0 ≤ (w p).toReal * Real.exp (n : Real) * (n : Real) := by
            positivity
          have hNonnegRhs : 0 ≤ (q p).toReal * truncatedLogRatio q w n p := by
            rw [htr]
            positivity
          rw [abs_of_nonneg hNonnegLhs, abs_of_nonneg hNonnegRhs]
          calc
            (w p).toReal * Real.exp (n : Real) * (n : Real)
                ≤ (q p).toReal * (n : Real) := by
                    gcongr
            _ = (q p).toReal * truncatedLogRatio q w n p := by rw [htr]
        have hQBound :
            ‖(q p).toReal * truncatedLogRatio q w n p‖
              ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
                  + (q p).toReal
                  + Real.exp (-1) * (w p).toReal :=
          truncatedRewardContribution_norm_le q w p n hCompat hqTop hwTop
        calc
          ‖(w p).toReal * Real.exp (n : Real) * (n : Real)‖
              = |(w p).toReal * Real.exp (n : Real) * (n : Real)| := by
                  rw [Real.norm_eq_abs]
          _ ≤ |(q p).toReal * truncatedLogRatio q w n p| := hBase
          _ = ‖(q p).toReal * truncatedLogRatio q w n p‖ := by
                rw [Real.norm_eq_abs]
          _ ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
                + (q p).toReal
                + Real.exp (-1) * (w p).toReal := hQBound
      · have htr :
          truncatedLogRatio q w n p = Real.log ((q p / w p).toReal) := by
            have hLower : -(n : Real) < Real.log ((q p / w p).toReal) := lt_of_not_ge hLow
            have hUpper : Real.log ((q p / w p).toReal) < (n : Real) := lt_of_not_ge hHigh
            have hBody :
                max (-(n : Real)) (min (Real.log ((q p / w p).toReal)) (n : Real)) =
                  Real.log ((q p / w p).toReal) := by
              rw [min_eq_left (le_of_lt hUpper), max_eq_right (le_of_lt hLower)]
            simpa [truncatedLogRatio, hqZero, hwZero] using hBody
        rw [genericGibbsWeight_truncatedLogRatio_toReal_eq_q q w n p hqZero hwZero hqTop hwTop htr]
        simpa [htr] using
          truncatedRewardContribution_norm_le q w p n hCompat hqTop hwTop

private theorem genericGibbsWeight_expectedReward_truncatedLogRatio_tendsto_kl_of_finite
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    Tendsto
      (fun n : Nat =>
        ∑' p : P,
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
            * truncatedLogRatio q w n p)
      atTop (𝓝 (genericWeightKLDivergence q w)) := by
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 :=
    genericSupportCompatible_of_finite q w hFinite
  have hqSummable : Summable (fun p : P => (q p).toReal) := genericWeightSummable_toReal hq
  have hwSummable : Summable (fun p : P => (w p).toReal) := genericWeightSummable_toReal hw
  have hTermSummable :
      Summable (fun p : P => (genericWeightKLDivergenceTerm (q p) (w p)).toReal) :=
    ENNReal.summable_toReal hFinite
  have hBoundSummable :
      Summable
        (fun p : P =>
          (genericWeightKLDivergenceTerm (q p) (w p)).toReal
            + (q p).toReal
            + Real.exp (-1) * (w p).toReal) := by
    exact (hTermSummable.add hqSummable).add (hwSummable.mul_left (Real.exp (-1)))
  have hPoint :
      ∀ p : P,
        Tendsto
          (fun n : Nat =>
            (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
              * truncatedLogRatio q w n p)
          atTop (𝓝 (genericWeightKLDivergenceContribution q w p)) :=
    genericGibbsWeight_truncatedRewardContribution_tendsto q w hq hw hCompat
  have hBound :
      ∀ᶠ n : Nat in atTop,
        ∀ p : P,
          ‖(genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
              * truncatedLogRatio q w n p‖
            ≤ (genericWeightKLDivergenceTerm (q p) (w p)).toReal
                + (q p).toReal
                + Real.exp (-1) * (w p).toReal := by
    refine Filter.Eventually.of_forall ?_
    intro n p
    exact genericGibbsWeight_truncatedRewardContribution_norm_le q w p n
      (fun h => hCompat p h)
      (genericWeight_ne_top_of_normalized hq p)
      (genericWeight_ne_top_of_normalized hw p)
  simpa [genericWeightKLDivergence] using
    (tendsto_tsum_of_dominated_convergence hBoundSummable hPoint hBound)

private theorem genericExpectedReward_truncatedGibbsLaw_truncatedLogRatio_tendsto_kl_of_finite
    (q w : P → ENNReal)
    (hq : ProbabilityWeight q)
    (hw : ProbabilityWeight w)
    (hFinite : genericWeightKLDivergenceInf q w ≠ ⊤) :
    Tendsto
      (fun n : Nat =>
        genericExpectedReward (genericGibbsLaw w (fun x => -truncatedLogRatio q w n x))
          (truncatedLogRatio q w n))
      atTop (𝓝 (genericWeightKLDivergence q w)) := by
  let qs : Nat → P → ENNReal := fun n => genericGibbsLaw w (fun x => -truncatedLogRatio q w n x)
  have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 :=
    genericSupportCompatible_of_finite q w hFinite
  have hNum :
      Tendsto
        (fun n : Nat =>
          ∑' p : P,
            (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
              * truncatedLogRatio q w n p)
        atTop (𝓝 (genericWeightKLDivergence q w)) :=
    genericGibbsWeight_expectedReward_truncatedLogRatio_tendsto_kl_of_finite q w hq hw hFinite
  have hDen :
      Tendsto
        (fun n : Nat =>
          (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 1) :=
    genericGibbsPartition_truncatedLogRatio_toReal_tendsto_one q w hq hw hCompat
  have hDenNe :
      ∀ᶠ n : Nat in atTop,
        (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal ≠ 0 := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hZne :
        genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ 0 :=
      genericGibbsPartition_ne_zero w (fun x => -truncatedLogRatio q w n x) hw
    have hZtop :
        genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ ⊤ :=
      genericGibbsPartition_ne_top_of_bounded w (fun x => -truncatedLogRatio q w n x) hw
        (boundedLossProfile_neg (boundedLossProfile_truncatedLogRatio q w n))
    exact ne_of_gt (ENNReal.toReal_pos hZne hZtop)
  have hQuot :
      Tendsto
        (fun n : Nat =>
          (∑' p : P,
              (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
                * truncatedLogRatio q w n p)
            / (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
        atTop (𝓝 (genericWeightKLDivergence q w / 1)) :=
    hNum.div hDen one_ne_zero
  have hEq :
      (fun n : Nat =>
        genericExpectedReward (qs n) (truncatedLogRatio q w n)) =
      (fun n : Nat =>
        (∑' p : P,
            (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
              * truncatedLogRatio q w n p)
          / (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal) := by
    funext n
    have hqs : ProbabilityWeight (qs n) := by
      dsimp [qs]
      exact genericGibbsLaw_normalized w (fun x => -truncatedLogRatio q w n x) hw
        (boundedLossProfile_neg (boundedLossProfile_truncatedLogRatio q w n))
    have hBounded : BoundedLossProfile (truncatedLogRatio q w n) :=
      boundedLossProfile_truncatedLogRatio q w n
    rw [genericExpectedReward_eq_tsum (qs n) (truncatedLogRatio q w n) hqs hBounded]
    have hZne :
        genericGibbsPartition w (fun x => -truncatedLogRatio q w n x) ≠ 0 :=
      genericGibbsPartition_ne_zero w (fun x => -truncatedLogRatio q w n x) hw
    have hWeightNormSummable :
        Summable (fun p : P =>
          ‖(genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
              * truncatedLogRatio q w n p‖) := by
      refine Summable.of_nonneg_of_le
        (f := fun p : P =>
          (genericWeightKLDivergenceTerm (q p) (w p)).toReal
            + (q p).toReal
            + Real.exp (-1) * (w p).toReal)
        (g := fun p : P =>
          ‖(genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
              * truncatedLogRatio q w n p‖)
        (fun p => norm_nonneg _)
        (fun p => genericGibbsWeight_truncatedRewardContribution_norm_le q w p n
          (fun h => hCompat p h)
          (genericWeight_ne_top_of_normalized hq p)
          (genericWeight_ne_top_of_normalized hw p))
        (((ENNReal.summable_toReal hFinite).add (genericWeightSummable_toReal hq)).add
          ((genericWeightSummable_toReal hw).mul_left (Real.exp (-1))))
    have hWeightSummable :
        Summable (fun p : P =>
          (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
            * truncatedLogRatio q w n p) := by
      exact Summable.of_norm hWeightNormSummable
    calc
      ∑' p : P, (qs n p).toReal * truncatedLogRatio q w n p
          = ∑' p : P,
              ((genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
                / (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)
                * truncatedLogRatio q w n p := by
                apply tsum_congr
                intro p
                dsimp [qs]
                rw [genericGibbsLaw, ENNReal.toReal_div]
      _ = ∑' p : P,
              ((genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
                * truncatedLogRatio q w n p)
                * ((genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)⁻¹ := by
              apply tsum_congr
              intro p
              rw [div_eq_mul_inv]
              ring
      _ = (∑' p : P,
              (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
                * truncatedLogRatio q w n p)
            * ((genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal)⁻¹ := by
              rw [tsum_mul_right]
      _ = (∑' p : P,
              (genericGibbsWeight w (fun x => -truncatedLogRatio q w n x) p).toReal
                * truncatedLogRatio q w n p)
            / (genericGibbsPartition w (fun x => -truncatedLogRatio q w n x)).toReal := by
              rw [div_eq_mul_inv]
  rw [hEq]
  simpa using hQuot

/--
Discrete KL-necessity on the countable simplex.

If an extended divergence on countable probability weights satisfies the exact bounded-loss
variational formula against a reference weight `w`, then it agrees with the honest discrete KL
divergence on every normalized law. The additional proper/convex/off-simplex hypotheses are kept
here to match the manuscript theorem surface; the direct discrete proof below only uses the exact
formula, its lower-semicontinuity, and the already established `D ≥ KL` half.
-/
theorem exactBoundedLossFormula_eq_kl
    (D : ExtendedDivergence P)
    (w q : P → ENNReal)
    (hw : ProbabilityWeight w)
    (hq : ProbabilityWeight q)
    (_hProper : ProperOnSimplex D)
    (_hConvex : ConvexOnSimplex D)
    (_hOffSimplex : OffSimplexTop D)
    (hSeq : SequentialLowerSemicontinuousOnSimplex D)
    (hExact : ExactBoundedLossFormula D w) :
    D q = genericWeightKLDivergenceEReal q w := by
  by_cases hFinite : genericWeightKLDivergenceInf q w ≠ ⊤
  · have hCompat : ∀ p : P, q p ≠ 0 → w p ≠ 0 :=
      genericSupportCompatible_of_finite q w hFinite
    let qs : Nat → P → ENNReal := fun n =>
      genericGibbsLaw w (fun x => -truncatedLogRatio q w n x)
    have hqs : ∀ n : Nat, ProbabilityWeight (qs n) := by
      intro n
      dsimp [qs]
      exact genericGibbsLaw_normalized w (fun x => -truncatedLogRatio q w n x) hw
        (boundedLossProfile_neg (boundedLossProfile_truncatedLogRatio q w n))
    have hDist :
        Tendsto (fun n : Nat => genericWeightL1Dist (qs n) q) atTop (𝓝 0) := by
      simpa [qs] using genericWeightL1Dist_truncatedGibbsLaw_tendsto_zero_of_finite q w hq hw hFinite
    have hKLTendsto :
        Tendsto (fun n : Nat => genericWeightKLDivergence (qs n) w)
          atTop (𝓝 (genericWeightKLDivergence q w)) := by
      have hReward :
          Tendsto
            (fun n : Nat => genericExpectedReward (qs n) (truncatedLogRatio q w n))
            atTop (𝓝 (genericWeightKLDivergence q w)) := by
        simpa [qs] using
          genericExpectedReward_truncatedGibbsLaw_truncatedLogRatio_tendsto_kl_of_finite q w hq hw hFinite
      have hLog :
          Tendsto
            (fun n : Nat => genericLogPartition w (truncatedLogRatio q w n))
            atTop (𝓝 0) :=
        genericLogPartition_truncatedLogRatio_tendsto_zero q w hq hw hCompat
      have hSub :
          Tendsto
            (fun n : Nat =>
              genericExpectedReward (qs n) (truncatedLogRatio q w n)
                - genericLogPartition w (truncatedLogRatio q w n))
            atTop (𝓝 (genericWeightKLDivergence q w - 0)) :=
        hReward.sub hLog
      have hEq :
          (fun n : Nat =>
            genericWeightKLDivergence (qs n) w) =
          (fun n : Nat =>
            genericExpectedReward (qs n) (truncatedLogRatio q w n)
              - genericLogPartition w (truncatedLogRatio q w n)) := by
        funext n
        dsimp [qs]
        have hL : BoundedLossProfile (fun x => -truncatedLogRatio q w n x) :=
          boundedLossProfile_neg (boundedLossProfile_truncatedLogRatio q w n)
        have hqsn : ProbabilityWeight (qs n) := hqs n
        have hLossSummable :
            Summable (fun p : P =>
              genericLossContribution (qs n) (fun x => -truncatedLogRatio q w n x) p) :=
          genericExpectedLossSummable_of_bounded (qs n) (fun x => -truncatedLogRatio q w n x)
            hqsn hL
        have hKLSummable :
            Summable (fun p : P => genericWeightKLDivergenceContribution (qs n) w p) :=
          genericWeightKLDivergenceSummable_of_gibbs w (fun x => -truncatedLogRatio q w n x) hw hL
        have hId :=
          genericExpectedLoss_add_genericWeightKLDivergence_eq_negativeLogPartition
            w (qs n) (fun x => -truncatedLogRatio q w n x) hw hqsn hLossSummable hKLSummable
            (fun p => rfl)
        have hRewardEq :
            genericExpectedLoss (qs n) (fun x => -truncatedLogRatio q w n x) =
              -genericExpectedReward (qs n) (truncatedLogRatio q w n) := by
          simp [genericExpectedReward]
        unfold genericLogPartition
        linarith
      rw [hEq]
      simpa using hSub
    have hUpper :
        D q ≤ (genericWeightKLDivergence q w : EReal) := by
      apply ereal_le_coe_of_forall_real_lt
      intro y hy
      by_contra hyLe
      have hyEventually :
          ∀ᶠ n : Nat in atTop, (y : EReal) < D (qs n) :=
        hSeq q qs hq hqs hDist y hy
      have hlt : genericWeightKLDivergence q w < y := lt_of_not_ge hyLe
      have hKlEventually :
          ∀ᶠ n : Nat in atTop, genericWeightKLDivergence (qs n) w < y := by
        have hMem : Set.Iio y ∈ 𝓝 (genericWeightKLDivergence q w) := Iio_mem_nhds hlt
        exact hKLTendsto.eventually hMem
      rcases (hyEventually.and hKlEventually).exists with ⟨n, hyN, hKlN⟩
      have hDqs :
          D (qs n) = (genericWeightKLDivergence (qs n) w : EReal) := by
        have hEqGibbs :
            D (qs n) = genericWeightKLDivergenceEReal (qs n) w := by
          dsimp [qs]
          exact exactBoundedLossFormula_eq_kl_at_gibbs D w hw hExact hSeq
            (fun x => -truncatedLogRatio q w n x)
            (boundedLossProfile_neg (boundedLossProfile_truncatedLogRatio q w n))
        have hL : BoundedLossProfile (fun x => -truncatedLogRatio q w n x) :=
          boundedLossProfile_neg (boundedLossProfile_truncatedLogRatio q w n)
        have hqsn : ProbabilityWeight (qs n) := hqs n
        have hCompatQs :
            ∀ p : P, qs n p ≠ 0 → w p ≠ 0 := by
          intro p hqp
          dsimp [qs] at hqp
          exact (genericGibbsLaw_eq_zero_iff w (fun x => -truncatedLogRatio q w n x) hw hL p).not.mp hqp
        have hKLSummable :
            Summable (fun p : P => genericWeightKLDivergenceContribution (qs n) w p) :=
          genericWeightKLDivergenceSummable_of_gibbs w (fun x => -truncatedLogRatio q w n x) hw hL
        have hE :
            genericWeightKLDivergenceEReal (qs n) w =
              (genericWeightKLDivergence (qs n) w : EReal) :=
          genericWeightKLDivergenceEReal_eq_of_summable (qs n) w hqsn hw hCompatQs hKLSummable
        simpa [hE] using hEqGibbs.trans hE
      have hyReal : y < genericWeightKLDivergence (qs n) w := by
        rw [hDqs] at hyN
        exact EReal.coe_lt_coe_iff.mp hyN
      exact (not_lt_of_ge hKlN.le) hyReal
    have hLower :
        genericWeightKLDivergenceEReal q w ≤ D q :=
      exactBoundedLossFormula_ge_kl D w hw hExact q hq
    have hRealEq :
        genericWeightKLDivergenceEReal q w = (genericWeightKLDivergence q w : EReal) :=
      genericWeightKLDivergenceEReal_eq_of_finite q w hq hw hFinite hCompat
    apply le_antisymm
    · simpa [hRealEq] using hUpper
    · exact hLower
  · have hInfTop : genericWeightKLDivergenceInf q w = ⊤ := not_ne_iff.mp hFinite
    have hLower :
        genericWeightKLDivergenceEReal q w ≤ D q :=
      exactBoundedLossFormula_ge_kl D w hw hExact q hq
    have hDTop : D q = ⊤ := by
      have : (⊤ : EReal) ≤ D q := by
        simpa [genericWeightKLDivergenceEReal, hInfTop] using hLower
      simpa using this
    simp [genericWeightKLDivergenceEReal, hInfTop, hDTop]

/-!
## Self-instantiation: KL itself satisfies the exact bounded-loss formula

The duality theorems in this file are stated abstractly over an
`ExtendedDivergence D` satisfying four predicates. This subsection certifies
that the predicates are non-vacuous: the honest discrete KL divergence is
itself an instance, so `lem_kl_necessity` applied to `D := KL` recovers the
trivial identity `KL = KL` rather than degenerating. This is the explicit
"sanity check" requested by `lean_open_issues.md` G2.

The lower-bound part of `ExactBoundedLossFormula` for KL is exactly
`genericKLVariationalObjective_lower_bound`. The ε-attainment part is
witnessed by the Gibbs law itself, which achieves the variational minimum
`-log Z` exactly via
`genericExpectedLoss_add_genericWeightKLDivergence_eq_negativeLogPartition`.
-/

theorem genericWeightKLDivergence_satisfies_ExactBoundedLossFormula
    (w : P → ENNReal) (hw : ProbabilityWeight w) :
    ExactBoundedLossFormula (fun q => genericWeightKLDivergenceEReal q w) w := by
  intro L hL
  refine ⟨?_, ?_⟩
  · -- Lower bound: -log Z ≤ E_q[L] + KL(q || w) for every probability weight q.
    -- This is `genericKLVariationalObjective_lower_bound`; the goal is
    -- definitionally `genericKLVariationalObjective q w L` after unfolding
    -- `genericVariationalValue` against `D := fun q => genericWeightKLDivergenceEReal q w`.
    intro q hq
    have hLower := genericKLVariationalObjective_lower_bound w q L hw hq hL
    show ((-Real.log (genericGibbsPartition w L).toReal : Real) : EReal) ≤
         genericExpectedLossEReal q L + genericWeightKLDivergenceEReal q w
    exact hLower
  · -- ε-attainment: the Gibbs law achieves -log Z exactly, so it is below
    -- -log Z + ε for every ε > 0.
    intro ε hε
    refine ⟨genericGibbsLaw w L, genericGibbsLaw_normalized w L hw hL, ?_⟩
    have hqStar : ProbabilityWeight (genericGibbsLaw w L) :=
      genericGibbsLaw_normalized w L hw hL
    have hCompat : ∀ p : P, genericGibbsLaw w L p ≠ 0 → w p ≠ 0 :=
      fun p hqp => (genericGibbsLaw_eq_zero_iff w L hw hL p).not.mp hqp
    have hLossSummable :
        Summable (fun p : P => genericLossContribution (genericGibbsLaw w L) L p) :=
      genericExpectedLossSummable_of_bounded (genericGibbsLaw w L) L hqStar hL
    have hKLSummable :
        Summable (fun p : P =>
          genericWeightKLDivergenceContribution (genericGibbsLaw w L) w p) :=
      genericWeightKLDivergenceSummable_of_gibbs w L hw hL
    have hGibbs : ∀ p : P, genericGibbsLaw w L p = genericGibbsLaw w L p := fun _ => rfl
    have hExactReal :
        genericExpectedLoss (genericGibbsLaw w L) L +
            genericWeightKLDivergence (genericGibbsLaw w L) w =
          -Real.log (genericGibbsPartition w L).toReal :=
      genericExpectedLoss_add_genericWeightKLDivergence_eq_negativeLogPartition
        w (genericGibbsLaw w L) L hw hqStar hLossSummable hKLSummable hGibbs
    have hKLEReal :
        genericWeightKLDivergenceEReal (genericGibbsLaw w L) w =
          (genericWeightKLDivergence (genericGibbsLaw w L) w : EReal) :=
      genericWeightKLDivergenceEReal_eq_of_summable (genericGibbsLaw w L) w
        hqStar hw hCompat hKLSummable
    have hValEq :
        genericExpectedLossEReal (genericGibbsLaw w L) L +
            genericWeightKLDivergenceEReal (genericGibbsLaw w L) w =
          ((-Real.log (genericGibbsPartition w L).toReal : Real) : EReal) := by
      unfold genericExpectedLossEReal
      rw [hKLEReal, ← EReal.coe_add, hExactReal]
    show genericExpectedLossEReal (genericGibbsLaw w L) L +
            genericWeightKLDivergenceEReal (genericGibbsLaw w L) w ≤
         ((-Real.log (genericGibbsPartition w L).toReal + ε : Real) : EReal)
    rw [hValEq]
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/--
Simplex-restricted KL divergence, returning `⊤` off the simplex. This is
the canonical extended-value form expected by `lem_kl_necessity`: the
unwrapped `genericWeightKLDivergenceEReal` does not return `⊤` for
non-normalized inputs, so the wrapper is required for the framework's
`OffSimplexTop` predicate to hold.
-/
noncomputable def klDivergenceOnSimplex
    (w : P → ENNReal) : ExtendedDivergence P :=
  fun q => if ProbabilityWeight q then genericWeightKLDivergenceEReal q w else ⊤

theorem klDivergenceOnSimplex_eq_kl_of_probabilityWeight
    (w q : P → ENNReal) (hq : ProbabilityWeight q) :
    klDivergenceOnSimplex w q = genericWeightKLDivergenceEReal q w := by
  simp [klDivergenceOnSimplex, hq]

theorem klDivergenceOnSimplex_satisfies_OffSimplexTop
    (w : P → ENNReal) :
    OffSimplexTop (klDivergenceOnSimplex w) := by
  intro q hq
  simp [klDivergenceOnSimplex, hq]

theorem klDivergenceOnSimplex_satisfies_ProperOnSimplex
    (w : P → ENNReal) (hw : ProbabilityWeight w) :
    ProperOnSimplex (klDivergenceOnSimplex w) := by
  refine ⟨w, hw, ?_, ?_⟩
  · -- klDivergenceOnSimplex w w ≠ ⊤
    rw [klDivergenceOnSimplex_eq_kl_of_probabilityWeight w w hw]
    have hZero : genericWeightKLDivergenceInf w w = 0 := by
      unfold genericWeightKLDivergenceInf
      apply ENNReal.tsum_eq_zero.mpr
      intro p
      have hwp : w p ≠ ⊤ := genericWeight_ne_top_of_normalized hw p
      exact (genericWeightKLDivergenceTerm_eq_zero_iff hwp).mpr rfl
    show (genericWeightKLDivergenceInf w w : EReal) ≠ ⊤
    rw [hZero]
    simp
  · -- klDivergenceOnSimplex w w ≠ ⊥
    rw [klDivergenceOnSimplex_eq_kl_of_probabilityWeight w w hw]
    -- KL is the EReal-cast of an ENNReal, which is ≥ 0 > ⊥.
    show (genericWeightKLDivergenceInf w w : EReal) ≠ ⊥
    exact EReal.coe_ennreal_ne_bot _

theorem klDivergenceOnSimplex_satisfies_ExactBoundedLossFormula
    (w : P → ENNReal) (hw : ProbabilityWeight w) :
    ExactBoundedLossFormula (klDivergenceOnSimplex w) w := by
  have hKL := genericWeightKLDivergence_satisfies_ExactBoundedLossFormula w hw
  intro L hL
  rcases hKL L hL with ⟨hLower, hAttain⟩
  refine ⟨?_, ?_⟩
  · intro q hq
    have hVal :
        genericVariationalValue (klDivergenceOnSimplex w) q L =
          genericVariationalValue (fun q' => genericWeightKLDivergenceEReal q' w) q L := by
      unfold genericVariationalValue
      rw [klDivergenceOnSimplex_eq_kl_of_probabilityWeight w q hq]
    rw [hVal]
    exact hLower q hq
  · intro ε hε
    rcases hAttain ε hε with ⟨q, hq, hq_le⟩
    refine ⟨q, hq, ?_⟩
    have hVal :
        genericVariationalValue (klDivergenceOnSimplex w) q L =
          genericVariationalValue (fun q' => genericWeightKLDivergenceEReal q' w) q L := by
      unfold genericVariationalValue
      rw [klDivergenceOnSimplex_eq_kl_of_probabilityWeight w q hq]
    rw [hVal]
    exact hq_le

/--
Self-instantiation of `lem_kl_necessity` against the canonical
`D := klDivergenceOnSimplex w`.

This corollary certifies that `lem_kl_necessity` is non-vacuous: the
abstract framework can be applied with KL itself (in its simplex-restricted
form) as the candidate divergence, and the conclusion is the tautological
self-identity `KL q w = KL q w` — confirming that the framework recovers
the right answer when fed the right answer.

`OffSimplexTop` for `klDivergenceOnSimplex w` is supplied internally;
`ExactBoundedLossFormula` for `klDivergenceOnSimplex w` is supplied
internally (lifted from the unwrapped instantiation
`genericWeightKLDivergence_satisfies_ExactBoundedLossFormula`). The
remaining two predicates `ConvexOnSimplex` and
`SequentialLowerSemicontinuousOnSimplex` for `klDivergenceOnSimplex w`
are exposed as hypotheses; they are standard (KL is convex and ℓ¹-l.s.c.
on the simplex via Fatou) but require additional bridging work in the
discrete-simplex setting and are tracked as the remaining piece of G2 in
`lean_open_issues.md`.
-/
theorem genericWeightKLDivergence_self_instantiation
    (w q : P → ENNReal) (hw : ProbabilityWeight w) (hq : ProbabilityWeight q)
    (hConvex : ConvexOnSimplex (klDivergenceOnSimplex w))
    (hSeq : SequentialLowerSemicontinuousOnSimplex (klDivergenceOnSimplex w)) :
    klDivergenceOnSimplex w q = genericWeightKLDivergenceEReal q w := by
  have hProper : ProperOnSimplex (klDivergenceOnSimplex w) :=
    klDivergenceOnSimplex_satisfies_ProperOnSimplex w hw
  have hOffSimplex : OffSimplexTop (klDivergenceOnSimplex w) :=
    klDivergenceOnSimplex_satisfies_OffSimplexTop w
  have hExact : ExactBoundedLossFormula (klDivergenceOnSimplex w) w :=
    klDivergenceOnSimplex_satisfies_ExactBoundedLossFormula w hw
  exact exactBoundedLossFormula_eq_kl
    (klDivergenceOnSimplex w) w q
    hw hq hProper hConvex hOffSimplex hSeq hExact

end DiscreteKLDuality

end

end SemanticConvergence
