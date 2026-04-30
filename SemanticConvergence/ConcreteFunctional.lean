import SemanticConvergence.ConcreteHierarchy
import SemanticConvergence.ConcretePMF

/-
NOTE [variational-core exactness]

The concrete declarations in this file are not allowed to become the semantic endpoint of the
belief / variational rewrite. The exact target is the paper's finite-support realization of the
same formulas locked in `variational_core_exactness_lock.md`, with no canonical dependence on
`Float` proxies.
-/

namespace SemanticConvergence

universe u v

open Classical

noncomputable section

namespace ConcreteLaw

variable {α : Type u}

/-- The identically-zero finitely supported law. -/
def zero : ConcreteLaw α where
  mass _ := 0
  support := []
  support_complete := by
    intro a ha
    simp at ha

/-- Total mass of a finitely supported law. -/
def totalMass (μ : ConcreteLaw α) : Rat :=
  listWeightedSum μ.support μ.mass

/-- Restrict a law to a predicate by zeroing out the complement. -/
def restrict (μ : ConcreteLaw α) (C : PredSet α) [DecidablePred C] : ConcreteLaw α where
  mass a := if C a then μ.mass a else 0
  support := μ.support.filter C
  support_complete := by
    intro a ha
    by_cases hC : C a
    · have hμ : μ.mass a ≠ 0 := by
        simpa [hC] using ha
      refine List.mem_filter.mpr ?_
      constructor
      · exact μ.support_complete a hμ
      · simp [hC]
    · simp [hC] at ha

theorem restrict_mass_of_pos {μ : ConcreteLaw α} {C : PredSet α} [DecidablePred C]
    {a : α} (hC : C a) :
    (μ.restrict C).mass a = μ.mass a := by
  simp [ConcreteLaw.restrict, hC]

theorem restrict_mass_of_neg {μ : ConcreteLaw α} {C : PredSet α} [DecidablePred C]
    {a : α} (hC : ¬ C a) :
    (μ.restrict C).mass a = 0 := by
  simp [ConcreteLaw.restrict, hC]

end ConcreteLaw

/-- Convert an integer into a `Float`. -/
def intToFloat : Int → Float
  | Int.ofNat n => Float.ofNat n
  | Int.negSucc n => Float.neg (Float.ofNat (n + 1))

/-- Convert a rational into a `Float`. -/
def ratToFloat (q : Rat) : Float :=
  intToFloat q.num / Float.ofNat q.den

/-- Clamp a rational to the nonnegative reals and then convert to `Float`. -/
def ratToNonnegFloat (q : Rat) : Float :=
  if q ≤ 0 then 0 else ratToFloat q

/-- Finite-support sum of `Float` weights over a list. -/
def listWeightedSumFloat {α : Type u} (xs : List α) (f : α → Float) : Float :=
  xs.foldr (fun x acc => f x + acc) (0 : Float)

/--
Mix a finitely supported source law through a branch family. Unlike `ConcreteLaw.bind`,
this version does not require decidable equality on the source type.
-/
def mixLaw {α : Type u} {β : Type v}
    [DecidableEq β] [BEq β] [LawfulBEq β]
    (μ : ConcreteLaw α) (κ : α → ConcreteLaw β) : ConcreteLaw β where
  mass b := listWeightedSum μ.support (fun a => μ.mass a * (κ a).mass b)
  support := (μ.support.flatMap fun a => (κ a).support).eraseDups
  support_complete := by
    intro b hb
    rcases listWeightedSum_ne_zero_exists (xs := μ.support)
        (f := fun a => μ.mass a * (κ a).mass b) hb with ⟨a, ha, hneq⟩
    have hk : (κ a).mass b ≠ 0 := by
      intro hz
      apply hneq
      simp [hz]
    have hmem : b ∈ (κ a).support := (κ a).support_complete b hk
    exact (List.mem_eraseDups).2 <| (List.mem_flatMap).2 ⟨a, ha, hmem⟩

section ConcreteScores

variable {A : Type u} {O : Type v}
variable [DecidableEq O] [BEq O] [LawfulBEq O]

/-- Finite support union used by the concrete overlap and Bhattacharyya scores. -/
def supportUnion (μ ν : ConcreteLaw O) : List O :=
  (μ.support ++ ν.support).eraseDups

/-- Rational overlap proxy based on pointwise minimum mass. -/
def overlapAffinity (μ ν : ConcreteLaw O) : Rat :=
  listWeightedSum (supportUnion μ ν) (fun o => min (μ.mass o) (ν.mass o))

/--
Concrete Bhattacharyya affinity on finitely supported laws, evaluated numerically in
`Float` from the rational masses carried by the concrete laws.
-/
def bhatAffinity (μ ν : ConcreteLaw O) : Float :=
  listWeightedSumFloat (supportUnion μ ν) (fun o =>
    Float.sqrt (ratToNonnegFloat (μ.mass o * ν.mass o)))

/--
Concrete Bhattacharyya separation. This uses the standard `-log` transform whenever the
computed affinity is positive and returns `0` at affinity `0`.
-/
def bhatSeparation (μ ν : ConcreteLaw O) : Float :=
  let aff := bhatAffinity μ ν
  if aff ≤ 0 then 0 else Float.neg (Float.log aff)

end ConcreteScores

section ConcreteFunctionals

variable {A : Type u} {O : Type v}
variable [DecidableEq O] [BEq O] [LawfulBEq O]

/-- Concrete program laws for the functional layer. -/
abbrev ProgramLaw (A : Type u) (O : Type v) := ConcreteLaw (EncodedProgram A O)

/-- Concrete local action laws for the functional layer. -/
abbrev ActionLaw (A : Type u) := ConcreteLaw A

/-- Concrete joint class-action laws for the kernel lift. -/
abbrev KernelLaw (A : Type u) (O : Type v) := ConcreteLaw (EncodedProgram A O × A)

/-- Concrete observation law emitted by a program after a full history and action. -/
def programObsLaw (h : FullHist A O) (a : A) (p : EncodedProgram A O) : ConcreteLaw O :=
  p.kernel h.1 h.2 a

/-- The concrete observer fiber through a target program. -/
def observerFiber (ω : Observer (EncodedProgram A O)) (pstar : EncodedProgram A O) :
    PredSet (EncodedProgram A O) :=
  fun p => ω.view p = ω.view pstar

/-- Concrete posterior/program mass assigned to an observer fiber. -/
def observerFiberMass
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (pstar : EncodedProgram A O) : Rat := by
  classical
  exact ConcreteLaw.totalMass (ConcreteLaw.restrict q (observerFiber ω pstar))

/-- Observation mixture over a designated concrete class/fiber. -/
def fiberObsMixture (q : ProgramLaw A O)
    (C : PredSet (EncodedProgram A O)) (h : FullHist A O) (a : A) : ConcreteLaw O := by
  classical
  exact mixLaw (ConcreteLaw.restrict q C) (programObsLaw h a)

/-- Observation mixture over the complement of a designated concrete class/fiber. -/
def complementObsMixture (q : ProgramLaw A O)
    (C : PredSet (EncodedProgram A O)) (h : FullHist A O) (a : A) : ConcreteLaw O := by
  classical
  exact fiberObsMixture q (fun p => ¬ C p) h a

/--
Concrete observer-indexed Bhattacharyya separation for a target program. This is the
first-principles analogue of the manuscript's `\mathfrak B_\omega`.
-/
def bhatOmega_legacy
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (q : ProgramLaw A O) (a : A) (h : FullHist A O) : Float :=
  bhatSeparation
    (fiberObsMixture q (observerFiber ω pstar) h a)
    (complementObsMixture q (observerFiber ω pstar) h a)

/-- Expectation of a `Float`-valued score under a concrete action law. -/
def actionExpectation (π : ActionLaw A) (f : A → Float) : Float :=
  listWeightedSumFloat π.support (fun a => ratToFloat (π.mass a) * f a)

/-- One-step predictive codelength of a finitely supported observation law. -/
def observationCodelength_legacy (μ : ConcreteLaw O) : Float :=
  listWeightedSumFloat μ.support (fun o =>
    let m := μ.mass o
    ratToFloat m * (if m ≤ 0 then 0 else Float.neg (Float.log (ratToNonnegFloat m))))

/-- Local predictive codelength term used by the concrete belief functional. -/
def historyCodelength_legacy
    (π : ActionLaw A) (h : FullHist A O) (p : EncodedProgram A O) : Float :=
  actionExpectation π (fun a => observationCodelength_legacy (programObsLaw h a p))

/-- Concrete code-length prior weight attached to a single encoded program. -/
def encodedProgramPriorWeight (p : EncodedProgram A O) : Rat :=
  codeWeight p.code

/--
Concrete generalized-KL proxy between two nonnegative rational weights. The paper-facing
layer only needs the variational shape here, so the impossible `r = 0 < q` branch is
recorded as a large positive penalty rather than an actual infinity.
-/
def concreteKLDivergenceTerm_legacy (q r : Rat) : Float :=
  if q = 0 then 0
  else if r = 0 then ratToFloat q * 1000000
  else ratToFloat q * Float.log (ratToNonnegFloat (q / r))

/-- Belief-side regularizer against the code-length prior. -/
def beliefRegularizer_legacy
    (q : ProgramLaw A O) : Float :=
  listWeightedSumFloat q.support
    (fun p => concreteKLDivergenceTerm_legacy (q.mass p) (encodedProgramPriorWeight p))

/--
Concrete belief term of the two-observer variational functional: expected codelength plus
the code-prior KL proxy.
-/
def beliefFunctional_legacy
    (q : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Float :=
  listWeightedSumFloat q.support
      (fun p => ratToFloat (q.mass p) * historyCodelength_legacy π h p) +
    beliefRegularizer_legacy q

/-- Capped Bhattacharyya score entering the concrete action-side variational term. -/
def cappedBhatOmega_legacy
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (q : ProgramLaw A O) (a : A) (h : FullHist A O) : Float :=
  let s := bhatOmega_legacy ω pstar q a h
  if s ≤ 1 then s else 1

/-- Concrete action-side class score induced by the realized local action law. -/
def classActionScore_legacy
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (π : ActionLaw A)
    (h : FullHist A O) (pstar : EncodedProgram A O) : Float :=
  actionExpectation π (fun a => cappedBhatOmega_legacy ω pstar q a h)

/-- Finite-list reference mass on a concrete observer class, induced by code weights. -/
def classReferenceWeightOnTargets
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat :=
  listWeightedSum targets
    (fun p => if ω.view p = ω.view pstar then encodedProgramPriorWeight p else 0)

/-- Concrete KL regularizer of the class law against the finite-list class reference mass. -/
def classLawRegularizer_legacy
    (ω : Observer (EncodedProgram A O))
    (ν : ProgramLaw A O) : Float :=
  listWeightedSumFloat ν.support
    (fun p => concreteKLDivergenceTerm_legacy
      (ν.mass p) (classReferenceWeightOnTargets ω ν.support p))

/-- Concrete expected class score under the current class-targeting law. -/
def expectedClassActionScore_legacy
    (ω : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Float :=
  listWeightedSumFloat ν.support
    (fun p => ratToFloat (ν.mass p) * classActionScore_legacy ω q π h p)

/--
Marginal action law induced by a concrete class-action kernel. This is the action-side
distribution that enters the belief term of the kernel lift.
-/
def kernelActionMarginal
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (κ : KernelLaw A O) : ActionLaw A where
  mass a := listWeightedSum κ.support (fun ca => if ca.2 = a then κ.mass ca else 0)
  support := (κ.support.map Prod.snd).eraseDups
  support_complete := by
    intro a ha
    rcases listWeightedSum_ne_zero_exists (xs := κ.support)
        (f := fun ca => if ca.2 = a then κ.mass ca else 0) ha with ⟨ca, hca, hneq⟩
    have hEq : ca.2 = a := by
      by_cases h : ca.2 = a
      · exact h
      · simp [h] at hneq
    exact (List.mem_eraseDups).2 <| (List.mem_map).2 ⟨ca, hca, hEq⟩

/-- Reference mass on a concrete target-action pair induced by class reference and `λ`. -/
def kernelReferenceWeightOnTargets
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (refLaw : ActionLaw A)
    (pstar : EncodedProgram A O) (a : A) : Rat :=
  classReferenceWeightOnTargets ω targets pstar * refLaw.mass a

/-- Concrete class-action score entering the kernel lift. -/
def kernelActionScore_legacy
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (h : FullHist A O)
    (pstar : EncodedProgram A O) (a : A) : Float :=
  cappedBhatOmega_legacy ω pstar q a h

/--
Concrete Gibbs weight on a target-action pair: the class reference mass times the action
reference mass, tilted by the capped class-action score.
-/
def kernelGibbsWeightOnTargets_legacy
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O)
    (targets : List (EncodedProgram A O))
    (refLaw : ActionLaw A)
    (h : FullHist A O)
    (pstar : EncodedProgram A O) (a : A) : Float :=
  ratToFloat (kernelReferenceWeightOnTargets ω targets refLaw pstar a) *
    Float.exp (kernelActionScore_legacy ω q h pstar a)

/-- Concrete expected class-action score under a joint kernel law. -/
def expectedKernelActionScore_legacy
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (κ : KernelLaw A O) (h : FullHist A O) : Float :=
  listWeightedSumFloat κ.support
    (fun ca => ratToFloat (κ.mass ca) * kernelActionScore_legacy ω q h ca.1 ca.2)

/--
Concrete KL regularizer of the class-action kernel against the product of the target-class
reference mass and the reference action law `λ`.
-/
def kernelLawRegularizer_legacy
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (κ : KernelLaw A O)
    (refLaw : ActionLaw A) : Float :=
  listWeightedSumFloat κ.support
    (fun ca => concreteKLDivergenceTerm_legacy
      (κ.mass ca) (kernelReferenceWeightOnTargets ω targets refLaw ca.1 ca.2))

/--
Concrete raw two-observer functional: the belief term together with the action-side class
score for a single target class.
-/
def rawTwoObserverFunctional_legacy
    (ωB ωA : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (π : ActionLaw A)
    (h : FullHist A O) (pstar : EncodedProgram A O) : Float :=
  let _ := ωB
  beliefFunctional_legacy q π h - classActionScore_legacy ωA q π h pstar

/--
Concrete two-observer variational functional: belief term, minus the expected class score
under `ν`, plus the class-law regularizer against the finite-list code-prior reference.
-/
def twoObserverFunctional_legacy
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Float :=
  let _ := ωB
  beliefFunctional_legacy q π h -
    expectedClassActionScore_legacy ωA q ν π h +
    classLawRegularizer_legacy ωA ν

/-- Rational `L^1`-distance between two concrete local action laws. -/
def lawL1 (κ refLaw : ActionLaw A) [DecidableEq A] [BEq A] [LawfulBEq A] : Rat :=
  listWeightedSum ((κ.support ++ refLaw.support).eraseDups)
    (fun a => Rat.abs (κ.mass a - refLaw.mass a))

/--
Concrete kernel lift of the two-observer functional. The regularizer is the rational
joint KL term against the product of the class reference mass and the action reference
law, and the belief term is evaluated at the action marginal induced by the kernel.
-/
def kernelFunctional_legacy
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (ωB ωA : Observer (EncodedProgram A O))
    (q : ProgramLaw A O)
    (κ : KernelLaw A O)
    (targets : List (EncodedProgram A O))
    (refLaw : ActionLaw A) (h : FullHist A O) : Float :=
  let _ := ωB
  beliefFunctional_legacy q (kernelActionMarginal κ) h -
    expectedKernelActionScore_legacy ωA q κ h +
    kernelLawRegularizer_legacy ωA targets κ refLaw

/-- Concrete meeting-point shorthand bundling the three local functionals. -/
def meetingPointShorthand_legacy
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O)
    (targets : List (EncodedProgram A O))
    (κ : KernelLaw A O)
    (refLaw : ActionLaw A) (h : FullHist A O) :
    (EncodedProgram A O → Float) × Float × Float :=
  (fun pstar => rawTwoObserverFunctional_legacy ωB ωA q (kernelActionMarginal κ) h pstar,
   twoObserverFunctional_legacy ωB ωA q ν (kernelActionMarginal κ) h,
   kernelFunctional_legacy ωB ωA q κ targets refLaw h)

/-- Exact conversion of a rational into a real. -/
def ratToReal (q : Rat) : Real :=
  q

/-- Clamp a rational to the nonnegative reals. This agrees with the exact value on probabilistic laws. -/
def ratToNonnegReal (q : Rat) : Real :=
  max 0 (q : Real)

/-- Finite-support sum of `Real` weights over a list. -/
def listWeightedSumReal {α : Type u} (xs : List α) (f : α → Real) : Real :=
  xs.foldr (fun x acc => f x + acc) (0 : Real)

/-- Exact finite-support sum of `Real` weights over a nodup list agrees with the `Finset` sum. -/
theorem listWeightedSumReal_eq_finset_sum
    {α : Type u} [DecidableEq α]
    (xs : List α) (hxs : xs.Nodup) (f : α → Real) :
    listWeightedSumReal xs f = ∑ x ∈ xs.toFinset, f x := by
  induction xs with
  | nil =>
      simp [listWeightedSumReal]
  | cons x xs ih =>
      rcases List.nodup_cons.mp hxs with ⟨hx, hxs'⟩
      rw [List.toFinset_cons, Finset.sum_insert]
      · simp only [listWeightedSumReal, List.foldr]
        simpa [listWeightedSumReal] using ih hxs'
      · simpa using hx

/-- Exact Bhattacharyya affinity on finitely supported laws, evaluated in `Real`. -/
def bhatAffinityReal (μ ν : ConcreteLaw O) : Real :=
  listWeightedSumReal (supportUnion μ ν) (fun o =>
    Real.sqrt (ratToNonnegReal (μ.mass o * ν.mass o)))

/-- Exact Bhattacharyya separation on finitely supported laws, evaluated in `Real`. -/
def bhatSeparationReal (μ ν : ConcreteLaw O) : Real :=
  let aff := bhatAffinityReal μ ν
  if aff ≤ 0 then 0 else -Real.log aff

/-- Exact observer-indexed Bhattacharyya separation for a target program. -/
def bhatOmega
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (q : ProgramLaw A O) (a : A) (h : FullHist A O) : Real :=
  bhatSeparationReal
    (fiberObsMixture q (observerFiber ω pstar) h a)
    (complementObsMixture q (observerFiber ω pstar) h a)

/-- Exact expectation of a `Real`-valued score under a concrete action law. -/
def actionExpectationReal (π : ActionLaw A) (f : A → Real) : Real :=
  listWeightedSumReal π.support (fun a => (π.mass a : Real) * f a)

/--
When a concrete action law has PMF mass and a nodup support list, the exact finite-support
expectation agrees with the corresponding PMF expectation over that support.
-/
theorem actionExpectationReal_eq_support_sum_toPMF
    [DecidableEq A] (π : ActionLaw A)
    (hπ : π.HasPMFMass)
    (f : A → Real)
    (hNodup : π.support.Nodup) :
    actionExpectationReal π f =
      ((π.support.toFinset).sum fun a => (π.toPMF hπ a).toReal * f a) := by
  unfold actionExpectationReal listWeightedSumReal
  let g : A → Real := fun a => (π.toPMF hπ a).toReal * f a
  have hmass_eq : ∀ a, ((π.mass a : Real) * f a) = g a := by
    intro a
    have hnonneg : 0 ≤ π.mass a := hπ.1 a
    simp [g, ConcreteLaw.toPMF_apply, ConcreteLaw.toENNRealMass, hnonneg]
  have hsum :
      ∀ l : List A, l.Nodup →
        List.foldr (fun x acc => ((π.mass x : Real) * f x) + acc) 0 l =
          ∑ a ∈ l.toFinset, g a := by
    intro l
    induction l with
    | nil =>
        intro _
        simp [g]
    | cons a xs ih =>
        intro hNodup
        rcases List.nodup_cons.mp hNodup with ⟨hnot, hxs⟩
        rw [List.toFinset_cons, Finset.sum_insert]
        · simp only [List.foldr]
          rw [ih hxs, hmass_eq a]
        · simpa using hnot
  simpa [g] using hsum π.support hNodup

/-- Exact one-step predictive codelength of a finitely supported observation law. -/
def observationCodelength (μ : ConcreteLaw O) : Real :=
  listWeightedSumReal μ.support (fun o =>
    let m := μ.mass o
    (m : Real) * (if m ≤ 0 then 0 else -Real.log (m : Real)))

/-- Exact local predictive codelength term used by the concrete belief functional. -/
def historyCodelength
    (π : ActionLaw A) (h : FullHist A O) (p : EncodedProgram A O) : Real :=
  actionExpectationReal π (fun a => observationCodelength (programObsLaw h a p))

/--
Exact finite-support generalized KL term. On admissible laws, the `r = 0` branch is unreachable;
it is kept only to make the definition total over arbitrary concrete laws.
-/
def concreteKLDivergenceTerm (q r : Rat) : Real :=
  if q = 0 then 0
  else if r = 0 then 0
  else (q : Real) * Real.log ((q / r : Rat) : Real)

/-- Concrete code prior weights are strictly positive. -/
theorem encodedProgramPriorWeight_pos (p : EncodedProgram A O) :
    0 < encodedProgramPriorWeight p := by
  unfold encodedProgramPriorWeight
  simpa [codeWeight, Rat.divInt] using
    (Rat.mkRat_pos (show (0 : Int) < 1 by decide) (pow2_ne_zero p.code.length))

/--
On nonnegative weights and a strictly positive reference mass, the exact concrete KL term is the
finite-support specialization of the countable `ENNReal` KL contribution.
-/
theorem concreteKLDivergenceTerm_eq_exactKL_of_positiveRef
    {q r : Rat} (hq : 0 ≤ q) (hr : 0 < r) :
    concreteKLDivergenceTerm q r =
      if hq0 : ENNReal.ofReal (q : Real) = 0 then
        0
      else
        (ENNReal.ofReal (q : Real)).toReal *
          Real.log (((ENNReal.ofReal (q : Real)) / ENNReal.ofReal (r : Real)).toReal) := by
  by_cases hq0 : q = 0
  · have hqENN0 : ENNReal.ofReal (q : Real) = 0 := by simp [hq0]
    simp [concreteKLDivergenceTerm, hq0, hqENN0]
  · have hqPos : 0 < q := by
      have hqne : (0 : Rat) ≠ q := by
        intro hZero
        apply hq0
        simpa using hZero.symm
      exact lt_of_le_of_ne hq hqne
    have hqENN0 : ENNReal.ofReal (q : Real) ≠ 0 := by
      have hqRealPos : 0 < (q : Real) := by
        exact_mod_cast hqPos
      exact ne_of_gt (by simpa using (ENNReal.ofReal_pos.mpr hqRealPos))
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hqReal : (ENNReal.ofReal (q : Real)).toReal = q := by
      simp [ENNReal.toReal_ofReal, hq]
    have hrReal : (ENNReal.ofReal (r : Real)).toReal = r := by
      simp [ENNReal.toReal_ofReal, le_of_lt hr]
    have hdivReal :
        (((ENNReal.ofReal (q : Real)) / ENNReal.ofReal (r : Real)).toReal) =
          ((q / r : Rat) : Real) := by
      simpa [hq, le_of_lt hr, Rat.cast_div] using
        (ENNReal.toReal_div (ENNReal.ofReal (q : Real)) (ENNReal.ofReal (r : Real)))
    simp [concreteKLDivergenceTerm, hq0, hr0, hqENN0, hqReal, hdivReal, hqPos.ne']

/-- Exact belief-side regularizer against the code-length prior. -/
def beliefRegularizer
    (q : ProgramLaw A O) : Real :=
  listWeightedSumReal q.support
    (fun p => concreteKLDivergenceTerm (q.mass p) (encodedProgramPriorWeight p))

/--
The exact concrete belief regularizer is the finite-support `toPMF` realization of the same
pointwise KL contribution used by the countable belief functional.
-/
theorem beliefRegularizer_eq_support_sum_toPMF
    [DecidableEq (EncodedProgram A O)]
    (q : ProgramLaw A O)
    (hq : q.HasPMFMass)
    (hNodup : q.support.Nodup) :
    beliefRegularizer q =
      ∑ p ∈ q.support.toFinset,
        if hp : q.toPMF hq p = 0 then
          0
        else
          (q.toPMF hq p).toReal *
            Real.log (((q.toPMF hq p) /
              ENNReal.ofReal (encodedProgramPriorWeight p : Real)).toReal) := by
  unfold beliefRegularizer
  rw [listWeightedSumReal_eq_finset_sum q.support hNodup]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hMassNonneg : 0 ≤ q.mass p := hq.1 p
  have hRefPos : 0 < encodedProgramPriorWeight p := encodedProgramPriorWeight_pos p
  simpa [ConcreteLaw.toPMF_apply, ConcreteLaw.toENNRealMass]
    using concreteKLDivergenceTerm_eq_exactKL_of_positiveRef hMassNonneg hRefPos

/--
Exact finite-support realization of the belief term:
expected history-fit loss plus prior KL regularization.
-/
def beliefFunctional
    (q : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Real :=
  listWeightedSumReal q.support
      (fun p => (q.mass p : Real) * historyCodelength π h p) +
    beliefRegularizer q

/-- Exact capped Bhattacharyya score entering the concrete action-side variational term. -/
def cappedBhatOmega
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (q : ProgramLaw A O) (a : A) (h : FullHist A O) : Real :=
  min (bhatOmega ω pstar q a h) 1

/-- Exact concrete action-side class score induced by the realized local action law. -/
def classActionScore
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (π : ActionLaw A)
    (h : FullHist A O) (pstar : EncodedProgram A O) : Real :=
  actionExpectationReal π (fun a => cappedBhatOmega ω pstar q a h)

/--
Exact finite-support class-law regularizer against the finite-list class reference mass induced by
code weights.
-/
def classLawRegularizer
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (ν : ProgramLaw A O) : Real :=
  listWeightedSumReal ν.support
    (fun p => concreteKLDivergenceTerm
      (ν.mass p) (classReferenceWeightOnTargets ω targets p))

/--
On finite-support class laws whose support lies in the positive class-reference region, the exact
concrete class regularizer is the finite-support realization of the countable class-side KL term.
-/
theorem classLawRegularizer_eq_support_sum_toPMF
    [DecidableEq (EncodedProgram A O)]
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (ν : ProgramLaw A O)
    (hν : ν.HasPMFMass)
    (hNodup : ν.support.Nodup)
    (href : ∀ p, p ∈ ν.support → 0 < classReferenceWeightOnTargets ω targets p) :
    classLawRegularizer ω targets ν =
      ∑ p ∈ ν.support.toFinset,
        if hp : ν.toPMF hν p = 0 then
          0
        else
          (ν.toPMF hν p).toReal *
            Real.log (((ν.toPMF hν p) /
              ENNReal.ofReal (classReferenceWeightOnTargets ω targets p : Real)).toReal) := by
  unfold classLawRegularizer
  rw [listWeightedSumReal_eq_finset_sum ν.support hNodup]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hMassNonneg : 0 ≤ ν.mass p := hν.1 p
  have hRefPos : 0 < classReferenceWeightOnTargets ω targets p :=
    href p (by simpa using hp)
  simpa [ConcreteLaw.toPMF_apply, ConcreteLaw.toENNRealMass]
    using concreteKLDivergenceTerm_eq_exactKL_of_positiveRef hMassNonneg hRefPos

/-- Exact expected class score under the current class-targeting law. -/
def expectedClassActionScore
    (ω : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Real :=
  listWeightedSumReal ν.support
    (fun p => (ν.mass p : Real) * classActionScore ω q π h p)

/-- Exact concrete class-action score entering the kernel lift. -/
def kernelActionScore
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (h : FullHist A O)
    (pstar : EncodedProgram A O) (a : A) : Real :=
  cappedBhatOmega ω pstar q a h

/--
Exact Gibbs weight on a target-action pair: the class reference mass times the action reference
mass, tilted by the exact capped class-action score.
-/
def kernelGibbsWeightOnTargets
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O)
    (targets : List (EncodedProgram A O))
    (refLaw : ActionLaw A)
    (h : FullHist A O)
    (pstar : EncodedProgram A O) (a : A) : Real :=
  (kernelReferenceWeightOnTargets ω targets refLaw pstar a : Real) *
    Real.exp (kernelActionScore ω q h pstar a)

/-- Exact expected class-action score under a joint kernel law. -/
def expectedKernelActionScore
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (κ : KernelLaw A O) (h : FullHist A O) : Real :=
  listWeightedSumReal κ.support
    (fun ca => (κ.mass ca : Real) * kernelActionScore ω q h ca.1 ca.2)

/--
Exact finite-support kernel-law regularizer against the product of the target-class reference mass
and the reference action law `λ`.
-/
def kernelLawRegularizer
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (κ : KernelLaw A O)
    (refLaw : ActionLaw A) : Real :=
  listWeightedSumReal κ.support
    (fun ca => concreteKLDivergenceTerm
      (κ.mass ca) (kernelReferenceWeightOnTargets ω targets refLaw ca.1 ca.2))

/--
On finite-support kernels whose support lies in the positive joint reference region, the exact
concrete kernel regularizer is the finite-support realization of the countable kernel-side KL term.
-/
theorem kernelLawRegularizer_eq_support_sum_toPMF
    [DecidableEq (EncodedProgram A O)] [DecidableEq A]
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (κ : KernelLaw A O)
    (refLaw : ActionLaw A)
    (hκ : κ.HasPMFMass)
    (hNodup : κ.support.Nodup)
    (href : ∀ ca, ca ∈ κ.support →
      0 < kernelReferenceWeightOnTargets ω targets refLaw ca.1 ca.2) :
    kernelLawRegularizer ω targets κ refLaw =
      ∑ ca ∈ κ.support.toFinset,
        if hca : κ.toPMF hκ ca = 0 then
          0
        else
          (κ.toPMF hκ ca).toReal *
            Real.log (((κ.toPMF hκ ca) /
              ENNReal.ofReal (kernelReferenceWeightOnTargets ω targets refLaw ca.1 ca.2 : Real)).toReal) := by
  unfold kernelLawRegularizer
  rw [listWeightedSumReal_eq_finset_sum κ.support hNodup]
  refine Finset.sum_congr rfl ?_
  intro ca hca
  have hMassNonneg : 0 ≤ κ.mass ca := hκ.1 ca
  have hRefPos : 0 < kernelReferenceWeightOnTargets ω targets refLaw ca.1 ca.2 :=
    href ca (by simpa using hca)
  simpa [ConcreteLaw.toPMF_apply, ConcreteLaw.toENNRealMass]
    using concreteKLDivergenceTerm_eq_exactKL_of_positiveRef hMassNonneg hRefPos

/--
Exact concrete raw two-observer functional:
the belief term together with the action-side class score for a single target class.
-/
def rawTwoObserverFunctional
    (ωB ωA : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (π : ActionLaw A)
    (h : FullHist A O) (pstar : EncodedProgram A O) : Real :=
  let _ := ωB
  beliefFunctional q π h - classActionScore ωA q π h pstar

/--
Exact concrete two-observer variational functional:
belief term, minus the expected class score under `ν`, plus the class-law regularizer against the
finite-list code-prior reference.
-/
def twoObserverFunctional
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O)
    (targets : List (EncodedProgram A O))
    (π : ActionLaw A) (h : FullHist A O) : Real :=
  let _ := ωB
  beliefFunctional q π h -
    expectedClassActionScore ωA q ν π h +
    classLawRegularizer ωA targets ν

/--
Exact concrete kernel lift of the two-observer functional. The regularizer is the exact joint
KL term against the product of the class reference mass and the action reference law, and the
belief term is evaluated at the action marginal induced by the kernel.
-/
def kernelFunctional
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (ωB ωA : Observer (EncodedProgram A O))
    (q : ProgramLaw A O)
    (κ : KernelLaw A O)
    (targets : List (EncodedProgram A O))
    (refLaw : ActionLaw A) (h : FullHist A O) : Real :=
  let _ := ωB
  beliefFunctional q (kernelActionMarginal κ) h -
    expectedKernelActionScore ωA q κ h +
    kernelLawRegularizer ωA targets κ refLaw

/-- Exact concrete meeting-point shorthand bundling the three local functionals. -/
def meetingPointShorthand
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O)
    (targets : List (EncodedProgram A O))
    (κ : KernelLaw A O)
    (refLaw : ActionLaw A) (h : FullHist A O) :
    (EncodedProgram A O → Real) × Real × Real :=
  (fun pstar => rawTwoObserverFunctional ωB ωA q (kernelActionMarginal κ) h pstar,
   twoObserverFunctional ωB ωA q ν targets (kernelActionMarginal κ) h,
   kernelFunctional ωB ωA q κ targets refLaw h)

theorem lawL1_self
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (κ : ActionLaw A) :
    lawL1 κ κ = 0 := by
  have hzero : ∀ a, Rat.abs (κ.mass a - κ.mass a) = 0 := by
    intro a
    rw [Rat.sub_self, Rat.abs_zero]
  have hsum :
      listWeightedSum ((κ.support ++ κ.support).eraseDups)
        (fun a => Rat.abs (κ.mass a - κ.mass a)) = 0 := by
    induction ((κ.support ++ κ.support).eraseDups) with
    | nil =>
        simp [listWeightedSum]
    | cons a xs ih =>
        rw [listWeightedSum_cons, hzero a, ih]
        exact Rat.zero_add 0
  simpa [lawL1] using hsum

end ConcreteFunctionals

section FiniteArgmin

variable {α : Type u}

/-- Witness that `x` is a minimizer of `f` on the finite list `xs`. -/
def MinimizesOnList (xs : List α) (f : α → Rat) (x : α) : Prop :=
  x ∈ xs ∧ ∀ y, y ∈ xs → f x ≤ f y

theorem exists_minimizerOnList (xs : List α) (f : α → Rat) (hxs : xs ≠ []) :
    ∃ x, MinimizesOnList xs f x := by
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
          exact Rat.le_refl
      · rcases ih htail with ⟨m, hm_mem, hm_min⟩
        by_cases hxm : f x ≤ f m
        · refine ⟨x, ?_⟩
          constructor
          · simp
          · intro y hy
            simp at hy
            rcases hy with rfl | hy
            · exact Rat.le_refl
            · exact Rat.le_trans hxm (hm_min y hy)
        · have hmx : f m ≤ f x := by
            have htot : f m ≤ f x ∨ f x ≤ f m := Rat.le_total
            rcases htot with h | h
            · exact h
            · exfalso
              exact hxm h
          refine ⟨m, ?_⟩
          constructor
          · simp [hm_mem]
          · intro y hy
            simp at hy
            rcases hy with rfl | hy
            · exact hmx
            · exact hm_min y hy

/-- A chosen minimizer on a nonempty finite list. -/
noncomputable def argminOnList (xs : List α) (f : α → Rat) (hxs : xs ≠ []) : α :=
  Classical.choose (exists_minimizerOnList xs f hxs)

theorem argminOnList_spec (xs : List α) (f : α → Rat) (hxs : xs ≠ []) :
    MinimizesOnList xs f (argminOnList xs f hxs) :=
  Classical.choose_spec (exists_minimizerOnList xs f hxs)

end FiniteArgmin

end

end SemanticConvergence
