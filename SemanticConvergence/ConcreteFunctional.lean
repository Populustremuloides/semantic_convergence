import SemanticConvergence.ConcreteHierarchy

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
def bhatOmega
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
def observationCodelength (μ : ConcreteLaw O) : Float :=
  listWeightedSumFloat μ.support (fun o =>
    let m := μ.mass o
    ratToFloat m * (if m ≤ 0 then 0 else Float.neg (Float.log (ratToNonnegFloat m))))

/-- Local predictive codelength term used by the concrete belief functional. -/
def historyCodelength
    (π : ActionLaw A) (h : FullHist A O) (p : EncodedProgram A O) : Float :=
  actionExpectation π (fun a => observationCodelength (programObsLaw h a p))

/-- Concrete code-length prior weight attached to a single encoded program. -/
def encodedProgramPriorWeight (p : EncodedProgram A O) : Rat :=
  codeWeight p.code

/--
Concrete generalized-KL proxy between two nonnegative rational weights. The paper-facing
layer only needs the variational shape here, so the impossible `r = 0 < q` branch is
recorded as a large positive penalty rather than an actual infinity.
-/
def concreteKLDivergenceTerm (q r : Rat) : Float :=
  if q = 0 then 0
  else if r = 0 then ratToFloat q * 1000000
  else ratToFloat q * Float.log (ratToNonnegFloat (q / r))

/-- Belief-side regularizer against the code-length prior. -/
def beliefRegularizer
    (q : ProgramLaw A O) : Float :=
  listWeightedSumFloat q.support
    (fun p => concreteKLDivergenceTerm (q.mass p) (encodedProgramPriorWeight p))

/--
Concrete belief term of the two-observer variational functional: expected codelength plus
the code-prior KL proxy.
-/
def beliefFunctional
    (q : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Float :=
  listWeightedSumFloat q.support
      (fun p => ratToFloat (q.mass p) * historyCodelength π h p) +
    beliefRegularizer q

/-- Capped Bhattacharyya score entering the concrete action-side variational term. -/
def cappedBhatOmega
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (q : ProgramLaw A O) (a : A) (h : FullHist A O) : Float :=
  let s := bhatOmega ω pstar q a h
  if s ≤ 1 then s else 1

/-- Concrete action-side class score induced by the realized local action law. -/
def classActionScore
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (π : ActionLaw A)
    (h : FullHist A O) (pstar : EncodedProgram A O) : Float :=
  actionExpectation π (fun a => cappedBhatOmega ω pstar q a h)

/-- Finite-list reference mass on a concrete observer class, induced by code weights. -/
def classReferenceWeightOnTargets
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat :=
  listWeightedSum targets
    (fun p => if ω.view p = ω.view pstar then encodedProgramPriorWeight p else 0)

/-- Concrete KL regularizer of the class law against the finite-list class reference mass. -/
def classLawRegularizer
    (ω : Observer (EncodedProgram A O))
    (ν : ProgramLaw A O) : Float :=
  listWeightedSumFloat ν.support
    (fun p => concreteKLDivergenceTerm
      (ν.mass p) (classReferenceWeightOnTargets ω ν.support p))

/-- Concrete expected class score under the current class-targeting law. -/
def expectedClassActionScore
    (ω : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Float :=
  listWeightedSumFloat ν.support
    (fun p => ratToFloat (ν.mass p) * classActionScore ω q π h p)

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
def kernelActionScore
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (h : FullHist A O)
    (pstar : EncodedProgram A O) (a : A) : Float :=
  cappedBhatOmega ω pstar q a h

/--
Concrete Gibbs weight on a target-action pair: the class reference mass times the action
reference mass, tilted by the capped class-action score.
-/
def kernelGibbsWeightOnTargets
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O)
    (targets : List (EncodedProgram A O))
    (refLaw : ActionLaw A)
    (h : FullHist A O)
    (pstar : EncodedProgram A O) (a : A) : Float :=
  ratToFloat (kernelReferenceWeightOnTargets ω targets refLaw pstar a) *
    Float.exp (kernelActionScore ω q h pstar a)

/-- Concrete expected class-action score under a joint kernel law. -/
def expectedKernelActionScore
    (ω : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (κ : KernelLaw A O) (h : FullHist A O) : Float :=
  listWeightedSumFloat κ.support
    (fun ca => ratToFloat (κ.mass ca) * kernelActionScore ω q h ca.1 ca.2)

/--
Concrete KL regularizer of the class-action kernel against the product of the target-class
reference mass and the reference action law `λ`.
-/
def kernelLawRegularizer
    (ω : Observer (EncodedProgram A O))
    (targets : List (EncodedProgram A O))
    (κ : KernelLaw A O)
    (refLaw : ActionLaw A) : Float :=
  listWeightedSumFloat κ.support
    (fun ca => concreteKLDivergenceTerm
      (κ.mass ca) (kernelReferenceWeightOnTargets ω targets refLaw ca.1 ca.2))

/--
Concrete raw two-observer functional: the belief term together with the action-side class
score for a single target class.
-/
def rawTwoObserverFunctional
    (ωB ωA : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (π : ActionLaw A)
    (h : FullHist A O) (pstar : EncodedProgram A O) : Float :=
  let _ := ωB
  beliefFunctional q π h - classActionScore ωA q π h pstar

/--
Concrete two-observer variational functional: belief term, minus the expected class score
under `ν`, plus the class-law regularizer against the finite-list code-prior reference.
-/
def twoObserverFunctional
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Float :=
  let _ := ωB
  beliefFunctional q π h -
    expectedClassActionScore ωA q ν π h +
    classLawRegularizer ωA ν

/-- Rational `L^1`-distance between two concrete local action laws. -/
def lawL1 (κ refLaw : ActionLaw A) [DecidableEq A] [BEq A] [LawfulBEq A] : Rat :=
  listWeightedSum ((κ.support ++ refLaw.support).eraseDups)
    (fun a => Rat.abs (κ.mass a - refLaw.mass a))

/--
Concrete kernel lift of the two-observer functional. The regularizer is the rational
joint KL term against the product of the class reference mass and the action reference
law, and the belief term is evaluated at the action marginal induced by the kernel.
-/
def kernelFunctional
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (ωB ωA : Observer (EncodedProgram A O))
    (q : ProgramLaw A O)
    (κ : KernelLaw A O)
    (targets : List (EncodedProgram A O))
    (refLaw : ActionLaw A) (h : FullHist A O) : Float :=
  let _ := ωB
  beliefFunctional q (kernelActionMarginal κ) h -
    expectedKernelActionScore ωA q κ h +
    kernelLawRegularizer ωA targets κ refLaw

/-- Concrete meeting-point shorthand bundling the three local functionals. -/
def meetingPointShorthand
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O)
    (targets : List (EncodedProgram A O))
    (κ : KernelLaw A O)
    (refLaw : ActionLaw A) (h : FullHist A O) :
    (EncodedProgram A O → Float) × Float × Float :=
  (fun pstar => rawTwoObserverFunctional ωB ωA q (kernelActionMarginal κ) h pstar,
   twoObserverFunctional ωB ωA q ν (kernelActionMarginal κ) h,
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
