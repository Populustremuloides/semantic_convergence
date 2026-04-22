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

/--
Concrete raw two-observer functional: belief-fiber mass under `ω_B` times the actionwise
Bhattacharyya gain evaluated at `ω_A`.
-/
def rawTwoObserverFunctional
    (ωB ωA : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (π : ActionLaw A)
    (h : FullHist A O) (pstar : EncodedProgram A O) : Float :=
  ratToFloat (observerFiberMass ωB q pstar) *
    actionExpectation π (fun a => bhatOmega ωA pstar q a h)

/--
Concrete two-observer functional obtained by averaging the raw target-program functional
against a finitely supported representative law on programs.
-/
def twoObserverFunctional
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Float :=
  listWeightedSumFloat ν.support (fun p =>
    ratToFloat (ν.mass p) * rawTwoObserverFunctional ωB ωA q π h p)

/-- Rational `L^1`-distance between two concrete local action laws. -/
def lawL1 (κ refLaw : ActionLaw A) [DecidableEq A] [BEq A] [LawfulBEq A] : Rat :=
  listWeightedSum ((κ.support ++ refLaw.support).eraseDups)
    (fun a => Rat.abs (κ.mass a - refLaw.mass a))

/--
Concrete kernel lift of the two-observer functional. The regularizer is the rational
`L^1` deviation from the reference action law.
-/
def kernelFunctional
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O)
    (κ refLaw : ActionLaw A) (h : FullHist A O) : Float :=
  twoObserverFunctional ωB ωA q ν κ h + ratToFloat (lawL1 κ refLaw)

/-- Concrete meeting-point shorthand bundling the three local functionals. -/
def meetingPointShorthand
    [DecidableEq A] [BEq A] [LawfulBEq A]
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O)
    (κ refLaw : ActionLaw A) (h : FullHist A O) :
    (EncodedProgram A O → Float) × Float × Float :=
  (fun pstar => rawTwoObserverFunctional ωB ωA q κ h pstar,
   twoObserverFunctional ωB ωA q ν κ h,
   kernelFunctional ωB ωA q ν κ refLaw h)

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
