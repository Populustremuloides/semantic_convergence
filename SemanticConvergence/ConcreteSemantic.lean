import SemanticConvergence.ConcreteBelief

namespace SemanticConvergence

universe u v

open Classical

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

namespace ConcreteLaw

variable {α : Type u}

/-- A finite reference law with strictly positive unit mass on a designated finite support. -/
def positiveReferenceLaw [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) : ConcreteLaw α where
  mass a := if a ∈ xs then 1 else 0
  support := xs.eraseDups
  support_complete := by
    intro a ha
    have hmem : a ∈ xs := by
      by_cases hx : a ∈ xs
      · exact hx
      · simp [hx] at ha
    exact (List.mem_eraseDups).2 hmem

/-- Pointwise positivity on an explicit finite list. -/
def strictlyPositiveOn (μ : ConcreteLaw α) (xs : List α) : Prop :=
  ∀ a, a ∈ xs → 0 < μ.mass a

/-- Pointwise nonnegativity on an explicit finite list. -/
def nonnegativeOn (μ : ConcreteLaw α) (xs : List α) : Prop :=
  ∀ a, a ∈ xs → 0 ≤ μ.mass a

/--
Additive positive-support smoothing of a finitely supported law by a reference law.

This does not normalize the result; it is a support-engineering device for the later
positive-support posterior-decay substrate.
-/
def soften [DecidableEq α] [BEq α] [LawfulBEq α]
    (μ ref : ConcreteLaw α) (ε : Rat) : ConcreteLaw α where
  mass a := μ.mass a + ε * ref.mass a
  support := (μ.support ++ ref.support).eraseDups
  support_complete := by
    intro a ha
    by_cases hμ : μ.mass a = 0
    · have href : ref.mass a ≠ 0 := by
        intro href0
        have hsoft : μ.mass a + ε * ref.mass a ≠ 0 := ha
        simp [hμ, href0] at hsoft
      have hmemRef : a ∈ ref.support := ref.support_complete a href
      exact (List.mem_eraseDups).2 <| List.mem_append_right _ hmemRef
    · have hmemμ : a ∈ μ.support := μ.support_complete a hμ
      exact (List.mem_eraseDups).2 <| List.mem_append_left _ hmemμ

theorem positiveReferenceLaw_strictlyPositiveOn
    [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) :
    strictlyPositiveOn (positiveReferenceLaw xs) xs := by
  intro a ha
  simp [positiveReferenceLaw, ha]

theorem positiveReferenceLaw_nonnegativeOn
    [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) :
    nonnegativeOn (positiveReferenceLaw xs) xs := by
  intro a ha
  have hpos := positiveReferenceLaw_strictlyPositiveOn (xs := xs) a ha
  exact le_of_lt hpos

theorem positiveReferenceLaw_mass_pos_of_mem
    [DecidableEq α] [BEq α] [LawfulBEq α]
    {xs : List α} {a : α} (ha : a ∈ xs) :
    0 < (positiveReferenceLaw xs).mass a := by
  simp [positiveReferenceLaw, ha]

theorem soften_mass_pos_of_nonneg_of_ref_pos
    [DecidableEq α] [BEq α] [LawfulBEq α]
    {μ ref : ConcreteLaw α} {ε : Rat} {a : α}
    (hμ : 0 ≤ μ.mass a)
    (hε : 0 < ε)
    (href : 0 < ref.mass a) :
    0 < (soften μ ref ε).mass a := by
  have hmul : 0 < ε * ref.mass a := mul_pos hε href
  have hsum : 0 < μ.mass a + ε * ref.mass a := by
    linarith
  simpa [soften] using hsum

theorem soften_mass_eq_of_zero_of_zero
    [DecidableEq α] [BEq α] [LawfulBEq α]
    {μ ref : ConcreteLaw α} {ε : Rat} {a : α}
    (hμ : μ.mass a = 0) (href : ref.mass a = 0) :
    (soften μ ref ε).mass a = 0 := by
  simp [soften, hμ, href]

end ConcreteLaw

/-- Posterior mass assigned to the complement of a machine-domain class. -/
def complementPosteriorMass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] : Rat := by
  classical
  exact ConcreteLaw.classMass (U.posteriorLaw π h) (fun p => ¬ C p)

/--
Posterior odds of a machine-domain class against its complement. If the complement has
zero posterior mass, this returns `0`.
-/
def classPosteriorOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] : Rat :=
  let mC := U.posteriorClassMass π h C
  let mComp := U.complementPosteriorMass π h C
  if _ : mComp = 0 then 0 else mC / mComp

/-- Posterior odds attached to an observer fiber through an encoded target program. -/
def observerFiberPosteriorOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat := by
  classical
  exact U.classPosteriorOdds π h (U.observerFiber ω pstar)

/-- Concrete observer-fiber predictive pair viewed as a class-vs-complement object. -/
def observerFiberClassComplement (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : ConcreteLaw O × ConcreteLaw O :=
  U.observerFiberComplementLaw π h a ω pstar

/--
Positive-support class-side predictive law obtained by additive smoothing against a
reference observation law.
-/
def softPredictiveLawInClass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) : ConcreteLaw O :=
  ConcreteLaw.soften (U.predictiveLawInClass π h a C) refLaw ε

/--
Positive-support complement-side predictive law obtained by additive smoothing against a
reference observation law.
-/
def softPredictiveLawOutsideClass (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) : ConcreteLaw O :=
  ConcreteLaw.soften (U.predictiveLawOutsideClass π h a C) refLaw ε

/-- Smoothed class-vs-complement predictive pair at a history-action pair. -/
def softClassComplementLaw (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) (ε : Rat) : ConcreteLaw O × ConcreteLaw O :=
  (U.softPredictiveLawInClass π h a C refLaw ε,
   U.softPredictiveLawOutsideClass π h a C refLaw ε)

/-- Smoothed observer-fiber predictive pair at a history-action pair. -/
def softObserverFiberClassComplement (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ConcreteLaw O) (ε : Rat) : ConcreteLaw O × ConcreteLaw O := by
  classical
  exact U.softClassComplementLaw π h a (U.observerFiber ω pstar) refLaw ε

/-- Concrete semantic separation at a history-action pair for an observer fiber. -/
def semanticSeparation (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  let pair := U.observerFiberClassComplement π h a ω pstar
  bhatSeparation pair.1 pair.2

/--
Concrete semantic gain: observer-fiber posterior mass times the concrete semantic
separation at the chosen history-action pair.
-/
def semanticGain (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  ratToFloat (U.observerFiberPosteriorMass π h ω pstar) *
    U.semanticSeparation π h a ω pstar

/-- An action is semantically separating when its concrete separation is positive. -/
def isSeparatingAction (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) (a : A) : Prop :=
  0 < U.semanticSeparation π h a ω pstar

/-- The separating-action set at a fixed history for an observer fiber. -/
def separatingActionSet (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : PredSet A :=
  fun a => U.isSeparatingAction π h ω pstar a

/-- Rational support weight assigned by a local action law to a separating set. -/
def separatingSupportWeight (κ : ActionLaw A) (actions : List A)
    (S : PredSet A) [DecidablePred S] : Rat :=
  listWeightedSum actions (fun a => if S a then κ.mass a else 0)

/-- Concrete lower-bound witness for separating support on a finite action list. -/
def hasSeparatingSupportFloor (κ : ActionLaw A) (actions : List A)
    (S : PredSet A) [DecidablePred S] (δ : Rat) : Prop :=
  δ ≤ separatingSupportWeight κ actions S

/-- Concrete local support on an explicit finite action list. -/
def hasSupportOn (κ : ActionLaw A) (actions : List A) : Prop :=
  ∀ a, a ∈ actions → κ.mass a ≠ 0

/-- Concrete separating support on an explicit finite action list. -/
def hasSeparatingSupportOn (κ : ActionLaw A) (actions : List A)
    (S : PredSet A) : Prop :=
  ∃ a, a ∈ actions ∧ κ.mass a ≠ 0 ∧ S a

/--
Simple full-support local action law on a finite action list. This is not normalized; it
is a support scaffold for later finite-action semantic support constructions.
-/
def fullSupportActionLaw (actions : List A) [DecidableEq A] [BEq A] [LawfulBEq A] :
    ActionLaw A where
  mass a := if a ∈ actions then 1 else 0
  support := actions.eraseDups
  support_complete := by
    intro a ha
    by_cases hmem : a ∈ actions
    · exact (List.mem_eraseDups).2 hmem
    · simp [hmem] at ha

set_option linter.unusedSectionVars false in
theorem fullSupportActionLaw_hasSupportOn
    (actions : List A) [DecidableEq A] [BEq A] [LawfulBEq A] :
    hasSupportOn (fullSupportActionLaw actions) actions := by
  intro a ha
  simp [fullSupportActionLaw, ha]

set_option linter.unusedSectionVars false in
theorem witness_hasSeparatingSupportOn
    (κ : ActionLaw A) (actions : List A) (S : PredSet A)
    {a : A} (ha : a ∈ actions) (hMass : κ.mass a ≠ 0) (hSep : S a) :
    hasSeparatingSupportOn κ actions S :=
  ⟨a, ha, hMass, hSep⟩

set_option linter.unusedSectionVars false in
theorem fullSupport_hasSeparatingSupportOn
    (κ : ActionLaw A) (actions : List A) (S : PredSet A)
    (hFull : hasSupportOn κ actions)
    {a : A} (ha : a ∈ actions) (hSep : S a) :
    hasSeparatingSupportOn κ actions S :=
  ⟨a, ha, hFull a ha, hSep⟩

theorem observerFiberComplementLaw_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberClassComplement π h a ω p =
      U.observerFiberClassComplement π h a ω q := by
  classical
  have hFib : U.observerFiber ω p = U.observerFiber ω q :=
    U.observerFiber_eq_of_sameView ω hView
  simpa [observerFiberClassComplement, observerFiberComplementLaw] using
    congrArg (fun C => U.classComplementLaw π h a C) hFib

theorem softObserverFiberComplementLaw_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (refLaw : ConcreteLaw O) (ε : Rat)
    (hView : ω.view p = ω.view q) :
    U.softObserverFiberClassComplement π h a ω p refLaw ε =
      U.softObserverFiberClassComplement π h a ω q refLaw ε := by
  classical
  have hFib : U.observerFiber ω p = U.observerFiber ω q :=
    U.observerFiber_eq_of_sameView ω hView
  simpa [softObserverFiberClassComplement, softClassComplementLaw,
    softPredictiveLawInClass, softPredictiveLawOutsideClass] using
    congrArg
      (fun C =>
        (ConcreteLaw.soften (U.predictiveLawInClass π h a C) refLaw ε,
         ConcreteLaw.soften (U.predictiveLawOutsideClass π h a C) refLaw ε))
      hFib

theorem observerFiberPosteriorOdds_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberPosteriorOdds π h ω p =
      U.observerFiberPosteriorOdds π h ω q := by
  classical
  have hFib : U.observerFiber ω p = U.observerFiber ω q :=
    U.observerFiber_eq_of_sameView ω hView
  simpa [observerFiberPosteriorOdds] using
    congrArg (fun C => U.classPosteriorOdds π h C) hFib

theorem complementPosteriorMass_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.complementPosteriorMass π h (U.observerFiber ω p) =
      U.complementPosteriorMass π h (U.observerFiber ω q) := by
  classical
  have hFib : U.observerFiber ω p = U.observerFiber ω q :=
    U.observerFiber_eq_of_sameView ω hView
  simpa [complementPosteriorMass] using
    congrArg
      (fun C => ConcreteLaw.classMass (U.posteriorLaw π h) (fun r => ¬ C r))
      hFib

theorem softPredictiveLawInClass_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (refLaw : ConcreteLaw O) (ε : Rat)
    (hView : ω.view p = ω.view q) :
    U.softPredictiveLawInClass π h a (U.observerFiber ω p) refLaw ε =
      U.softPredictiveLawInClass π h a (U.observerFiber ω q) refLaw ε := by
  classical
  have hFib : U.observerFiber ω p = U.observerFiber ω q :=
    U.observerFiber_eq_of_sameView ω hView
  simpa [softPredictiveLawInClass] using
    congrArg
      (fun C => ConcreteLaw.soften (U.predictiveLawInClass π h a C) refLaw ε)
      hFib

theorem softPredictiveLawOutsideClass_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (refLaw : ConcreteLaw O) (ε : Rat)
    (hView : ω.view p = ω.view q) :
    U.softPredictiveLawOutsideClass π h a (U.observerFiber ω p) refLaw ε =
      U.softPredictiveLawOutsideClass π h a (U.observerFiber ω q) refLaw ε := by
  classical
  have hFib : U.observerFiber ω p = U.observerFiber ω q :=
    U.observerFiber_eq_of_sameView ω hView
  simpa [softPredictiveLawOutsideClass] using
    congrArg
      (fun C => ConcreteLaw.soften (U.predictiveLawOutsideClass π h a C) refLaw ε)
      hFib

theorem semanticSeparation_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.semanticSeparation π h a ω p =
      U.semanticSeparation π h a ω q := by
  have hPair := U.observerFiberComplementLaw_eq_of_sameView π h a ω hView
  simpa [semanticSeparation] using congrArg (fun pair => bhatSeparation pair.1 pair.2) hPair

theorem semanticGain_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.semanticGain π h a ω p =
      U.semanticGain π h a ω q := by
  have hMass := U.observerFiberPosteriorMass_eq_of_sameView π h ω hView
  have hSep := U.semanticSeparation_eq_of_sameView π h a ω hView
  simp [semanticGain, hMass, hSep]

theorem softPredictiveLawInClass_mass_pos_of_reference
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) {ε : Rat} {o : O}
    (hInNonneg : 0 ≤ (U.predictiveLawInClass π h a C).mass o)
    (hε : 0 < ε)
    (hRef : 0 < refLaw.mass o) :
    0 < (U.softPredictiveLawInClass π h a C refLaw ε).mass o := by
  exact ConcreteLaw.soften_mass_pos_of_nonneg_of_ref_pos hInNonneg hε hRef

theorem softPredictiveLawOutsideClass_mass_pos_of_reference
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    (refLaw : ConcreteLaw O) {ε : Rat} {o : O}
    (hOutNonneg : 0 ≤ (U.predictiveLawOutsideClass π h a C).mass o)
    (hε : 0 < ε)
    (hRef : 0 < refLaw.mass o) :
    0 < (U.softPredictiveLawOutsideClass π h a C refLaw ε).mass o := by
  exact ConcreteLaw.soften_mass_pos_of_nonneg_of_ref_pos hOutNonneg hε hRef

set_option linter.unusedSectionVars false in
theorem mem_supportUnion_of_left_mass_ne_zero
    {μ ν : ConcreteLaw O} {o : O}
    (hμ : μ.mass o ≠ 0) :
    o ∈ supportUnion μ ν := by
  have hmemμ : o ∈ μ.support := μ.support_complete o hμ
  apply List.mem_eraseDups.2
  exact List.mem_append_left _ hmemμ

set_option linter.unusedSectionVars false in
theorem mem_supportUnion_of_right_mass_ne_zero
    {μ ν : ConcreteLaw O} {o : O}
    (hν : ν.mass o ≠ 0) :
    o ∈ supportUnion μ ν := by
  have hmemν : o ∈ ν.support := ν.support_complete o hν
  apply List.mem_eraseDups.2
  exact List.mem_append_right _ hmemν

theorem positiveReferenceLaw_supportUnion_mass_pos_of_left_mass_ne_zero
    {μ ν : ConcreteLaw O} {o : O}
    (hμ : μ.mass o ≠ 0) :
    0 < (ConcreteLaw.positiveReferenceLaw (supportUnion μ ν)).mass o := by
  exact ConcreteLaw.positiveReferenceLaw_mass_pos_of_mem
    (mem_supportUnion_of_left_mass_ne_zero (μ := μ) (ν := ν) hμ)

theorem positiveReferenceLaw_supportUnion_mass_eq_one_of_left_mass_ne_zero
    {μ ν : ConcreteLaw O} {o : O}
    (hμ : μ.mass o ≠ 0) :
    (ConcreteLaw.positiveReferenceLaw (supportUnion μ ν)).mass o = 1 := by
  have hmem : o ∈ supportUnion μ ν :=
    mem_supportUnion_of_left_mass_ne_zero (μ := μ) (ν := ν) hμ
  simp [ConcreteLaw.positiveReferenceLaw, hmem]

theorem positiveReferenceLaw_supportUnion_mass_pos_of_right_mass_ne_zero
    {μ ν : ConcreteLaw O} {o : O}
    (hν : ν.mass o ≠ 0) :
    0 < (ConcreteLaw.positiveReferenceLaw (supportUnion μ ν)).mass o := by
  exact ConcreteLaw.positiveReferenceLaw_mass_pos_of_mem
    (mem_supportUnion_of_right_mass_ne_zero (μ := μ) (ν := ν) hν)

theorem softPredictiveLawInClass_mass_pos_of_positiveReferenceLaw_supportUnion
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    {ε : Rat} {o : O}
    (hInNonneg : 0 ≤ (U.predictiveLawInClass π h a C).mass o)
    (hIn : (U.predictiveLawInClass π h a C).mass o ≠ 0)
    (hε : 0 < ε) :
    0 <
      (U.softPredictiveLawInClass π h a C
        (ConcreteLaw.positiveReferenceLaw
          (supportUnion (U.predictiveLawInClass π h a C)
            (U.predictiveLawOutsideClass π h a C)))
        ε).mass o := by
  have hRef :
      0 <
        (ConcreteLaw.positiveReferenceLaw
          (supportUnion (U.predictiveLawInClass π h a C)
            (U.predictiveLawOutsideClass π h a C))).mass o :=
    positiveReferenceLaw_supportUnion_mass_pos_of_left_mass_ne_zero
      (μ := U.predictiveLawInClass π h a C)
      (ν := U.predictiveLawOutsideClass π h a C)
      hIn
  exact U.softPredictiveLawInClass_mass_pos_of_reference
    π h a C
    (ConcreteLaw.positiveReferenceLaw
      (supportUnion (U.predictiveLawInClass π h a C)
        (U.predictiveLawOutsideClass π h a C)))
    hInNonneg hε hRef

theorem softPredictiveLawOutsideClass_mass_pos_of_positiveReferenceLaw_supportUnion
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C]
    {ε : Rat} {o : O}
    (hOutNonneg : 0 ≤ (U.predictiveLawOutsideClass π h a C).mass o)
    (hOut : (U.predictiveLawOutsideClass π h a C).mass o ≠ 0)
    (hε : 0 < ε) :
    0 <
      (U.softPredictiveLawOutsideClass π h a C
        (ConcreteLaw.positiveReferenceLaw
          (supportUnion (U.predictiveLawInClass π h a C)
            (U.predictiveLawOutsideClass π h a C)))
        ε).mass o := by
  have hRef :
      0 <
        (ConcreteLaw.positiveReferenceLaw
          (supportUnion (U.predictiveLawInClass π h a C)
            (U.predictiveLawOutsideClass π h a C))).mass o :=
    positiveReferenceLaw_supportUnion_mass_pos_of_right_mass_ne_zero
      (μ := U.predictiveLawInClass π h a C)
      (ν := U.predictiveLawOutsideClass π h a C)
      hOut
  exact U.softPredictiveLawOutsideClass_mass_pos_of_reference
    π h a C
    (ConcreteLaw.positiveReferenceLaw
      (supportUnion (U.predictiveLawInClass π h a C)
        (U.predictiveLawOutsideClass π h a C)))
    hOutNonneg hε hRef

theorem fullSupportActionLaw_hasSeparatingSupportOn
    (U : ConcretePrefixMachine A O)
    (actions : List A)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    {a : A} (ha : a ∈ actions)
    (hSep : U.isSeparatingAction π h ω pstar a) :
    hasSeparatingSupportOn
      (fullSupportActionLaw actions)
      actions
      (U.separatingActionSet π h ω pstar) :=
  fullSupport_hasSeparatingSupportOn
    (κ := fullSupportActionLaw actions)
    (actions := actions)
    (S := U.separatingActionSet π h ω pstar)
    (fullSupportActionLaw_hasSupportOn actions)
    ha hSep

end ConcretePrefixMachine

namespace CountableConcrete

namespace CountablePrefixMachine

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

/--
Countable semantic separation scaffold. At the broadened substrate level this is the
observer-fiber posterior odds; later phases can replace it by the sharper predictive-law
separation once the countable Bayes update stack is fully in place.
-/
def semanticSeparation (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.observerFiberPosteriorOdds π t h ω pstar

/-- Countable semantic gain scaffold: posterior fiber weight times semantic separation. -/
def semanticGain (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    (pstar : CountableEncodedProgram A O) : ENNReal :=
  U.observerFiberPosteriorWeight π t h ω pstar *
    U.semanticSeparation π t h ω pstar

/-- Same-view targets have the same countable semantic separation. -/
theorem semanticSeparation_eq_of_sameView
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.semanticSeparation π t h ω p =
      U.semanticSeparation π t h ω q := by
  simpa [semanticSeparation] using
    U.observerFiberPosteriorOdds_eq_of_sameView π t h ω hView

/-- Same-view targets have the same countable semantic gain. -/
theorem semanticGain_eq_of_sameView
    (U : CountablePrefixMachine A O)
    (π : CountablePolicy A O) (t : Nat) (h : CountHist A O)
    (ω : Observer (CountableEncodedProgram A O))
    {p q : CountableEncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.semanticGain π t h ω p =
      U.semanticGain π t h ω q := by
  have hMass := U.observerFiberPosteriorWeight_eq_of_sameView π t h ω hView
  have hSep := U.semanticSeparation_eq_of_sameView π t h ω hView
  simp [semanticGain, hMass, hSep]

end CountablePrefixMachine

end CountableConcrete

end

end SemanticConvergence
