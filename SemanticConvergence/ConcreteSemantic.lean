import SemanticConvergence.ConcreteBelief

namespace SemanticConvergence

universe u v

open Classical

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

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

end

end SemanticConvergence
