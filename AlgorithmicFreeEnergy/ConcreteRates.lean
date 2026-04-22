import AlgorithmicFreeEnergy.ConcreteSemantic

namespace AlgorithmicFreeEnergy

universe u v

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Float-valued log-odds proxy for a rational posterior-odds quantity. -/
def logOddsFloat (r : Rat) : Float :=
  if r ≤ 0 then 0 else Float.log (ratToNonnegFloat r)

/-- Concrete observer-fiber log-odds process at a finite history. -/
def observerFiberLogOdds (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  logOddsFloat (U.observerFiberPosteriorOdds π h ω pstar)

/-- Concrete one-step log-odds drift between two finite histories. -/
def oneStepLogOddsDrift (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Float :=
  U.observerFiberLogOdds π h' ω pstar - U.observerFiberLogOdds π h ω pstar

/-- Expected concrete semantic gain under a local action law. -/
def expectedSemanticGain (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) : Float :=
  actionExpectation κ (fun a => U.semanticGain π h a ω pstar)

/-- Rational support weight assigned by a local action law to a separating set. -/
def separatingSupportWeight (κ : ActionLaw A) (actions : List A)
    (S : PredSet A) [DecidablePred S] : Rat :=
  listWeightedSum actions (fun a => if S a then κ.mass a else 0)

/-- Concrete lower-bound witness for separating support on a finite action list. -/
def hasSeparatingSupportFloor (κ : ActionLaw A) (actions : List A)
    (S : PredSet A) [DecidablePred S] (δ : Rat) : Prop :=
  δ ≤ separatingSupportWeight κ actions S

/-- Concrete lower-bound witness for expected semantic gain. -/
def hasExpectedGainLowerBound (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) (δ : Float) : Prop :=
  δ ≤ U.expectedSemanticGain π h ω pstar κ

theorem observerFiberLogOdds_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberLogOdds π h ω p =
      U.observerFiberLogOdds π h ω q := by
  have hOdds := U.observerFiberPosteriorOdds_eq_of_sameView π h ω hView
  simp [observerFiberLogOdds, hOdds]

theorem oneStepLogOddsDrift_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h h' : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.oneStepLogOddsDrift π h h' ω p =
      U.oneStepLogOddsDrift π h h' ω q := by
  have hNow := U.observerFiberLogOdds_eq_of_sameView π h ω hView
  have hNext := U.observerFiberLogOdds_eq_of_sameView π h' ω hView
  simp [oneStepLogOddsDrift, hNow, hNext]

theorem expectedSemanticGain_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (κ : ActionLaw A)
    (hView : ω.view p = ω.view q) :
    U.expectedSemanticGain π h ω p κ =
      U.expectedSemanticGain π h ω q κ := by
  have hFun :
      (fun a => U.semanticGain π h a ω p) =
        (fun a => U.semanticGain π h a ω q) := by
    funext a
    exact U.semanticGain_eq_of_sameView π h a ω hView
  simp [expectedSemanticGain, hFun]

set_option linter.unusedSectionVars false in
theorem hasSeparatingSupportFloor_of_weight
    (κ : ActionLaw A) (actions : List A)
    (S : PredSet A) [DecidablePred S] {δ : Rat}
    (hWeight : δ ≤ separatingSupportWeight κ actions S) :
    hasSeparatingSupportFloor κ actions S δ :=
  hWeight

theorem hasExpectedGainLowerBound_of_value
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (κ : ActionLaw A) {δ : Float}
    (hGain : δ ≤ U.expectedSemanticGain π h ω pstar κ) :
    hasExpectedGainLowerBound U π h ω pstar κ δ :=
  hGain

end ConcretePrefixMachine

end

end AlgorithmicFreeEnergy
