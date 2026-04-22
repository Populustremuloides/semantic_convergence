import AlgorithmicFreeEnergy.ConcreteFunctional

namespace AlgorithmicFreeEnergy

universe u v

open Classical

noncomputable section

namespace ConcreteLaw

variable {α : Type u}

/-- Mass assigned by a concrete law to a predicate-defined class. -/
def classMass (μ : ConcreteLaw α) (C : PredSet α) [DecidablePred C] : Rat :=
  totalMass (restrict μ C)

end ConcreteLaw

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}

/-- Enumerate the finite machine domain as a list of machine programs. -/
def allPrograms (U : ConcretePrefixMachine A O) : List U.Program :=
  U.codes.attach

theorem mem_allPrograms (U : ConcretePrefixMachine A O) (p : U.Program) :
    p ∈ U.allPrograms :=
  List.mem_attach U.codes p

/-- Forget a machine-domain program down to its concrete encoded semantics. -/
def toEncodedProgram (U : ConcretePrefixMachine A O) (p : U.Program) : EncodedProgram A O where
  code := p.1
  kernel := U.programSemantics p

theorem toEncodedProgram_code (U : ConcretePrefixMachine A O) (p : U.Program) :
    (U.toEncodedProgram p).code = p.1 :=
  rfl

/-- Prior law on the finite machine domain. -/
def priorLaw (U : ConcretePrefixMachine A O) : ConcreteLaw U.Program where
  mass := U.universalPrior
  support := U.allPrograms
  support_complete := by
    intro p hp
    exact U.mem_allPrograms p

/-- Likelihood of a realized finite history under a concrete machine-domain program. -/
def likelihood (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) (p : U.Program) : Rat :=
  (histLaw π (U.programSemantics p) h.1).mass h.2

/-- Unnormalized Bayes numerator law on machine-domain programs. -/
def bayesNumeratorLaw (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) : ConcreteLaw U.Program where
  mass p := U.universalPrior p * U.likelihood π h p
  support := U.allPrograms
  support_complete := by
    intro p hp
    exact U.mem_allPrograms p

/-- Bayesian evidence for a realized finite history. -/
def evidence (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) : Rat :=
  ConcreteLaw.totalMass (U.bayesNumeratorLaw π h)

/-- Concrete Bayes posterior on the finite machine domain. -/
def normalizeOnPrograms (U : ConcretePrefixMachine A O)
    (μ : ConcreteLaw U.Program) (Z : Rat) : ConcreteLaw U.Program where
  mass p := if hZ : Z = 0 then 0 else μ.mass p / Z
  support := U.allPrograms
  support_complete := by
    intro p hp
    exact U.mem_allPrograms p

/-- Concrete Bayes posterior on the finite machine domain. -/
def posteriorLaw (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) : ConcreteLaw U.Program :=
  U.normalizeOnPrograms (U.bayesNumeratorLaw π h) (U.evidence π h)

/-- Posterior mass assigned to a concrete machine-domain class. -/
def posteriorClassMass (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] : Rat :=
  ConcreteLaw.classMass (U.posteriorLaw π h) C

/-- Posterior restricted and renormalized to a concrete class. -/
def posteriorWithinClass (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] : ConcreteLaw U.Program :=
  U.normalizeOnPrograms
    (ConcreteLaw.restrict (U.posteriorLaw π h) C)
    (U.posteriorClassMass π h C)

/-- Posterior restricted and renormalized to the complement of a concrete class. -/
def posteriorOutsideClass (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] : ConcreteLaw U.Program := by
  classical
  exact U.normalizeOnPrograms
    (ConcreteLaw.restrict (U.posteriorLaw π h) (fun p => ¬ C p))
    (ConcreteLaw.classMass (U.posteriorLaw π h) (fun p => ¬ C p))

/-- Observer fiber on machine-domain programs through an encoded target program. -/
def observerFiber (U : ConcretePrefixMachine A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : PredSet U.Program :=
  fun p => ω.view (U.toEncodedProgram p) = ω.view pstar

/-- Posterior mass assigned to an observer fiber on machine-domain programs. -/
def observerFiberPosteriorMass (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat := by
  classical
  exact U.posteriorClassMass π h (U.observerFiber ω pstar)

/-- Same-view targets induce the same observer fiber predicate on machine programs. -/
theorem observerFiber_eq_of_sameView (U : ConcretePrefixMachine A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiber ω p = U.observerFiber ω q := by
  funext r
  simp [observerFiber, hView]

/-- Same-view targets have the same observer-fiber posterior mass. -/
theorem observerFiberPosteriorMass_eq_of_sameView (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (hView : ω.view p = ω.view q) :
    U.observerFiberPosteriorMass π h ω p =
      U.observerFiberPosteriorMass π h ω q := by
  classical
  have hFib : U.observerFiber ω p = U.observerFiber ω q :=
    U.observerFiber_eq_of_sameView ω hView
  simpa [observerFiberPosteriorMass] using
    congrArg (fun C => U.posteriorClassMass π h C) hFib

/--
Push forward the concrete machine-domain posterior through an encoded-program observer.
This is the concrete quotient-pushforward object needed by later first-principles phases.
-/
def pushforwardPosterior (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    [DecidableEq ω.Ω] [BEq ω.Ω] [LawfulBEq ω.Ω] : ConcreteLaw ω.Ω :=
  ConcreteLaw.map (fun p => ω.view (U.toEncodedProgram p)) (U.posteriorLaw π h)

/--
Concrete predictive law under a posterior restricted to a machine-domain class.
This is the class-side ingredient for the paper's class-vs-complement semantics.
-/
def predictiveLawInClass (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] : ConcreteLaw O := by
  classical
  exact mixLaw (U.posteriorWithinClass π h C)
    (fun p => programObsLaw h a (U.toEncodedProgram p))

/--
Concrete predictive law under the posterior complement of a machine-domain class.
-/
def predictiveLawOutsideClass (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] : ConcreteLaw O := by
  classical
  exact mixLaw (U.posteriorOutsideClass π h C)
    (fun p => programObsLaw h a (U.toEncodedProgram p))

/-- Concrete class-vs-complement predictive pair at a history-action pair. -/
def classComplementLaw (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (C : PredSet U.Program) [DecidablePred C] : ConcreteLaw O × ConcreteLaw O :=
  (U.predictiveLawInClass π h a C,
   U.predictiveLawOutsideClass π h a C)

/--
Concrete observer-fiber predictive pair at a history-action pair.
-/
def observerFiberComplementLaw (U : ConcretePrefixMachine A O)
    [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : ConcreteLaw O × ConcreteLaw O := by
  classical
  exact U.classComplementLaw π h a (U.observerFiber ω pstar)

end ConcretePrefixMachine

end

end AlgorithmicFreeEnergy
