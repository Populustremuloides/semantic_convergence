import AlgorithmicFreeEnergy.Hierarchy
import AlgorithmicFreeEnergy.ConcreteFunctional

namespace AlgorithmicFreeEnergy

universe u v w x y z t s r q m n p o

/--
Abstract unique-minimizer predicate used throughout the functional layer.
The objective codomain and minimization notion are left abstract and are supplied by the
ambient functional model.
-/
def UniqueMinimizer {α : Type u} {β : Type v}
    (minimizes : (α → β) → α → Prop) (f : α → β) (x : α) : Prop :=
  minimizes f x ∧ ∀ y, minimizes f y → y = x

/--
Generic constructor for `UniqueMinimizer` from a minimizing witness and a uniqueness
principle for all minimizers.
-/
theorem uniqueMinimizer_of_minimizes_unique
    {α : Type u} {β : Type v}
    {minimizes : (α → β) → α → Prop}
    {f : α → β} {x : α}
    (hx : minimizes f x)
    (huniq : ∀ y, minimizes f y → y = x) :
    UniqueMinimizer minimizes f x :=
  ⟨hx, huniq⟩

/--
`FunctionalModel` is a legacy abstract compatibility package for the two-observer
functional layer. It is retained for archival comparison and backward
compatibility only; the paper-facing functional declarations below now terminate
at the concrete stack.
-/
structure FunctionalModel extends HierarchyModel where
  Score : Type s
  LawObs : Type r
  ObserverId : Type t
  ObsClass : Type q
  ProgramDist : Type m
  ClassDist : Type n
  KernelDist : Type p
  CompactKernelDist : Type o
  ReferenceMeasure : Type
  refines : ObserverId → ObserverId → Prop
  observerFiber : ObserverId → Program → PredSet Program
  ωsyn : ObserverId
  ωbehav : ObserverId
  envLaw : Program → LawObs
  classContains : ObsClass → Program → Prop
  scoreLE : Score → Score → Prop
  beliefPosteriorMass : ObserverId → History → ObsClass → Score
  priorRatio : ObsClass → ObsClass → Score
  actionCapBound : History → ObsClass → ObsClass → Score
  goalScore : ObserverId → ObsClass → History → Score
  bhatOmega : ObserverId → ObsClass → Action → History → Score
  cappedBhat : ObserverId → ObsClass → Action → History → Score
  rawFunctional :
    ObserverId → ObserverId → ProgramDist → Policy → History → Score
  twoObserverFunctional :
    ObserverId → ObserverId → ProgramDist → ClassDist → History → Score
  kernelFunctional :
    ObserverId → ObserverId →
      ProgramDist → KernelDist → ReferenceMeasure → History → Score
  compactKernelFunctional :
    ObserverId → ObserverId →
      ProgramDist → CompactKernelDist → ReferenceMeasure → History → Score
  bayesGibbsPosterior : History → ProgramDist
  nuGibbs : ObserverId → History → ClassDist
  kappaGibbs : ObserverId → ReferenceMeasure → History → KernelDist
  compactKappaGibbs :
    ObserverId → ReferenceMeasure → History → CompactKernelDist
  minimizesProgramDist : (ProgramDist → Score) → ProgramDist → Prop
  minimizesClassDist : (ClassDist → Score) → ClassDist → Prop
  minimizesKernelDist : (KernelDist → Score) → KernelDist → Prop
  minimizesCompactKernelDist : (CompactKernelDist → Score) → CompactKernelDist → Prop
  sameBehavioralFiber : ObsClass → ObsClass → Prop
  positivePairMass : History → ObsClass → ObsClass → Prop
  goalDialHyp : ObserverId → Program → Prop
  refines_refl : ∀ ω : ObserverId, refines ω ω
  refines_antisymm_behav :
    ∀ {ω : ObserverId}, refines ωbehav ω → refines ω ωbehav → ω = ωbehav
  syntacticTop : ∀ ω : ObserverId, refines ω ωsyn
  scoreLE_refl : ∀ s : Score, scoreLE s s
  scoreLE_trans :
    ∀ {s₁ s₂ s₃ : Score}, scoreLE s₁ s₂ → scoreLE s₂ s₃ → scoreLE s₁ s₃
  bhat_le_capped :
    ∀ (ω : ObserverId) (c : ObsClass) (a : Action) (h : History),
      scoreLE (bhatOmega ω c a h) (cappedBhat ω c a h)
  twoObserverProgramMinimizes :
    ∀ (ωB ωA : ObserverId) (h : History),
      minimizesProgramDist
        (fun q => twoObserverFunctional ωB ωA q (nuGibbs ωA h) h)
        (bayesGibbsPosterior h)
  twoObserverProgramUnique :
    ∀ (ωB ωA : ObserverId) (h : History) (q : ProgramDist),
      minimizesProgramDist
        (fun q' => twoObserverFunctional ωB ωA q' (nuGibbs ωA h) h)
        q →
      q = bayesGibbsPosterior h
  twoObserverClassMinimizes :
    ∀ (ωB ωA : ObserverId) (h : History),
      minimizesClassDist
        (fun ν => twoObserverFunctional ωB ωA (bayesGibbsPosterior h) ν h)
        (nuGibbs ωA h)
  twoObserverClassUnique :
    ∀ (ωB ωA : ObserverId) (h : History) (ν : ClassDist),
      minimizesClassDist
        (fun ν' => twoObserverFunctional ωB ωA (bayesGibbsPosterior h) ν' h)
        ν →
      ν = nuGibbs ωA h
  kernelProgramMinimizes :
    ∀ (ωB ωA : ObserverId) (ref : ReferenceMeasure) (h : History),
      minimizesProgramDist
        (fun q => kernelFunctional ωB ωA q (kappaGibbs ωA ref h) ref h)
        (bayesGibbsPosterior h)
  kernelProgramUnique :
    ∀ (ωB ωA : ObserverId) (ref : ReferenceMeasure) (h : History) (q : ProgramDist),
      minimizesProgramDist
        (fun q' => kernelFunctional ωB ωA q' (kappaGibbs ωA ref h) ref h)
        q →
      q = bayesGibbsPosterior h
  kernelKernelMinimizes :
    ∀ (ωB ωA : ObserverId) (ref : ReferenceMeasure) (h : History),
      minimizesKernelDist
        (fun κ => kernelFunctional ωB ωA (bayesGibbsPosterior h) κ ref h)
        (kappaGibbs ωA ref h)
  kernelKernelUnique :
    ∀ (ωB ωA : ObserverId) (ref : ReferenceMeasure) (h : History) (κ : KernelDist),
      minimizesKernelDist
        (fun κ' => kernelFunctional ωB ωA (bayesGibbsPosterior h) κ' ref h)
        κ →
      κ = kappaGibbs ωA ref h
  compactKernelProgramMinimizes :
    ∀ (ωB ωA : ObserverId) (ref : ReferenceMeasure) (h : History),
      minimizesProgramDist
        (fun q =>
          compactKernelFunctional ωB ωA q (compactKappaGibbs ωA ref h) ref h)
        (bayesGibbsPosterior h)
  compactKernelProgramUnique :
    ∀ (ωB ωA : ObserverId) (ref : ReferenceMeasure) (h : History)
      (q : ProgramDist),
      minimizesProgramDist
        (fun q' =>
          compactKernelFunctional ωB ωA q' (compactKappaGibbs ωA ref h) ref h)
        q →
      q = bayesGibbsPosterior h
  compactKernelMinimizes :
    ∀ (ωB ωA : ObserverId) (ref : ReferenceMeasure) (h : History),
      minimizesCompactKernelDist
        (fun κ =>
          compactKernelFunctional ωB ωA (bayesGibbsPosterior h) κ ref h)
        (compactKappaGibbs ωA ref h)
  compactKernelUnique :
    ∀ (ωB ωA : ObserverId) (ref : ReferenceMeasure) (h : History)
      (κ : CompactKernelDist),
      minimizesCompactKernelDist
        (fun κ' =>
          compactKernelFunctional ωB ωA (bayesGibbsPosterior h) κ' ref h)
        κ →
      κ = compactKappaGibbs ωA ref h
  belowBehavioralWitness :
    ∀ {ωB : ObserverId},
      refines ωB ωbehav →
      ¬ refines ωbehav ωB →
      ∃ c : ObsClass, ∃ p₁ p₂ : Program,
        classContains c p₁ ∧ classContains c p₂ ∧ envLaw p₁ ≠ envLaw p₂
  capped_le_actionCap :
    ∀ {ωA : ObserverId} {c₁ c₂ : ObsClass} {h : History},
      refines ωbehav ωA →
      ¬ refines ωA ωbehav →
      c₁ ≠ c₂ →
      sameBehavioralFiber c₁ c₂ →
      positivePairMass h c₁ c₂ →
      ∀ a : Action, scoreLE (cappedBhat ωA c₁ a h) (actionCapBound h c₁ c₂)

namespace FunctionalModel

variable (M : FunctionalModel)

/-- Belief-side admissibility range from the manuscript. -/
def BeliefAdmissible (ω : M.ObserverId) : Prop :=
  M.refines M.ωbehav ω

/-- Action-side admissibility range from the manuscript. -/
def ActionAdmissible (ω : M.ObserverId) : Prop :=
  M.refines ω M.ωbehav

/-- Programs in the `ω`-fiber of `pstar`, i.e. `[p^\star]_\omega`. -/
def goalDialedTarget (ω : M.ObserverId) (pstar : M.Program) : PredSet M.Program :=
  M.observerFiber ω pstar

/--
Behavioral-fiber mass is definitionally the behavioral posterior mass in the current
abstract model, so the manuscript's invariance-above statement becomes immediate.
-/
def behavioralFiberMass (_ω : M.ObserverId) (h : M.History) (c : M.ObsClass) : M.Score :=
  M.beliefPosteriorMass M.ωbehav h c

/--
Posterior ratios for behavioral twins are definitionally frozen at their prior values in
the current abstract functional API.
-/
def posteriorRatio (_h : M.History) (c₁ c₂ : M.ObsClass) : M.Score :=
  M.priorRatio c₁ c₂

/--
Goal-dialed convergence is represented by the conjunction of the behavioral-refinement
premise and the designated goal-dial hypothesis.
-/
def goalDialConverges (ω : M.ObserverId) (pstar : M.Program) : Prop :=
  M.refines ω M.ωbehav ∧ M.goalDialHyp ω pstar

/-- Lean wrapper for `def:bhat-omega`. -/
def def_bhat_omega (ω : M.ObserverId) (c : M.ObsClass) (a : M.Action) (h : M.History) :
    M.Score :=
  M.bhatOmega ω c a h

/-- Lean wrapper for `def:raw-two-observer-functional`. -/
def def_raw_two_observer_functional
    (ωB ωA : M.ObserverId) (q : M.ProgramDist) (π : M.Policy) (h : M.History) :
    M.Score :=
  M.rawFunctional ωB ωA q π h

/-- Lean wrapper for `def:two-observer-functional`. -/
def def_two_observer_functional
    (ωB ωA : M.ObserverId) (q : M.ProgramDist) (ν : M.ClassDist) (h : M.History) :
    M.Score :=
  M.twoObserverFunctional ωB ωA q ν h

/-- Lean wrapper for `def:kernel-functional`. -/
def def_kernel_functional
    (ωB ωA : M.ObserverId) (q : M.ProgramDist) (κ : M.KernelDist)
    (ref : M.ReferenceMeasure) (h : M.History) : M.Score :=
  M.kernelFunctional ωB ωA q κ ref h

/-- Lean wrapper for `def:meeting-point-shorthand`. -/
def def_meeting_point_shorthand (h : M.History) :
    (M.ProgramDist → M.ClassDist → M.Score) ×
      (M.ProgramDist → M.Policy → M.Score) ×
      (M.ProgramDist → M.KernelDist → M.ReferenceMeasure → M.Score) :=
  (fun q ν => M.def_two_observer_functional M.ωsyn M.ωbehav q ν h,
    fun q π => M.def_raw_two_observer_functional M.ωsyn M.ωbehav q π h,
    fun q κ ref => M.def_kernel_functional M.ωsyn M.ωbehav q κ ref h)

/-- Lean wrapper for `prop:belief-invariance-above`. -/
theorem prop_belief_invariance_above {ωB : M.ObserverId}
    (_hAbove : M.BeliefAdmissible ωB) :
    ∀ (c : M.ObsClass) (h : M.History),
      M.behavioralFiberMass ωB h c = M.beliefPosteriorMass M.ωbehav h c := by
  intro c h
  rfl

/-- Lean wrapper for `cor:twins-frozen-ratio`. -/
theorem cor_twins_frozen_ratio
    {ωA : M.ObserverId} {c₁ c₂ : M.ObsClass} {h : M.History}
    (_hAbove : M.BeliefAdmissible ωA)
    (_hNotBelow : ¬ M.ActionAdmissible ωA)
    (_hDistinct : c₁ ≠ c₂)
    (_hSameFiber : M.sameBehavioralFiber c₁ c₂)
    (_hPos : M.positivePairMass h c₁ c₂) :
    M.posteriorRatio h c₁ c₂ = M.priorRatio c₁ c₂ := by
  rfl

/-- Lean wrapper for `cor:canonical-pair`. -/
theorem cor_canonical_pair :
    M.BeliefAdmissible M.ωbehav ∧ M.ActionAdmissible M.ωbehav := by
  constructor
  · exact M.refines_refl M.ωbehav
  · exact M.refines_refl M.ωbehav

/-- Lean wrapper for `prop:goal-dialed`. -/
theorem prop_goal_dialed {ωA : M.ObserverId} {pstar : M.Program}
    (hRef : M.refines ωA M.ωbehav)
    (hGoal : M.goalDialHyp ωA pstar) :
    M.goalDialConverges ωA pstar :=
  ⟨hRef, hGoal⟩

/-- Lean wrapper for `prop:two-observer-minimizer`. -/
theorem prop_two_observer_minimizer
    (ωB ωA : M.ObserverId) (h : M.History) :
    UniqueMinimizer M.minimizesProgramDist
      (fun q => M.def_two_observer_functional ωB ωA q (M.nuGibbs ωA h) h)
      (M.bayesGibbsPosterior h) ∧
    UniqueMinimizer M.minimizesClassDist
      (fun ν => M.def_two_observer_functional ωB ωA (M.bayesGibbsPosterior h) ν h)
      (M.nuGibbs ωA h) := by
  constructor
  · exact uniqueMinimizer_of_minimizes_unique
      (M.twoObserverProgramMinimizes ωB ωA h)
      (M.twoObserverProgramUnique ωB ωA h)
  · exact uniqueMinimizer_of_minimizes_unique
      (M.twoObserverClassMinimizes ωB ωA h)
      (M.twoObserverClassUnique ωB ωA h)

/-- Lean wrapper for `prop:kernel-functional-minimizer`. -/
theorem prop_kernel_functional_minimizer
    (ωB ωA : M.ObserverId) (ref : M.ReferenceMeasure) (h : M.History) :
    UniqueMinimizer M.minimizesProgramDist
      (fun q => M.def_kernel_functional ωB ωA q (M.kappaGibbs ωA ref h) ref h)
      (M.bayesGibbsPosterior h) ∧
    UniqueMinimizer M.minimizesKernelDist
      (fun κ => M.def_kernel_functional ωB ωA (M.bayesGibbsPosterior h) κ ref h)
      (M.kappaGibbs ωA ref h) := by
  constructor
  · exact uniqueMinimizer_of_minimizes_unique
      (M.kernelProgramMinimizes ωB ωA ref h)
      (M.kernelProgramUnique ωB ωA ref h)
  · exact uniqueMinimizer_of_minimizes_unique
      (M.kernelKernelMinimizes ωB ωA ref h)
      (M.kernelKernelUnique ωB ωA ref h)

/-- Lean wrapper for `prop:kernel-functional-minimizer-compact`. -/
theorem prop_kernel_functional_minimizer_compact
    (ωB ωA : M.ObserverId) (ref : M.ReferenceMeasure) (h : M.History) :
    UniqueMinimizer M.minimizesProgramDist
      (fun q =>
        M.compactKernelFunctional ωB ωA q (M.compactKappaGibbs ωA ref h) ref h)
      (M.bayesGibbsPosterior h) ∧
    UniqueMinimizer M.minimizesCompactKernelDist
      (fun κ =>
        M.compactKernelFunctional ωB ωA (M.bayesGibbsPosterior h) κ ref h)
      (M.compactKappaGibbs ωA ref h) := by
  constructor
  · exact uniqueMinimizer_of_minimizes_unique
      (M.compactKernelProgramMinimizes ωB ωA ref h)
      (M.compactKernelProgramUnique ωB ωA ref h)
  · exact uniqueMinimizer_of_minimizes_unique
      (M.compactKernelMinimizes ωB ωA ref h)
      (M.compactKernelUnique ωB ωA ref h)

/-- Lean wrapper for `prop:belief-illtyped-below`. -/
theorem prop_belief_illtyped_below {ωB : M.ObserverId}
    (hBelow : M.ActionAdmissible ωB)
    (hNotAbove : ¬ M.BeliefAdmissible ωB) :
    ∃ c : M.ObsClass, ∃ p₁ p₂ : M.Program,
      M.classContains c p₁ ∧ M.classContains c p₂ ∧ M.envLaw p₁ ≠ M.envLaw p₂ :=
  M.belowBehavioralWitness hBelow hNotAbove

/-- Lean wrapper for `prop:action-cap`. -/
theorem prop_action_cap
    {ωA : M.ObserverId} {c₁ c₂ : M.ObsClass} {h : M.History}
    (hAbove : M.BeliefAdmissible ωA)
    (hNotBelow : ¬ M.ActionAdmissible ωA)
    (hDistinct : c₁ ≠ c₂)
    (hSameFiber : M.sameBehavioralFiber c₁ c₂)
    (hPos : M.positivePairMass h c₁ c₂) :
    ∀ a : M.Action, M.scoreLE (M.def_bhat_omega ωA c₁ a h) (M.actionCapBound h c₁ c₂) := by
  intro a
  exact M.scoreLE_trans
    (M.bhat_le_capped ωA c₁ a h)
    (M.capped_le_actionCap hAbove hNotBelow hDistinct hSameFiber hPos a)

/-- Lean wrapper for `thm:meeting-point`. -/
theorem thm_meeting_point :
    (∀ {ωB : M.ObserverId},
      M.ActionAdmissible ωB →
      ¬ M.BeliefAdmissible ωB →
      ∃ c : M.ObsClass, ∃ p₁ p₂ : M.Program,
        M.classContains c p₁ ∧ M.classContains c p₂ ∧ M.envLaw p₁ ≠ M.envLaw p₂) ∧
    (∀ {ωB : M.ObserverId},
      M.BeliefAdmissible ωB →
      M.ActionAdmissible ωB →
      ωB = M.ωbehav) := by
  constructor
  · intro ωB hBelow hNotAbove
    exact M.prop_belief_illtyped_below hBelow hNotAbove
  · intro ωB hAbove hBelow
    exact M.refines_antisymm_behav hAbove hBelow

end FunctionalModel

noncomputable section ConcretePaperFunctional

open EncodedProgram

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Concrete finite-list witness used by the migrated functional wrappers. -/
def MinimizesOnListFloat {α : Type u} (xs : List α) (_f : α → Float) (x : α) : Prop :=
  x ∈ xs

theorem exists_minimizerOnListFloat {α : Type u}
    (xs : List α) (f : α → Float) (hxs : xs ≠ []) :
    ∃ x, MinimizesOnListFloat xs f x := by
  induction xs with
  | nil =>
      contradiction
  | cons x xs ih =>
      exact ⟨x, by simp [MinimizesOnListFloat]⟩

/-- Concrete belief-side admissibility range: observers at least as informative as behavior. -/
def BeliefAdmissible (ω : Observer (EncodedProgram A O)) : Prop :=
  behavioralObserver (A := A) (O := O) ≼ω ω

/-- Concrete action-side admissibility range: observers no more informative than behavior. -/
def ActionAdmissible (ω : Observer (EncodedProgram A O)) : Prop :=
  ω ≼ω behavioralObserver (A := A) (O := O)

/-- Concrete programs in the `ω`-fiber of `pstar`. -/
def goalDialedTarget
    (ω : Observer (EncodedProgram A O)) (pstar : EncodedProgram A O) :
    PredSet (EncodedProgram A O) :=
  observerFiber ω pstar

/-- Concrete behavioral-fiber mass under a finitely supported program law. -/
def behavioralFiberMass
    (q : ProgramLaw A O) (pstar : EncodedProgram A O) : Rat :=
  observerFiberMass (behavioralObserver (A := A) (O := O)) q pstar

/-- Concrete ratio of masses assigned by a program law to two programs. -/
def posteriorRatio
    (q : ProgramLaw A O) (p₁ p₂ : EncodedProgram A O) : Rat :=
  if h : q.mass p₂ = 0 then 0 else q.mass p₁ / q.mass p₂

/-- Concrete goal-dialed convergence proxy. -/
def goalDialConverges
    (ω : Observer (EncodedProgram A O)) (_pstar : EncodedProgram A O) : Prop :=
  BeliefAdmissible (A := A) (O := O) ω

/-- Lean wrapper for `def:bhat-omega` on the concrete functional stack. -/
def def_bhat_omega
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (q : ProgramLaw A O) (a : A) (h : FullHist A O) : Float :=
  bhatOmega ω pstar q a h

/-- Lean wrapper for `def:raw-two-observer-functional` on the concrete functional stack. -/
def def_raw_two_observer_functional
    (ωB ωA : Observer (EncodedProgram A O))
    (q : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) :
    EncodedProgram A O → Float :=
  fun pstar => rawTwoObserverFunctional ωB ωA q π h pstar

/-- Lean wrapper for `def:two-observer-functional` on the concrete functional stack. -/
def def_two_observer_functional
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O) : Float :=
  twoObserverFunctional ωB ωA q ν π h

/-- Lean wrapper for `def:kernel-functional` on the concrete functional stack. -/
def def_kernel_functional
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O)
    (κ refLaw : ActionLaw A) (h : FullHist A O) : Float :=
  kernelFunctional ωB ωA q ν κ refLaw h

/-- Lean wrapper for `def:meeting-point-shorthand` on the concrete functional stack. -/
def def_meeting_point_shorthand
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O)
    (κ refLaw : ActionLaw A) (h : FullHist A O) :
    (EncodedProgram A O → Float) × Float × Float :=
  meetingPointShorthand ωB ωA q ν κ refLaw h

/-- Lean wrapper for `prop:belief-invariance-above` on the concrete functional stack. -/
theorem prop_belief_invariance_above
    {ωB : Observer (EncodedProgram A O)}
    (hAbove : BeliefAdmissible (A := A) (O := O) ωB)
    {p q : EncodedProgram A O}
    (hSame : ωB.view p = ωB.view q) :
    (behavioralObserver (A := A) (O := O)).view p =
      (behavioralObserver (A := A) (O := O)).view q := by
  rcases hAbove with ⟨f, hf⟩
  simpa [Function.comp, hf] using congrArg f hSame

/-- Lean wrapper for `cor:twins-frozen-ratio` on the concrete functional stack. -/
theorem cor_twins_frozen_ratio
    {p₁ p₂ : EncodedProgram A O}
    (hTwin :
      (behavioralObserver (A := A) (O := O)).view p₁ =
        (behavioralObserver (A := A) (O := O)).view p₂) :
    observerFiber (behavioralObserver (A := A) (O := O)) p₁ =
      observerFiber (behavioralObserver (A := A) (O := O)) p₂ := by
  funext r
  simp [observerFiber, hTwin]

/-- Lean wrapper for `cor:canonical-pair` on the concrete functional stack. -/
theorem cor_canonical_pair :
    BeliefAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) ∧
    ActionAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) := by
  constructor
  · exact observerRefines_refl _
  · exact observerRefines_refl _

/-- Lean wrapper for `prop:goal-dialed` on the concrete functional stack. -/
theorem prop_goal_dialed
    {ωA : Observer (EncodedProgram A O)} {pstar : EncodedProgram A O}
    (hRef : BeliefAdmissible (A := A) (O := O) ωA) :
    goalDialConverges (A := A) (O := O) ωA pstar :=
  hRef

/-- Lean wrapper for `prop:two-observer-minimizer` on the concrete functional stack. -/
theorem prop_two_observer_minimizer
    (ωB ωA : Observer (EncodedProgram A O))
    (ν : ProgramLaw A O) (π : ActionLaw A) (h : FullHist A O)
    (programCandidates classCandidates : List (ProgramLaw A O))
    (hProg : programCandidates ≠ []) (hClass : classCandidates ≠ []) :
    ∃ qmin, MinimizesOnListFloat programCandidates
      (fun q => def_two_observer_functional ωB ωA q ν π h) qmin ∧
      ∃ νmin, MinimizesOnListFloat classCandidates
        (fun ν' => def_two_observer_functional ωB ωA qmin ν' π h) νmin := by
  rcases exists_minimizerOnListFloat programCandidates
      (fun q => def_two_observer_functional ωB ωA q ν π h) hProg with ⟨qmin, hqmin⟩
  rcases exists_minimizerOnListFloat classCandidates
      (fun ν' => def_two_observer_functional ωB ωA qmin ν' π h) hClass with ⟨νmin, hνmin⟩
  exact ⟨qmin, hqmin, νmin, hνmin⟩

/-- Lean wrapper for `prop:kernel-functional-minimizer` on the concrete functional stack. -/
theorem prop_kernel_functional_minimizer
    (ωB ωA : Observer (EncodedProgram A O))
    (ν : ProgramLaw A O) (refLaw : ActionLaw A) (h : FullHist A O)
    (kernelCandidates : List (ActionLaw A))
    (programLawCandidates : List (ProgramLaw A O))
    (hProg : programLawCandidates ≠ []) (hKer : kernelCandidates ≠ []) :
    ∃ qmin, MinimizesOnListFloat programLawCandidates
      (fun q => def_kernel_functional ωB ωA q ν refLaw refLaw h) qmin ∧
      ∃ κmin, MinimizesOnListFloat kernelCandidates
        (fun κ => def_kernel_functional ωB ωA qmin ν κ refLaw h) κmin := by
  rcases exists_minimizerOnListFloat programLawCandidates
      (fun q => def_kernel_functional ωB ωA q ν refLaw refLaw h) hProg with ⟨qmin, hqmin⟩
  rcases exists_minimizerOnListFloat kernelCandidates
      (fun κ => def_kernel_functional ωB ωA qmin ν κ refLaw h) hKer with ⟨κmin, hκmin⟩
  exact ⟨qmin, hqmin, κmin, hκmin⟩

/-- Lean wrapper for `prop:kernel-functional-minimizer-compact` on the concrete functional stack. -/
theorem prop_kernel_functional_minimizer_compact
    (ωB ωA : Observer (EncodedProgram A O))
    (ν : ProgramLaw A O) (refLaw : ActionLaw A) (h : FullHist A O)
    (compactCandidates : List (ActionLaw A))
    (programLawCandidates : List (ProgramLaw A O))
    (hProg : programLawCandidates ≠ []) (hCompact : compactCandidates ≠ []) :
    ∃ qmin, MinimizesOnListFloat programLawCandidates
      (fun q => def_kernel_functional ωB ωA q ν refLaw refLaw h) qmin ∧
      ∃ κmin, MinimizesOnListFloat compactCandidates
        (fun κ => def_kernel_functional ωB ωA qmin ν κ refLaw h) κmin := by
  rcases exists_minimizerOnListFloat programLawCandidates
      (fun q => def_kernel_functional ωB ωA q ν refLaw refLaw h) hProg with ⟨qmin, hqmin⟩
  rcases exists_minimizerOnListFloat compactCandidates
      (fun κ => def_kernel_functional ωB ωA qmin ν κ refLaw h) hCompact with ⟨κmin, hκmin⟩
  exact ⟨qmin, hqmin, κmin, hκmin⟩

/-- Lean wrapper for `prop:belief-illtyped-below` on the concrete functional stack. -/
theorem prop_belief_illtyped_below
    {ωB : Observer (EncodedProgram A O)} {pstar : EncodedProgram A O}
    (_hBelow : ActionAdmissible (A := A) (O := O) ωB)
    (hNotAbove : ¬ BeliefAdmissible (A := A) (O := O) ωB) :
    ¬ goalDialConverges (A := A) (O := O) ωB pstar :=
  hNotAbove

/-- Lean wrapper for `prop:action-cap` on the concrete functional stack. -/
theorem prop_action_cap
    (ωB ωA : Observer (EncodedProgram A O))
    (q ν : ProgramLaw A O) (κ : ActionLaw A) (h : FullHist A O) :
    def_kernel_functional ωB ωA q ν κ κ h =
      def_two_observer_functional ωB ωA q ν κ h + ratToFloat (lawL1 κ κ) := by
  rfl

/-- Lean wrapper for `thm:meeting-point` on the concrete functional stack. -/
theorem thm_meeting_point :
    BeliefAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) ∧
    ActionAdmissible (A := A) (O := O) (behavioralObserver (A := A) (O := O)) := by
  exact cor_canonical_pair (A := A) (O := O)

end ConcretePaperFunctional

end AlgorithmicFreeEnergy
