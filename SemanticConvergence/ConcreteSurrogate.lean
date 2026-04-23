import SemanticConvergence.ConcreteBoundary

namespace SemanticConvergence

universe u v

open Classical

noncomputable section

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [BEq A] [LawfulBEq A] [BEq O] [LawfulBEq O]

/-- Concrete surrogate information score inherited from the boundary layer. -/
def surrogateInformationScore (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O) : Rat :=
  U.boundaryInformationGainTerm π h a ω pstar

/-- Simple rational regularization penalty against a reference local action law. -/
def surrogateRegularization
    (refLaw : ActionLaw A) (a : A) : Rat :=
  Rat.abs (1 - refLaw.mass a)

/--
Concrete amortized-surrogate energy: expected free energy plus a rational regularization
term against a reference local action law.
-/
def surrogateEnergy (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) : Rat :=
  U.expectedFreeEnergyRat π h a ω pstar +
    reg * surrogateRegularization refLaw a

/-- Finite-list concrete surrogate minimizer. -/
noncomputable def surrogateArgmin (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) : A :=
  argminOnList actions
    (fun a => U.surrogateEnergy π h a ω pstar refLaw reg)
    hActions

/--
Concrete local action law induced by the surrogate minimizer, represented as a
deterministic singleton-support law on the chosen finite-list minimizer.
-/
def surrogateChosenLaw (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) : ActionLaw A :=
  fullSupportActionLaw [U.surrogateArgmin π h actions hActions ω pstar refLaw reg]

theorem surrogateEnergy_eq_of_sameView
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (a : A)
    (ω : Observer (EncodedProgram A O))
    {p q : EncodedProgram A O}
    (refLaw : ActionLaw A) (reg : Rat)
    (hView : ω.view p = ω.view q) :
    U.surrogateEnergy π h a ω p refLaw reg =
      U.surrogateEnergy π h a ω q refLaw reg := by
  have hEfe := U.expectedFreeEnergyRat_eq_of_sameView π h a ω hView
  simp [surrogateEnergy, hEfe]

theorem surrogateArgmin_spec
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) :
    MinimizesOnList actions
      (fun a => U.surrogateEnergy π h a ω pstar refLaw reg)
      (U.surrogateArgmin π h actions hActions ω pstar refLaw reg) :=
  argminOnList_spec actions
    (fun a => U.surrogateEnergy π h a ω pstar refLaw reg)
    hActions

theorem surrogateChosenLaw_supportsArgmin
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat) :
    (U.surrogateChosenLaw π h actions hActions ω pstar refLaw reg).mass
      (U.surrogateArgmin π h actions hActions ω pstar refLaw reg) ≠ 0 := by
  simp [surrogateChosenLaw, fullSupportActionLaw]

theorem surrogateChosenLaw_hasSeparatingSupport_of_argmin
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat)
    (hSep :
      U.isSeparatingAction π h ω pstar
        (U.surrogateArgmin π h actions hActions ω pstar refLaw reg)) :
    hasSeparatingSupportOn
      (U.surrogateChosenLaw π h actions hActions ω pstar refLaw reg)
      [U.surrogateArgmin π h actions hActions ω pstar refLaw reg]
      (U.separatingActionSet π h ω pstar) := by
  refine ⟨U.surrogateArgmin π h actions hActions ω pstar refLaw reg, by simp, ?_, hSep⟩
  exact U.surrogateChosenLaw_supportsArgmin π h actions hActions ω pstar refLaw reg

/--
Witness-driven finite-list surrogate theorem: if the concrete surrogate minimizer is
itself semantically separating, then the induced singleton-support action law already has
separating support.
-/
theorem amortizedSurrogate_from_witness
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O) (actions : List A)
    (hActions : actions ≠ [])
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (refLaw : ActionLaw A) (reg : Rat)
    (hSep :
      U.isSeparatingAction π h ω pstar
        (U.surrogateArgmin π h actions hActions ω pstar refLaw reg)) :
    hasSeparatingSupportOn
      (U.surrogateChosenLaw π h actions hActions ω pstar refLaw reg)
      [U.surrogateArgmin π h actions hActions ω pstar refLaw reg]
      (U.separatingActionSet π h ω pstar) :=
  U.surrogateChosenLaw_hasSeparatingSupport_of_argmin
    π h actions hActions ω pstar refLaw reg hSep

/--
Deployment-side implemented surrogate law on a finite learned high-score set.

This is the action-marginal scaffold used by the paper-facing amortized-surrogate theorem:
each action in the learned high-score set receives the reference mass `λ(a)` scaled by the
distinguished latent-class floor `ρ̂⋆` and by a deployment-side bonus floor. Outside the
high-score set the implemented law carries zero mass.
-/
def surrogateImplementedLaw
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoStar bonusFloor : Rat) : ActionLaw A where
  mass a := if a ∈ highScoreActions then rhoStar * bonusFloor * refLaw.mass a else 0
  support := highScoreActions.eraseDups
  support_complete := by
    intro a ha
    by_cases hMem : a ∈ highScoreActions
    · exact (List.mem_eraseDups).2 hMem
    · simp [hMem] at ha

/-- The paper's assumption `(A1)` in finite-list surrogate form. -/
def surrogateAssumptionA1 (rhoFloor rhoStar : Rat) : Prop :=
  rhoFloor ≤ rhoStar

/--
The paper's assumption `(A2)` in finite-list surrogate form: the learned high-score set
has positive reference mass under `λ`.
-/
def surrogateAssumptionA2
    (refLaw : ActionLaw A) (highScoreActions : List A) (lambdaFloor : Rat) : Prop :=
  lambdaFloor ≤ listWeightedSum highScoreActions refLaw.mass

/--
The paper's assumption `(A3)` in finite-list surrogate form: every action in the learned
high-score set is genuinely semantically separating for the true class.
-/
def surrogateAssumptionA3
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (highScoreActions : List A) : Prop :=
  ∀ a, a ∈ highScoreActions → U.isSeparatingAction π h ω pstar a

/--
Concrete deployment-side lower bound `δ_impl` for the implemented surrogate law.

The paper's displayed formula is `ρ̲ λ̲ exp(-(β/γ)(1-s0))`. In the concrete finite-list
scaffold we expose the same object as `rhoFloor * lambdaFloor * bonusFloor`, where
`bonusFloor` is the deployment-side lower envelope standing in for the Gibbs factor.
-/
def surrogateDeltaImpl
    (rhoFloor lambdaFloor bonusFloor : Rat) : Rat :=
  rhoFloor * lambdaFloor * bonusFloor

theorem surrogateImplementedLaw_mass_of_mem
    {highScoreActions : List A} {refLaw : ActionLaw A}
    {rhoStar bonusFloor : Rat} {a : A}
    (ha : a ∈ highScoreActions) :
    (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a =
      rhoStar * bonusFloor * refLaw.mass a := by
  simp [surrogateImplementedLaw, ha]

theorem surrogateImplementedLaw_mass_of_not_mem
    {highScoreActions : List A} {refLaw : ActionLaw A}
    {rhoStar bonusFloor : Rat} {a : A}
    (ha : a ∉ highScoreActions) :
    (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a = 0 := by
  simp [surrogateImplementedLaw, ha]

theorem listWeightedSum_mul_left
    (xs : List A) (c : Rat) (f : A → Rat) :
    listWeightedSum xs (fun a => c * f a) = c * listWeightedSum xs f := by
  induction xs with
  | nil =>
      simp [listWeightedSum]
  | cons x xs ih =>
      simp [listWeightedSum_cons, ih]
      ring

theorem listWeightedSum_congr
    (xs : List A) {f g : A → Rat}
    (hfg : ∀ a, a ∈ xs → f a = g a) :
    listWeightedSum xs f = listWeightedSum xs g := by
  induction xs with
  | nil =>
      simp [listWeightedSum]
  | cons x xs ih =>
      have hx : f x = g x := hfg x (by simp)
      have htail : ∀ a, a ∈ xs → f a = g a := by
        intro a ha
        exact hfg a (by simp [ha])
      simp [listWeightedSum_cons, hx, ih htail]

theorem surrogateImplementedLaw_weight_on_highScore
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoStar bonusFloor : Rat) :
    listWeightedSum highScoreActions
      (fun a => (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a) =
      rhoStar * bonusFloor * listWeightedSum highScoreActions refLaw.mass := by
  have hPointwise :
      ∀ a, a ∈ highScoreActions →
        (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor).mass a =
          rhoStar * bonusFloor * refLaw.mass a := by
    intro a ha
    simp [surrogateImplementedLaw, ha]
  rw [listWeightedSum_congr highScoreActions hPointwise]
  exact listWeightedSum_mul_left highScoreActions (rhoStar * bonusFloor) refLaw.mass

theorem separatingSupportWeight_eq_of_all_separating
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (highScoreActions : List A)
    (κ : ActionLaw A)
    (hA3 : surrogateAssumptionA3 U π h ω pstar highScoreActions) :
    separatingSupportWeight κ highScoreActions (U.separatingActionSet π h ω pstar) =
      listWeightedSum highScoreActions (fun a => κ.mass a) := by
  unfold separatingSupportWeight
  apply listWeightedSum_congr
  intro a ha
  have hSep : U.isSeparatingAction π h ω pstar a := hA3 a ha
  have hSepSet : U.separatingActionSet π h ω pstar a := hSep
  simp [hSepSet]

/--
Deployment-side support-floor theorem for the implemented surrogate law.

Under finite-list counterparts of the paper's assumptions `(A1)`--`(A3)`, the
implemented surrogate law carries at least `δ_impl` mass on genuinely separating actions.
-/
theorem surrogateImplementedLaw_hasSeparatingSupportFloor
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoFloor rhoStar lambdaFloor bonusFloor : Rat)
    (hRhoFloorPos : 0 < rhoFloor)
    (hLambdaFloorPos : 0 < lambdaFloor)
    (hBonusFloorPos : 0 < bonusFloor)
    (hA1 : surrogateAssumptionA1 rhoFloor rhoStar)
    (hA2 : surrogateAssumptionA2 refLaw highScoreActions lambdaFloor)
    (hA3 : surrogateAssumptionA3 U π h ω pstar highScoreActions) :
    hasSeparatingSupportFloor
      (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
      highScoreActions
      (U.separatingActionSet π h ω pstar)
      (surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor) := by
  unfold hasSeparatingSupportFloor surrogateDeltaImpl
  rw [separatingSupportWeight_eq_of_all_separating U π h ω pstar highScoreActions
    (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor) hA3]
  rw [surrogateImplementedLaw_weight_on_highScore highScoreActions refLaw rhoStar bonusFloor]
  have hRhoStarNonneg : 0 ≤ rhoStar := le_trans (le_of_lt hRhoFloorPos) hA1
  have hScaledRho :
      rhoFloor * lambdaFloor ≤ rhoStar * lambdaFloor := by
    exact mul_le_mul_of_nonneg_right hA1 (le_of_lt hLambdaFloorPos)
  have hScaledMass :
      rhoStar * lambdaFloor ≤ rhoStar * listWeightedSum highScoreActions refLaw.mass := by
    exact mul_le_mul_of_nonneg_left hA2 hRhoStarNonneg
  have hCombined :
      rhoFloor * lambdaFloor ≤ rhoStar * listWeightedSum highScoreActions refLaw.mass := by
    exact le_trans hScaledRho hScaledMass
  have hBonusScaled :
      bonusFloor * (rhoFloor * lambdaFloor) ≤
        bonusFloor * (rhoStar * listWeightedSum highScoreActions refLaw.mass) := by
    exact mul_le_mul_of_nonneg_left hCombined (le_of_lt hBonusFloorPos)
  have hReassoc :
      rhoFloor * lambdaFloor * bonusFloor ≤
        rhoStar * bonusFloor * listWeightedSum highScoreActions refLaw.mass := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hBonusScaled
  exact hReassoc

theorem surrogateImplementedLaw_hasSeparatingSupportOn
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : EncodedProgram A O)
    (highScoreActions : List A)
    (refLaw : ActionLaw A)
    (rhoFloor rhoStar lambdaFloor bonusFloor : Rat)
    (hRhoFloorPos : 0 < rhoFloor)
    (hLambdaFloorPos : 0 < lambdaFloor)
    (hBonusFloorPos : 0 < bonusFloor)
    (hA1 : surrogateAssumptionA1 rhoFloor rhoStar)
    (hA2 : surrogateAssumptionA2 refLaw highScoreActions lambdaFloor)
    (hA3 : surrogateAssumptionA3 U π h ω pstar highScoreActions) :
    hasSeparatingSupportOn
      (surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
      highScoreActions
      (U.separatingActionSet π h ω pstar) := by
  have hFloor :=
    U.surrogateImplementedLaw_hasSeparatingSupportFloor
      π h ω pstar highScoreActions refLaw
      rhoFloor rhoStar lambdaFloor bonusFloor
      hRhoFloorPos hLambdaFloorPos hBonusFloorPos hA1 hA2 hA3
  have hDeltaPos :
      0 < surrogateDeltaImpl rhoFloor lambdaFloor bonusFloor := by
    unfold surrogateDeltaImpl
    have hMul : 0 < rhoFloor * lambdaFloor := mul_pos hRhoFloorPos hLambdaFloorPos
    exact mul_pos hMul hBonusFloorPos
  rcases exists_supported_action_of_positiveSeparatingSupportFloor
      (κ := surrogateImplementedLaw highScoreActions refLaw rhoStar bonusFloor)
      (actions := highScoreActions)
      (S := U.separatingActionSet π h ω pstar)
      hDeltaPos hFloor with
    ⟨a, ha, hMass, hSep⟩
  exact ⟨a, ha, hMass, hSep⟩

end ConcretePrefixMachine

end

end SemanticConvergence
