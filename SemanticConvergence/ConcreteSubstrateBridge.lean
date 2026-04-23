import SemanticConvergence.ConcreteProbabilisticConvergence

namespace SemanticConvergence

universe u v

open Classical
open scoped BigOperators

noncomputable section

namespace ConcreteLaw

variable {α : Type u} [DecidableEq α]

/-- `ENNReal` mass function associated to a finite-support rational law. -/
def toENNRealMass (μ : ConcreteLaw α) (a : α) : ENNReal :=
  ENNReal.ofReal (μ.mass a : ℝ)

/--
The finite-support law can be transported to a PMF: masses are nonnegative and sum to one over
the deduplicated support.
-/
def HasPMFMass (μ : ConcreteLaw α) : Prop :=
  (∀ a, 0 ≤ μ.mass a) ∧ ((μ.support.toFinset.sum fun a => μ.toENNRealMass a) = 1)

theorem mass_eq_zero_of_not_mem_support (μ : ConcreteLaw α) {a : α}
    (ha : a ∉ μ.support.toFinset) :
    μ.mass a = 0 := by
  by_contra hne
  exact ha <| by simpa using μ.support_complete a hne

theorem toENNRealMass_eq_zero_of_not_mem_support (μ : ConcreteLaw α) {a : α}
    (ha : a ∉ μ.support.toFinset) :
    μ.toENNRealMass a = 0 := by
  simp [toENNRealMass, μ.mass_eq_zero_of_not_mem_support ha]

/-- Transport a finite-support rational law to a PMF once its probability constraints are given. -/
def toPMF (μ : ConcreteLaw α) (hμ : μ.HasPMFMass) : PMF α :=
  PMF.ofFinset (μ.toENNRealMass) μ.support.toFinset hμ.2
    (fun _ ha => μ.toENNRealMass_eq_zero_of_not_mem_support ha)

@[simp]
theorem toPMF_apply (μ : ConcreteLaw α) (hμ : μ.HasPMFMass) (a : α) :
    μ.toPMF hμ a = μ.toENNRealMass a :=
  rfl

theorem mem_support_toPMF_iff (μ : ConcreteLaw α) (hμ : μ.HasPMFMass) (a : α) :
    a ∈ (μ.toPMF hμ).support ↔ μ.mass a ≠ 0 := by
  constructor
  · intro ha
    have hpmf : μ.toPMF hμ a ≠ 0 := (PMF.mem_support_iff _ _).1 ha
    have hnonneg := hμ.1 a
    by_contra hmass
    apply hpmf
    simp [ConcreteLaw.toPMF, ConcreteLaw.toENNRealMass, hmass]
  · intro hmass
    have hnonneg := hμ.1 a
    have hmassENN : μ.toENNRealMass a ≠ 0 := by
      intro hzero
      apply hmass
      have hnonneg_real : (0 : ℝ) ≤ μ.mass a := by
        exact_mod_cast hnonneg
      have hle_real : (μ.mass a : ℝ) ≤ 0 := by
        simpa [ConcreteLaw.toENNRealMass] using (ENNReal.ofReal_eq_zero.mp hzero)
      have hzero_real : (μ.mass a : ℝ) = 0 := le_antisymm hle_real hnonneg_real
      exact_mod_cast hzero_real
    exact (PMF.mem_support_iff _ _).2 <| by
      simpa [ConcreteLaw.toPMF] using hmassENN

end ConcreteLaw

namespace ConcreteBridge

variable {A : Type u} {O : Type v}

/-- Forget a length-indexed history down to the list-based countable-history substrate. -/
def countHistOfHist {t : Nat} (h : Hist A O t) : CountableConcrete.CountHist A O :=
  List.ofFn h

@[simp]
theorem countHistOfHist_length {t : Nat} (h : Hist A O t) :
    (countHistOfHist h).length = t := by
  simp [countHistOfHist]

/-- Rebuild a length-indexed history from a list-based countable history. -/
def histOfCountHist (h : CountableConcrete.CountHist A O) : Hist A O h.length :=
  fun i => h[i]

@[simp]
theorem countHistOfHist_histOfCountHist (h : CountableConcrete.CountHist A O) :
    countHistOfHist (histOfCountHist h) = h := by
  apply List.ext_getElem
  · simp [countHistOfHist]
  · intro i hi₁ hi₂
    simp [countHistOfHist, histOfCountHist, List.getElem_ofFn]

@[simp]
theorem histOfCountHist_countHistOfHist_apply {t : Nat} (h : Hist A O t) (i : Fin t) :
    histOfCountHist (countHistOfHist h)
      (Fin.cast (by simp [countHistOfHist]) i) = h i := by
  simp [histOfCountHist, countHistOfHist, List.getElem_ofFn]

@[simp]
theorem countHistOfHist_snoc {t : Nat} (h : Hist A O t) (e : HistEvent A O) :
    countHistOfHist (snoc h e) =
      CountableConcrete.appendEvent (countHistOfHist h) e := by
  rw [countHistOfHist, List.ofFn_add]
  congr
  · funext i
    simp [snoc]
  · have htail :
        List.ofFn (fun i : Fin 1 => snoc h e (Fin.natAdd t i)) = [e] := by
      simpa [snoc] using
        (List.ofFn_succ (f := fun i : Fin 1 => snoc h e (Fin.natAdd t i)))
    simpa using htail

end ConcreteBridge

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [Encodable A] [Encodable O]

/-- Probability-side well-formedness of a concrete policy. -/
def ProbabilisticPolicy (π : ConcretePolicy A O) : Prop :=
  ∀ t h, ConcreteLaw.HasPMFMass (π t h)

/-- Probability-side well-formedness of a concrete kernel/program. -/
def ProbabilisticKernel (κ : ConcreteKernel A O) : Prop :=
  ∀ t h a, ConcreteLaw.HasPMFMass (κ t h a)

/-- Transport a concrete policy to the countable PMF-based history substrate. -/
def toCountablePolicy (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π) :
    CountableConcrete.CountablePolicy A O :=
  fun h => (π h.length (ConcreteBridge.histOfCountHist h)).toPMF (hπ _ _)

/-- Transport a concrete kernel/program to the countable PMF-based history substrate. -/
def toCountableKernel (κ : ConcreteKernel A O) (hκ : ProbabilisticKernel κ) :
    CountableConcrete.CountableKernel A O :=
  fun h a => (κ h.length (ConcreteBridge.histOfCountHist h) a).toPMF (hκ _ _ _)

@[simp]
theorem toCountablePolicy_apply (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (h : CountableConcrete.CountHist A O) (a : A) :
    toCountablePolicy π hπ h a =
      ConcreteLaw.toENNRealMass (π h.length (ConcreteBridge.histOfCountHist h)) a :=
  rfl

@[simp]
theorem toCountableKernel_apply (κ : ConcreteKernel A O) (hκ : ProbabilisticKernel κ)
    (h : CountableConcrete.CountHist A O) (a : A) (o : O) :
    toCountableKernel κ hκ h a o =
      ConcreteLaw.toENNRealMass (κ h.length (ConcreteBridge.histOfCountHist h) a) o :=
  rfl

theorem mem_support_toCountablePolicy_iff
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (h : CountableConcrete.CountHist A O) (a : A) :
    a ∈ (toCountablePolicy π hπ h).support ↔
      (π h.length (ConcreteBridge.histOfCountHist h)).mass a ≠ 0 := by
  simpa [toCountablePolicy] using
    ConcreteLaw.mem_support_toPMF_iff (π h.length (ConcreteBridge.histOfCountHist h)) (hπ _ _) a

theorem mem_support_toCountableKernel_iff
    (κ : ConcreteKernel A O) (hκ : ProbabilisticKernel κ)
    (h : CountableConcrete.CountHist A O) (a : A) (o : O) :
    o ∈ (toCountableKernel κ hκ h a).support ↔
      (κ h.length (ConcreteBridge.histOfCountHist h) a).mass o ≠ 0 := by
  simpa [toCountableKernel] using
    ConcreteLaw.mem_support_toPMF_iff
      (κ h.length (ConcreteBridge.histOfCountHist h) a) (hκ _ _ _) o

/-- Canonical deduplicated code enumeration used by the countable bridge machine. -/
def codeList (U : ConcretePrefixMachine A O) : List BitCode :=
  U.codes.toFinset.toList

theorem codeList_nodup (U : ConcretePrefixMachine A O) :
    U.codeList.Nodup := by
  simpa [codeList] using U.codes.toFinset.nodup_toList

theorem mem_codeList (U : ConcretePrefixMachine A O) {c : BitCode} :
    c ∈ U.codeList ↔ c ∈ U.codes := by
  simp [codeList]

/-- A concrete machine program viewed as an encoded countable program. -/
def toCountableEncodedProgram (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : U.Program) :
    CountableConcrete.CountableEncodedProgram A O where
  code := p.1
  kernel := toCountableKernel (U.programSemantics p) (by
    simpa [ConcretePrefixMachine.programSemantics] using hSem p.1 p.2)

@[simp]
theorem toCountableEncodedProgram_code (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : U.Program) :
    (U.toCountableEncodedProgram hSem p).code = p.1 :=
  rfl

/-- The countable-prefix-machine image of a finite concrete prefix machine. -/
def toCountablePrefixMachine (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc)) :
    CountableConcrete.CountablePrefixMachine A O where
  codeAt n := U.codeList[n]?
  prefixFree := by
    intro m n cm cn hmn hm hn
    rcases (List.getElem?_eq_some_iff).1 hm with ⟨hm_lt, hcm⟩
    rcases (List.getElem?_eq_some_iff).1 hn with ⟨hn_lt, hcn⟩
    have hneq : cm ≠ cn := by
      intro hEq
      have hsame : U.codeList[m] = U.codeList[n] := by
        rw [hcm, hcn, hEq]
      have hNodup : U.codeList.Nodup := by
        simpa [codeList] using (U.codes.toFinset.nodup_toList)
      exact hmn <| (hNodup.getElem_inj_iff).1 hsame
    have hcm_mem : cm ∈ U.codes := by
      have : cm ∈ U.codeList := by
        rw [← hcm]
        exact List.getElem_mem hm_lt
      exact (U.mem_codeList).1 this
    have hcn_mem : cn ∈ U.codes := by
      have : cn ∈ U.codeList := by
        rw [← hcn]
        exact List.getElem_mem hn_lt
      exact (U.mem_codeList).1 this
    exact U.prefixFree hcm_mem hcn_mem hneq
  semantics := by
    intro n c hc
    have hc_mem_codeList : c ∈ U.codeList := by
      rw [List.mem_iff_getElem?]
      exact ⟨n, hc⟩
    have hc_mem_codes : c ∈ U.codes := (U.mem_codeList).1 hc_mem_codeList
    exact toCountableKernel (U.semantics c hc_mem_codes) (hSem c hc_mem_codes)

/-- Concrete programs viewed as bridged countable-machine programs. -/
def toCountableProgram (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : U.Program) :
    (U.toCountablePrefixMachine hSem).Program :=
  ⟨U.codeList.idxOf p.1, ⟨p.1, by
    simpa [ConcretePrefixMachine.toCountablePrefixMachine] using
      (List.getElem?_idxOf ((U.mem_codeList).2 p.2))
  ⟩⟩

/-- Bridged countable-machine programs pulled back to the original concrete program domain. -/
def toConcreteProgram (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : (U.toCountablePrefixMachine hSem).Program) :
    U.Program := by
  let c := (U.toCountablePrefixMachine hSem).programCode p
  have hc_mem_codeList : c ∈ U.codeList := by
    rw [List.mem_iff_getElem?]
    exact ⟨p.1, by
      simpa [ConcretePrefixMachine.toCountablePrefixMachine] using
        (U.toCountablePrefixMachine hSem).programCode_spec p⟩
  exact ⟨c, (U.mem_codeList).1 hc_mem_codeList⟩

@[simp]
theorem toCountableProgram_programCode (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : U.Program) :
    (U.toCountablePrefixMachine hSem).programCode (U.toCountableProgram hSem p) = p.1 := by
  have hcode :
      (U.toCountablePrefixMachine hSem).codeAt (U.codeList.idxOf p.1) = some p.1 := by
    simpa [ConcretePrefixMachine.toCountablePrefixMachine] using
      (List.getElem?_idxOf ((U.mem_codeList).2 p.2))
  have hspec :
      (U.toCountablePrefixMachine hSem).codeAt (U.codeList.idxOf p.1) =
        some ((U.toCountablePrefixMachine hSem).programCode (U.toCountableProgram hSem p)) := by
    simpa [toCountableProgram] using
      (U.toCountablePrefixMachine hSem).programCode_spec (U.toCountableProgram hSem p)
  exact (Option.some.inj (hcode.symm.trans hspec)).symm

@[simp]
theorem toConcreteProgram_code (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : (U.toCountablePrefixMachine hSem).Program) :
    (U.toConcreteProgram hSem p).1 = (U.toCountablePrefixMachine hSem).programCode p := by
  simp [toConcreteProgram]

@[simp]
theorem toConcreteProgram_toCountableProgram (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : U.Program) :
    U.toConcreteProgram hSem (U.toCountableProgram hSem p) = p := by
  apply Subtype.ext
  simp [toConcreteProgram, U.toCountableProgram_programCode hSem p]

@[simp]
theorem toCountableProgram_toConcreteProgram (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : (U.toCountablePrefixMachine hSem).Program) :
    U.toCountableProgram hSem (U.toConcreteProgram hSem p) = p := by
  apply Subtype.ext
  have hspec := (U.toCountablePrefixMachine hSem).programCode_spec p
  rcases (List.getElem?_eq_some_iff).1 (by
      simpa [ConcretePrefixMachine.toCountablePrefixMachine] using hspec) with ⟨hp_lt, hp_code⟩
  simpa [toCountableProgram, toConcreteProgram, hp_code] using
    U.codeList_nodup.idxOf_getElem p.1 hp_lt

/-- The bridged concrete and countable machine domains are equivalent. -/
def programEquiv (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc)) :
    U.Program ≃ (U.toCountablePrefixMachine hSem).Program where
  toFun := U.toCountableProgram hSem
  invFun := U.toConcreteProgram hSem
  left_inv := U.toConcreteProgram_toCountableProgram hSem
  right_inv := U.toCountableProgram_toConcreteProgram hSem

/--
Observer transport along the finite-to-countable bridge. On programs in the image of the
bridge machine, this agrees with the original concrete observer; outside the bridge image it
returns `none`.
-/
def liftObserver (U : ConcretePrefixMachine A O)
    (ω : Observer (EncodedProgram A O)) :
    Observer (CountableConcrete.CountableEncodedProgram A O) where
  Ω := Option ω.Ω
  view p := if hc : p.code ∈ U.codes then
      some (ω.view ⟨p.code, U.semantics p.code hc⟩)
    else
      none

@[simp]
theorem liftObserver_view_toCountableEncodedProgram
    (U : ConcretePrefixMachine A O)
    (ω : Observer (EncodedProgram A O))
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : U.Program) :
    (U.liftObserver ω).view (U.toCountableEncodedProgram hSem p) =
      some (ω.view (U.toEncodedProgram p)) := by
  simp [liftObserver, toCountableEncodedProgram, ConcretePrefixMachine.toEncodedProgram,
    ConcretePrefixMachine.programSemantics, p.2]

theorem liftObserver_sameView_toCountableEncodedProgram_iff
    (U : ConcretePrefixMachine A O)
    (ω : Observer (EncodedProgram A O))
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p q : U.Program) :
    (U.liftObserver ω).view (U.toCountableEncodedProgram hSem p) =
      (U.liftObserver ω).view (U.toCountableEncodedProgram hSem q) ↔
        ω.view (U.toEncodedProgram p) = ω.view (U.toEncodedProgram q) := by
  constructor
  · intro hView
    have hSome := hView
    rw [U.liftObserver_view_toCountableEncodedProgram ω hSem p,
      U.liftObserver_view_toCountableEncodedProgram ω hSem q] at hSome
    exact Option.some.inj hSome
  · intro hView
    rw [U.liftObserver_view_toCountableEncodedProgram ω hSem p,
      U.liftObserver_view_toCountableEncodedProgram ω hSem q]
    exact congrArg some hView

/-- Concrete full-history prefix cut out of a realized countable trajectory. -/
def prefixFullHist (ξ : CountableConcrete.CountHist A O) (n : Nat) : FullHist A O :=
  asFullHist (ConcreteBridge.histOfCountHist
    (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n))

@[simp]
theorem prefixFullHist_hist_length (ξ : CountableConcrete.CountHist A O) (n : Nat) :
    (prefixFullHist ξ n).1 =
      (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n).length := by
  rfl

/--
`Rat`-valued prefixwise residual decay on the deterministic substrate transports to the
`ENNReal` codomain used by the countable probabilistic wrapper, provided the concrete
residual odds are nonnegative on the relevant prefixes.
-/
theorem prefixwiseResidualDecayENNReal_of_rat
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O)
    (ω : Observer (EncodedProgram A O))
    (pstar : U.Program)
    (δ : Rat)
    (ξ : CountableConcrete.CountHist A O)
    (n : Nat)
    (hStep :
      U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω (U.toEncodedProgram pstar) ≤
        posteriorDecayFactor δ *
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω (U.toEncodedProgram pstar)) :
    ENNReal.ofReal
        (U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
          (U.toEncodedProgram pstar) : ℝ) ≤
      CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ *
        ENNReal.ofReal
          (U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
            (U.toEncodedProgram pstar) : ℝ) := by
  have hStepReal : (U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
      (U.toEncodedProgram pstar) : ℝ) ≤
      (posteriorDecayFactor δ *
        U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
          (U.toEncodedProgram pstar) : Rat) := by
    exact_mod_cast hStep
  have hFacNonnegReal : (0 : ℝ) ≤ posteriorDecayFactor δ := by
    exact_mod_cast posteriorDecayFactor_nonneg δ
  have hEqFac :
      CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ =
        ENNReal.ofReal (posteriorDecayFactor δ : ℝ) := rfl
  calc
    ENNReal.ofReal
        (U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
          (U.toEncodedProgram pstar) : ℝ) ≤
      ENNReal.ofReal
        ((posteriorDecayFactor δ *
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
            (U.toEncodedProgram pstar) : Rat) : ℝ) := by
      exact ENNReal.ofReal_le_ofReal hStepReal
    _ = ENNReal.ofReal
          ((posteriorDecayFactor δ : ℝ) *
            (U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
              (U.toEncodedProgram pstar) : ℝ)) := by
      norm_num
    _ = CountableConcrete.CountablePrefixMachine.posteriorDecayFactorENNReal δ *
        ENNReal.ofReal
          (U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
            (U.toEncodedProgram pstar) : ℝ) := by
      rw [hEqFac, ENNReal.ofReal_mul hFacNonnegReal]

/--
Constructor theorem for the probabilistic supportwise residual-contraction witness on the
bridged countable machine. The actual contraction is supplied on the deterministic
prefix-history side and transported across an explicit residual-process bridge.
-/
theorem hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
    (hBridge :
      ∀ ξ n,
        (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
            (toCountablePolicy π hπ) (U.liftObserver ω)
            (U.toCountableEncodedProgram hSem pstar) n ξ =
          ENNReal.ofReal
            (U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
              (U.toEncodedProgram pstar) : ℝ))
    (hStep :
      ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
        (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
        ∀ n, n < T →
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
              (U.toEncodedProgram pstar) ≤
            posteriorDecayFactor δ *
              U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
                (U.toEncodedProgram pstar)) :
    (U.toCountablePrefixMachine hSem).HasSupportwiseResidualContractionWitness
      (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) (U.liftObserver ω)
      (U.toCountableEncodedProgram hSem pstar) δ T := by
  intro ξ hξ n hn
  refine ⟨(U.toCountablePrefixMachine hSem).residualObserverFiberProcess
      (toCountablePolicy π hπ) (U.liftObserver ω)
      (U.toCountableEncodedProgram hSem pstar) (n + 1) ξ, rfl, ?_⟩
  rw [hBridge ξ (n + 1), hBridge ξ n]
  exact U.prefixwiseResidualDecayENNReal_of_rat π ω pstar δ ξ n (hStep ξ hξ n hn)

end ConcretePrefixMachine

end

end SemanticConvergence
