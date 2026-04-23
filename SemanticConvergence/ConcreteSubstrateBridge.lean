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

@[simp]
theorem appendEvent_eq_appendEvent_iff
    (h₁ h₂ : CountableConcrete.CountHist A O) (e₁ e₂ : HistEvent A O) :
    CountableConcrete.appendEvent h₁ e₁ = CountableConcrete.appendEvent h₂ e₂ ↔
      h₁ = h₂ ∧ e₁ = e₂ := by
  constructor
  · intro hEq
    have hDrop :
        List.dropLast (CountableConcrete.appendEvent h₁ e₁) =
          List.dropLast (CountableConcrete.appendEvent h₂ e₂) := by
      exact congrArg List.dropLast hEq
    have hLast :
        List.getLast? (CountableConcrete.appendEvent h₁ e₁) =
          List.getLast? (CountableConcrete.appendEvent h₂ e₂) := by
      exact congrArg List.getLast? hEq
    constructor
    · simpa [CountableConcrete.appendEvent] using hDrop
    · simpa [CountableConcrete.appendEvent] using hLast
  · rintro ⟨rfl, rfl⟩
    rfl

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

theorem countHistOfHist_injective {t : Nat} {h₁ h₂ : Hist A O t}
    (hEq : countHistOfHist h₁ = countHistOfHist h₂) :
    h₁ = h₂ := by
  funext i
  have hNth := congrArg (fun l => l[i.1]?) hEq
  simpa [countHistOfHist] using hNth

theorem hist_cast_apply {t u : Nat} (hEq : t = u) (h : Hist A O t) (i : Fin u) :
    cast (by cases hEq; rfl : Hist A O t = Hist A O u) h i =
      h (Fin.cast hEq.symm i) := by
  cases hEq
  rfl

theorem snoc_eq_snoc_iff {t : Nat} (h₁ h₂ : Hist A O t)
    (e₁ e₂ : HistEvent A O) :
    snoc h₁ e₁ = snoc h₂ e₂ ↔ h₁ = h₂ ∧ e₁ = e₂ := by
  constructor
  · intro hEq
    have hCount :
        CountableConcrete.appendEvent (countHistOfHist h₁) e₁ =
          CountableConcrete.appendEvent (countHistOfHist h₂) e₂ := by
      simpa [countHistOfHist_snoc] using congrArg countHistOfHist hEq
    rcases (appendEvent_eq_appendEvent_iff _ _ _ _).1 hCount with
      ⟨hHist, hEvent⟩
    exact ⟨countHistOfHist_injective hHist, hEvent⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem hist_snoc_decompose {t : Nat} (h : Hist A O (t + 1)) :
    snoc (fun i : Fin t => h (Fin.castSucc i)) (h ⟨t, Nat.lt_succ_self t⟩) = h := by
  funext i
  by_cases hi : i.val < t
  · simp [snoc, hi]
  · have hEqVal : i.val = t := by omega
    have hEq : i = ⟨t, Nat.lt_succ_self t⟩ := by
      apply Fin.ext
      simpa using hEqVal
    simp [snoc, hEq]

end ConcreteBridge

theorem listWeightedSum_eq_if_mem {α : Type u} [DecidableEq α]
    (xs : List α) (hxs : xs.Nodup) (a : α) (f : α → Rat) :
    listWeightedSum xs (fun x => if x = a then f x else 0) =
      if a ∈ xs then f a else 0 := by
  induction xs with
  | nil =>
      simp [listWeightedSum]
  | cons x xs ih =>
      have hxs' : xs.Nodup := (List.nodup_cons.1 hxs).2
      by_cases hx : x = a
      · subst hx
        have hnot : x ∉ xs := (List.nodup_cons.1 hxs).1
        rw [listWeightedSum_cons, if_pos rfl]
        rw [ih hxs']
        rw [if_neg hnot]
        simp
      · rw [listWeightedSum_cons, if_neg hx]
        rw [ih hxs']
        have hx' : ¬ a = x := by simpa [eq_comm] using hx
        simp [hx']

namespace CountableConcrete

variable {A : Type u} {O : Type v}
variable [Encodable A] [Encodable O]

theorem histPMF_appendEvent
    (π : CountablePolicy A O) (κ : CountableKernel A O)
    (t : Nat) (h : CountHist A O) (a : A) (o : O) :
    histPMF π κ (t + 1) (appendEvent h (a, o)) =
      histPMF π κ t h * π h a * κ h a o := by
  simp [histPMF, PMF.bind_apply, ConcreteBridge.appendEvent_eq_appendEvent_iff]
  rw [ENNReal.tsum_eq_add_tsum_ite h]
  simp only [eq_self_iff_true, true_and]
  have hSumAZero :
      ∀ x : CountHist A O, x ≠ h →
        (∑' (a₁ : A), (π x) a₁ *
            ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) = 0 := by
    intro x hx
    rw [ENNReal.tsum_eq_zero]
    intro a₁
    have hSumO :
        (∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro o₁
      have hx' : ¬ h = x := by
        intro hEq
        exact hx hEq.symm
      simp [hx']
    simp [hSumO]
  have hOuter :
      (∑' (x : CountHist A O), if x = h then 0 else
          histPMF π κ t x *
            ∑' (a₁ : A), (π x) a₁ *
              ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : x = h
    · simp [hx]
    · simp [hx, hSumAZero x hx]
  have hOuter' :
      ((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
        ∑' (x : CountHist A O), if x = h then 0 else
          histPMF π κ t x *
            ∑' (a₁ : A), (π x) a₁ *
              ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) =
        histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0 := by
    simpa [hOuter]
  have hOuter'' :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) =
        histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0 := by
    simpa using hOuter'
  have hSumOMid :
      ∀ x : A, x ≠ a →
        (∑' (o₁ : O), if a = x ∧ o = o₁ then (κ h x) o₁ else 0) = 0 := by
    intro x hx
    rw [ENNReal.tsum_eq_zero]
    intro o₁
    have hx' : ¬ a = x := by
      intro hEq
      exact hx hEq.symm
    simp [hx']
  have hMidEval :
      (∑' (a₁ : A), (π h) a₁ *
          ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) =
        π h a * κ h a o := by
    rw [ENNReal.tsum_eq_add_tsum_ite a]
    have hMid :
        (∑' (x : A), if x = a then 0 else
            (π h) x * ∑' (o₁ : O), if a = x ∧ o = o₁ then (κ h x) o₁ else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro x
      by_cases hx : x = a
      · simp [hx]
      · simp [hx, hSumOMid x hx]
    rw [hMid, add_zero]
    rw [ENNReal.tsum_eq_add_tsum_ite o]
    have hInnerEval :
        (∑' (x : O), if x = o then 0 else if a = a ∧ o = x then (κ h a) x else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro x
      by_cases hx : x = o
      · simp [hx]
      · have hx' : ¬ o = x := by
          intro hEq
          exact hx hEq.symm
        simp [hx, hx']
    rw [hInnerEval, add_zero]
    simp
  have hOuterGoal :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) =
        histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0 := by
    simpa using hOuter''
  have hOuterSimple :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) =
        histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0 := by
    simpa using hOuterGoal
  have hCollapse :
      (histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) =
        histPMF π κ t h * π h a * κ h a o := by
    calc
      (histPMF π κ t h *
          ∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) =
        histPMF π κ t h *
          (∑' (a₁ : A), (π h) a₁ *
            ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) := by
        simp [mul_assoc]
      _ = histPMF π κ t h * (π h a * κ h a o) := by rw [hMidEval]
      _ = histPMF π κ t h * π h a * κ h a o := by simp [mul_assoc]
  have hStartSimplify :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) =
        (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if h = h ∧ a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O), if x = h then 0 else
            histPMF π κ t x *
              ∑' (a₁ : A), (π x) a₁ *
                ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0) : ENNReal) := by
    simp [true_and]
  have hDecider :
      (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O),
            @ite ENNReal (x = h) (propDecidable (x = h)) 0
              (histPMF π κ t x *
                ∑' (a₁ : A), (π x) a₁ *
                  ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0)) : ENNReal) =
        (((histPMF π κ t h *
            ∑' (a₁ : A), (π h) a₁ *
              ∑' (o₁ : O), if a = a₁ ∧ o = o₁ then (κ h a₁) o₁ else 0) +
          ∑' (x : CountHist A O),
            @ite ENNReal (x = h) (instDecidableEqList x h) 0
              (histPMF π κ t x *
                ∑' (a₁ : A), (π x) a₁ *
                  ∑' (o₁ : O), if h = x ∧ a = a₁ ∧ o = o₁ then (κ x a₁) o₁ else 0)) : ENNReal) := by
    congr 1
    refine tsum_congr (fun x => ?_)
    by_cases hx : x = h <;> simp [hx]
  exact hDecider.trans (hStartSimplify.trans (hOuterSimple.trans hCollapse))

end CountableConcrete

namespace ConcretePrefixMachine

variable {A : Type u} {O : Type v}
variable [DecidableEq A] [DecidableEq O] [Encodable A] [Encodable O]

/-- Probability-side well-formedness of a concrete policy. -/
def ProbabilisticPolicy (π : ConcretePolicy A O) : Prop :=
  ∀ t h, ConcreteLaw.HasPMFMass (π t h)

/-- Probability-side well-formedness of a concrete kernel/program. -/
def ProbabilisticKernel (κ : ConcreteKernel A O) : Prop :=
  ∀ t h a, ConcreteLaw.HasPMFMass (κ t h a)

/-- The concrete machine-domain code list is duplicate-free. -/
def CodesNodup (U : ConcretePrefixMachine A O) : Prop :=
  U.codes.Nodup

/-- Every concrete policy support list is duplicate-free. -/
def PolicySupportNodup (π : ConcretePolicy A O) : Prop :=
  ∀ t h, (π t h).support.Nodup

/-- Every concrete kernel support list is duplicate-free. -/
def KernelSupportNodup (κ : ConcreteKernel A O) : Prop :=
  ∀ t h a, (κ t h a).support.Nodup

theorem mass_eq_if_mem_support {α : Type u} [DecidableEq α]
    (μ : ConcreteLaw α) (a : α) :
    (if a ∈ μ.support then μ.mass a else 0) = μ.mass a := by
  by_cases ha : a ∈ μ.support
  · simp [ha]
  · by_cases hmass : μ.mass a = 0
    · simp [ha, hmass]
    · exact (ha (μ.support_complete a hmass)).elim

theorem allPrograms_nodup (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup) :
    U.allPrograms.Nodup := by
  simpa [ConcretePrefixMachine.allPrograms] using hCodes.attach

/-- Finiteness of the concrete program domain when the concrete code list is duplicate-free. -/
@[reducible] def programFintype (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup) : Fintype U.Program where
  elems := U.allPrograms.toFinset
  complete := by
    intro p
    simpa [ConcretePrefixMachine.allPrograms] using U.mem_allPrograms p

theorem eraseDups_nodup {α : Type u} [BEq α] [LawfulBEq α] :
    ∀ xs : List α, xs.eraseDups.Nodup
  | [] => by
      simp
  | a :: as => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.2 ?_
      constructor
      · intro ha
        have hmem : a ∈ List.filter (fun b => !b == a) as := (List.mem_eraseDups).1 ha
        have hneq : !(a == a) = true := by
          simpa using (List.mem_filter.1 hmem).2
        simp at hneq
      · exact eraseDups_nodup _
termination_by xs => xs.length
decreasing_by
  simpa using (List.length_filter_le (fun b => !b == a) as)

theorem listWeightedSum_div_right {α : Type u}
    (xs : List α) (f : α → Rat) (c : Rat) :
    listWeightedSum xs (fun a => f a / c) = listWeightedSum xs f / c := by
  induction xs with
  | nil =>
      simp [listWeightedSum]
  | cons x xs ih =>
      simp [listWeightedSum_cons, ih]
      ring

theorem listWeightedSum_filter_eq {α : Type u}
    (xs : List α) (C : α → Prop) [DecidablePred C] (f : α → Rat) :
    listWeightedSum (xs.filter C) f =
      listWeightedSum xs (fun a => if C a then f a else 0) := by
  induction xs with
  | nil =>
      simp [listWeightedSum]
  | cons x xs ih =>
      by_cases hC : C x
      · simp [listWeightedSum_cons, hC, ih]
      · simp [listWeightedSum_cons, hC, ih]

theorem listWeightedSum_filter_cond_eq {α : Type u}
    (xs : List α) (C : α → Prop) [DecidablePred C] (f : α → Rat) :
    listWeightedSum (xs.filter C) (fun a => if C a then f a else 0) =
      listWeightedSum (xs.filter C) f := by
  induction xs with
  | nil =>
      simp [listWeightedSum]
  | cons x xs ih =>
      by_cases hC : C x
      · simp [listWeightedSum_cons, hC, ih]
      · simp [listWeightedSum_cons, hC, ih]

theorem finset_sum_toFinset_eq_listWeightedSum {α : Type u} [DecidableEq α]
    (xs : List α) (hxs : xs.Nodup) (f : α → Rat) :
    Finset.sum xs.toFinset f = listWeightedSum xs f := by
  induction xs with
  | nil =>
      simp [listWeightedSum]
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.1 hxs).1
      have hxs' : xs.Nodup := (List.nodup_cons.1 hxs).2
      simp [List.toFinset_cons, hx, listWeightedSum_cons, ih hxs']

theorem sum_programFintype_eq_listWeightedSum
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (f : U.Program → Rat) :
    letI := U.programFintype hCodes
    (∑ p : U.Program, f p) = listWeightedSum U.allPrograms f := by
  letI := U.programFintype hCodes
  simpa [programFintype] using
    (finset_sum_toFinset_eq_listWeightedSum (xs := U.allPrograms)
      (hxs := U.allPrograms_nodup hCodes) (f := f))

theorem histLaw_support_nodup
    (π : ConcretePolicy A O) (κ : ConcreteKernel A O) :
    ∀ t, (histLaw π κ t).support.Nodup
  | 0 => by
      simp [histLaw, ConcreteLaw.pure]
  | t + 1 => by
      let l :=
        List.flatMap
          (fun h =>
            (List.flatMap
              (fun a => (List.map (fun o => snoc h (a, o)) (κ t h a).support).eraseDups)
              (π t h).support).eraseDups)
          (histLaw π κ t).support
      simpa [l, histLaw, ConcreteLaw.bind, ConcreteLaw.map] using eraseDups_nodup l

theorem map_snoc_mass
    (κ : ConcreteKernel A O) (hκN : KernelSupportNodup κ)
    (t : Nat) (h h' : Hist A O t) (a a' : A) (o : O) :
    (ConcreteLaw.map (fun o' => snoc h' (a', o')) (κ t h' a')).mass (snoc h (a, o)) =
      if h' = h ∧ a' = a then (κ t h a).mass o else 0 := by
  by_cases hh : h' = h ∧ a' = a
  · rcases hh with ⟨hhHist, hhAct⟩
    subst h'
    subst a'
    have hsum :
        listWeightedSum (κ t h a).support
            (fun o' => if snoc h (a, o') = snoc h (a, o) then (κ t h a).mass o' else 0) =
          if o ∈ (κ t h a).support then (κ t h a).mass o else 0 := by
      simpa [ConcreteBridge.snoc_eq_snoc_iff] using
        (listWeightedSum_eq_if_mem ((κ t h a).support) (hκN t h a) o (κ t h a).mass)
    simpa [ConcreteLaw.map, mass_eq_if_mem_support] using hsum
  · have hzero :
        ∀ o' : O,
          (if snoc h' (a', o') = snoc h (a, o) then (κ t h' a').mass o' else 0) = 0 := by
      intro o'
      by_cases hEq : snoc h' (a', o') = snoc h (a, o)
      · rcases (ConcreteBridge.snoc_eq_snoc_iff _ _ _ _).1 hEq with ⟨hhHist, hhActObs⟩
        cases hhActObs
        exact (hh ⟨hhHist, rfl⟩).elim
      · simp [hEq]
    calc
      (ConcreteLaw.map (fun o' => snoc h' (a', o')) (κ t h' a')).mass (snoc h (a, o)) =
        listWeightedSum (κ t h' a').support (fun _ => (0 : Rat)) := by
          refine congrArg (listWeightedSum (κ t h' a').support) ?_
          funext o'
          exact hzero o'
      _ = 0 := by
          simp [listWeightedSum]
      _ = if h' = h ∧ a' = a then (κ t h a).mass o else 0 := by
          simp [hh]

theorem actionStep_snoc_mass
    (π : ConcretePolicy A O) (κ : ConcreteKernel A O)
    (hπN : PolicySupportNodup π) (hκN : KernelSupportNodup κ)
    (t : Nat) (h h' : Hist A O t) (a : A) (o : O) :
    (ConcreteLaw.bind (π t h') (fun a' =>
        ConcreteLaw.map (fun o' => snoc h' (a', o')) (κ t h' a'))).mass (snoc h (a, o)) =
      if h' = h then (π t h).mass a * (κ t h a).mass o else 0 := by
  by_cases hh : h' = h
  · subst h'
    have hsum :
        listWeightedSum (π t h).support
            (fun a' =>
              if a' = a then (π t h).mass a' * (κ t h a).mass o else 0) =
          if a ∈ (π t h).support then (π t h).mass a * (κ t h a).mass o else 0 := by
      simpa using
        (listWeightedSum_eq_if_mem ((π t h).support) (hπN t h) a
          (fun a' => (π t h).mass a' * (κ t h a).mass o))
    have hrewrite :
        listWeightedSum (π t h).support
            (fun a' =>
              (π t h).mass a' *
                (ConcreteLaw.map (fun o' => snoc h (a', o')) (κ t h a')).mass (snoc h (a, o))) =
          listWeightedSum (π t h).support
            (fun a' =>
              if a' = a then (π t h).mass a' * (κ t h a).mass o else 0) := by
      refine congrArg (listWeightedSum (π t h).support) ?_
      funext a'
      by_cases ha' : a' = a
      · subst ha'
        simp [map_snoc_mass, hκN]
      · simp [map_snoc_mass, hκN, ha']
    have hmem :
        (if a ∈ (π t h).support then (π t h).mass a * (κ t h a).mass o else 0) =
          (π t h).mass a * (κ t h a).mass o := by
      by_cases ha : a ∈ (π t h).support
      · simp [ha]
      · have hmass : (π t h).mass a = 0 := by
          by_cases hne : (π t h).mass a = 0
          · exact hne
          · exact (ha ((π t h).support_complete a hne)).elim
        simp [ha, hmass]
    calc
      (ConcreteLaw.bind (π t h) (fun a' =>
          ConcreteLaw.map (fun o' => snoc h (a', o')) (κ t h a'))).mass (snoc h (a, o)) =
        listWeightedSum (π t h).support
          (fun a' =>
            (π t h).mass a' *
              (ConcreteLaw.map (fun o' => snoc h (a', o')) (κ t h a')).mass (snoc h (a, o))) := by
          rfl
      _ =
        listWeightedSum (π t h).support
          (fun a' =>
            if a' = a then (π t h).mass a' * (κ t h a).mass o else 0) := hrewrite
      _ = if a ∈ (π t h).support then (π t h).mass a * (κ t h a).mass o else 0 := hsum
      _ = (π t h).mass a * (κ t h a).mass o := hmem
      _ = if h = h then (π t h).mass a * (κ t h a).mass o else 0 := by
          simp
  · have hzero :
        ∀ a' : A,
          (π t h').mass a' *
              (ConcreteLaw.map (fun o' => snoc h' (a', o')) (κ t h' a')).mass (snoc h (a, o)) = 0 := by
      intro a'
      simp [map_snoc_mass, hκN, hh]
    calc
      (ConcreteLaw.bind (π t h') (fun a' =>
          ConcreteLaw.map (fun o' => snoc h' (a', o')) (κ t h' a'))).mass (snoc h (a, o)) =
        listWeightedSum (π t h').support (fun _ => (0 : Rat)) := by
          refine congrArg (listWeightedSum (π t h').support) ?_
          funext a'
          exact hzero a'
      _ = 0 := by
          simp [listWeightedSum]
      _ = if h' = h then (π t h).mass a * (κ t h a).mass o else 0 := by
          simp [hh]

theorem histLaw_snoc_mass
    (π : ConcretePolicy A O) (κ : ConcreteKernel A O)
    (hπN : PolicySupportNodup π) (hκN : KernelSupportNodup κ)
    {t : Nat} (h : Hist A O t) (a : A) (o : O) :
    (histLaw π κ (t + 1)).mass (snoc h (a, o)) =
      (histLaw π κ t).mass h * (π t h).mass a * (κ t h a).mass o := by
  have hsum :
      listWeightedSum (histLaw π κ t).support
          (fun h' =>
            if h' = h then
              (histLaw π κ t).mass h' * ((π t h).mass a * (κ t h a).mass o)
            else 0) =
        if h ∈ (histLaw π κ t).support then
          (histLaw π κ t).mass h * ((π t h).mass a * (κ t h a).mass o)
        else 0 := by
    exact listWeightedSum_eq_if_mem ((histLaw π κ t).support)
      (histLaw_support_nodup π κ t) h
      (fun h' => (histLaw π κ t).mass h' * ((π t h).mass a * (κ t h a).mass o))
  have hrewrite :
      listWeightedSum (histLaw π κ t).support
          (fun h' =>
            (histLaw π κ t).mass h' *
              (ConcreteLaw.bind (π t h') (fun a' =>
                ConcreteLaw.map (fun o' => snoc h' (a', o')) (κ t h' a'))).mass
                (snoc h (a, o))) =
        listWeightedSum (histLaw π κ t).support
          (fun h' =>
            if h' = h then
              (histLaw π κ t).mass h' * ((π t h).mass a * (κ t h a).mass o)
            else 0) := by
    refine congrArg (listWeightedSum (histLaw π κ t).support) ?_
    funext h'
    by_cases hh' : h' = h
    · simp [actionStep_snoc_mass, hπN, hκN, hh']
    · simp [actionStep_snoc_mass, hπN, hκN, hh']
  have hmem :
      (if h ∈ (histLaw π κ t).support then
          (histLaw π κ t).mass h * ((π t h).mass a * (κ t h a).mass o)
        else 0) =
        (histLaw π κ t).mass h * ((π t h).mass a * (κ t h a).mass o) := by
    by_cases hhmem : h ∈ (histLaw π κ t).support
    · simp [hhmem]
    · by_cases hmass : (histLaw π κ t).mass h = 0
      · simp [hhmem, hmass]
      · exact (hhmem ((histLaw π κ t).support_complete h hmass)).elim
  calc
    (histLaw π κ (t + 1)).mass (snoc h (a, o)) =
      listWeightedSum (histLaw π κ t).support
        (fun h' =>
          (histLaw π κ t).mass h' *
            (ConcreteLaw.bind (π t h') (fun a' =>
              ConcreteLaw.map (fun o' => snoc h' (a', o')) (κ t h' a'))).mass
              (snoc h (a, o))) := by
        rfl
    _ =
      listWeightedSum (histLaw π κ t).support
        (fun h' =>
          if h' = h then
            (histLaw π κ t).mass h' * ((π t h).mass a * (κ t h a).mass o)
          else 0) := hrewrite
    _ = if h ∈ (histLaw π κ t).support then
          (histLaw π κ t).mass h * ((π t h).mass a * (κ t h a).mass o)
        else 0 := hsum
    _ = (histLaw π κ t).mass h * ((π t h).mass a * (κ t h a).mass o) := hmem
    _ = (histLaw π κ t).mass h * (π t h).mass a * (κ t h a).mass o := by
        ring

theorem histLaw_mass_nonneg
    (π : ConcretePolicy A O) (κ : ConcreteKernel A O)
    (hπ : ProbabilisticPolicy π) (hκ : ProbabilisticKernel κ)
    (hπN : PolicySupportNodup π) (hκN : KernelSupportNodup κ) :
    ∀ {t : Nat} (h : Hist A O t), 0 ≤ (histLaw π κ t).mass h
  | 0, h => by
      have hnil : h = (emptyHist : Hist A O 0) := by
        funext i
        exact Fin.elim0 i
      subst h
      simp [histLaw, ConcreteLaw.pure]
  | t + 1, h => by
      let hPrev : Hist A O t := fun i => h (Fin.castSucc i)
      let e : HistEvent A O := h ⟨t, Nat.lt_succ_self t⟩
      have hdecomp : snoc hPrev e = h := by
        simpa [hPrev, e] using ConcreteBridge.hist_snoc_decompose h
      rcases e with ⟨a, o⟩
      have hPrevNonneg : 0 ≤ (histLaw π κ t).mass hPrev :=
        histLaw_mass_nonneg π κ hπ hκ hπN hκN hPrev
      have hπNonneg : 0 ≤ (π t hPrev).mass a := (hπ t hPrev).1 a
      have hκNonneg : 0 ≤ (κ t hPrev a).mass o := (hκ t hPrev a).1 o
      rw [← hdecomp, histLaw_snoc_mass π κ hπN hκN hPrev a o]
      exact mul_nonneg (mul_nonneg hPrevNonneg hπNonneg) hκNonneg

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

/-- Duplicate-free support lists for every machine semantics in a concrete prefix machine. -/
def SemanticsSupportNodup (U : ConcretePrefixMachine A O) : Prop :=
  ∀ c hc, KernelSupportNodup (U.semantics c hc)

theorem policy_cast_mass
    (π : ConcretePolicy A O)
    {t u : Nat} (hEq : t = u) (h : Hist A O t) (a : A) :
    ((π u (cast (by cases hEq; rfl : Hist A O t = Hist A O u) h)).mass a : Rat) =
      (π t h).mass a := by
  cases hEq
  rfl

theorem kernel_cast_mass
    (κ : ConcreteKernel A O)
    {t u : Nat} (hEq : t = u) (h : Hist A O t) (a : A) (o : O) :
    ((κ u (cast (by cases hEq; rfl : Hist A O t = Hist A O u) h) a).mass o : Rat) =
      (κ t h a).mass o := by
  cases hEq
  rfl

theorem histPMF_countHistOfHist_eq_histLaw
    (π : ConcretePolicy A O) (κ : ConcreteKernel A O)
    (hπ : ProbabilisticPolicy π) (hκ : ProbabilisticKernel κ)
    (hπN : PolicySupportNodup π) (hκN : KernelSupportNodup κ) :
    ∀ {t : Nat} (h : Hist A O t),
      CountableConcrete.histPMF (toCountablePolicy π hπ) (toCountableKernel κ hκ) t
          (ConcreteBridge.countHistOfHist h) =
        ENNReal.ofReal ((histLaw π κ t).mass h : ℝ)
  | 0, h => by
      have hnil : h = (emptyHist : Hist A O 0) := by
        funext i
        exact Fin.elim0 i
      subst h
      simp [CountableConcrete.histPMF, ConcreteBridge.countHistOfHist, histLaw, ConcreteLaw.pure]
  | t + 1, h => by
      let hPrev : Hist A O t := fun i => h (Fin.castSucc i)
      let e : HistEvent A O := h ⟨t, Nat.lt_succ_self t⟩
      have hdecomp : snoc hPrev e = h := by
        simpa [hPrev, e] using ConcreteBridge.hist_snoc_decompose h
      rcases e with ⟨a, o⟩
      have hdecomp' : snoc hPrev (a, o) = h := by
        simpa using hdecomp
      rw [← hdecomp']
      have ih :=
        histPMF_countHistOfHist_eq_histLaw π κ hπ hκ hπN hκN (h := hPrev)
      let hPrevRound : Hist A O t := fun i =>
        ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev)
          (Fin.cast (by simp [ConcreteBridge.countHistOfHist]) i)
      have hRawRound :
          cast (by simp [ConcreteBridge.countHistOfHist])
            (ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev)) = hPrevRound := by
        funext i
        simpa [hPrevRound] using
          (ConcreteBridge.hist_cast_apply
            (hEq := by simp [ConcreteBridge.countHistOfHist])
            (h := ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev))
            (i := i))
      have hPrevRound_eq : hPrevRound = hPrev := by
        funext i
        simp [hPrevRound, ConcreteBridge.histOfCountHist_countHistOfHist_apply]
      have hPiMass :
          ((π (List.length (ConcreteBridge.countHistOfHist hPrev))
              (ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev))).mass a : Rat) =
            (π t hPrev).mass a := by
        have hPiMassRound : ((π t hPrevRound).mass a : Rat) = (π t hPrev).mass a := by
          simpa using congrArg (fun hh : Hist A O t => (π t hh).mass a) hPrevRound_eq
        have hPiCast :
            ((π t
                (cast (by simp [ConcreteBridge.countHistOfHist])
                  (ConcreteBridge.histOfCountHist
                    (ConcreteBridge.countHistOfHist hPrev)))).mass a : Rat) =
              (π (List.length (ConcreteBridge.countHistOfHist hPrev))
                (ConcreteBridge.histOfCountHist
                  (ConcreteBridge.countHistOfHist hPrev))).mass a := by
          simpa [ConcreteBridge.countHistOfHist] using
            (policy_cast_mass π
              (t := (ConcreteBridge.countHistOfHist hPrev).length)
              (u := t)
              (hEq := by simp [ConcreteBridge.countHistOfHist])
              (h := ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev))
              (a := a))
        have hPiBridge :
            ((π (List.length (ConcreteBridge.countHistOfHist hPrev))
                (ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev))).mass a : Rat) =
              (π t hPrevRound).mass a := by
          have hPiBridgeCast :
              ((π t
                  (cast (by simp [ConcreteBridge.countHistOfHist])
                    (ConcreteBridge.histOfCountHist
                      (ConcreteBridge.countHistOfHist hPrev)))).mass a : Rat) =
                (π t hPrevRound).mass a := by
            simpa using congrArg (fun hh : Hist A O t => (π t hh).mass a) hRawRound
          exact hPiCast.symm.trans hPiBridgeCast
        exact hPiBridge.trans hPiMassRound
      have hKappaMass :
          ((κ (List.length (ConcreteBridge.countHistOfHist hPrev))
              (ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev)) a).mass o : Rat) =
            (κ t hPrev a).mass o := by
        have hKappaMassRound : ((κ t hPrevRound a).mass o : Rat) = (κ t hPrev a).mass o := by
          simpa using congrArg (fun hh : Hist A O t => (κ t hh a).mass o) hPrevRound_eq
        have hKappaCast :
            ((κ t
                (cast (by simp [ConcreteBridge.countHistOfHist])
                  (ConcreteBridge.histOfCountHist
                    (ConcreteBridge.countHistOfHist hPrev))) a).mass o : Rat) =
              (κ (List.length (ConcreteBridge.countHistOfHist hPrev))
                (ConcreteBridge.histOfCountHist
                  (ConcreteBridge.countHistOfHist hPrev)) a).mass o := by
          simpa [ConcreteBridge.countHistOfHist] using
            (kernel_cast_mass κ
              (t := (ConcreteBridge.countHistOfHist hPrev).length)
              (u := t)
              (hEq := by simp [ConcreteBridge.countHistOfHist])
              (h := ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev))
              (a := a) (o := o))
        have hKappaBridge :
            ((κ (List.length (ConcreteBridge.countHistOfHist hPrev))
                (ConcreteBridge.histOfCountHist (ConcreteBridge.countHistOfHist hPrev)) a).mass o : Rat) =
              (κ t hPrevRound a).mass o := by
          have hKappaBridgeCast :
              ((κ t
                  (cast (by simp [ConcreteBridge.countHistOfHist])
                    (ConcreteBridge.histOfCountHist
                      (ConcreteBridge.countHistOfHist hPrev))) a).mass o : Rat) =
                (κ t hPrevRound a).mass o := by
            simpa using congrArg (fun hh : Hist A O t => (κ t hh a).mass o) hRawRound
          exact hKappaCast.symm.trans hKappaBridgeCast
        exact hKappaBridge.trans hKappaMassRound
      have hπnonneg : (0 : ℝ) ≤ ((π t hPrev).mass a : Rat) := by
        exact_mod_cast (hπ t hPrev).1 a
      have hκnonneg : (0 : ℝ) ≤ ((κ t hPrev a).mass o : Rat) := by
        exact_mod_cast (hκ t hPrev a).1 o
      calc
        CountableConcrete.histPMF (toCountablePolicy π hπ) (toCountableKernel κ hκ) (t + 1)
            (ConcreteBridge.countHistOfHist (snoc hPrev (a, o))) =
          CountableConcrete.histPMF (toCountablePolicy π hπ) (toCountableKernel κ hκ) t
              (ConcreteBridge.countHistOfHist hPrev) *
            ENNReal.ofReal (((π t hPrev).mass a : Rat) : ℝ) *
            ENNReal.ofReal (((κ t hPrev a).mass o : Rat) : ℝ) := by
            rw [ConcreteBridge.countHistOfHist_snoc, CountableConcrete.histPMF_appendEvent]
            simp [toCountablePolicy_apply, toCountableKernel_apply, ConcreteLaw.toENNRealMass,
              hPiMass, hKappaMass]
        _ =
          ENNReal.ofReal (((histLaw π κ t).mass hPrev : Rat) : ℝ) *
            ENNReal.ofReal (((π t hPrev).mass a : Rat) : ℝ) *
            ENNReal.ofReal (((κ t hPrev a).mass o : Rat) : ℝ) := by
            simp [ih]
        _ =
          ENNReal.ofReal (((π t hPrev).mass a : Rat) : ℝ) *
            (ENNReal.ofReal (((κ t hPrev a).mass o : Rat) : ℝ) *
              ENNReal.ofReal (((histLaw π κ t).mass hPrev : Rat) : ℝ)) := by
            ac_rfl
        _ =
          ENNReal.ofReal
            ((((π t hPrev).mass a : Rat) : ℝ) *
              ((((κ t hPrev a).mass o : Rat) : ℝ) *
                (((histLaw π κ t).mass hPrev : Rat) : ℝ))) := by
            rw [← ENNReal.ofReal_mul hκnonneg, ← ENNReal.ofReal_mul hπnonneg]
        _ =
          ENNReal.ofReal
            (((histLaw π κ t).mass hPrev * (π t hPrev).mass a * (κ t hPrev a).mass o : Rat) : ℝ) := by
            norm_num [Rat.cast_mul, mul_assoc, mul_comm, mul_left_comm]
        _ =
          ENNReal.ofReal ((histLaw π κ (t + 1)).mass (snoc hPrev (a, o)) : ℝ) := by
            rw [histLaw_snoc_mass π κ hπN hκN hPrev a o]

/-- Canonical deduplicated code enumeration used by the countable bridge machine. -/
def codeList (U : ConcretePrefixMachine A O) : List BitCode :=
  U.codes.toFinset.toList

theorem codeList_nodup (U : ConcretePrefixMachine A O) :
    U.codeList.Nodup := by
  simpa [codeList] using U.codes.toFinset.nodup_toList

theorem mem_codeList (U : ConcretePrefixMachine A O) {c : BitCode} :
    c ∈ U.codeList ↔ c ∈ U.codes := by
  simp [codeList]

theorem semantics_eq_of_proof_irrel (U : ConcretePrefixMachine A O)
    {c : BitCode} {hc₁ hc₂ : c ∈ U.codes} :
    U.semantics c hc₁ = U.semantics c hc₂ := by
  cases Subsingleton.elim hc₁ hc₂
  rfl

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

theorem observerFiber_toCountableProgram_iff
    (U : ConcretePrefixMachine A O)
    (ω : Observer (EncodedProgram A O))
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (pstar p : U.Program) :
    (U.toCountablePrefixMachine hSem).observerFiber
        (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
        (U.toCountableProgram hSem p) ↔
      U.observerFiber ω (U.toEncodedProgram pstar) p := by
  have hViewStar :
      (U.liftObserver ω).view (U.toCountableEncodedProgram hSem pstar) =
        some (ω.view (U.toEncodedProgram pstar)) :=
    U.liftObserver_view_toCountableEncodedProgram ω hSem pstar
  have hViewP :
      (U.liftObserver ω).view
          ((U.toCountablePrefixMachine hSem).toEncodedProgram
            (U.toCountableProgram hSem p)) =
        some (ω.view (U.toEncodedProgram p)) := by
    change (U.liftObserver ω).view
        { code := (U.toCountablePrefixMachine hSem).programCode (U.toCountableProgram hSem p)
          kernel := (U.toCountablePrefixMachine hSem).programSemantics (U.toCountableProgram hSem p) } =
      some (ω.view (U.toEncodedProgram p))
    rw [U.toCountableProgram_programCode hSem p]
    simp [liftObserver, ConcretePrefixMachine.toEncodedProgram,
      ConcretePrefixMachine.programSemantics, p.2]
  rw [CountableConcrete.CountablePrefixMachine.observerFiber,
    ConcretePrefixMachine.observerFiber, hViewStar, hViewP]
  constructor <;> intro hView
  · exact Option.some.inj hView
  · exact congrArg some hView

theorem programSemantics_toCountableProgram_eq
    (U : ConcretePrefixMachine A O)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (p : U.Program) :
    (U.toCountablePrefixMachine hSem).programSemantics (U.toCountableProgram hSem p) =
      toCountableKernel (U.programSemantics p)
        (by simpa [ConcretePrefixMachine.programSemantics] using hSem p.1 p.2) := by
  have hCodeListMem : p.1 ∈ U.codeList := (U.mem_codeList).2 p.2
  have hIdx : U.codeList[U.codeList.idxOf p.1]? = some p.1 :=
    List.getElem?_idxOf hCodeListMem
  ext h a o
  simp [CountableConcrete.CountablePrefixMachine.programSemantics,
    CountableConcrete.CountablePrefixMachine.programCode,
    CountableConcrete.CountablePrefixMachine.programCode_spec,
    ConcretePrefixMachine.toCountablePrefixMachine,
    ConcretePrefixMachine.toCountableProgram,
    toCountableKernel, ConcretePrefixMachine.programSemantics, hIdx]

theorem likelihood_toCountableProgram_eq
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (p : U.Program) :
    ∀ {t : Nat} (h : Hist A O t),
      (U.toCountablePrefixMachine hSem).likelihood
          (toCountablePolicy π hπ) t (ConcreteBridge.countHistOfHist h)
          (U.toCountableProgram hSem p) =
        ENNReal.ofReal ((U.likelihood π (asFullHist h) p : Rat) : ℝ)
  | t, h => by
      have hProg : ProbabilisticKernel (U.programSemantics p) := by
        simpa [ConcretePrefixMachine.programSemantics] using hSem p.1 p.2
      have hProgN : KernelSupportNodup (U.programSemantics p) := by
        simpa [ConcretePrefixMachine.programSemantics] using hSemN p.1 p.2
      rw [CountableConcrete.CountablePrefixMachine.likelihood,
        U.programSemantics_toCountableProgram_eq hSem p]
      simpa [ConcretePrefixMachine.likelihood, asFullHist] using
        (histPMF_countHistOfHist_eq_histLaw
          π (U.programSemantics p) hπ hProg hπN hProgN (h := h))

theorem posteriorWeight_toCountableProgram_eq
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (p : U.Program) :
    ∀ {t : Nat} (h : Hist A O t),
      (U.toCountablePrefixMachine hSem).posteriorWeight
          (toCountablePolicy π hπ) t (ConcreteBridge.countHistOfHist h)
          (U.toCountableProgram hSem p) =
        ENNReal.ofReal (((U.bayesNumeratorLaw π (asFullHist h)).mass p : Rat) : ℝ)
  | t, h => by
      have hPriorNonnegRat : (0 : Rat) ≤ U.universalPrior p := by
        unfold ConcretePrefixMachine.universalPrior codeWeight
        exact Rat.divInt_nonneg (by decide)
          (by exact_mod_cast Nat.zero_le (pow2 p.1.length))
      have hPriorNonneg : (0 : ℝ) ≤ ((U.universalPrior p : Rat) : ℝ) := by
        exact_mod_cast hPriorNonnegRat
      simp [CountableConcrete.CountablePrefixMachine.posteriorWeight,
        CountableConcrete.CountablePrefixMachine.universalWeight,
        ConcretePrefixMachine.universalPrior,
        CountableConcrete.CountablePrefixMachine.codeWeightENNReal,
        ConcretePrefixMachine.bayesNumeratorLaw,
        U.toCountableProgram_programCode hSem p]
      rw [U.likelihood_toCountableProgram_eq π hπ hπN hSem hSemN p (h := h)]
      simpa using
        (ENNReal.ofReal_mul hPriorNonneg).symm

theorem bayesNumeratorLaw_mass_nonneg
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (h : FullHist A O) (p : U.Program) :
    0 ≤ (U.bayesNumeratorLaw π h).mass p := by
  have hPriorNonneg : 0 ≤ U.universalPrior p := by
    unfold ConcretePrefixMachine.universalPrior codeWeight
    exact Rat.divInt_nonneg (by decide)
      (by exact_mod_cast Nat.zero_le (pow2 p.1.length))
  have hLikNonneg : 0 ≤ U.likelihood π h p := by
    exact histLaw_mass_nonneg π (U.programSemantics p) hπ
      (by
        simpa [ConcretePrefixMachine.programSemantics] using hSem p.1 p.2)
      hπN
      (by
        simpa [ConcretePrefixMachine.programSemantics] using hSemN p.1 p.2)
      h.2
  unfold ConcretePrefixMachine.bayesNumeratorLaw ConcretePrefixMachine.likelihood
  exact mul_nonneg hPriorNonneg hLikNonneg

theorem classMass_normalizeOnPrograms_eq
    (U : ConcretePrefixMachine A O)
    (μ : ConcreteLaw U.Program) (Z : Rat)
    (C : PredSet U.Program) [DecidablePred C] :
    ConcreteLaw.classMass (U.normalizeOnPrograms μ Z) C =
      if hZ : Z = 0 then 0 else
        listWeightedSum (U.allPrograms.filter C) μ.mass / Z := by
  unfold ConcreteLaw.classMass ConcreteLaw.totalMass ConcretePrefixMachine.normalizeOnPrograms
  rw [listWeightedSum_filter_eq]
  by_cases hZ : Z = 0
  · simp [hZ, ConcreteLaw.restrict, listWeightedSum]
  · simp [hZ, ConcreteLaw.restrict]
    rw [listWeightedSum_filter_cond_eq]
    rw [listWeightedSum_div_right]
    rw [← listWeightedSum_filter_eq (xs := U.allPrograms) (C := C) (f := μ.mass)]

theorem posteriorClassMass_eq_bayesNumeratorClassMass_div_evidence
    (U : ConcretePrefixMachine A O)
    (π : ConcretePolicy A O) (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] :
    U.posteriorClassMass π h C =
      if hZ : U.evidence π h = 0 then 0 else
        ConcreteLaw.classMass (U.bayesNumeratorLaw π h) C / U.evidence π h := by
  rw [ConcretePrefixMachine.posteriorClassMass, ConcretePrefixMachine.posteriorLaw,
    classMass_normalizeOnPrograms_eq (U := U) (μ := U.bayesNumeratorLaw π h)
      (Z := U.evidence π h) (C := C)]
  by_cases hZ : U.evidence π h = 0
  · simp [hZ]
  · unfold ConcreteLaw.classMass ConcreteLaw.totalMass
    simp [hZ, ConcreteLaw.restrict, ConcretePrefixMachine.bayesNumeratorLaw,
      listWeightedSum_filter_eq]
    refine congrArg (listWeightedSum U.allPrograms) ?_
    funext a
    by_cases hCa : C a <;> simp [hCa]

theorem observerFiberBayesNumeratorMass_toCountable_eq
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (ω : Observer (EncodedProgram A O))
    (pstar : U.Program) :
    ∀ {t : Nat} (h : Hist A O t),
      (U.toCountablePrefixMachine hSem).observerFiberPosteriorWeight
          (toCountablePolicy π hπ) t (ConcreteBridge.countHistOfHist h)
          (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar) =
        ENNReal.ofReal
          ((ConcreteLaw.classMass (U.bayesNumeratorLaw π (asFullHist h))
            (U.observerFiber ω (U.toEncodedProgram pstar)) : Rat) : ℝ)
  | t, h => by
      classical
      let Uc := U.toCountablePrefixMachine hSem
      letI := U.programFintype hCodes
      rw [CountableConcrete.CountablePrefixMachine.observerFiberPosteriorWeight]
      rw [← (U.programEquiv hSem).tsum_eq
        (fun q : Uc.Program =>
          if Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar) q then
            Uc.posteriorWeight (toCountablePolicy π hπ) t (ConcreteBridge.countHistOfHist h) q
          else 0)]
      rw [tsum_fintype]
      have hTerm :
          ∀ p : U.Program,
            (if Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
                ((U.programEquiv hSem) p) then
                Uc.posteriorWeight (toCountablePolicy π hπ) t
                  (ConcreteBridge.countHistOfHist h) ((U.programEquiv hSem) p)
              else 0) =
              ENNReal.ofReal
                (((if U.observerFiber ω (U.toEncodedProgram pstar) p then
                    (U.bayesNumeratorLaw π (asFullHist h)).mass p
                  else 0 : Rat) : ℝ)) := by
        intro p
        by_cases hFib : U.observerFiber ω (U.toEncodedProgram pstar) p
        · have hFib' :
            Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
              ((U.programEquiv hSem) p) := by
            exact (U.observerFiber_toCountableProgram_iff ω hSem pstar p).2 hFib
          rw [if_pos hFib']
          simpa [ConcretePrefixMachine.programEquiv, hFib] using
            (U.posteriorWeight_toCountableProgram_eq π hπ hπN hSem hSemN p (h := h))
        · have hFib' :
            ¬ Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
              ((U.programEquiv hSem) p) := by
            intro hCount
            exact hFib ((U.observerFiber_toCountableProgram_iff ω hSem pstar p).1 hCount)
          rw [if_neg hFib']
          simp [hFib]
      have hSumRewrite :
          (∑ p : U.Program,
              if Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
                  ((U.programEquiv hSem) p) then
                Uc.posteriorWeight (toCountablePolicy π hπ) t
                  (ConcreteBridge.countHistOfHist h) ((U.programEquiv hSem) p)
              else 0) =
            (∑ p : U.Program,
              ENNReal.ofReal
                (((if U.observerFiber ω (U.toEncodedProgram pstar) p then
                    (U.bayesNumeratorLaw π (asFullHist h)).mass p
                  else 0 : Rat) : ℝ))) := by
        exact congrArg (fun g : U.Program → ENNReal => ∑ p : U.Program, g p) (funext hTerm)
      rw [hSumRewrite]
      have hsumENN :
          (∑ p : U.Program,
              ENNReal.ofReal
                (((if U.observerFiber ω (U.toEncodedProgram pstar) p then
                    (U.bayesNumeratorLaw π (asFullHist h)).mass p
                  else 0 : Rat) : ℝ))) =
            ENNReal.ofReal
              (((∑ p : U.Program,
                    if U.observerFiber ω (U.toEncodedProgram pstar) p then
                      (U.bayesNumeratorLaw π (asFullHist h)).mass p
                    else 0 : Rat) : Rat) : ℝ) := by
        simpa using
          (ENNReal.ofReal_sum_of_nonneg
            (s := Finset.univ)
            (f := fun p : U.Program =>
              (((if U.observerFiber ω (U.toEncodedProgram pstar) p then
                  (U.bayesNumeratorLaw π (asFullHist h)).mass p
                else 0 : Rat) : ℝ)))
            (by
              intro p hp
              by_cases hFib : U.observerFiber ω (U.toEncodedProgram pstar) p
              · have hNonneg :
                    (0 : ℝ) ≤ ((U.bayesNumeratorLaw π (asFullHist h)).mass p : ℝ) := by
                  exact_mod_cast
                    U.bayesNumeratorLaw_mass_nonneg π hπ hπN hSem hSemN (asFullHist h) p
                simpa [hFib] using hNonneg
              · simp [hFib])).symm
      rw [hsumENN]
      have hsumRat :
          (∑ p : U.Program,
              if U.observerFiber ω (U.toEncodedProgram pstar) p then
                (U.bayesNumeratorLaw π (asFullHist h)).mass p
              else 0 : Rat) =
            ConcreteLaw.classMass (U.bayesNumeratorLaw π (asFullHist h))
              (U.observerFiber ω (U.toEncodedProgram pstar)) := by
        rw [U.sum_programFintype_eq_listWeightedSum hCodes]
        unfold ConcreteLaw.classMass ConcreteLaw.totalMass
        simp [ConcreteLaw.restrict, ConcretePrefixMachine.bayesNumeratorLaw,
          listWeightedSum_filter_eq]
        refine congrArg (listWeightedSum U.allPrograms) ?_
        funext p
        by_cases hFib : U.observerFiber ω (U.toEncodedProgram pstar) p <;> simp [hFib]
      rw [hsumRat]

theorem bayesNumeratorClassMass_nonneg
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] :
    0 ≤ ConcreteLaw.classMass (U.bayesNumeratorLaw π h) C := by
  classical
  letI := U.programFintype hCodes
  have hClassEq :
      (∑ p : U.Program,
          if C p then (U.bayesNumeratorLaw π h).mass p else 0 : Rat) =
        ConcreteLaw.classMass (U.bayesNumeratorLaw π h) C := by
    rw [U.sum_programFintype_eq_listWeightedSum hCodes]
    unfold ConcreteLaw.classMass ConcreteLaw.totalMass
    simp [ConcreteLaw.restrict, ConcretePrefixMachine.bayesNumeratorLaw, listWeightedSum_filter_eq]
    refine congrArg (listWeightedSum U.allPrograms) ?_
    funext p
    by_cases hC : C p <;> simp [hC]
  rw [← hClassEq]
  have hTermNonneg :
      ∀ p : U.Program,
        0 ≤ if C p then (U.bayesNumeratorLaw π h).mass p else 0 := by
    intro p
    by_cases hC : C p
    · simp [hC, U.bayesNumeratorLaw_mass_nonneg π hπ hπN hSem hSemN h p]
    · simp [hC]
  exact Finset.sum_nonneg (fun p _ => hTermNonneg p)

theorem bayesNumeratorClassMass_le_evidence
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C] :
    ConcreteLaw.classMass (U.bayesNumeratorLaw π h) C ≤ U.evidence π h := by
  classical
  letI := U.programFintype hCodes
  have hClassEq :
      (∑ p : U.Program,
          if C p then (U.bayesNumeratorLaw π h).mass p else 0 : Rat) =
        ConcreteLaw.classMass (U.bayesNumeratorLaw π h) C := by
    rw [U.sum_programFintype_eq_listWeightedSum hCodes]
    unfold ConcreteLaw.classMass ConcreteLaw.totalMass
    simp [ConcreteLaw.restrict, ConcretePrefixMachine.bayesNumeratorLaw, listWeightedSum_filter_eq]
    refine congrArg (listWeightedSum U.allPrograms) ?_
    funext p
    by_cases hC : C p <;> simp [hC]
  rw [← hClassEq, ConcretePrefixMachine.evidence, ConcreteLaw.totalMass,
    ConcretePrefixMachine.bayesNumeratorLaw]
  rw [← U.sum_programFintype_eq_listWeightedSum hCodes]
  refine Finset.sum_le_sum ?_
  intro p hp
  by_cases hC : C p
  · simp [hC]
  · have hNonneg := U.bayesNumeratorLaw_mass_nonneg π hπ hπN hSem hSemN h p
    simpa [hC, ConcretePrefixMachine.bayesNumeratorLaw] using hNonneg

theorem evidence_ne_zero_of_bayesNumeratorClassMass_ne_zero
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (h : FullHist A O)
    (C : PredSet U.Program) [DecidablePred C]
    (hC : ConcreteLaw.classMass (U.bayesNumeratorLaw π h) C ≠ 0) :
    U.evidence π h ≠ 0 := by
  intro hZ
  have hLe :=
    U.bayesNumeratorClassMass_le_evidence hCodes π hπ hπN hSem hSemN h C
  have hNonneg :=
    U.bayesNumeratorClassMass_nonneg hCodes π hπ hπN hSem hSemN h C
  have hLeZero :
      ConcreteLaw.classMass (U.bayesNumeratorLaw π h) C ≤ 0 := by
    simpa [hZ] using hLe
  exact hC (le_antisymm hLeZero hNonneg)

theorem observerFiberComplementBayesNumeratorMass_toCountable_eq
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (ω : Observer (EncodedProgram A O))
    (pstar : U.Program) :
    ∀ {t : Nat} (h : Hist A O t),
      (U.toCountablePrefixMachine hSem).observerFiberComplementWeight
          (toCountablePolicy π hπ) t (ConcreteBridge.countHistOfHist h)
          (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar) =
        ENNReal.ofReal
          ((ConcreteLaw.classMass (U.bayesNumeratorLaw π (asFullHist h))
            (fun p => ¬ U.observerFiber ω (U.toEncodedProgram pstar) p) : Rat) : ℝ)
  | t, h => by
      classical
      let Uc := U.toCountablePrefixMachine hSem
      letI := U.programFintype hCodes
      rw [CountableConcrete.CountablePrefixMachine.observerFiberComplementWeight]
      rw [← (U.programEquiv hSem).tsum_eq
        (fun q : Uc.Program =>
          if Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar) q then
            0
          else
            Uc.posteriorWeight (toCountablePolicy π hπ) t (ConcreteBridge.countHistOfHist h) q)]
      rw [tsum_fintype]
      have hTerm :
          ∀ p : U.Program,
            (if Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
                ((U.programEquiv hSem) p) then
                0
              else
                Uc.posteriorWeight (toCountablePolicy π hπ) t
                  (ConcreteBridge.countHistOfHist h) ((U.programEquiv hSem) p)) =
              ENNReal.ofReal
                (((if U.observerFiber ω (U.toEncodedProgram pstar) p then
                    0
                  else (U.bayesNumeratorLaw π (asFullHist h)).mass p : Rat) : ℝ)) := by
        intro p
        by_cases hFib : U.observerFiber ω (U.toEncodedProgram pstar) p
        · have hFib' :
            Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
              ((U.programEquiv hSem) p) := by
            exact (U.observerFiber_toCountableProgram_iff ω hSem pstar p).2 hFib
          rw [if_pos hFib']
          simp [hFib]
        · have hFib' :
            ¬ Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
              ((U.programEquiv hSem) p) := by
            intro hCount
            exact hFib ((U.observerFiber_toCountableProgram_iff ω hSem pstar p).1 hCount)
          rw [if_neg hFib']
          simpa [ConcretePrefixMachine.programEquiv, hFib] using
            (U.posteriorWeight_toCountableProgram_eq π hπ hπN hSem hSemN p (h := h))
      have hSumRewrite :
          (∑ p : U.Program,
              if Uc.observerFiber (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar)
                  ((U.programEquiv hSem) p) then
                0
              else
                Uc.posteriorWeight (toCountablePolicy π hπ) t
                  (ConcreteBridge.countHistOfHist h) ((U.programEquiv hSem) p)) =
            (∑ p : U.Program,
              ENNReal.ofReal
                (((if U.observerFiber ω (U.toEncodedProgram pstar) p then
                    0
                  else (U.bayesNumeratorLaw π (asFullHist h)).mass p : Rat) : ℝ))) := by
        exact congrArg (fun g : U.Program → ENNReal => ∑ p : U.Program, g p) (funext hTerm)
      rw [hSumRewrite]
      have hsumENN :
          (∑ p : U.Program,
              ENNReal.ofReal
                (((if U.observerFiber ω (U.toEncodedProgram pstar) p then
                    0
                  else (U.bayesNumeratorLaw π (asFullHist h)).mass p : Rat) : ℝ))) =
            ENNReal.ofReal
              (((∑ p : U.Program,
                    if U.observerFiber ω (U.toEncodedProgram pstar) p then
                      0
                    else (U.bayesNumeratorLaw π (asFullHist h)).mass p : Rat) : Rat) : ℝ) := by
        simpa using
          (ENNReal.ofReal_sum_of_nonneg
            (s := Finset.univ)
            (f := fun p : U.Program =>
              (((if U.observerFiber ω (U.toEncodedProgram pstar) p then
                  0
                else (U.bayesNumeratorLaw π (asFullHist h)).mass p : Rat) : ℝ)))
            (by
              intro p hp
              by_cases hFib : U.observerFiber ω (U.toEncodedProgram pstar) p
              · simp [hFib]
              · have hNonneg :
                    (0 : ℝ) ≤ ((U.bayesNumeratorLaw π (asFullHist h)).mass p : ℝ) := by
                  exact_mod_cast
                    U.bayesNumeratorLaw_mass_nonneg π hπ hπN hSem hSemN (asFullHist h) p
                simpa [hFib] using hNonneg)).symm
      rw [hsumENN]
      have hsumRat :
          (∑ p : U.Program,
              if U.observerFiber ω (U.toEncodedProgram pstar) p then
                0
              else (U.bayesNumeratorLaw π (asFullHist h)).mass p : Rat) =
            ConcreteLaw.classMass (U.bayesNumeratorLaw π (asFullHist h))
              (fun p => ¬ U.observerFiber ω (U.toEncodedProgram pstar) p) := by
        have hCond :
            listWeightedSum
                (List.filter
                  (fun b => ¬ U.observerFiber ω (U.toEncodedProgram pstar) b)
                  U.allPrograms)
                (fun p =>
                  if U.observerFiber ω (U.toEncodedProgram pstar) p then
                    0
                  else U.universalPrior p * U.likelihood π (asFullHist h) p) =
              listWeightedSum
                (List.filter
                  (fun b => ¬ U.observerFiber ω (U.toEncodedProgram pstar) b)
                  U.allPrograms)
                (fun p => U.universalPrior p * U.likelihood π (asFullHist h) p) := by
          simpa [not_not] using
            (listWeightedSum_filter_cond_eq
              (xs := U.allPrograms)
              (C := fun p => ¬ U.observerFiber ω (U.toEncodedProgram pstar) p)
              (f := fun p => U.universalPrior p * U.likelihood π (asFullHist h) p))
        rw [U.sum_programFintype_eq_listWeightedSum hCodes]
        unfold ConcreteLaw.classMass ConcreteLaw.totalMass
        simp [ConcreteLaw.restrict, ConcretePrefixMachine.bayesNumeratorLaw]
        have hFilter :
            listWeightedSum U.allPrograms
                (fun p =>
                  if U.observerFiber ω (U.toEncodedProgram pstar) p then
                    0
                  else U.universalPrior p * U.likelihood π (asFullHist h) p) =
              listWeightedSum
                (List.filter
                  (fun b => ¬ U.observerFiber ω (U.toEncodedProgram pstar) b)
                  U.allPrograms)
                (fun p => U.universalPrior p * U.likelihood π (asFullHist h) p) := by
          simpa [not_not] using
            (listWeightedSum_filter_eq
              (xs := U.allPrograms)
              (C := fun p => ¬ U.observerFiber ω (U.toEncodedProgram pstar) p)
              (f := fun p => U.universalPrior p * U.likelihood π (asFullHist h) p)).symm
        simpa using hFilter.trans hCond.symm
      rw [hsumRat]

theorem residualObserverFiberPosteriorOdds_toCountable_eq
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (ω : Observer (EncodedProgram A O))
    (pstar : U.Program) :
    ∀ {t : Nat} (h : Hist A O t),
      (U.toCountablePrefixMachine hSem).residualObserverFiberPosteriorOdds
          (toCountablePolicy π hπ) t (ConcreteBridge.countHistOfHist h)
          (U.liftObserver ω) (U.toCountableEncodedProgram hSem pstar) =
        ENNReal.ofReal
          (U.residualObserverFiberPosteriorOdds π (asFullHist h) ω
            (U.toEncodedProgram pstar) : ℝ)
  | t, h => by
      classical
      let Uc := U.toCountablePrefixMachine hSem
      let C : PredSet U.Program := U.observerFiber ω (U.toEncodedProgram pstar)
      let mC : Rat := ConcreteLaw.classMass (U.bayesNumeratorLaw π (asFullHist h)) C
      let mComp : Rat :=
        ConcreteLaw.classMass (U.bayesNumeratorLaw π (asFullHist h)) (fun p => ¬ C p)
      have hMassC :
          Uc.observerFiberPosteriorWeight (toCountablePolicy π hπ) t
              (ConcreteBridge.countHistOfHist h) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) =
            ENNReal.ofReal (mC : ℝ) := by
        simpa [Uc, C, mC] using
          U.observerFiberBayesNumeratorMass_toCountable_eq
            hCodes π hπ hπN hSem hSemN ω pstar (h := h)
      have hMassComp :
          Uc.observerFiberComplementWeight (toCountablePolicy π hπ) t
              (ConcreteBridge.countHistOfHist h) (U.liftObserver ω)
              (U.toCountableEncodedProgram hSem pstar) =
            ENNReal.ofReal (mComp : ℝ) := by
        simpa [Uc, C, mComp] using
          U.observerFiberComplementBayesNumeratorMass_toCountable_eq
            hCodes π hπ hπN hSem hSemN ω pstar (h := h)
      have hPostClass :
          U.posteriorClassMass π (asFullHist h) C =
            if hZ : U.evidence π (asFullHist h) = 0 then 0 else
              mC / U.evidence π (asFullHist h) := by
        simpa [C, mC] using
          U.posteriorClassMass_eq_bayesNumeratorClassMass_div_evidence π (asFullHist h) C
      have hPostComp :
          U.complementPosteriorMass π (asFullHist h) C =
            if hZ : U.evidence π (asFullHist h) = 0 then 0 else
              mComp / U.evidence π (asFullHist h) := by
        simpa [ConcretePrefixMachine.complementPosteriorMass, C, mComp] using
          U.posteriorClassMass_eq_bayesNumeratorClassMass_div_evidence
            π (asFullHist h) (fun p => ¬ C p)
      by_cases hClassZero : mC = 0
      · have hPostClassZero : U.posteriorClassMass π (asFullHist h) C = 0 := by
          by_cases hZ : U.evidence π (asFullHist h) = 0
          · simpa [hPostClass, hZ]
          · simpa [hPostClass, hZ, hClassZero]
        rw [CountableConcrete.CountablePrefixMachine.residualObserverFiberPosteriorOdds]
        rw [hMassC, hMassComp]
        have hMassCZero : ENNReal.ofReal (mC : ℝ) = 0 := by
          simp [hClassZero]
        rw [if_pos hMassCZero]
        simp [ConcretePrefixMachine.residualObserverFiberPosteriorOdds,
          ConcretePrefixMachine.residualClassPosteriorOdds, C, hPostClassZero]
      · have hClassNonneg : 0 ≤ mC := by
          simpa [C, mC] using
            U.bayesNumeratorClassMass_nonneg hCodes π hπ hπN hSem hSemN (asFullHist h) C
        have hCompNonneg : 0 ≤ mComp := by
          simpa [C, mComp] using
            U.bayesNumeratorClassMass_nonneg hCodes π hπ hπN hSem hSemN
              (asFullHist h) (fun p => ¬ C p)
        have hEvidenceNe : U.evidence π (asFullHist h) ≠ 0 := by
          simpa [C, mC] using
            U.evidence_ne_zero_of_bayesNumeratorClassMass_ne_zero
              hCodes π hπ hπN hSem hSemN (asFullHist h) C hClassZero
        have hPostClassEq :
            U.posteriorClassMass π (asFullHist h) C =
              mC / U.evidence π (asFullHist h) := by
          simpa [hEvidenceNe] using hPostClass
        have hPostCompEq :
            U.complementPosteriorMass π (asFullHist h) C =
              mComp / U.evidence π (asFullHist h) := by
          simpa [hEvidenceNe] using hPostComp
        have hResidualRat :
            U.residualObserverFiberPosteriorOdds π (asFullHist h) ω
                (U.toEncodedProgram pstar) =
              mComp / mC := by
          unfold ConcretePrefixMachine.residualObserverFiberPosteriorOdds
            ConcretePrefixMachine.residualClassPosteriorOdds
          rw [hPostClassEq, hPostCompEq]
          have hPostClassNe : mC / U.evidence π (asFullHist h) ≠ 0 := by
            exact div_ne_zero hClassZero hEvidenceNe
          simp [hPostClassNe]
          field_simp [hEvidenceNe, hClassZero]
        have hClassPos : 0 < mC := lt_of_le_of_ne hClassNonneg (Ne.symm hClassZero)
        have hClassPosReal : 0 < (mC : ℝ) := by
          exact_mod_cast hClassPos
        have hMassCNe :
            ENNReal.ofReal (mC : ℝ) ≠ 0 := by
          exact ne_of_gt (by simpa using (ENNReal.ofReal_pos.2 hClassPosReal))
        rw [CountableConcrete.CountablePrefixMachine.residualObserverFiberPosteriorOdds]
        rw [hMassC, hMassComp, if_neg hMassCNe, hResidualRat]
        calc
          ENNReal.ofReal (mComp : ℝ) / ENNReal.ofReal (mC : ℝ) =
              ENNReal.ofReal ((mComp : ℝ) / (mC : ℝ)) := by
                exact (ENNReal.ofReal_div_of_pos hClassPosReal).symm
          _ = ENNReal.ofReal ((mComp / mC : Rat) : ℝ) := by
                norm_num

theorem histPMF_mem_support_length
    {π : CountableConcrete.CountablePolicy A O}
    {κ : CountableConcrete.CountableKernel A O}
    {t : Nat} {h : CountableConcrete.CountHist A O}
    (hSupp : h ∈ (CountableConcrete.histPMF π κ t).support) :
    h.length = t := by
  induction t generalizing h with
  | zero =>
      simpa [CountableConcrete.histPMF] using hSupp
  | succ t ih =>
      rw [CountableConcrete.histPMF] at hSupp
      rw [PMF.mem_support_bind_iff] at hSupp
      rcases hSupp with ⟨hPrev, hPrevSupp, hActSupp⟩
      rw [PMF.mem_support_bind_iff] at hActSupp
      rcases hActSupp with ⟨a, haSupp, hObsSupp⟩
      rw [PMF.mem_support_bind_iff] at hObsSupp
      rcases hObsSupp with ⟨o, hoSupp, hPureSupp⟩
      have hEq : h = CountableConcrete.appendEvent hPrev (a, o) := by
        simpa using hPureSupp
      have hPrevLen : hPrev.length = t := ih hPrevSupp
      simpa [hEq, hPrevLen, CountableConcrete.appendEvent_length]

theorem trajectoryLaw_mem_support_length
    (U : CountableConcrete.CountablePrefixMachine A O)
    (π : CountableConcrete.CountablePolicy A O)
    (penv : U.Program) (T : Nat)
    {ξ : CountableConcrete.CountablePrefixMachine.Trajectory A O}
    (hξ : ξ ∈ (U.trajectoryLaw π penv T).support) :
    ξ.length = T := by
  simpa [CountableConcrete.CountablePrefixMachine.trajectoryLaw] using
    (histPMF_mem_support_length (hSupp := hξ))

theorem residualObserverFiberProcess_toCountable_eq_of_prefix_length
    (U : ConcretePrefixMachine A O)
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (ω : Observer (EncodedProgram A O))
    (pstar : U.Program)
    (ξ : CountableConcrete.CountHist A O)
    (n : Nat)
    (hLen : (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n).length = n) :
    (U.toCountablePrefixMachine hSem).residualObserverFiberProcess
        (toCountablePolicy π hπ) (U.liftObserver ω)
        (U.toCountableEncodedProgram hSem pstar) n ξ =
      ENNReal.ofReal
        (U.residualObserverFiberPosteriorOdds π
          (asFullHist (ConcreteBridge.histOfCountHist
            (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n))) ω
          (U.toEncodedProgram pstar) : ℝ) := by
  simpa [CountableConcrete.CountablePrefixMachine.residualObserverFiberProcess, hLen] using
    U.residualObserverFiberPosteriorOdds_toCountable_eq
      hCodes π hπ hπN hSem hSemN ω pstar
      (h := ConcreteBridge.histOfCountHist
        (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n))

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
    (hCodes : U.CodesNodup)
    (π : ConcretePolicy A O) (hπ : ProbabilisticPolicy π)
    (hπN : PolicySupportNodup π)
    (hSem : ∀ c hc, ProbabilisticKernel (U.semantics c hc))
    (hSemN : SemanticsSupportNodup U)
    (penv pstar : U.Program)
    (ω : Observer (EncodedProgram A O))
    (δ : Rat) (T : Nat)
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
  have hξLen :
      ξ.length = T := by
    simpa using
      trajectoryLaw_mem_support_length
        (U := U.toCountablePrefixMachine hSem)
        (π := toCountablePolicy π hπ) (penv := U.toCountableProgram hSem penv)
        (T := T) hξ
  have hPrefixLen :
      (CountableConcrete.CountablePrefixMachine.historyPrefix ξ n).length = n := by
    simpa [CountableConcrete.CountablePrefixMachine.historyPrefix, hξLen,
      Nat.min_eq_left (Nat.le_of_lt hn)] using List.length_take n ξ
  refine ⟨(U.toCountablePrefixMachine hSem).residualObserverFiberProcess
      (toCountablePolicy π hπ) (U.liftObserver ω)
      (U.toCountableEncodedProgram hSem pstar) (n + 1) ξ, rfl, ?_⟩
  have hPrefixLenSucc :
      (CountableConcrete.CountablePrefixMachine.historyPrefix ξ (n + 1)).length = n + 1 := by
    simpa [CountableConcrete.CountablePrefixMachine.historyPrefix, hξLen,
      Nat.min_eq_left (Nat.succ_le_of_lt hn)] using List.length_take (n + 1) ξ
  rw [U.residualObserverFiberProcess_toCountable_eq_of_prefix_length
      hCodes π hπ hπN hSem hSemN ω pstar ξ (n + 1) hPrefixLenSucc]
  rw [U.residualObserverFiberProcess_toCountable_eq_of_prefix_length
      hCodes π hπ hπN hSem hSemN ω pstar ξ n hPrefixLen]
  exact U.prefixwiseResidualDecayENNReal_of_rat π ω pstar δ ξ n (hStep ξ hξ n hn)

end ConcretePrefixMachine

end

end SemanticConvergence
