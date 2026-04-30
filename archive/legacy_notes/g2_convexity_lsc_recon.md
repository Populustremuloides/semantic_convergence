# G2 Convexity and Lower Semicontinuity Reconnaissance Report

## Overview

This report surveys Mathlib tooling and existing file infrastructure for proving:
1. **ConvexOnSimplex** for `klDivergenceOnSimplex w`
2. **SequentialLowerSemicontinuousOnSimplex** for `klDivergenceOnSimplex w`

Both are required to complete `genericWeightKLDivergence_self_instantiation` (DiscreteConvexDuality.lean, L4165-4178).

---

## Question 1: Mathlib's klFun Convexity

### Location
**File**: `/sessions/exciting-wizardly-cannon/mnt/algorithmic_free_energy/.lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/KLFun.lean`

### Key Theorems

**klFun definition** (L53):
```lean
noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x
```

**Strict Convexity** (L62):
```lean
lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun :=
  (strictConvexOn_mul_log.add_convexOn (convexOn_const _ (convex_Ici _))).sub_concaveOn
    (concaveOn_id (convex_Ici _))
```

**Convexity** (L67):
```lean
lemma convexOn_klFun : ConvexOn ℝ (Ici 0) klFun := strictConvexOn_klFun.convexOn
```

**Convexity on (0,∞)** (L71-72):
```lean
lemma convexOn_Ioi_klFun : ConvexOn ℝ (Ioi 0) klFun :=
  convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)
```

**Nonnegativity** (L149):
```lean
lemma klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x := klFun_one ▸ isMinOn_klFun hx
```

**Zero iff one** (L151-154):
```lean
lemma klFun_eq_zero_iff (hx : 0 ≤ x) : klFun x = 0 ↔ x = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [klFun_apply, h]⟩
  exact strictConvexOn_klFun.eq_of_isMinOn (isMinOn_iff.mpr fun y hy ↦ h ▸ klFun_nonneg hy)
    isMinOn_klFun hx (zero_le_one' ℝ)
```

**Continuity** (L76):
```lean
lemma continuous_klFun : Continuous klFun := by unfold klFun; fun_prop
```

### Answer to Q1
**Mathlib provides** `ConvexOn ℝ (Ici 0) klFun`, which states `klFun` is convex on `[0, ∞)`.

The direct form is:
```lean
ConvexOn ℝ (Ici 0) klFun
```
This gives: `∀ x y ∈ [0, ∞), ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → klFun(ax + by) ≤ a·klFun(x) + b·klFun(y)`.

---

## Question 2: Mathlib's klFun Lower Semicontinuity / Continuity

### Location
**File**: Same as above, KLFun.lean (L76)

### Key Theorem

**Continuity** (L76):
```lean
@[continuity, fun_prop]
lemma continuous_klFun : Continuous klFun := by unfold klFun; fun_prop
```

### Answer to Q2
Mathlib provides **`Continuous klFun`**, which immediately implies `LowerSemicontinuous klFun`.

No dedicated LSC lemma exists because continuity subsumes it. Use:
```lean
Continuous.lowerSemicontinuous continuous_klFun
```

---

## Question 3: Existing Per-Program Decomposition in DiscreteConvexDuality.lean

### Location
**File**: `/sessions/exciting-wizardly-cannon/mnt/algorithmic_free_energy/SemanticConvergence/DiscreteConvexDuality.lean`

### The Key Definition (L97-103)
```lean
def genericWeightKLDivergenceContribution
    (q w : P → ENNReal)
    (p : P) : Real :=
  if hq : q p = 0 then
    0
  else
    (q p).toReal * Real.log ((q p / w p).toReal)
```

### Bridge Lemma (L315-365)
**`genericWeightKLDivergenceContribution_eq_term_toReal_sub`**

For any individual ENNReal pair `(q, r)` with `q ≠ ⊤`, `r ≠ ⊤`, and `q ≠ 0 → r ≠ 0`:
```lean
genericWeightKLDivergenceContribution (fun _ : Unit => q) (fun _ : Unit => r) ()
  = (genericWeightKLDivergenceTerm q r).toReal - r.toReal + q.toReal
```

The proof **crucially uses** (L342-357):
```lean
r.toReal * klFun ((q / r).toReal) - r.toReal + q.toReal
  = q.toReal * Real.log ((q / r).toReal)
```

This **IS** the identity you're looking for: the discrete KL contribution equals the klFun formula modulo arithmetic.

### Support Compatibility (L318)
```lean
(hCompat : q ≠ 0 → r ≠ 0)
```

When `q ≠ 0` but `r = 0`, the term evaluates to `⊤` (see `genericWeightKLDivergenceTerm`, L112-119):
```lean
def genericWeightKLDivergenceTerm (q r : ENNReal) : ENNReal :=
  if hqTop : q = (⊤ : ENNReal) then
    (⊤ : ENNReal)
  else if hrZero : r = 0 then
    if hqZero : q = 0 then 0 else (⊤ : ENNReal)  -- ← penalty for off-support
  else
    r * ENNReal.ofReal (InformationTheory.klFun ((q / r).toReal))
```

### ENNReal to Real Conversion Tools

**`genericWeight_toReal_tsum_eq_one`** (L233-240):
```lean
private theorem genericWeight_toReal_tsum_eq_one
    {μ : P → ENNReal}
    (hμ : ProbabilityWeight μ) :
    ∑' p : P, (μ p).toReal = 1
```

**`genericWeightSummable_toReal`** (L242-246):
```lean
private theorem genericWeightSummable_toReal
    {μ : P → ENNReal}
    (hμ : ProbabilityWeight μ) :
    Summable (fun p : P => (μ p).toReal)
```

### Answer to Q3
The decomposition **exists and is key**: `genericWeightKLDivergenceContribution q w p = (q p).toReal * log((q p / w p).toReal)` for `q p ≠ 0`, zero otherwise. The link to `klFun` is encoded in `genericWeightKLDivergenceContribution_eq_term_toReal_sub`, which shows the pointwise term equals `w(p).toReal * klFun((q p / w p).toReal) - w(p).toReal + (q p).toReal` under support compatibility.

---

## Question 4: ENNReal-Real Bridges

### Key Lemmas in the File

**ENNReal division and toReal** (used extensively, e.g., L329-330):
```lean
have hDivReal : (q / r).toReal = q.toReal / r.toReal := by
  rw [ENNReal.toReal_div]
```

**ENNReal multiplication and toReal** (L339-340):
```lean
rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
  (InformationTheory.klFun_nonneg ENNReal.toReal_nonneg)]
```

**Convex combination in ENNReal** (L197 from ConvexOnSimplex definition):
```lean
D (fun p => ENNReal.ofNNReal a * q p + ENNReal.ofNNReal b * r p)
```

### Mathlib Tools Available

From Mathlib type theory:
- `ENNReal.toReal_mul`: `(x * y).toReal = x.toReal * y.toReal` (when finite)
- `ENNReal.toReal_div`: `(x / y).toReal = x.toReal / y.toReal` (standard arithmetic)
- `ENNReal.toReal_add`: similar for addition
- `ENNReal.ofNNReal_coe_nnreal`: conversion lemmas

### Answer to Q4
The file already uses these bridges extensively. For the convex combination:
```lean
(ENNReal.ofNNReal a * q p + ENNReal.ofNNReal b * r p).toReal
  = a.toReal * (q p).toReal + b.toReal * (r p).toReal
```
This follows from `ENNReal.toReal_add` and `ENNReal.toReal_mul` and the fact that `(ENNReal.ofNNReal a).toReal = a.toNReal` (when `a : NNReal`).

---

## Question 5: Existing Convexity / LSC Results in This File

### Search Results
Grep for `ConvexOn|LowerSemicontinuous|Convex|LSC|lowerSemicontinuous` yields:

1. **L192-198**: The definition itself (`ConvexOnSimplex`)
2. **L1524**: A use of `convexOn_exp` in a lemma proof (not directly relevant)
3. **L3874**: A hypothesis `_hConvex : ConvexOnSimplex D` (unused)
4. **L4158-4167**: Comment and theorem about the predicates being "remaining piece of G2"

### Answer to Q5
**No partial convexity or LSC results exist yet.** The file defines the predicates but does not prove them for KL. This is the open work.

---

## Question 6: L1 Distance and Fatou

### Definition in File (L42-44)
```lean
def genericWeightL1Dist
    (q r : P → ENNReal) : Real :=
  ∑' p : P, |(q p).toReal - (r p).toReal|
```

### Mathlib Fatou / Liminf Tools

**Lower Semicontinuity of tsum** (Mathlib/Topology/Semicontinuity/Basic.lean, L684-694):
```lean
theorem lowerSemicontinuousAt_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ∑' i, f i x') x

theorem lowerSemicontinuousOn_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ∑' i, f i x') s

theorem lowerSemicontinuous_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ∑' i, f i x'
```

**Liminf lemmas** (Mathlib/Order/LiminfLimsup.lean, various):
```lean
theorem le_liminf_of_le {f : Filter β} {u : β → α} {a} ...
theorem liminf_le_of_le {f : Filter β} {u : β → α} {a} ...
theorem liminf_le_limsup {f : Filter β} [NeBot f] {u : β → α} ...
```

**Jensen's inequality / Integral convexity** (Mathlib/Analysis/Convex/Integral.lean, L199-202):
```lean
theorem ConvexOn.map_integral_le [IsProbabilityMeasure μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ
```

### Answer to Q6
Fatou is available via Mathlib's liminf infrastructure. For discrete sums with L1 convergence, you need:
1. `Tendsto (fun n => genericWeightL1Dist (qs n) q) atTop (𝓝 0)` implies pointwise convergence (Cauchy-type argument)
2. Pointwise convergence + lower semicontinuity of the summand yields lower semicontinuity of the tsum
3. Use `lowerSemicontinuous_tsum` from Mathlib.Topology.Semicontinuity.Basic

---

## Recommended Proof Sketch

### For ConvexOnSimplex

**Strategy**: Show that `klDivergenceOnSimplex w` is convex by decomposing into pointwise klFun convexity.

**Steps**:
1. Assume `q, r : P → ENNReal` are probability weights with `a + b = 1` (nonnegative).
2. For a convex combination `aq + br`:
   - Pointwise: `(aq + br)(p) = a·(q p) + b·(r p)` (by ENNReal arithmetic)
   - Convert to reals: `((aq + br)(p)).toReal = a.toReal·(q p).toReal + b.toReal·(r p).toReal`
3. Use `convexOn_klFun` on each pointwise ratio `(q p / w p).toReal`:
   - `klFun(a·(q p).toReal/w(p).toReal + b·(r p).toReal/w(p).toReal) ≤ a·klFun((q p).toReal/w(p).toReal) + b·klFun((r p).toReal/w(p).toReal)`
4. Scale by `w(p)` and tsum over `p`:
   - `∑' p, w(p)·klFun(...) ≤ a·∑' p, w(p)·klFun(...) + b·∑' p, w(p)·klFun(...)`
5. Handle support-compatibility edge cases (`q p ≠ 0 → w p ≠ 0`) using the `⊤` penalty in `genericWeightKLDivergenceTerm`.
6. Relate tsum of ENNReal KL term to EReal cast of total KL.

**Key Mathlib Lemmas**:
- `ConvexOn.convexOn_iff_forall_pos` (Analysis/Convex/Function.lean, L311)
- `convexOn_klFun` (InformationTheory/KullbackLeibler/KLFun.lean, L67)
- `ConvexOn.comp` (Analysis/Convex/Function.lean, L137) for function composition
- `lowerSemicontinuous_tsum` (Topology/Semicontinuity/Basic.lean, L693) for the sum

**Estimated length**: 120–180 lines.

---

### For SequentialLowerSemicontinuousOnSimplex

**Strategy**: Use Fatou-type lower semicontinuity of pointwise KL + L1 convergence.

**Steps**:
1. Assume `Tendsto (fun n => genericWeightL1Dist (qs n) q) atTop (𝓝 0)`.
2. L1 convergence → pointwise convergence in magnitude: `∀ y : Real, y < KL(q||w) ∧ y : EReal` gives a margin.
3. For each `p`, the pointwise term `(qs n p).toReal / (w p).toReal` tends to `(q p).toReal / (w p).toReal`.
4. By continuity of `klFun`, the pointwise scaled term `w(p)·klFun(...)` is lower semicontinuous.
5. By `lowerSemicontinuous_tsum`, the total `∑' p, (...)` is lower semicontinuous.
6. Apply the definition of lower semicontinuity: `y < D(q) ⇒ ∃ N, ∀ n ≥ N, y < D(qs n)`.

**Key Mathlib Lemmas**:
- `lowerSemicontinuous_tsum` (Topology/Semicontinuity/Basic.lean, L693)
- `continuous_klFun` (InformationTheory/KullbackLeibler/KLFun.lean, L76)
- `Continuous.lowerSemicontinuous` (Topology/Semicontinuity/Basic.lean)
- `liminf_le_of_le` or `le_liminf_of_le` (Order/LiminfLimsup.lean) for handling the limit
- Existing `genericWeightL1Dist` definition and tsum structure

**Estimated length**: 150–220 lines.

---

## Critical Findings

1. **klFun is already convex**: `ConvexOn ℝ (Ici 0) klFun` is proven in Mathlib. ✓

2. **Pointwise KL decomposition exists**: The file's `genericWeightKLDivergenceContribution` already manifests the pointwise klFun structure (proven via `genericWeightKLDivergenceContribution_eq_term_toReal_sub`). ✓

3. **ENNReal-Real bridges are in place**: The file extensively uses `toReal`, `toReal_mul`, `toReal_div`, etc. Convex combinations in ENNReal reduce to real arithmetic. ✓

4. **Semicontinuity of tsum is available**: Mathlib provides `lowerSemicontinuous_tsum` for ENNReal-valued functions. ✓

5. **No existing proofs in the file**: The file only defines the predicates; you must prove them from scratch using Mathlib + the file's existing infrastructure.

6. **Support compatibility is automatic**: The `⊤` penalty in `genericWeightKLDivergenceTerm` handles the off-support case (`q p ≠ 0 ∧ w p = 0 ⇒ term = ⊤`). Just ensure your decomposition respects this.

---

## File Structure Summary

| Concept | Location | Status |
|---------|----------|--------|
| KL divergence on simplex | L127–134 | Defined |
| ConvexOnSimplex predicate | L192–198 | Defined, needs proof |
| SequentialLowerSemicontinuousOnSimplex predicate | L60–65 | Defined, needs proof |
| genericWeightKLDivergenceContribution | L97–103 | Defined |
| genericWeightKLDivergenceTerm | L112–119 | Defined |
| Pointwise decomposition bridge | L315–365 | Proven (`genericWeightKLDivergenceContribution_eq_term_toReal_sub`) |
| ENNReal ↔ Real conversion | Throughout | Used extensively |
| L1 distance definition | L42–44 | Defined |

---

## Conclusion

Both proofs are tractable with the tools at hand. Mathlib provides all the high-level convexity and lower-semicontinuity machinery. The file's existing infrastructure (`genericWeightKLDivergenceContribution`, `genericWeightKLDivergenceTerm`, the bridge lemma) handles the discrete decomposition. Your proofs will primarily:

1. **For Convexity**: Pointwise appeal to `convexOn_klFun`, then lift to tsum via ENNReal arithmetic.
2. **For LSC**: Pointwise lower semicontinuity via `continuous_klFun` → LSC, then lift to tsum via `lowerSemicontinuous_tsum`, and connect L1 convergence to the liminf machinery.

Both proofs should run 200–400 lines of Lean in total.
