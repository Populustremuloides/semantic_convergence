# Compact Kernel Exactness Lock

This file freezes the target for the compact-action kernel overhaul. It is
deliberately narrower than the full variational-core lock: it concerns only the
measure-theoretic compact-action kernel lift and its manuscript-facing Lean
declarations.

The purpose of this lock is to prevent the current finite-action specialization
from continuing to occupy the compact theorem slot.

## Authoritative Manuscript Target

Primary target:

- `prop:kernel-functional-minimizer-compact`
- Manuscript location: `semantic_convergence_interactive_learning.tex`, the
  proposition titled "Exact global minimizer of the compact-action kernel lift"

Closely coupled downstream compact-action targets now closed:

- `prop:kernel-promotion-support-compact`
- `prop:compact-action-kernel-separation`
- `cor:compact-action-kernel`

The compact minimizer theorem must formalize the proposition as a genuine
measure-theoretic compact-action theorem. A finite action chart is allowed as a
special case, but it may not be the canonical meaning of the compact theorem.

## Mathematical Target

Data:

- A countable program machine and the repaired belief-side AFE already supplied
  by `SemanticConvergence.def_afe` and `SemanticConvergence.lem_variational`.
- A finite or countable observer class space `C = Ω_A`, treated as a
  discrete measurable space.
- A compact metric action space `X`.
- The Borel measurable structure on `X`.
- A full-support Borel probability reference measure `λ` on `X`.
- A class reference law `wbar : C -> ENNReal`, normalized and nonnegative.
- The product reference measure `wbar ⊗ λ` on `C × X`.
- A bounded measurable score `Bbar : C -> X -> Real`.
- For the compact-action support corollaries, `Bbar c` must be continuous in
  the action coordinate, at least for the target class-neighborhood arguments.
- Parameters `β γ : Real` with `0 ≤ β` and `0 < γ`.
- A probability law `κ` on `C × X`.

Functional:

The compact kernel functional must be the manuscript object:

```text
J_ker[q, κ; h_t]
  = F_t[q; h_t]
    - β * ∫ Bbar(c, a) dκ(c, a)
    + γ * KL(κ || wbar ⊗ λ).
```

The KL term is extended-valued off absolute continuity. The implementation may
package a finite-value admissible domain for `Real`-valued corollaries, but the
canonical compact minimizer theorem must not erase the off-support `+∞` case.

Gibbs law:

```text
dκ_G / d(wbar ⊗ λ)(c, a)
  = exp((β / γ) * Bbar(c, a)) / Z,

Z = ∫ exp((β / γ) * Bbar(c, a)) d(wbar ⊗ λ)(c, a).
```

Required proof content:

- `Z` is finite and positive.
- `κ_G` is a probability measure.
- `κ_G` is absolutely continuous with respect to `wbar ⊗ λ`.
- The kernel part decomposes as

```text
-β * E_κ[Bbar] + γ * KL(κ || wbar ⊗ λ)
  = -γ * log Z + γ * KL(κ || κ_G).
```

- Therefore `κ_G` uniquely minimizes the kernel part.
- Combining with the repaired belief theorem, `(q_t*, κ_G)` is the exact global
  minimizer of the compact-action kernel lift.

## Lean Representation Choice

Preferred Lean representation:

- Action space:
  `X : Type*` with a compact metric/Borel structure, e.g.
  `[MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]`.
- Reference action law:
  `λ : Measure X` with `[IsProbabilityMeasure λ]` plus a full-support predicate.
- Class law:
  a normalized discrete law on the observer codomain, either as a finite measure
  or as weights converted into a measure on the discrete class type.
- Joint law:
  `κ : Measure (C × X)` with `[IsProbabilityMeasure κ]`.
- Product reference:
  the product of the discrete class reference measure and `λ`.
- KL:
  a measure-theoretic extended KL/relative-entropy object. If Mathlib's
  available relative entropy API is insufficient, the repo should define the
  exact Radon-Nikodym density integral needed here, with `+∞` for non-dominated
  laws.
- Score integral:
  the Bochner/Lebesgue integral of the bounded measurable real score against
  `κ`.

The generic compact Gibbs variational theorem should live in a reusable module,
likely `SemanticConvergence.CompactKernel`, before it is instantiated by the
paper-facing functional layer.

## Phase 1 Primitive Layer Status

Phase 1 introduces `SemanticConvergence.CompactKernel` as the reusable
measure-theoretic substrate for the compact-action overhaul.

Implemented primitives:

- `CompactKernel.HasFullSupport`, including nonzero-mass lemmas for open balls.
- `CompactKernel.BoundedKernelScore`, a bounded measurable score on `C × X`
  with explicit lower and upper interval witnesses.
- `CompactKernel.referenceMeasure`, the product law `wbar ⊗ λ`.
- `CompactKernel.kernelKL`, an alias for Mathlib's extended
  `InformationTheory.klDiv`, with the non-dominated `+∞` case exposed.
- `CompactKernel.scoreIntegral` and `CompactKernel.kernelObjectiveEReal`, the
  extended-valued kernel objective `-β * Eκ[B] + γ * KL(κ || ref)`.
- `CompactKernel.gibbsWeight`, `CompactKernel.partition`,
  `CompactKernel.gibbsDensity`, and `CompactKernel.gibbsMeasure`.
- Proofs that the Gibbs partition is positive and finite under
  `0 ≤ β`, `0 < γ`, and a probability reference law.
- Proofs that the normalized Gibbs law is absolutely continuous with respect to
  the product reference and has total mass one.
- `CompactKernel.Setup`, packaging class/action references, probability
  witnesses, and action full support.

This phase does **not** close the compact exactness lock. The remaining
paper-facing work is still to prove the Gibbs/KL variational identity, prove the
unique minimizer theorem, demote the finite-action theorem, and rewire
`prop:kernel-functional-minimizer-compact` to the measure-theoretic theorem.

## Phase 2 Variational Identity Status

Phase 2 adds the first genuine compact Gibbs/KL decomposition layer in
`SemanticConvergence.CompactKernel`.

Implemented identity-layer primitives:

- `CompactKernel.scaledScore`, the real exponent `(β / γ) * B(c,a)`.
- Integrability proofs for the scaled score and its exponential against any
  finite/probability kernel law under `0 ≤ β` and `0 < γ`.
- `CompactKernel.partition_eq_ofReal_integral_exp` and
  `CompactKernel.partition_toReal_eq_integral_exp`, connecting the `ENNReal`
  partition used by the density to the Bochner integral used by Mathlib's
  tilted-measure KL lemmas.
- `CompactKernel.gibbsMeasure_eq_tilted`, proving that the project's normalized
  Gibbs density is exactly Mathlib's exponentially tilted measure
  `ref.tilted (scaledScore β γ B)`.
- Mutual absolute-continuity support needed for later minimization:
  `gibbsMeasure ref β γ B ≪ ref` and, under the Phase 2 hypotheses,
  `ref ≪ gibbsMeasure ref β γ B`.
- Explicit top-case lemmas:
  `kernelObjectiveEReal_eq_top_of_not_ac` and
  `kernelKL_gibbs_eq_top_of_not_ac_reference`, so non-dominated laws remain
  extended-valued rather than being coerced into a finite chart.
- `CompactKernel.kernelKL_gibbs_toReal_decomposition`, the finite-KL identity

```text
KL(κ || κ_G)
  = KL(κ || ref) - (β / γ) * E_κ[B] + log Z.
```

- `CompactKernel.kernelObjectiveReal_decomposition`, the corresponding
  finite-KL objective identity

```text
-β * E_κ[B] + γ * KL(κ || ref)
  = -γ * log Z + γ * KL(κ || κ_G).
```

This phase still does **not** close the compact exactness lock. The remaining
work is to derive the unique minimizer theorem from KL nonnegativity/zero
criteria, combine it with the repaired belief-side minimizer, demote the
finite-action compact theorem, and rewire the manifest-facing compact
declaration.

## Phase 3 Gibbs Minimizer Status

Phase 3 adds the compact Gibbs minimizer layer in
`SemanticConvergence.CompactKernel`.

Implemented minimizer-layer primitives:

- `CompactKernel.kernelKL_eq_zero_iff_eq`, exposing Mathlib's converse Gibbs
  inequality as a kernel-specific theorem: finite-measure KL is zero exactly
  when the two measures are equal.
- `CompactKernel.kernelKL_toReal_eq_zero_iff_eq_of_ne_top`, the finite extended
  KL bridge needed to reason with the `Real` objective without confusing
  `∞.toReal = 0` for a genuine zero.
- `CompactKernel.llr_gibbs_integrable_of_reference` and
  `CompactKernel.kernelKL_gibbs_ne_top_of_reference`, proving that every
  reference-dominated finite-KL probability law also has finite KL to the
  Gibbs kernel.
- `CompactKernel.gibbs_llr_reference_integrable` and
  `CompactKernel.gibbs_kernelKL_reference_ne_top`, proving that the normalized
  Gibbs kernel itself has finite KL to the product reference.
- `CompactKernel.kernelObjectiveReal_gibbs_value`, computing the Gibbs
  objective value as `-γ * log Z`.
- `CompactKernel.kernelObjectiveReal_gibbs_gap`, proving the exact objective
  gap identity

```text
J(κ) - J(κ_G) = γ * KL(κ || κ_G).
```

- `CompactKernel.kernelObjectiveReal_gibbs_le`,
  `CompactKernel.kernelObjectiveReal_eq_gibbs_iff`, and
  `CompactKernel.kernelObjectiveReal_gibbs_unique_minimizer`, proving that the
  Gibbs kernel minimizes the compact kernel objective on the finite-KL
  admissible domain and that equality forces `κ = κ_G`.

This phase still does **not** close the compact exactness lock. The remaining
work is to combine this kernel minimizer with the repaired belief-side
minimizer, demote the finite-action compact theorem, and rewire the
manifest-facing `prop:kernel-functional-minimizer-compact` declaration to the
measure-theoretic compact theorem.

## Phase 4 Belief/Compact Product Status

Phase 4 combines the repaired belief-side variational theorem with the
measure-theoretic compact kernel minimizer.

Implemented paper-facing product-layer declarations:

- `SemanticConvergence.def_compact_kernel_functional_measureEReal`, the
  extended-valued combined objective

```text
F_t[q; h_t] + (-β * E_κ[B] + γ * KL(κ || ref)).
```

- `SemanticConvergence.def_compact_kernel_functional_measureEReal_eq_top_of_not_ac`,
  proving that the combined objective is `⊤` whenever the candidate kernel law
  is not dominated by the reference law.
- `SemanticConvergence.def_compact_kernel_functional_measure`, the finite-KL
  `Real` chart used for exact equality/minimizer corollaries.
- `SemanticConvergence.prop_compact_kernel_functional_minimizer_measure`,
  proving the exact product decomposition

```text
J[q, κ; h_t]
  = -log evidence - γ log Z
    + posteriorIGap(q || q_t*)
    + γ * KL(κ || κ_G),
```

  the lower bound by `-log evidence - γ log Z`, and the equality
  characterization

```text
J[q, κ; h_t] = -log evidence - γ log Z
  ↔ q = q_t* pointwise ∧ κ = κ_G.
```

This phase proves the combined minimizer on the finite-KL admissible domain
while preserving the extended-valued off-support branch in the product-layer
API.

## Phase 4B Public Compact Minimizer Rewire Status

Phase 4B moves the manifest-facing compact minimizer theorem off the finite
action chart and onto the measure-theoretic compact kernel surface.

Implemented public-surface changes:

- The old finite-action theorem has been demoted to
  `SemanticConvergence.prop_kernel_functional_minimizer_finiteAction`.
- The canonical paper-facing declaration
  `SemanticConvergence.prop_kernel_functional_minimizer_compact` is now a
  measure-theoretic theorem over `CompactKernel.Setup`.
- The theorem surface carries a compact/Borel action type, a full-support
  action reference law, a class reference law, and the explicit product
  reference `S.reference = S.classRef.prod S.actionRef`.
- The theorem routes through
  `SemanticConvergence.prop_compact_kernel_functional_minimizer_measure`, so it
  proves the exact product decomposition, lower bound, and unique equality
  characterization at `(q_t*, κ_G)`.
- The manifest generator maps `prop:kernel-functional-minimizer-compact` to the
  measure-theoretic compact theorem in `SemanticConvergence.Belief`.

This closes the compact minimizer's stale finite-action public-surface issue.
The downstream compact support, separation, and kernel corollary declarations
are tracked in the phases below.

## Phase 4B Compact Support Floor Status

Phase 4B rewires the compact promotion-support theorem to the compact/Borel
kernel stack.

Implemented support-floor primitives:

- `CompactKernel.partition_upper_bound_unit_interval`, proving
  `Z ≤ exp(β / γ)` for `[0,1]` scores under a probability product reference.
- `CompactKernel.one_le_gibbsWeight_of_nonnegative`, proving pointwise Gibbs
  weight is at least `1` for nonnegative scores.
- `CompactKernel.gibbsDensity_unit_interval_floor`, proving the normalized
  Gibbs density is pointwise at least `exp(-β / γ)`.
- `CompactKernel.gibbsMeasure_reference_mass_floor`, lifting the density floor
  to every measurable set.
- `CompactKernel.gibbsMeasure_product_mass_floor`, specializing the floor to
  rectangles `C₀ × S` under the product reference `wbar ⊗ λ`.
- `SemanticConvergence.prop_kernel_promotion_support_compact`, now a
  compact/Borel theorem over `CompactKernel.Setup` proving
  `κ_G({c} × S) ≥ exp(-β / γ) * wbar({c}) * λ(S)` for every measurable action
  set `S`.

This closes the stale finite-action support wrapper for
`prop:kernel-promotion-support-compact`.

## Phase 4C Compact Separation And Kernel Corollary Status

Phase 4C rewires the remaining downstream compact declarations to the
compact/Borel kernel stack.

Implemented separation/corollary primitives:

- `CompactKernel.ballMassFloor`, the Lean counterpart of the manuscript's
  `m_\lambda(r) = inf_a λ(U_r(a))`.
- `CompactKernel.exists_positive_le_ball_mass_floor`, proving via compactness
  and full support that a positive uniform radius-`r` ball-mass lower bound
  exists.
- `CompactKernel.ballMassFloor_ne_zero_of_fullSupport`, proving the actual
  `ballMassFloor` is nonzero under compactness and full support.
- `SemanticConvergence.prop_compact_action_kernel_separation`, now a compact
  theorem: a continuous score with local modulus, a separating witness
  `score a₀ ≥ η`, and a full-support compact action reference imply
  `η / 2 > 0`, measurability of the superlevel set, and
  `ballMassFloor actionRef r ≤ actionRef {a | η / 2 ≤ score a}`.
- `SemanticConvergence.cor_compact_action_kernel`, now composes compact
  separation with `prop_kernel_promotion_support_compact` to prove the Gibbs
  kernel mass floor
  `κ_G({c} × S_c) ≥ exp(-β / γ) * wbar({c}) * ballMassFloor λ r`
  for the compact superlevel set `S_c`.

This closes the compact exactness lock. Any remaining first-principles gap is
outside the compact-kernel axis; currently the Section 6 `hStep` standing
assumption is tracked separately in `lean_open_issues.md` and the generated
manifest exactness-lock counter.

## Current Finite-Chart Declarations

These declarations are exact finite-action or finite-chart results. They are
useful, but they are not the final compact-action theorem:

- `SemanticConvergence.prop_kernel_functional_minimizer`
- `SemanticConvergence.prop_kernel_functional_minimizer_finiteAction`
- `SemanticConvergence.prop_kernel_functional_minimizer_compact_legacy`
- `SemanticConvergence.def_kernel_functional_legacy`

The finite-action theorem has been demoted to
`SemanticConvergence.prop_kernel_functional_minimizer_finiteAction`. The
manifest-facing label `prop:kernel-functional-minimizer-compact` now points to
the measure-theoretic compact theorem
`SemanticConvergence.prop_kernel_functional_minimizer_compact`.

## Downstream Compact Declarations

All compact-kernel downstream declarations in this lock now route through the
compact reference measure, continuity/modulus hypotheses, full support, and the
measure-theoretic Gibbs support floor.

## Acceptance Conditions For The Overhaul

The compact kernel overhaul is complete only when:

- the compact theorem uses a compact/Borel action space and a full-support
  Borel probability reference measure;
- the product reference measure `wbar ⊗ λ` is explicit;
- KL is relative to that product reference and handles non-dominated laws
  honestly;
- the Gibbs kernel law is constructed as a normalized density;
- the minimizer theorem is proved by a Gibbs/KL variational identity;
- the current finite-action theorem is renamed or demoted;
- `prop:kernel-functional-minimizer-compact` maps to the measure-theoretic
  theorem, not the finite-action specialization;
- downstream compact separation/rate declarations are audited against the new
  theorem.

All compact-kernel acceptance conditions above are now satisfied.
