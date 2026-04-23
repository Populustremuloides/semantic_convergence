# Semantic Convergence in Interactive Learning

This repository contains the current manuscript source for
`semantic_convergence_interactive_learning.tex` together with its Lean 4
formalization.

## Current status

The Lean project is mechanically checked over the concrete foundation adopted
in the repo. The generated manifest and audit artifacts now report full
manuscript coverage, semantic-audit closure, and first-principles closure; the
separate axiom audit records the exact dependency profile of each declaration
and classifies deviations from the canonical baseline.

- `106/106` core manuscript declarations are formalized
- `106/106` are marked `derived`
- `106/106` are marked `concrete-stack`
- `fullyFirstPrinciples = true`
- `semanticAuditClosed = true`
- `0` manifest-tracked entries are in suspicious proof classes
- `lean_axiom_audit.md` currently reports `62` canonical-baseline rows, `34`
  expected `native_decide`-auxiliary rows, `10` lighter-than-baseline rows,
  and `0` genuine unexpected drift rows
- `lean_axiom_audit.md` records the actual per-declaration axiom dependencies

Belief and variational status note:

- `SemanticConvergence.def_afe` now implements the countable generalized
  KL / I-divergence against the posterior-weight scaffold, and
  `SemanticConvergence.lem_variational` plus
  `SemanticConvergence.lem_kl_necessity` certify the exact Bayes/Gibbs
  minimizer and the necessity direction on that repaired belief-side object.
- `SemanticConvergence.def_two_observer_functional` now exposes the repaired
  three-part Gibbs variational shape on the paper-facing countable stack:
  belief term, class-score term, and class-law regularizer. The matching exact
  minimizer theorem is `SemanticConvergence.prop_two_observer_minimizer`.
- `SemanticConvergence.def_kernel_functional` now exposes the repaired joint
  class-action kernel lift with reference-law regularization, and
  `SemanticConvergence.prop_kernel_functional_minimizer` together with
  `SemanticConvergence.prop_kernel_functional_minimizer_compact` certify the
  exact and compact-action Gibbs kernel minimizers on that surface.

Section 6 status note:

- `SemanticConvergence.thm_separating_support_convergence` currently proves a
  probabilistic one-step residual-odds contraction on the realized trajectory
  law, derived from the deterministic soft-substrate contraction through the
  explicit concrete-to-countable bridge in
  `SemanticConvergence.ConcreteSubstrateBridge`: almost surely, each next-step
  residual observer-fiber odds value is bounded by the floor-dependent
  contraction factor times the current one.
- `SemanticConvergence.thm_separating_support_rate` and
  `SemanticConvergence.cor_separating_support_finite_time` currently add the
  corresponding almost-sure `N`-step residual-odds rate bound and almost-sure
  lower bound on the realized observer-fiber posterior share on the same
  bridged realized process.
- No public Section 6 theorem now carries an external bridge-equation
  hypothesis: the deterministic-to-probabilistic process transport is derived
  internally through `SemanticConvergence.ConcreteSubstrateBridge`.
- `SemanticConvergence.thm_semantic_convergence` and
  `SemanticConvergence.thm_kernel_semantic_convergence` currently certify the
  corresponding selector and kernel realizations inside that closed semantic
  theorem stack.

Boundary and surrogate status note:

- `SemanticConvergence.thm_afe_near_miss` now packages both the explicit
  action-level near-miss witness and the paper-facing finite-horizon
  frozen-posterior failure shape.
- `SemanticConvergence.thm_amortized_surrogate_selector_existence` and
  `SemanticConvergence.cor_amortized_surrogate_selector_support` now give the
  repaired countable finite-list wrapper carrying counterparts of `(A1)`--`(A3)`
  to an implemented-law support-floor / supported-action conclusion.
- `SemanticConvergence.thm_amortized_surrogate` now lives on the concrete
  deployment-side stack, exposes finite-list counterparts of the paper's
  assumptions `(A1)`--`(A3)`, and derives the separating-support floor/support
  theorem for the implemented surrogate law.
- `SemanticConvergence.cor_amortized_surrogate_finite_time` then converts that
  deployment-side support floor into the corresponding deterministic residual-
  odds finite-time consequence used by the recovery stack.

The generated status artifacts are:

- [formalization_manifest.md](formalization_manifest.md)
- [formalization_audit.md](formalization_audit.md)
- [formalization_bridge.md](formalization_bridge.md)
- [lean_theorem_census.md](lean_theorem_census.md)
- [lean_proof_audit.md](lean_proof_audit.md)
- [lean_concrete_theorem_audit.md](lean_concrete_theorem_audit.md)
- [lean_verification_progress.md](lean_verification_progress.md)
- [lean_axiom_audit.md](lean_axiom_audit.md)

The generated Lean-side axiom audit driver is:

- [SemanticConvergence/AxiomAudit.lean](SemanticConvergence/AxiomAudit.lean)

## Repository layout

- `SemanticConvergence/`: Lean source files
- `SemanticConvergence.lean`: top-level Lean import surface
- `semantic_convergence_interactive_learning.tex`: canonical manuscript source
- `scripts/generate_formalization_manifest.py`: regenerates the manifest and
  audit artifacts

## Build

This project uses Lean `v4.29.0` together with Mathlib `v4.29.0`.

```bash
lake build
```

To refresh the generated formalization and audit reports:

```bash
python3 scripts/generate_formalization_manifest.py
```

That command regenerates:

- `formalization_manifest.md`
- `formalization_audit.md`
- `formalization_bridge.md`
- `lean_theorem_census.md`
- `lean_proof_audit.md`
- `lean_concrete_theorem_audit.md`
- `lean_verification_progress.md`
- `lean_axiom_audit.md`
- `SemanticConvergence/Manifest.lean`
- `SemanticConvergence/AxiomAudit.lean`

To run the raw per-declaration axiom audit directly:

```bash
lake env lean SemanticConvergence/AxiomAudit.lean
```

Expected output:

- one `#print axioms` line for each of the `106` manifest-tracked declarations
- `lean_axiom_audit.md` records the actual dependency set for each entry
- the audit classifies each row as canonical baseline, expected
  `native_decide` auxiliary, lighter-than-baseline, or genuine drift

## CI

GitHub Actions verification lives in:

- `.github/workflows/lean-verification.yml`

That workflow:

- installs the pinned Lean toolchain
- fetches Mathlib cache artifacts
- runs `lake build`
- regenerates all formalization and axiom-audit reports
- fails if generated artifacts are out of date
- uploads the generated verification artifacts

## Notes

- The concrete `Concrete*` modules are the active first-principles foundation.
- The paper-facing theorem modules now terminate directly at that concrete
  stack; there is no remaining abstract `...Model` / `...Theory` proof boundary
  for manifest-tracked manuscript declarations.
