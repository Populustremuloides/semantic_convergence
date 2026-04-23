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
- `lean_axiom_audit.md` currently reports `72` canonical-baseline rows, `24`
  expected `native_decide`-auxiliary rows, `10` lighter-than-baseline rows,
  and `0` genuine unexpected drift rows
- `lean_axiom_audit.md` records the actual per-declaration axiom dependencies

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
- `SemanticConvergence.thm_semantic_convergence` and
  `SemanticConvergence.thm_kernel_semantic_convergence` currently certify the
  corresponding selector and kernel realizations inside that closed semantic
  theorem stack.

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
