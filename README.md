# Semantic Convergence in Interactive Learning

This repository contains the H10 manuscript source and its Lean 4
formalization.

## Current Source

- Canonical manuscript: `semantic_convergence_interactive_learning.tex`
- Bibliography: `semantic_convergence_interactive_learning.bib`
- Lean import surface: `SemanticConvergence.lean`
- H10 ontology façade: `SemanticConvergence/Ontology.lean`
- H10 formal-item ledger: `h10_formal_item_ledger.md`
- H10 correspondence punchlist: `h10_lean_correspondence_punchlist.md`

Older manuscript drafts, generated previews, source tarballs, and stale
hand-written Lean issue notes have been moved under `archive/`.

## Verification Status

The Lean project builds on the concrete foundation in `SemanticConvergence/`.
The current H10 manuscript is aligned with the verified route-2
Bayes/Gibbs/kernel-functional theorem through the ontology façade, and the
zero-out support/rate/noise companion route is now stated as an explicit
certificate package rather than as an unstated statistical rate theorem.

The generated `formalization_*.md`, `lean_*_audit.md`,
`SemanticConvergence/Manifest.lean`, and `SemanticConvergence/AxiomAudit.lean`
files are generated from the H10 source. The current generated audit reports
paper-complete coverage, paper-complete derivation, proof-citation closure,
zero active H10 correspondence risks, zero suspicious manifest entries, and
`SemanticConvergence.fullyFirstPrinciples = true`.

## Repository Layout

- `SemanticConvergence/`: Lean source files.
- `SemanticConvergence.lean`: top-level Lean import surface.
- `semantic_convergence_interactive_learning.tex`: canonical H10 manuscript.
- `scripts/generate_formalization_manifest.py`: generates paper-to-Lean
  coverage and audit artifacts.
- `archive/`: older drafts and stale hand-written notes removed from the
  active working surface.

## Build

This project uses Lean `v4.29.0` with Mathlib `v4.29.0`.

```bash
lake build
```

To refresh generated formalization and audit reports:

```bash
python3 scripts/generate_formalization_manifest.py
```

That command regenerates:

- `formalization_manifest.md`
- `h10_formal_item_ledger.md`
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

## CI

GitHub Actions verification lives in:

- `.github/workflows/lean-verification.yml`

The workflow installs the pinned Lean toolchain, fetches Mathlib cache
artifacts, runs `lake build`, regenerates formalization and axiom-audit
reports, and fails if generated artifacts are out of date.
