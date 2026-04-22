# Semantic Convergence in Interactive Learning

This repository contains the current manuscript source for
`semantic_convergence_interactive_learning.tex` together with its Lean 4
formalization.

## Current status

The Lean project is mechanically checked and first-principles complete relative
to the concrete foundation adopted in the repo.

- `106/106` core manuscript declarations are formalized
- `106/106` are marked `derived`
- `106/106` are marked `concrete-stack`
- `fullyFirstPrinciples = true`

The generated status artifacts are:

- [formalization_manifest.md](formalization_manifest.md)
- [formalization_audit.md](formalization_audit.md)
- [formalization_bridge.md](formalization_bridge.md)

## Repository layout

- `SemanticConvergence/`: Lean source files
- `SemanticConvergence.lean`: top-level Lean import surface
- `semantic_convergence_interactive_learning.tex`: canonical manuscript source
- `scripts/generate_formalization_manifest.py`: regenerates the manifest and
  audit artifacts

## Build

This project uses Lean `v4.29.0`.

```bash
lake build
```

To refresh the generated formalization reports:

```bash
python3 scripts/generate_formalization_manifest.py
```

## Notes

- The concrete `Concrete*` modules are the active first-principles foundation.
- Some older abstract `...Model` / `...Theory` APIs remain in the source tree as
  legacy compatibility scaffolding, but they are not part of the active trust
  boundary for manifest-tracked manuscript declarations.
