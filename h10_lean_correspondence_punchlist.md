# H10 Lean Correspondence Punchlist

Canonical manuscript: `semantic_convergence_interactive_learning.tex`

Goal: every formal proof-bearing claim in the H10 manuscript should either cite
an exact Lean declaration or be explicitly marked as narrative, interpretation,
or an open problem. A reader should be able to read any proof and see the
corresponding Lean code without guessing which older draft, stale lock file, or
historical theorem name is authoritative.

## Completion Standard

A manuscript item is one-to-one complete only when all of the following hold.

- The item appears in the H10 ledger with its TeX label, section, title, and
  exact Lean declaration.
- The Lean declaration has the same mathematical statement, not just a related
  helper statement.
- Any assumptions in the manuscript are named in Lean as fields or explicit
  hypotheses with the same content.
- The manuscript proof cites the Lean declaration, or the statement is
  downgraded to a remark/prose explanation.
- The generated manifest and axiom/proof audits are regenerated from the H10
  source and compile with `lake build`.

## Already Completed In This Cleanup

- H10 is now the canonical root manuscript at
  `semantic_convergence_interactive_learning.tex`.
- Earlier manuscript drafts, generated previews, source tarballs, and stale
  handwritten Lean issue notes are under `archive/`.
- The active root now contains a fresh H10-centered punchlist instead of the old
  lock/punchlist files.
- The H10 manuscript label text has been normalized from “H7” to “H10”.
- `SemanticConvergence/Ontology.lean` exposes the H10 observer/agent/coupling
  surface and wraps the existing route-2 convergence theorem.

## Kitchen-Sink Pass Status

- Phase 1 is implemented: the generator now parses the H10 root manuscript,
  includes the `assumptions` environment, no longer cites archived lock files as
  active sources, and regenerates the manifest, bridge, proof, axiom, and
  progress artifacts from H10.
- Phase 2 is implemented as `h10_formal_item_ledger.md`: every H10 formal
  environment has a ledger row, exact Lean declaration, correspondence status,
  and missing-declaration check. The current missing-declaration count is zero.
- Phase 3 is implemented for the main H10 package: `Ontology.lean` now exposes
  `SemanticLearningPackage`, the manuscript triplet `𝔎`, the assumptions alias
  `ass_main_verified_package`, and the public theorem
  `h10_verified_semantic_learning_package_converges`, while retaining H7
  compatibility aliases.
- Phase 4 is implemented for proof environments: every manuscript proof now
  carries a local `Lean: \path{...}` citation to the exact declaration selected
  by the H10 ledger, with conditional companion proofs marked as conditional.
  The generated audit now counts this proof-citation surface and reports zero
  missing proof citations.
- Phase 5 is implemented for the active H10 surface: the manuscript prose and
  formal statements have been softened where needed so the H10 ledger is the
  authoritative paper-to-Lean correspondence map.
- Phase 6 is implemented: the support/rate/noise companion stack now exposes
  `ZeroOutRatePackage` and package-level residual/posterior-share wrappers,
  and the generated audit reports zero active H10 correspondence risks.

## Phase 1: Make H10 The Only Manifest Source

- Update `scripts/generate_formalization_manifest.py` so the canonical source
  is the active H10 manuscript and the generated comments no longer reference
  archived lock files.
- Extend the extractor to include the `assumptions` environment, especially
  `ass:main-verified-package`, because the main theorem depends on that package
  as a formal object.
- Regenerate `formalization_manifest.md`, `formalization_audit.md`,
  `formalization_bridge.md`, `lean_theorem_census.md`, `lean_proof_audit.md`,
  `lean_concrete_theorem_audit.md`, `lean_verification_progress.md`,
  `lean_axiom_audit.md`, `SemanticConvergence/Manifest.lean`, and
  `SemanticConvergence/AxiomAudit.lean`.
- Confirm generated H10 correspondence notes do not cite archived issue files as
  active sources.
- Acceptance check: `python3 scripts/generate_formalization_manifest.py`
  followed by `lake build` produces no unstaged generated drift.

## Phase 2: Establish The H10 Formal-Item Ledger

- Build a ledger for every H10 `definition`, `lemma`, `proposition`,
  `corollary`, `theorem`, and `assumptions` block.
- Record the exact Lean declaration for each item, including the new ontology
  wrapper where it is the cleanest H10-facing name.
- Mark each item as one of `exact Lean counterpart`, `conditional Lean
  counterpart`, `needs Lean wrapper`, `needs manuscript softening`, or
  `narrative only`.
- Add a CI-checkable failure mode for any formal item without a Lean
  declaration or an explicit non-formal classification.
- Acceptance check: the H10 ledger accounts for every formal environment in
  the manuscript and has no blank Lean-declaration cells except items explicitly
  classified as non-formal.

## Phase 3: Normalize H10 Lean Names

- Add H10-facing aliases or renames in `SemanticConvergence/Ontology.lean` so
  the public names say `H10`, not `H7`, while preserving old names as
  compatibility aliases if useful.
- Give the semantic-learning package a Lean declaration whose name matches the
  manuscript object `𝔎 = (𝓘, 𝓙, 𝓢)`.
- Make `ass:main-verified-package` correspond to a single Lean package with
  fields matching `(M1)` through `(M7)`.
- Prefer the H10-facing theorem name in manuscript proofs, for example a short
  ontology-level wrapper over the long route-2 theorem name.
- Acceptance check: the main theorem proof can cite one compact H10 Lean path
  plus the package fields, instead of a long internal theorem name and prose
  reconstruction.

## Phase 4: Add Proof-Level Lean Citations In The Manuscript

- Define a consistent citation convention, such as `Lean: \path{...}` at the
  start or end of every proof.
- Insert the Lean citation into every proof of a formal theorem, proposition,
  lemma, corollary, and definition whose correctness is claimed as verified.
- For proof sketches that combine several Lean lemmas, list the exact Lean
  declarations used by the composition.
- For prose-only arguments in the introduction, implications, discussion,
  conclusion, and diagnostic appendix, avoid saying they are Lean-verified
  unless they point to a formal declaration.
- Acceptance check: a text search for `\begin{proof}` can be matched against a
  nearby `\path{SemanticConvergence...}` citation or an explicit “prose
  explanation” marker. The generated manifest now performs this check by
  matching each proof body against the exact Lean declaration selected by the
  H10 ledger.

## Phase 5: Section-By-Section Correspondence Audit

- Sections 1-2: ensure setup claims are either notation conventions or point to
  Lean definitions in `Foundations`, `ConcreteCore`, `ConcretePrior`, or
  `ConcreteSubstrateBridge`.
- Section 3: tie the ontology prose to `SemanticConvergence.Ontology.Observer`,
  `SemanticConvergence.Ontology.Agent`, and
  `SemanticConvergence.Ontology.Coupling`; classify the diagnostic checklist as
  narrative unless formalized.
- Section 4: verify the four-set hierarchy, refinement chain, strict hierarchy,
  and observable quotient against the existing hierarchy declarations.
- Sections 5-6: verify the two-observer functional, kernel lift, compact kernel
  lift, variational identity, and KL-necessity against `Functional`, `Belief`,
  `CompactKernel`, and `DiscreteConvexDuality`.
- Section 7: re-audit the long action/noise/compact-action block. This section
  has many formal statements and is the highest risk for stale theorem names or
  claims that are true only under an older support-route interface.
- Section 8: make the H10 main theorem and `(M1)`--`(M7)` package exact. This is
  the central one-to-one target.
- Section 9: verify all self-referential reduction statements against
  `SelfReference` and `ConcreteSelfReference`; explicitly mark eventual
  isolation as a hypothesis where Lean treats it as one.
- Section 10: verify the boundary/near-miss statements against `Boundary`,
  `ConcreteBoundary`, and the EFE/MI declarations.
- Section 11: separate application prose from formal surrogate claims. The
  amortized-surrogate theorem currently needs special attention because H10
  phrases semantic recovery through an additional Hellinger-spine condition,
  while the Lean surrogate stack primarily derives the separating-support floor
  and finite-time consequence.
- Sections 12-13: treat discussion and conclusion as synthesis unless each
  mathematical sentence cites an already-ledgered theorem.
- Appendix: decide whether the diagnostic procedure remains a prose checklist
  or gets a small Lean structure. If it remains prose, do not count it as a
  verified theorem.
- Acceptance check: every section has a completed audit note saying exactly
  which claims are formal, conditional, or narrative.

## Phase 6: Resolve Known H10 Mismatch Risks

- Closed in this pass: the main theorem now cites the H10 ontology wrapper
  `SemanticConvergence.Ontology.Coupling.h10_verified_semantic_learning_package_converges`.
- Closed in this pass: the triplet object `(𝓘, 𝓙, 𝓢)` is surfaced as
  `SemanticLearningPackage`, with `def_semantic_learning_package` and
  `predictiveKernelSemanticLearningPackage` as manuscript-facing declarations.
- Closed in this pass: the assumptions package `(M1)`--`(M7)` is surfaced as
  `ass_main_verified_package` and appears as a formal `assumptions` item in the
  H10 ledger.
- Closed in this pass: every proof that belongs to a conditional support/rate,
  noise, surrogate, or support-route item now marks itself as a conditional
  counterpart or conditional companion route at the local Lean citation.
- Closed in this pass: the seven prior support/rate/noise risks have been
  resolved by stating the rate surface through `ZeroOutRatePackage` and the
  package-level Lean declarations
  `zeroOutRatePackage_residualRate`,
  `zeroOutRatePackage_posteriorShareFiniteTime`,
  `zeroOutRatePackage_oneStepResidual`,
  `zeroOutRatePackage_expRate`,
  `zeroOutRatePackage_sameViewResidualRate`,
  `zeroOutRatePackage_sameViewPosteriorShareFiniteTime`, and
  `zeroOutRatePackage_decodableNoiseTransfer`.
- Closed in this pass: the generator classifies those package-level wrappers as
  `rate-composition` rather than suspicious single-helper proof bodies, so the
  semantic manifest audit closes without hiding them.
- Current status: `formalization_audit.md` reports first-principles complete
  `yes`, active H10 correspondence risks `0`, proof-citation surface closed
  `yes`, and suspicious manifest entries `0`.
- Remaining non-formal work: the diagnostic appendix is treated as an
  operational guide, not a theorem, unless a future pass adds a Lean diagnostic
  classification object.

## Phase 7: Final Verification Gate

- Run `lake build`.
- Run `python3 scripts/generate_formalization_manifest.py`.
- Run `lake env lean SemanticConvergence/AxiomAudit.lean`.
- Compile the canonical manuscript PDF from
  `semantic_convergence_interactive_learning.tex`.
- Confirm the generated audit reports zero missing Lean declarations and zero
  manuscript proof environments without exact Lean citations.
- Check `git diff` to ensure generated artifacts, manuscript citations, and
  Lean names agree.
- Acceptance check: the final README can truthfully say that the H10 manuscript
  has a one-to-one Lean correspondence for every formal proof-bearing claim,
  while clearly separating narrative discussion and open problems from formal
  verification.
