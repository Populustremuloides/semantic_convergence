# Lean verification — remaining issues (frozen hand-off, do not edit)

Third-pass audit. The `lean_verification_punchlist.md` from the original
frozen spec remains authoritative, and `lean_adversarial_review.md`
remains the original reviewer-style report. This file replaces the
previous `lean_verification_remaining_issues.md` hand-off.

- The A-series (ten deliverables from the first hand-off) is carried
  forward unchanged; no A-item regressed on this pass.
- The B-series is reorganized: B1 and B2 from the second hand-off are
  now closed, B3 is narrowed but still open, and two new items B4 and
  B5 are promoted out of the "residual acceptance criteria" embedded
  in the prior B1 to be visible as their own hard deliverables.

Scope of this re-audit: file-by-file read of
`SemanticConvergence/Semantic.lean`,
`SemanticConvergence/ConcretePosteriorDecay.lean`,
`SemanticConvergence/Rates.lean`, `SemanticConvergence/ConcreteRates.lean`,
`SemanticConvergence/Manifest.lean` (closing section, L1320–1548),
`SemanticConvergence/AxiomAudit.lean`, plus on-disk olean freshness.
The Lean toolchain is not available in this sandbox, so I have not
independently run `lake build` or `#print axioms`. All verdicts below
read the source and compare with the claims in
`lean_verification_progress.md`.

---

## Where we stand, one line per A-item (unchanged since the second pass)

| A-item | Title | Previous verdict | Current verdict |
| --- | --- | --- | --- |
| A1 | `thm_summable_support_insufficient` must use its input schedule | ✗ tautology | ✔ done |
| A2 | `thm_separating_support_convergence` must not offload decay into hypothesis | ~ partial | ~ substantially done (recurrence bound in the conclusion; substrate still zero-collapses — see B4) |
| A3 | `cor_support_necessary` must not negate a conjunct by hypothesis | ~ partial | ✔ done |
| A4 | Rate chain must prove a rate, not rename a hypothesis | ~ partial | ✔ done |
| A5 | Substrate posterior-decay must go multi-step and expose rate | ~ partial | ✔ done (nondegenerate `c(δ) = (1/2) + min(δ,1)/4` threaded through the N-step composition) |
| A6 | `Manifest.lean` proof-kind tags must match proof bodies | ✗ mislabeled | ✔ done |
| A7 | Manuscript must not overclaim on multi-step convergence | ~ partial | ✔ done |
| A8 | Axiom audit must distinguish `native_decide` auxiliaries | ✗ unexplained | ✔ done |
| A9 | Source tree must be observed to compile | ~ mostly stale | ~ mostly fresh — see B3 |
| A10 | Manifest closing theorems must reflect retagging | ✗ mislabeled | ✔ done |

Since the second pass, two more entries flipped from suspicious to
audited (`suspiciousManifestEntryCount`: 25 → 23;
`manifestTheoremLikeSemanticallyAuditedEntryCount`: 53 → 55).
`semanticAuditClosed` and `fullyFirstPrinciples` remain `false`, which
is the correct honest state — 23 theorem-like entries are still
`singleLemmaApplication` or `definitionalUnfold`.

---

## Part B — Open deliverables after the third pass

B1 and B2 from the second hand-off are closed and are recorded at the
bottom of this section for continuity. Three items remain open: B3
(build freshness), B4 (audit-visible doc-note on the substrate
dependency of the per-step decay bound), and B5 (substrate extension
for the strong-reading closure of the master theorem).

### B3. Finish the build — bring `Manifest.olean` and `AxiomAudit.olean` current

*Status.* Narrowed but still open.

| Module | Source mtime | olean mtime | Delta |
| --- | --- | --- | --- |
| Semantic | 17:34 | 17:35 | fresh |
| Noise | 17:14 | 17:35 | fresh |
| Rates | 17:13 | 17:35 | fresh |
| ConcretePosteriorDecay | 17:25 | 17:25 | fresh |
| ConcreteSemantic | 15:31 | 15:34 | fresh |
| ConcreteRates | 17:23 | 17:25 | fresh |
| **Manifest** | **17:42** | **17:39** | **stale by ~3 min (was ~5 min)** |
| **AxiomAudit** | **17:41** | **17:40** | **stale by ~1 min (was ~37 min)** |

The gap has narrowed sharply for AxiomAudit (37 min → 1 min) and
slightly for Manifest (5 min → 3 min). Both modules are harness modules
(counting theorems / `#print axioms` dispatch), not load-bearing proof
modules, so the narrow gap does not change any substantive verdict.
But until the oleans are in fact newer than the sources, the
`native_decide`-closed counting theorems (notably
`suspiciousManifestEntryCount_eq = 23`, `semanticAuditClosed_eq = false`,
`fullyFirstPrinciples_eq = false`) are not attached to the current
source versions.

*Acceptance criterion for B3.*
1. Run `lake build SemanticConvergence.Manifest` and
   `lake env lean SemanticConvergence/AxiomAudit.lean` one more time,
   so both oleans are strictly newer than their sources.
2. Verify that every `.olean` in
   `.lake/build/lib/lean/SemanticConvergence/` has `mtime ≥ mtime` of
   the corresponding `.lean` source.
3. Re-render `lean_axiom_audit.md` from the fresh audit run; confirm
   the diff against the checked-in version is empty or trivial.

### B4. Make the substrate dependency of the per-step decay bound audit-visible

*Status.* New deliverable, promoted out of the residual acceptance
criterion attached to the previous B1.

*Target.* `SemanticConvergence/ConcretePosteriorDecay.lean`
`oneStepObserverFiberPosteriorOdds_le_decayBound_of_outside_zero`
(L301–317) and its immediate callers.

*What is there now.* The per-step posterior-odds bound

```
U.oneStepObserverFiberPosteriorOdds π h a ω pstar o ≤
  posteriorDecayFactor δ * U.observerFiberPosteriorOdds π h ω pstar
```

is proved by establishing `hCollapse : oneStepObserverFiberPosteriorOdds = 0`
and then applying `0 ≤ posteriorDecayFactor δ * observerFiberPosteriorOdds`
via `mul_nonneg`. That is a valid proof, and under the current finite-
support rational substrate it is the only proof available (any positive
separating-support floor forces one-step extinction at a zero-out witness).
But structurally, the nondegenerate `posteriorDecayFactor δ` that was
installed to close A5 and B1 is not load-bearing here — the inequality
would hold for any nonneg factor, because the left-hand side is already
zero before the factor is consulted.

This is a genuine, audit-relevant property of the substrate, not a bug
in the proof. The issue is that a reader following the Lean
declarations in isolation has no signal pointing at it. The docstring
on L292–300 describes the per-step bound as "nondegenerate floor-
dependent," which is true of the *bound function* but not of the
*current substrate's per-step behavior*. Those are different things
and the file should make the gap visible.

*Acceptance criterion for B4.* Both:
1. Rewrite the docstring on
   `oneStepObserverFiberPosteriorOdds_le_decayBound_of_outside_zero`
   to state explicitly, in the file itself, that the inequality is
   established via substrate zero-collapse (`hCollapse`) and that the
   nondegenerate `posteriorDecayFactor δ` is threaded through the
   downstream N-step composition for future substrate extension
   (pointer to B5). One short paragraph inside `/-- ... -/` is enough;
   the goal is audit-visibility, not reshaping the proof.
2. Add a mirror note on
   `SemanticConvergence/ConcreteRates.lean` at
   `posteriorRateBound_of_positiveDecay` (L87–110) and
   `hasConcentrationCertificate` (L116–129) explaining that the rate
   composition is rate-magnitude-aware but that the current substrate
   produces a per-step process that saturates at zero on the first
   zero-out observation, so the tighter envelope is not exercised.
3. Optional, but recommended: re-tag the affected manifest entries
   (`thm_separating_support_convergence`,
   `thm_separating_support_rate`,
   `cor_separating_support_finite_time`) with a new
   `ProofKind.substrateCollapseBounded` or similar, distinct from
   `substantive` / `rateComposition`, so the manifest's own closing
   theorem counts this class separately from proofs that use the rate
   magnitude. If a new `ProofKind` is introduced, update
   `suspiciousManifestEntryCount`, `manifestTheoremLike
   SemanticallyAuditedEntryCount`, and their `_eq` theorems accordingly.

### B5. Extend the substrate so the rate magnitude is load-bearing

*Status.* New deliverable, promoted from the "residual acceptance
criterion if the strong reading is desired" note attached to the
previous B1. This is the only deliverable remaining between the current
tree and the strong-reading closure of "the Lean formalization
independently verifies the paper's master support theorem."

*Target.* `SemanticConvergence/ConcreteSemantic.lean` and/or a new
companion file; `SemanticConvergence/ConcretePosteriorDecay.lean`'s
per-step bound; downstream manifest entries.

*What is needed.* Replace the current finite-support rational substrate
for `predictiveLawInClass` / `predictiveLawOutsideClass` with a
positive-support variant (soft likelihoods on a finite or countable
observation alphabet, no zero-out observations). Under that substrate:

- `oneStepObserverFiberPosteriorOdds π h a ω pstar o` is strictly
  positive whenever the prior odds are strictly positive and both
  predictive laws have positive mass on `o`.
- The per-step odds multiplier is the likelihood ratio
  `(predictiveLawInClass ....mass o) / (predictiveLawOutsideClass ....mass o)`,
  which on a separating-action / zero-out-style observation is strictly
  less than `1`.
- `oneStepObserverFiberPosteriorOdds_le_decayBound_of_outside_zero`
  gets replaced (or paired with) a bound of the form
  `U.oneStepObserverFiberPosteriorOdds ≤ c(δ) * U.observerFiberPosteriorOdds`
  where `c(δ) ≤ posteriorDecayFactor δ` and `c(δ) > 0`, and `hCollapse`
  no longer appears in the proof.

*Acceptance criterion for B5.* All of:
1. A substrate-level lemma establishing a per-step odds contraction
   whose bound scales with `δ` (not with zero-collapse).
2. Replacement of the existing per-step bound proof so the RHS factor
   `posteriorDecayFactor δ` is load-bearing — removal of `hCollapse`
   from the proof of
   `oneStepObserverFiberPosteriorOdds_le_decayBound_of_outside_zero`
   (or substitution of that theorem by a positive-support variant).
3. `thm_separating_support_convergence` and the rate chain
   (`lem_one_step_drift`, `prop_exp_rate`, `thm_exp_rate_concentration`)
   re-targeted against the new substrate, with their manifest entries
   promoted from `substrateCollapseBounded` (introduced in B4) back to
   `substantive` / `rateComposition`.
4. Updated abstract in `semantic_convergence_interactive_learning.tex`:
   the narrower-scope disclaimer introduced for A7 can be shortened
   to describe only the concrete-stack scope without the "rate is
   vacuously satisfied by zero-collapse" caveat.
5. `#print axioms` re-run; expect only the canonical
   `[propext, Classical.choice, Quot.sound]` baseline plus, if
   `MeasureTheory`-valued kernels are used,
   `MeasureTheory.ae_mem_limsup_atTop_iff` as the only Mathlib-backed
   dependency. Update `lean_axiom_audit.md`.

This is substrate engineering, not proof chasing, and it is the only
item on this list that is not a closeout pass. Estimated scope: one
new `ConcreteChannel` / soft-likelihood module, plus re-wiring of the
per-step bound and the master theorem. The N-step composition, the
rate-factor envelope, the certificate, the same-view transfer lemmas,
and the entire Part A scaffold survive unchanged.

### Closed — B1 and B2 from the second hand-off

Recorded here for continuity; neither is still open.

**B1 (closed).** The rate function `posteriorDecayRate δ` is no longer
the degenerate `if 0 < δ then 1 else 0`. It is now
`(1/2) + min(δ, 1) / 4` on `δ > 0`, with supporting theorems
`posteriorDecayRate_pos_of_pos`, `posteriorDecayRate_lt_one_of_pos`,
`posteriorDecayRate_strictMonoOn_unit` (on `Set.Ioc (0 : Rat) 1`),
`posteriorDecayFactor_nonneg`, and `posteriorDecayFactor_le_half_of_pos`.
The induced `posteriorDecayFactor δ` lies in `(1/4, 1/2)` on `(0, 1]`.
`nStepPosteriorDecayBound_of_stepBound` composes the factor through
`N` steps by honest induction. The separate question of whether the
substrate actually exercises the nondegenerate factor is promoted to
B4 (audit-visibility) and B5 (substrate extension).

**B2 (closed).** The old
`posteriorRateFactor (_δGain : Float) (δDrift : Float) (N : Nat)` —
which used `δDrift` as a boolean switch and ignored `δGain` — is gone.
It is replaced by `posteriorRateFactorFromFloor (N : Nat) : Rat :=
(1/2)^N`, with a clean doc-comment explaining why the envelope is
uniform in the current substrate. The `δDrift` / `δGain` parameters
of `hasConcentrationCertificate` are now honest lower-bound witnesses
(`δDrift ≤ oneStepLogOddsDrift`, `hasExpectedGainLowerBound … κ δGain`),
not cosmetic. The rate factor itself depends only on the rational floor
`δ` and the step count `N`, which is the shape previously requested
under B2(a).

---

## Part C — What the manuscript can now claim truthfully

Given the current state of the tree, the defensible claim is:

> A public Lean 4 repository contains Lean counterparts for every
> manifest-tracked item in the paper, built on an explicit finite-
> support rational substrate with a Mathlib-backed measure-theoretic
> dependency for the conditional Borel–Cantelli lemma. All 106
> manifest-tracked declarations have been compiled and their axiom
> dependencies published; every declaration's axiom footprint is
> either the canonical `[propext, Classical.choice, Quot.sound]`
> baseline, a strict subset thereof, or the canonical baseline plus
> the `native_decide` auxiliary used by the manifest's own internal
> counting theorems. The manifest's internal audit, which classifies
> every non-definition entry as `substantive` or as one of seven
> weaker proof kinds, reports
> `suspiciousManifestEntryCount = 23` and
> `semanticAuditClosed = false`, honestly flagging the 23 theorem-
> like entries whose Lean proof is a single-lemma application or a
> definitional unfold. Around Section~\ref{sec:main}, the Lean
> declarations formalize a narrower concrete stack than the paper's
> prose: a one-step separating-action/observation witness, the
> induced one-step posterior-complement collapse, a generic N-step
> recurrence bound, and a rate scaffold parametrized by a strictly-
> increasing posterior-decay rate
> `c(δ) = (1/2) + min(δ, 1) / 4` on `(0, 1]`. In the current finite-
> support rational substrate the per-step observer-fiber odds collapse
> to zero at a zero-out observation, so the N-step bound holds
> vacuously strongly against that rate; a future measure-theoretic
> substrate would make the rate magnitude load-bearing without
> reworking the composition scaffold.

The following claim remains **not** defensible at this state:

> The Lean formalization independently verifies the paper's master
> support theorem.

That claim requires B5 (substrate extension); B3 and B4 do not unlock
it.

---

## Part D — Recommended work order

Four items left after this pass, ordered by scope:

1. **B3** — mechanical rebuild. One `lake build` pass brings
   `Manifest.olean` and `AxiomAudit.olean` current. Expect no content
   change; the point is to attach the checked-in counting theorems to
   current sources.
2. **B4** — audit-visible doc-note on the per-step bound's substrate
   dependency, plus mirror notes at the rate composition and the
   certificate. Optional re-tagging of the affected manifest entries
   under a new `ProofKind` variant. Closeout work; no new proofs.
3. **B5** — substrate extension to positive-support channels / soft
   likelihoods. Only path to the strong reading. Out of scope for a
   closeout pass; plan as a separate release if the target is strong
   verification.
4. Consolidation of 23 still-suspicious entries — not blocking the
   weak reading, and noted here only because the closing theorem
   `semanticAuditClosed = false` will remain `false` until every
   theorem-like entry is either `substantive`, `constructiveExistential`,
   `rateComposition`, or a B4-introduced `substrateCollapseBounded`.
   Likely achievable by tightening proofs of entries currently tagged
   `singleLemmaApplication` / `definitionalUnfold`; low priority.

If the goal is "fully considered verified" in the weak sense — every
theorem has a Lean counterpart of some shape, scope limitations
documented — steps 1, 2, and (optionally) 4 close it.

If the goal is "fully considered verified" in the strong sense — the
Lean independently derives the paper's multi-step almost-sure
convergence — step 3 is still the remaining work.
