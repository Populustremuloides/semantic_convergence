# Lean verification — remaining issues (frozen hand-off, do not edit)

Fifth-pass audit. The `lean_verification_punchlist.md` from the original
frozen spec remains authoritative, and `lean_adversarial_review.md`
remains the original reviewer-style report. This file replaces the
previous (fourth-pass) `lean_verification_remaining_issues.md` hand-off.

- The A-series (ten deliverables from the first hand-off) is carried
  forward unchanged; no A-item regressed on this pass.
- The B-series: **B1, B2 closed on second pass; B4 closed on fourth
  pass; B5 substantially closed on fourth pass; C1 closed on fifth
  pass (converse retargeted against the residual-odds predicate with a
  fresh `no_oneStepResidualPosteriorConcentrates` counterexample);
  C3 PARTIALLY addressed on fifth pass by the new
  `ConcreteProbabilisticConvergence.lean` module. B3 regressed (harness
  olean staleness is now worse than on the fourth pass).**
- Fifth-pass findings: C1 closed, C3 partially addressed but replaced
  by a new hypothesis-laundering gap (D1), C4 closes with B3, and five
  new D-series residuals are recorded below.

Scope of this re-audit: file-by-file read of the newly added
`SemanticConvergence/ConcreteProbabilisticConvergence.lean`,
the updated `SemanticConvergence/Semantic.lean`,
`SemanticConvergence/Rates.lean`,
`SemanticConvergence/Noise.lean`,
`SemanticConvergence/Manifest.lean` (closing section),
`SemanticConvergence/AxiomAudit.lean`, plus on-disk olean freshness and
a cross-check against the abstract and conclusion of
`semantic_convergence_interactive_learning.tex`. The Lean toolchain is
not available in this sandbox, so I have not independently run
`lake build` or `#print axioms`. All verdicts below read the source and
compare with the claims in `lean_verification_progress.md` and the
retargeted master-theorem bodies.

---

## Where we stand, one line per A-item (unchanged since the third pass)

| A-item | Title | Previous verdict | Current verdict |
| --- | --- | --- | --- |
| A1 | `thm_summable_support_insufficient` must use its input schedule | ✗ tautology | ✔ done, retargeted against residual-odds predicate on fifth pass (see C1-closed) |
| A2 | `thm_separating_support_convergence` must not offload decay into hypothesis | ~ partial | ~ shifted: the deterministic sibling is clean; the new probabilistic entry offloads the contraction into `HasSupportwiseResidualContractionWitness` (see D1) |
| A3 | `cor_support_necessary` must not negate a conjunct by hypothesis | ~ partial | ✔ done |
| A4 | Rate chain must prove a rate, not rename a hypothesis | ~ partial | ✔ done |
| A5 | Substrate posterior-decay must go multi-step and expose rate | ~ partial | ✔ done |
| A6 | `Manifest.lean` proof-kind tags must match proof bodies | ✗ mislabeled | ~ partial — retag of `thm_separating_support_convergence` to `ProofKind.substantive` masks the D1 hypothesis-laundering |
| A7 | Manuscript must not overclaim on multi-step convergence | ~ partial | ~ partial — abstract and conclusion now say "proves an almost-sure one-step residual-odds contraction" without mentioning the supportwise-witness hypothesis (see D6) |
| A8 | Axiom audit must distinguish `native_decide` auxiliaries | ✗ unexplained | ~ regressed by B3 staleness |
| A9 | Source tree must be observed to compile | ~ mostly stale | ~ regressed — see B3 |
| A10 | Manifest closing theorems must reflect retagging | ✗ mislabeled | ✔ done (counts updated: 65 substantive / 10 constructiveExistential / 3 rateComposition / 0 suspicious) |

Current closing theorems in `Manifest.lean` (unverified until B3
closes):
`substantiveEntryCount_eq = 65`,
`constructiveExistentialEntryCount_eq = 10`,
`rateCompositionEntryCount_eq = 3`,
`singleLemmaApplicationEntryCount_eq = 0`,
`definitionalUnfoldEntryCount_eq = 0`,
`fieldProjectionEntryCount_eq = 0`,
`placeholderTruthEntryCount_eq = 0`,
`heuristicOtherEntryCount_eq = 0`,
`suspiciousManifestEntryCount_eq = 0`,
`semanticAuditClosed_eq = true`,
`fullyFirstPrinciples_eq = true`.

---

## Part B — Open / closed deliverables after the fifth pass

**B1, B2, B4 closed. B5 substantially closed (deterministic
positive-support substrate is live and load-bearing in the deterministic
master theorem). C1 closed on fifth pass. C3 partially addressed by a
new probabilistic wrapper module; see D1. B3 regressed (olean staleness
is worse than on the fourth pass).**

### B3. Finish the build — bring `Manifest.olean` and `AxiomAudit.olean` current

*Status.* Regressed from fourth pass. Both harness oleans are now
stale, and the AxiomAudit gap is larger than before.

| Module | Source mtime | olean mtime | Delta |
| --- | --- | --- | --- |
| Semantic | 21:48 | 21:49 | fresh |
| ConcreteProbabilisticConvergence | 21:41 | 21:41 | fresh (newly added) |
| ConcretePosteriorDecay | 18:24 | 18:24 | fresh (unchanged since fourth pass) |
| ConcreteSemantic | 18:20 | 18:21 | fresh (unchanged since fourth pass) |
| Rates | 21:48 | 21:49 | fresh |
| Noise | 21:41 | 21:42 | fresh |
| **Manifest** | **21:49** | **21:43** | **stale by 6 min** |
| **AxiomAudit** | **21:49** | **21:17** | **stale by 32 min** |

AxiomAudit was 2 min stale on the fourth pass; it is 32 min stale now,
and the `AxiomAudit.lean` source references
`SemanticConvergence.thm_separating_support_convergence`, which in the
current source tree resolves to the newly-added probabilistic
declaration. The checked-in `AxiomAudit.olean` was therefore built
against the old deterministic declaration and does not reflect the
current symbol table.

*Acceptance criterion for B3.* Unchanged from the fourth pass:
1. `lake build SemanticConvergence.Manifest` and
   `lake env lean SemanticConvergence/AxiomAudit.lean` so both oleans
   are strictly newer than their sources.
2. Every `.olean` in `.lake/build/lib/lean/SemanticConvergence/` has
   `mtime ≥ mtime` of the corresponding `.lean` source.
3. Re-render `lean_axiom_audit.md` from the fresh audit run; diff the
   checked-in version against the fresh output.

### B4 (closed on fourth pass)

Unchanged.

### B5 (substantially closed on fourth pass; deterministic track)

Unchanged. Note the `ConcretePrefixMachine` soft-substrate work in
`ConcretePosteriorDecay.lean` and `ConcreteSemantic.lean` has not been
touched since the fourth pass (both files at 18:20 / 18:24). The master
theorem on that substrate (now renamed
`thm_separating_support_convergence_deterministic`,
`Semantic.lean` L318) is still load-bearing against
`softOneStepObserverFiberResidualOdds_le_decayBound_of_zeroOut_supportUnion`.

### Closed — B1 and B2 from the second hand-off

Unchanged.

---

## Part C — Residual issues from the fourth pass — final status

### C1 (CLOSED on fifth pass)

`thm_summable_support_insufficient` (`Semantic.lean` L747–767) is now
stated against `oneStepResidualPosteriorConcentrates`, and a fresh
counterexample `no_oneStepResidualPosteriorConcentrates`
(`Semantic.lean` L689–742) supplies the witness. The converse and
positive sides now share the residual-odds predicate.

### C2 (NOT YET CLOSED — still cosmetic)

No legacy docstring has been added on `oneStepPosteriorConcentrates`
(`Semantic.lean` L241–251). A reader sweeping the file still sees two
sibling predicates with no indication that the first is strictly weaker
and retained for bookkeeping. Still minor. Acceptance criterion
unchanged.

### C3 (PARTIALLY ADDRESSED on fifth pass; see D1)

A new module `SemanticConvergence/ConcreteProbabilisticConvergence.lean`
(424 lines, 19 KB) has been added. It is substantive measure-theoretic
content, not a stub:

- `Trajectory A O := CountableConcrete.CountHist A O` with the top
  `MeasurableSpace` (discrete `σ`-algebra) (L32–52).
- `CountablePrefixMachine.trajectoryLaw π penv T : PMF (Trajectory A O)`
  threads an ENNReal-valued prefix-machine law through `T` steps of
  policy × environment interaction (L66–139).
- `prefixFiltration` and `AdaptedToPrefixFiltration` record the
  canonical filtration (L143–177).
- `HasSupportwiseResidualContractionWitness` (L214–223) states the
  supportwise one-step residual contraction hypothesis along realized
  trajectories.
- `ae_residualObserverFiberRecurrence_of_supportwise` (L293–309) and
  `ae_residualObserverFiberRateBound_of_witness` (L311–341) convert
  the supportwise statement into an almost-sure statement under
  `(U.trajectoryLaw π penv T).toMeasure`, using
  `PMF.toMeasure_apply_eq_zero_iff` and `MeasureTheory.ae_iff`.
- `ae_observerFiberPosteriorShareLowerBound_of_witness` (L387–415)
  converts the residual-odds bound to a lower bound on the realized
  observer-fiber posterior share via `posteriorShareFromResidual r =
  (1 + r)⁻¹`.

On top of this module, `Semantic.lean` now exposes a probabilistic
`thm_separating_support_convergence` (L449–468) on
`CountablePrefixMachine A O`, with companion
`thm_separating_support_rate` (L471–490) and
`cor_separating_support_finite_time` (L493–527). The deterministic
siblings have been renamed with a `_deterministic` suffix and remain
in place.

This closes the C3 gap in the weak sense: there is now a real
measure-theoretic wrapper that produces a.s. statements over the
realized trajectory law. **It does not close C3 in the strong sense**,
because the probabilistic master theorem takes the
`HasSupportwiseResidualContractionWitness` as a hypothesis that is not
derived from the deterministic Section 6 work. See D1.

### C4 (CLOSES WITH B3)

Unchanged. The closing theorems
`semanticAuditClosed_eq = true` and `fullyFirstPrinciples_eq = true`
(Manifest L1538, L1545) remain `native_decide`-over-a-list claims that
are attached to the current `manifestEntries` literal only once
`Manifest.olean` is rebuilt. With the B3 regression, the gap is larger
than on the fourth pass.

---

## Part D — New residuals surfaced by the fifth-pass read

### D1. Hypothesis laundering: `HasSupportwiseResidualContractionWitness` has no constructor

*Status.* New, substantive. The critical finding of this pass.

*Problem.* The new probabilistic `thm_separating_support_convergence`
(`Semantic.lean` L449–468) takes
`U.HasSupportwiseResidualContractionWitness π penv ω pstar δ T` as an
input and converts it to an a.s. one-step contraction statement. The
hypothesis is itself a supportwise per-trajectory one-step contraction:

```
∀ ξ ∈ (U.trajectoryLaw π penv T).support,
  ∀ n < T, ∃ y, y = U.residualObserverFiberProcess … (n+1) ξ ∧
    y ≤ posteriorDecayFactorENNReal δ * U.residualObserverFiberProcess … n ξ
```

A grep for `HasSupportwiseResidualContractionWitness` returns only:

- the definition itself (L214–223 of
  `ConcreteProbabilisticConvergence.lean`);
- a same-view transport theorem
  `hasSupportwiseResidualContractionWitness_of_sameView` (L226–240);
- seventeen further uses, all as hypotheses in downstream theorems.

There is **no constructor theorem** of the form "from the Section 6
deterministic one-step contraction, one obtains
`HasSupportwiseResidualContractionWitness`." The
`softOneStepObserverFiberResidualOdds_le_decayBound_of_zeroOut_supportUnion`
machinery lives on `ConcretePrefixMachine` (Rat-valued,
finite-support), while `HasSupportwiseResidualContractionWitness` is
stated on `CountablePrefixMachine` (ENNReal-valued, countable). The two
substrates are parallel with no bridge.

So the probabilistic master theorem is essentially "if you hand me the
supportwise one-step contraction hypothesis, I will give you its
almost-sure upgrade." That is a transport theorem, not the full
probabilistic support theorem.

*Acceptance criterion for D1.* Either:
1. Add a constructor `hasSupportwiseResidualContractionWitness_of_…`
   that derives the hypothesis from a nontrivial downstream fact
   (e.g. the softened-substrate contraction transported from the
   deterministic track via a substrate-bridge lemma). This requires
   either a new bridge between `ConcretePrefixMachine` and
   `CountablePrefixMachine`, or reconstructing the soft-substrate
   machinery on `CountablePrefixMachine` directly.
2. Document, in a visible docstring on `thm_separating_support_convergence`
   (and in the paper's abstract/conclusion), that this is a
   hypothesis-transport theorem, and that the supportwise-contraction
   hypothesis is not yet derived from first principles in the
   countable-probabilistic track.

Option 2 is a paper-side documentation fix; option 1 is substantial new
Lean content.

### D2. Hypothesis and conclusion are structurally close

*Status.* New, weaker than D1 but worth naming.

*Problem.* The supportwise-contraction hypothesis quantifies over all
`ξ` in the support of the trajectory PMF, and asserts the same one-step
contraction for each. The a.s. conclusion quantifies the same one-step
contraction for `(U.trajectoryLaw π penv T).toMeasure`-almost-every
`ξ`. The proof (see `ae_residualObserverFiberRecurrence_of_supportwise`)
converts the supportwise statement to the a.s. statement via the
standard identity `PMF.toMeasure_apply_eq_zero_iff` (a set is null iff
it is disjoint from the support). This is correct and checkable, but
the Lean theorem is doing a narrow logical transport rather than
deriving the almost-sure statement from a simpler hypothesis.

The deterministic track has a genuine rate derivation (the soft
substrate's per-step inequality is computed from the softening scale
`ε = posteriorDecayFactor δ · mass o / 2`). The probabilistic track
currently does not.

*Acceptance criterion for D2.* No fresh criterion; resolves with D1.

### D3. Substrate mismatch between deterministic and probabilistic tracks

*Status.* New, substantive.

*Problem.* The deterministic machinery lives on
`ConcretePrefixMachine A O` with `[DecidableEq A] [DecidableEq O]` and
Rat-valued finite-support laws. The probabilistic machinery lives on
`CountablePrefixMachine A O` with `[Encodable A] [Encodable O]` and
ENNReal-valued countable laws. There is no declared relation between
the two. An author intending "the Lean formalization derives the
probabilistic master theorem from first principles" must either:

1. Build a bridge functor / type-class pair that produces a
   `CountablePrefixMachine` from a `ConcretePrefixMachine` and
   transports the deterministic contraction along it, or
2. Rebuild the soft-substrate positive-support machinery directly on
   `CountablePrefixMachine` (soften-for-ENNReal with a countable
   reference measure, softened residual odds, softened one-step
   bound, etc.).

Either path is genuine new formalization work.

*Acceptance criterion for D3.* Resolves with D1.

### D4. Harness olean regression — AxiomAudit is now 32 min stale

*Status.* New, mechanical, and worse than on the fourth pass.

*Problem.* See B3 above. AxiomAudit staleness went from 2 min to 32 min
between fourth and fifth passes. `AxiomAudit.lean` L77 references
`SemanticConvergence.thm_separating_support_convergence`, a symbol
whose declaration shape changed during this pass (deterministic ➜
probabilistic). The checked-in `AxiomAudit.olean` therefore encodes
axiom lists for the old declaration, which is misleading to any
downstream consumer who reads `lean_axiom_audit.md`.

*Acceptance criterion for D4.* Resolves with B3: re-run
`lake env lean SemanticConvergence/AxiomAudit.lean`, regenerate
`lean_axiom_audit.md`, diff against the checked-in version.

### D5. Manifest substrate ambiguity

*Status.* New, cosmetic.

*Problem.* The manifest entry for `thm:separating-support-convergence`
(`Manifest.lean` L834–845) points at the unqualified
`SemanticConvergence.thm_separating_support_convergence`, which in the
current source tree is the probabilistic (countable) version on
`CountablePrefixMachine`. A reader who follows the manifest pointer
may expect the deterministic (finite-support) version used by the
paper's constructive sufficiency theorems
(`thm_semantic_convergence`, `thm_kernel_semantic_convergence`, etc.),
which are still on `ConcretePrefixMachine`. No cross-reference flags
the substrate change.

*Acceptance criterion for D5.* Add a comment block at the top of the
manifest entry noting the two-substrate layout and that the
constructive sufficiency theorems use the deterministic substrate, or
add a sibling manifest entry pointing at
`thm_separating_support_convergence_deterministic`.

### D6. Abstract and conclusion wording is not fully precise about the hypothesis shape

*Status.* New, paper-side.

*Problem.* Abstract (L54) and conclusion (L3939) both say the new Lean
declaration "proves an almost-sure one-step residual-odds contraction
on the realized trajectory law." Read strictly, this is accurate —
applied to its hypothesis, the declaration proves that conclusion.
But the wording does not tell the reader that the declaration takes a
supportwise-contraction witness as input, and that the witness is not
derived from the deterministic track. A careful reader will recognize
the statement as a transport theorem; a casual reader will not.

*Acceptance criterion for D6.* Add a parenthetical to the abstract and
conclusion of the form "(assuming a supportwise one-step residual
contraction along realized trajectories, supplied as a hypothesis to
the Lean declaration)" or equivalent, so the status of the hypothesis
is visible in prose.

---

## Part E — What the manuscript can now claim truthfully

Given the current state of the tree — B4 closed, B5 substantially
closed, C1 closed on fifth pass, C3 partially addressed on fifth pass
but replaced by D1, B3 regressed, D1–D6 as above — the defensible
claim is:

> A public Lean 4 repository contains Lean counterparts for every
> manifest-tracked item in the paper. The Section~\ref{sec:main}
> support/rate stack has two parallel tracks: a deterministic
> `ConcretePrefixMachine` (finite-support Rat) track in which the
> soft-substrate one-step residual-odds contraction is derived from
> first principles and composed into an $N$-step recurrence, and a
> probabilistic `CountablePrefixMachine` (countable ENNReal) track in
> which a supportwise one-step residual-odds contraction, supplied as
> a hypothesis, is transported to an almost-sure one-step contraction,
> an $N$-step rate bound, and a realized observer-fiber posterior
> share lower bound along the trajectory PMF. The two tracks are not
> yet bridged: no theorem derives the probabilistic track's
> supportwise-contraction hypothesis from the deterministic track's
> soft-substrate machinery. The manifest and audit report
> `suspiciousManifestEntryCount = 0`, `semanticAuditClosed = true`,
> and `fullyFirstPrinciples = true` once the harness modules
> `Manifest.lean` and `AxiomAudit.lean` are rebuilt against their
> current sources.

The following claims remain **not** defensible at this state:

> 1. "The Lean formalization derives the paper's probabilistic
>    master support theorem from first principles."
>    *Blocked by D1 — the probabilistic theorem takes a supportwise
>    contraction as a hypothesis that is not derived from the
>    deterministic track or from elsewhere in the tree.*
> 2. "The probabilistic and deterministic tracks are connected by a
>    bridge or substrate-functor."
>    *Blocked by D3 — no such bridge exists.*
> 3. "The manifest's own closure theorems (`semanticAuditClosed`,
>    `fullyFirstPrinciples`) are attached to the current source."
>    *Blocked by C4/B3 — Manifest.olean 6 min stale, AxiomAudit.olean
>    32 min stale.*
> 4. "The paper's abstract and conclusion are fully precise about the
>    shape of the new Lean probabilistic theorem."
>    *Blocked by D6 — the supportwise-witness hypothesis is not
>    mentioned in prose.*

---

## Part F — Recommended work order

After the fifth pass, eight items remain, ordered by scope:

1. **B3 / D4** — mechanical rebuild. One `lake build` pass brings
   `Manifest.olean` and `AxiomAudit.olean` current. Regenerate
   `lean_axiom_audit.md`. Closes C4 and D4 automatically. Expect no
   content change.
2. **C2** — add a one-line legacy note on
   `oneStepPosteriorConcentrates` explaining why it is retained.
   Trivial.
3. **D5** — clarify substrate in the manifest entry for
   `thm:separating-support-convergence` (one-line comment or sibling
   deterministic entry).
4. **D6** — adjust abstract and conclusion wording to name the
   supportwise-witness hypothesis. Paper-side, small.
5. **D1 (option 2)** — add a visible docstring on
   `thm_separating_support_convergence` stating that the declaration
   is a hypothesis-transport theorem. Lean-side, small.
6. **D1 (option 1) / D2 / D3** — substantial new Lean content:
   either build a bridge between `ConcretePrefixMachine` and
   `CountablePrefixMachine` that transports the deterministic
   contraction along the substrate change, or rebuild the
   soft-substrate positive-support machinery directly on
   `CountablePrefixMachine`. This is the remaining work for a strong
   reading of "the Lean formalization derives the probabilistic
   master theorem from first principles."

If the goal is "fully considered verified" in the weak reading —
every theorem has a Lean counterpart of some shape, scope limitations
documented — closing B3/D4, C2, D5, D6, and D1-option-2 finishes it.

If the goal is "fully considered verified" in the strong reading —
the Lean independently derives the paper's probabilistic master
support theorem from first principles on a single substrate — D1
option 1 (or an equivalent substrate rebuild) is the remaining work,
and it is strictly outside any closeout pass.
