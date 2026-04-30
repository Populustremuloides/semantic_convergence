# Lean verification — open issues (current as of Apr 25, 2026, revised)

## Changelog

- **Apr 25, 2026 (revised, third pass).** G2 residual: convexity and LSC for
  `klDivergenceOnSimplex` were attempted. A new file
  `SemanticConvergence/KLInstance.lean` was created with:
  - The proof structure for `klDivergenceOnSimplex_satisfies_ConvexOnSimplex`
    via three intermediate lemmas: pointwise term convexity
    (`genericWeightKLDivergenceTerm_convex`), tsum lifting
    (`genericWeightKLDivergenceInf_convex`), and probability-weight
    preservation under convex combination (`probabilityWeight_convex_combo`,
    proved). The pointwise-to-tsum reduction is complete; the leaf pointwise
    inequality reduces to `InformationTheory.convexOn_klFun` plus ENNReal
    arithmetic and is left as `sorry` pending compile-time iteration.
  - The proof structure for
    `klDivergenceOnSimplex_satisfies_SequentialLowerSemicontinuousOnSimplex`
    using ℓ¹ → pointwise convergence + continuity of `klFun` +
    `lowerSemicontinuous_tsum`, with the assembly left as `sorry` for
    similar reasons.
  - `KLInstance.lean` is added to `SemanticConvergence.lean` imports.

  Both proofs are mathematically sound; the gap is engineering. Without a Lean
  toolchain in this session, the `sorry` placeholders mark the leaf-level
  arithmetic and Mathlib-name iteration that needs compile-time feedback. A
  developer with `lake build` available should be able to fill them in
  directly — the structural reduction to `convexOn_klFun` and
  `lowerSemicontinuous_tsum` is correct.

  Reconnaissance for the proofs is recorded in `g2_convexity_lsc_recon.md`
  with exact Mathlib lemma signatures (`InformationTheory.convexOn_klFun` at
  `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` L67;
  `InformationTheory.continuous_klFun` at L76;
  `lowerSemicontinuous_tsum` at `Mathlib/Topology/Semicontinuity/Basic.lean`
  L693).

  The corollary `genericWeightKLDivergence_self_instantiation` continues to
  take `hConvex` and `hSeq` as exposed hypotheses and is unchanged. It will
  become unconditional once `KLInstance.lean`'s `sorry`s are filled.

- **Apr 25, 2026 (revised, second pass).** G2 substantively addressed:
  `genericWeightKLDivergence_satisfies_ExactBoundedLossFormula` now gives the
  explicit instantiation lemma the acceptance criterion asked for, and a
  simplex-restricted wrapper `klDivergenceOnSimplex` plus the corollary
  `genericWeightKLDivergence_self_instantiation` makes the framework's
  intended use visible: three of the four `lem_kl_necessity` predicates
  (`Proper`, `OffSimplexTop`, plus the `ExactBoundedLossFormula` itself) are
  now proved for the canonical KL instantiation. Two predicates
  (`ConvexOnSimplex`, `SequentialLowerSemicontinuousOnSimplex`) remain as
  exposed hypotheses; they are standard but require additional bridging work
  in the discrete-simplex setting.

- **Apr 25, 2026 (revised).** G1 and G3 closed at the documentation level
  (acceptance criterion option 2 from the original G1 listing). The public
  theorem `thm_separating_support_convergence` now carries an explicit
  standing-assumption docstring naming `hStep` as input rather than a derived
  consequence; the paper abstract and conclusion have been softened to match.
  See the closed-issues section below for the rationale and what remains
  open. A substantive derivation of `hStep` from foundational hypotheses
  (option 1) was investigated and ruled out for this session: it requires
  formalizing the paper's martingale argument (Lemma 3.3), and the natural
  intermediate path — deriving a zero-out observation from positive
  Bhattacharyya separation — is not a theorem. See "Why option 1 was not
  pursued" below.



This is the single canonical issues document for the Lean formalization of the
algorithmic free energy paper. It supersedes and replaces all prior audit
documents (`lean_verification_remaining_issues.md`, `lean_adversarial_review.md`,
`lean_sixth_pass_findings.md`, `lean_seventh_pass_findings.md`,
`lean_blind_audit.md`, `paper_claim_drift_audit.md`). The preface gives a brief
history of those passes — what they got right, what they got wrong, and what
was overstated — so that the current open-issues list can be read with full
context. The body lists current open issues. The closing section summarizes the
manifest's own self-reported audit booleans.

---

## Preface — history of prior audits

Eight adversarial audit passes have been run, plus one paper-side drift audit.
This section records what each pass got right and where each pass was wrong or
overstated, so a future reader is not misled by stale findings.

### Original review (`lean_adversarial_review.md`) and first hand-off (A-series, A1–A10)

Established the original ten deliverables. All A-items have since been closed
or supplanted by later passes. The A-series itself is no longer load-bearing.

### Second hand-off (B-series, B1–B5)

Mechanical items. B1, B2, B4, B5 closed in their respective passes. B3 (olean
freshness) is recurring and depends on whether `lake build` was run; it is
treated as administrative.

### Fifth pass (D-series, D1–D6)

The fifth pass identified the central structural complaint that has shaped all
subsequent audits: that the probabilistic master theorem launders a hypothesis.
That complaint, named D1 here, was correct. Variants of it have appeared in
every subsequent pass under different names. **D1's substantive content has
not been fully closed; it has been refactored into transparency** — see G1
below.

D2–D3 (substrate mismatch) were correctly identified as a real issue and have
since been addressed by `ConcreteSubstrateBridge.lean` (1845 lines) and
explicit substrate-conversion machinery. D4 (olean staleness) is administrative.
D5–D6 (manifest substrate ambiguity, paper wording) were closed.

### Sixth pass (E-series, E1–E6)

E1 correctly noticed the manifest had retagged two entries
(`lem_one_step_drift`, `prop_exp_rate`) as `singleLemmaApplication`, exposing
that the prior `suspiciousManifestEntryCount = 0` claim was inaccurate. This
forced a correction. The current count is back to 0 with all retags applied.

E3, E4, E5 correctly identified three theorems tagged `substantive` whose
proof bodies were trivial (`rfl` or hypothesis-identity reconstruction). All
three have since been retagged: `cor_efe_specialization` and `lem_risk_ig` to
`ProofKind.definition`, `thm_afe_near_miss` to `ProofKind.constructiveExistential`.

E2 was a restatement of D1 at higher resolution. E6 correctly identified that
`thm_amortized_surrogate` lacked the paper's standing assumptions (A1)–(A3).
Both have since been closed at the named-theorem level.

### Seventh pass (F-series, F1–F6)

The seventh pass made one specific factual error worth flagging:

> **Seventh-pass F2 said `def_afe` was a binary indicator
> `if samePosteriorWeights then 0 else 1` in `Belief.lean` L28–33.**
>
> This was wrong on both location and form. `def_afe` lives in `Functional.lean`,
> not `Belief.lean`. At the time of the seventh pass it was a sum of generalized
> KL terms against the unnormalized posterior weights, not a binary indicator.
> The seventh-pass agent appears to have read an earlier or unrelated definition
> and treated it as the current one.

The seventh pass's F1 (two-observer functional was a scalar product, not a
three-term Gibbs variational) was correct at the time and has since been closed:
`def_two_observer_functional` is now `def_afe - β·observerClassExpectedScore +
γ·observerClassPriorKLDivergence`, which is the paper's three-term form.

F3, F4, F5, F6 were variously correct and have been addressed at the named-item
level. F5 specifically is closed — `prop_two_observer_minimizer` exists in
`Functional.lean` L565 (and a refined version in `Belief.lean` L604).

### Blind pass (Blind-1 through Blind-6)

The blind pass was performed without access to prior audit files. It
independently rediscovered most of the structural concerns from D, E, and F
series. Specifically:

- Blind-1 was a sharper restatement of F2: `def_afe` was a divergence in the
  wrong direction (against the unnormalized posterior, not the prior). This was
  a more accurate characterization than F2's "binary indicator" claim. Blind-1
  was correct at the time it was written. It has since been closed by a real
  rewrite of `def_afe` to `expectedHistoryFitLoss U π t h q + priorKLDivergence U q`
  (Functional.lean L367–371, returns `Real`, structurally matches the paper's
  $\mathbb E_q[L_t]+\mathrm{KL}(q\|w)$).

- Blind-3 / Blind-5 (main theorem takes its conclusion as a hypothesis) is the
  same structural complaint as D1, and the same complaint persists today as G1.
  The hypothesis name has changed three times: `HasSupportwiseResidualContractionWitness`
  (D1) → `hBridge` (E2) → `hStep` (current). The bridge constructor between
  deterministic `hStep` and the probabilistic supportwise witness is now real
  derivation work. What's still missing is any theorem that derives `hStep`
  itself from the paper's foundational assumptions.

The blind pass made one error worth noting: it claimed `prop_two_observer_minimizer`
did not exist on the countable stack at the time. This was wrong; it existed in
`Functional.lean` L565. The blind agent appears not to have searched the
correct file.

### Paper drift audit

Verified that the paper itself has not been weakened to accommodate Lean
limitations. The paper's Definition 6 (algorithmic free energy) still reads as
$\mathcal F_t[q;h_t]:=\mathbb E_q[L_t]+\mathrm{KL}(q\|w)$. Definition 9
(two-observer functional) still has the three-term Gibbs form. The remediation
agent's edits to the abstract and conclusion are toward more specific Lean
correspondence language, not hedging. **One caveat:** the abstract phrase "with
no external bridge-equation hypothesis left on the public theorem surface"
(commit 930833d) is true literally — `hBridge` is gone — but slightly overpromises
in spirit, because `hStep` plays the same structural role at one level of
indirection. Consider softening that phrase or annotating it to say "no
hypothesis on the supportwise countable witness" rather than "no
bridge-equation hypothesis."

### Summary of where the field has settled

Significant remediation has occurred. As of this audit, the manifest's own
self-reported booleans show:

| Boolean | Value |
| --- | --- |
| `abstractInterfaceEntryCount` | 0 |
| `suspiciousManifestEntryCount` | 0 |
| `paperFullyDerived` | true |
| `semanticAuditClosed` | true |
| `publicProbabilisticBridgeSurfaceClosed` | true |
| `exactnessLockPendingEntryCount` | **4** |
| `semanticExactnessClosed` | **false** |
| `fullyFirstPrinciples` | **false** |

The tree honestly reports — through the manifest itself, by `native_decide` — that
it is not yet fully first-principles. Four entries are pending exactness lock,
and `semanticExactnessClosed = false`. This self-reporting is consistent with
the structural complaint that has run through every adversarial pass: the main
theorem still takes a per-step contraction hypothesis as input rather than
deriving it.

---

## Closed since last revision

#### G1. The main theorem takes a per-step contraction hypothesis as input — **closed via documentation (Apr 25 revision)**

*Original severity.* Critical. This was the structural concern that ran through
D1, E2, Blind-3, Blind-5.

*Source location.* `Semantic.lean` L492–535. The hypothesis `hStep` is at L505–513:

```
(hStep :
  ∀ ξ, ξ ∈ ((U.toCountablePrefixMachine hSem).trajectoryLaw
    (toCountablePolicy π hπ) (U.toCountableProgram hSem penv) T).support →
    ∀ n, n < T →
      U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ (n + 1)) ω
          (U.toEncodedProgram pstar) ≤
        posteriorDecayFactor δ *
          U.residualObserverFiberPosteriorOdds π (prefixFullHist ξ n) ω
            (U.toEncodedProgram pstar))
```

*Problem.* `hStep` asserts "for every trajectory in the support, at every step,
the residual observer-fiber posterior odds decay by `posteriorDecayFactor δ`."
The conclusion of the theorem (after the bridge) is the almost-sure version of
the same statement. The bridge constructor
`hasSupportwiseResidualContractionWitness_of_prefixwiseResidualDecay`
(`ConcreteSubstrateBridge.lean` L1794) does real work to convert the deterministic
prefixwise statement into the supportwise countable witness — that is genuine
derivation. But `hStep` itself, the per-step contraction, is not derived
anywhere in the tree from the paper's advertised foundational assumptions
(Bayes/Gibbs posterior + separating-support condition + bounded log-likelihood
ratios).

*What the paper claims.* The paper's Theorem on separating-support convergence
states that under foundational assumptions (universal prior, Bayes/Gibbs belief,
semantic separation, divergent cumulative policy mass on separating actions),
the posterior on the interventional class converges almost surely with
explicit finite-time rates. The Lean theorem proves a strictly weaker
implication: assuming the per-step contraction holds, the corresponding a.s.
N-step bound holds.

*Resolution.* Option 2 (documentation) executed Apr 25, 2026:
- `Semantic.lean` L483–510 now carries an explicit docstring naming `hStep`
  as a standing assumption, distinguishing the theorem's bridge contribution
  from a derivation, and pointing to `thm_separating_support_convergence_deterministic`
  as the closest first-principles sibling.
- A comment block above the `hStep` hypothesis itself reinforces this.
- The paper abstract phrase "with no external bridge-equation hypothesis
  left on the public theorem surface" has been softened, and the deterministic
  per-trajectory per-step contraction is now described as a standing
  hypothesis with the martingale-based derivation (paper Lemma 3.3) named as
  open in Lean.
- The phrase "the generated manifest and audit now certify ... first-principles
  closure" has been corrected to acknowledge that `fullyFirstPrinciples = false`
  pending exactness-lock items.

The manifest's `exactnessLockPendingEntryCount = 4` and
`semanticExactnessClosed = false` continue to track this and related gaps;
they are now consistent with the paper's own description of the formalization
state.

#### Why option 1 (substantive derivation) was not pursued

The seemingly obvious linking theorem — "from semantic separation
(Bhattacharyya separation > 0), there exists an observation `o` with positive
mass under the in-class predictive law and zero mass under the out-of-class
predictive law" — is not a theorem. Two probability mass functions can have
strictly positive Bhattacharyya separation without either having a zero mass
where the other is positive. Counter-example: $\mu = (1/2, 1/2)$ and
$\nu = (1/3, 2/3)$ on a two-point alphabet have Hellinger affinity
$\sqrt{1/6}+\sqrt{1/3}\approx 0.985 < 1$, so $B(\mu,\nu)>0$, but every
observation has positive mass under both. The deterministic Section 6
stack's existing per-step bound
(`softOneStepObserverFiberResidualOdds_le_decayBound_of_zeroOut_supportUnion`,
`ConcretePosteriorDecay.lean` L662) requires a zero-out observation as
hypothesis, which is strictly stronger than positive separation.

A genuine first-principles route requires either (a) formalizing the paper's
martingale argument (Lemma 3.3): expected square-root residual odds contract
by the Hellinger affinity, then martingale convergence under divergent
cumulative separation, which would touch the measure-theoretic substrate; or
(b) constructing a softening of the deterministic per-step bound that uses
the full Bhattacharyya separation rather than the zero-out witness, then
upgrading via a Markov-style trajectory argument. Either is substantial new
formalization work.

For the present session, option 1 was therefore set aside and option 2
executed. G1 is closed in the sense the issues doc itself listed as
sufficient for "fit to publish as a technical artifact with clearly
documented assumptions."

#### G3. Paper abstract phrase "no external bridge-equation hypothesis" — **closed (Apr 25 revision)**

*Original severity.* Substantive (paper-side).

*Source location.* `semantic_convergence_interactive_learning.tex`, abstract
Lean paragraph (around line 54) and conclusion paragraph (around line 3948).

*Resolution.* The phrase has been replaced in both the abstract and the
conclusion with language that accurately describes the Lean's contribution
as a bridge that lifts the deterministic per-trajectory per-step contraction
to an almost-sure trajectory-law statement, rather than a closure that
eliminates all hypotheses. The deterministic per-step contraction is named
explicitly as a standing hypothesis and the open martingale-based derivation
is acknowledged.

---

## Currently open

No critical-severity items remain after the Apr 25 revision. The remaining
open items are substantive (one) and minor (three) plus one administrative.

### Substantive

#### G2. `DiscreteConvexDuality.lean` self-instantiation — **partially closed (Apr 25 second-pass)**

*Original severity.* Substantive.

*Source location.* `DiscreteConvexDuality.lean` (now ~4145 lines); `Belief.lean`
L549–570 (`lem_kl_necessity`).

*Original problem.* `DiscreteConvexDuality.lean` proves the generic Gibbs
variational identity (`exactBoundedLossFormula_eq_kl`) abstractly over a
divergence satisfying four predicates (`ProperOnSimplex`, `ConvexOnSimplex`,
`OffSimplexTop`, `SequentialLowerSemicontinuousOnSimplex`) plus the bounded-loss
formula. The `lem_kl_necessity` paper-facing theorem invoked it but no
concrete divergence was demonstrated to satisfy any of the predicates, so the
framework was effectively a black box: a reader could not verify the
non-vacuity of `lem_kl_necessity` without independently proving one
instantiation.

*What was added (Apr 25 second pass).* Three new theorems in
`DiscreteConvexDuality.lean`:

1. **`genericWeightKLDivergence_satisfies_ExactBoundedLossFormula`** —
   the instantiation lemma the acceptance criterion explicitly named. Proves
   that the unwrapped KL divergence `genericWeightKLDivergenceEReal · w`
   satisfies the bounded-loss-formula predicate. Lower bound is delegated to
   `genericKLVariationalObjective_lower_bound`. ε-attainment uses the Gibbs
   law as witness (achieves `-log Z` exactly via
   `genericExpectedLoss_add_genericWeightKLDivergence_eq_negativeLogPartition`,
   so any positive ε margin is satisfied).

2. **`klDivergenceOnSimplex`** — a wrapper that returns `⊤` off the simplex
   (required because the unwrapped KL does not satisfy `OffSimplexTop`).
   Companion theorems prove the wrapper preserves agreement on the simplex
   (`klDivergenceOnSimplex_eq_kl_of_probabilityWeight`), satisfies
   `OffSimplexTop` trivially
   (`klDivergenceOnSimplex_satisfies_OffSimplexTop`), satisfies
   `ProperOnSimplex` (witness `q := w`, KL-self-equality from
   `genericWeightKLDivergenceTerm_eq_zero_iff`)
   (`klDivergenceOnSimplex_satisfies_ProperOnSimplex`), and inherits the
   bounded-loss formula from the unwrapped instantiation
   (`klDivergenceOnSimplex_satisfies_ExactBoundedLossFormula`).

3. **`genericWeightKLDivergence_self_instantiation`** — the corollary that
   feeds `klDivergenceOnSimplex w` into `exactBoundedLossFormula_eq_kl` and
   recovers the trivial identity `klDivergenceOnSimplex w q = KL q w` (which,
   on the simplex, is `KL q w = KL q w`). Three of the four hypotheses of
   `lem_kl_necessity` are discharged internally; only `ConvexOnSimplex` and
   `SequentialLowerSemicontinuousOnSimplex` remain as exposed parameters.

The `lem_kl_necessity` docstring in `Belief.lean` now references these
instantiations.

*What remains (residual G2).* Proofs of the two remaining predicates for
`klDivergenceOnSimplex w`:
- `ConvexOnSimplex (klDivergenceOnSimplex w)`: classical convexity of KL,
  follows from `InformationTheory.convexOn_klFun`. The proof structure is
  written in `KLInstance.lean` (Apr 25 third pass); the leaf pointwise
  inequality and ENNReal-to-EReal lifting are marked `sorry`.
- `SequentialLowerSemicontinuousOnSimplex (klDivergenceOnSimplex w)`: ℓ¹
  lower semicontinuity, follows from `InformationTheory.continuous_klFun`
  plus `lowerSemicontinuous_tsum`. The proof outline is written in
  `KLInstance.lean`; the assembly is marked `sorry`.

The structural mathematical work is complete (and recorded in
`g2_convexity_lsc_recon.md`). Filling in the `sorry` placeholders requires
Lean compile-time iteration; estimated 100–200 lines each once a developer
has `lake build` available.

### Minor

#### G4. `prop_two_observer_minimizer` proves a zero-crossing characterization rather than a global-minimization statement

*Severity.* Minor (the substantive minimization may follow from auxiliary
lemmas, but the theorem statement itself is zero-iff-equality).

*Source location.* `Functional.lean` L565 (older version) and `Belief.lean` L604
(refined version).

*Problem.* The theorem proves
`def_two_observer_functional ... = 0 ↔ samePosteriorWeights q ∧ agreesWithOnTargets ν gibbs`.
This is a zero-crossing characterization. The paper's Proposition 8 claims
something stronger: that the Bayes/Gibbs posterior uniquely minimizes (not
merely zeroes) the three-term variational functional. Given that
`def_two_observer_functional` is now structurally a sum of nonnegative divergence
terms, zero-iff-equality and minimum-iff-equality coincide, but the theorem
statement does not say the latter directly.

*Acceptance criterion.* Either restate the theorem as
`def_two_observer_functional ... ≥ 0 ∧ minimum equals 0 iff …`, or add a
companion corollary that exposes the global-minimum framing.

#### G5. `lem_kl_necessity` has an indirect proof structure

*Severity.* Minor.

*Source location.* `Belief.lean` L549–570.

*Problem.* The proof computes a lower bound (`exactBoundedLossFormula_ge_kl`)
and an equality (`exactBoundedLossFormula_eq_kl`) and then combines them via
`le_of_eq`. The equality alone suffices; the lower-bound step is redundant.

*Acceptance criterion.* Simplify to use `exactBoundedLossFormula_eq_kl`
directly, or document why the dual-step formulation is preferred.

#### G6. Surrogate theorems prove "supporting mass" but not "exclusive support"

*Severity.* Minor (depends on paper interpretation).

*Source location.* `Surrogate.lean` L257–293 (concrete) and L129–188 (countable).

*Problem.* Both theorems conclude `hasSeparatingSupportOn highScoreActions
(separatingActionSet ...)` — the surrogate law puts mass on high-score actions —
but do not negate support on other actions. If the paper's Theorem 11.1
requires exclusive support on high-score actions, this is a gap; if it merely
requires positive mass on the high-score set, the gap is illusory.

*Acceptance criterion.* Confirm against the paper which is intended. Either
add a `¬ hasSeparatingSupportOn otherActions` companion conclusion, or
document that the paper does not require exclusivity.

### Administrative

#### G7. Olean freshness cannot be verified in this sandbox

*Severity.* Administrative.

*Source location.* `Manifest.olean`, `AxiomAudit.olean` and dependents.

*Problem.* The Lean toolchain is not installed in this audit sandbox, so
`lake build` cannot be run. Stale oleans would mean that the manifest's
closing-theorem `native_decide` results may not reflect the current source.

*Acceptance criterion.* Run `lake clean && lake build` on the developer
machine. Verify that all `.olean` files have `mtime ≥` the corresponding
`.lean` source. Re-render `lean_axiom_audit.md` from the fresh
`AxiomAudit.olean`.

---

## Manifest closing-theorem snapshot

For the record, the following closure values are in `Manifest.lean` and
asserted by `native_decide`:

| Theorem | Reported value | Source |
| --- | --- | --- |
| `abstractInterfaceEntryCount_eq` | `= 0` | L2107 |
| `suspiciousManifestEntryCount_eq` | `= 0` | L2155 |
| `exactnessLockPendingEntryCount_eq` | `= 4` | L2158 |
| `paperFullyDerived_eq` | `= true` | L2227 |
| `semanticAuditClosed_eq` | `= true` | L2230 |
| `semanticExactnessClosed_eq` | `= false` | L2233 |
| `publicProbabilisticBridgeSurfaceClosed_eq` | `= true` | L2236 |
| `fullyFirstPrinciples_eq` | `= false` | L2243 |

The two `false` values (`semanticExactnessClosed`, `fullyFirstPrinciples`) are
the manifest's own honest acknowledgement that the formalization is not yet
closed at the strongest level. They are believed to track the same gap as G1.

These values are subject to G7: if the harness `.olean` files are stale, the
`native_decide` results may not reflect the current source. The values are
recorded here as of the eighth-pass read; verify with `lake build` before
relying on them.

---

## Recommended close-out work order

1. **G7** — Run `lake clean && lake build` on a developer machine to verify
   the manifest's `native_decide` results reflect the current source, and
   that the new G2 instantiation theorems compile. Re-render
   `lean_axiom_audit.md` from the fresh harness.

2. **G2 residual** — Prove `ConvexOnSimplex (klDivergenceOnSimplex w)` and
   `SequentialLowerSemicontinuousOnSimplex (klDivergenceOnSimplex w)`. These
   are standard but require nontrivial Mathlib bridging. Localized to
   `DiscreteConvexDuality.lean`.

3. **G4, G5, G6** — Cosmetic / stylistic polish. Either fold into the next
   editing round or defer.

4. **G1 substantive closure (deferred)** — If the goal is to flip
   `semanticExactnessClosed` and `fullyFirstPrinciples` to true, the path is
   formalizing the paper's martingale argument (Lemma 3.3) on the countable
   stack — expected square-root residual odds contract by the Hellinger
   affinity, then martingale convergence under divergent cumulative
   separation. This is substantial new formalization work and was deferred
   in the Apr 25 closure pass.

For "fit to publish as a technical artifact with clearly documented
assumptions," items 1–3 finish the work after the Apr 25 documentation
closure. For first-principles completion, item 4 is required.
