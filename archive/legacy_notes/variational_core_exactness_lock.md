# Variational Core Exactness Lock

Frozen on 2026-04-23.

This document locks the exact mathematical targets for the belief / variational overhaul before
any further Section 6 contraction work. Its purpose is to prevent another round of "shape-correct"
or "morally equivalent" repairs. From this point onward, the canonical variational declarations are
reserved for exact paper-level objects only.

## Scope

This lock governs the following paper-facing declarations:

- `SemanticConvergence.def_afe`
- `SemanticConvergence.lem_variational`
- `SemanticConvergence.lem_kl_necessity`
- `SemanticConvergence.def_raw_two_observer_functional`
- `SemanticConvergence.def_two_observer_functional`
- `SemanticConvergence.prop_two_observer_minimizer`
- `SemanticConvergence.def_raw_kernel_functional`
- `SemanticConvergence.def_kernel_functional`
- `SemanticConvergence.prop_kernel_functional_minimizer`
- `SemanticConvergence.prop_kernel_functional_minimizer_compact`

It also governs any concrete finite-support realizations used to justify those declarations.

## Authoritative paper targets

The authoritative formulas are the manuscript definitions and propositions in
`semantic_convergence_interactive_learning.tex`:

- Definition `def:afe`
- Lemma `lem:variational`
- Lemma `lem:kl-necessity`
- Definition `def:raw-two-observer-functional`
- Definition `def:two-observer-functional`
- Proposition `prop:two-observer-minimizer`
- Definition `def:kernel-functional`
- Proposition `prop:kernel-functional-minimizer`
- Proposition `prop:kernel-functional-minimizer-compact`

These formulas are not to be weakened to match existing Lean scaffolds. The Lean must move to the
paper, not the reverse.

## Current mismatches to eliminate

The current tree still has three structural mismatches:

1. `def_afe` is centered on a generalized divergence against `posteriorWeight`, not the paper's
   `E_q[L_t] + KL(q || w)`.
2. `prop_two_observer_minimizer` is currently a zero-crossing characterization of the implemented
   divergence scaffold, not the paper's exact Gibbs minimizer theorem for the two-observer
   functional.
3. `prop_kernel_functional_minimizer` is currently a zero-crossing characterization on a finite
   target-action chart, not the paper's exact Gibbs minimizer theorem for the kernel lift.

Closing this overhaul means eliminating those mismatches at the definition level.

## Locked target map

### 1. Algorithmic free energy

Canonical declaration:

- `SemanticConvergence.def_afe`

Required mathematical content:

- Domain: an admissible posterior `q` on `P`.
- Formula:
  `F_t[q; h_t] = E_q[L_t(p; h_t)] + KL(q || w)`.
- Here `L_t(p; h_t) = -log μ_p(o_{1:t} | a_{1:t})`, with the paper's infinite-loss convention when
  the likelihood vanishes.

Lean-side consequence:

- `def_afe` may not be defined as a divergence against `posteriorWeight`.
- The paper-facing variational identity must be proved from the exact Definition 6 formula.

### 2. Variational identity

Canonical declaration:

- `SemanticConvergence.lem_variational`

Required mathematical content:

- Assumption: evidence `ξ̄(o_{1:t} | a_{1:t}) > 0`.
- Posterior:
  `q_t*(p | h_t) = w(p) μ_p(o_{1:t} | a_{1:t}) / ξ̄(o_{1:t} | a_{1:t})`.
- Identity:
  `F_t[q; h_t] = KL(q || q_t*) - log ξ̄(o_{1:t} | a_{1:t})`.
- Conclusion: `q_t*` uniquely minimizes `F_t`.

Lean-side consequence:

- A theorem of the form "AFE is zero iff `q` equals posterior weights" is only an auxiliary fact,
  not the canonical statement.

### 3. KL necessity

Canonical declaration:

- `SemanticConvergence.lem_kl_necessity`

Required mathematical content:

- A convex-duality / Fenchel-Moreau style uniqueness theorem matching the manuscript statement.
- The theorem is not a zero-crossing corollary of the implemented `def_afe`.

### 3A. Exact theorem shape for `lem_kl_necessity`

This theorem is now locked to the manuscript statement at
`semantic_convergence_interactive_learning.tex:874-889`.

Authoritative mathematical target:

- Prior data: a countable program space `P` equipped with a normalized prior `w`.
- Candidate divergence: a functional `D(· || w)` that is
  - proper,
  - convex,
  - lower-semicontinuous,
  - and extended by `+∞` off the simplex.
- Loss family: every bounded profile `L ∈ ℓ^∞(P)`.
- Variational hypothesis:
  `inf_{q ∈ Δ(P)} { E_q[L] + D(q || w) } = -log ∑_p w(p) e^{-L(p)}` for every bounded `L`.
- Conclusion:
  `D(q || w) = KL(q || w)` for every `q ∈ Δ(P)`.

The Lean theorem is not allowed to weaken any of the following:

1. quantification over every bounded loss profile,
2. the exact Gibbs partition value on the right-hand side,
3. the conclusion for every normalized posterior `q`,
4. the off-simplex `+∞` extension semantics,
5. the convex-duality route of proof.

Allowed specialization:

- The Lean proof may specialize from the full manuscript presentation on `(ℓ^1(P), ℓ^∞(P))`
  to a countable-simplex theorem over discrete weight functions on a countable type `P`,
  but only if the resulting statement still carries the exact mathematical content above.
- In particular, the specialization may not replace the theorem by an
  "exact Gibbs attainment implies KL" lemma. That theorem is only a helper.

### 3B. Representation decision for `lem_kl_necessity`

The canonical paper-facing AFE / two-observer / kernel objects remain `Real`-valued on explicit
admissible domains as locked below. However, `lem_kl_necessity` is different: it is a theorem about
arbitrary candidate divergence functionals, including `+∞` values off the simplex.

For this theorem only, the representation choice is now fixed as follows:

- The ambient belief objects are **unbundled** countable weight functions
  `q : P → ENNReal`, not bundled `PMF`s.
- Simplex membership is carried explicitly by a predicate like `ProbabilityWeight q`.
- The candidate divergence has **extended-real codomain**:
  it is to be represented by a type equivalent in content to `EReal`, not by `Real`.
- The KL side may be developed first in `ENNReal` / `Real` helper form, but the final theorem must
  compare `D(q || w)` to KL in an extended-value presentation that can state the infinite case
  honestly.

Reason for this choice:

1. the manuscript theorem explicitly quantifies over functionals extended by `+∞` off `Δ(P)`,
2. bundled `PMF`-only formulations hide the off-simplex clause rather than formalizing it,
3. bounded losses may take negative values, so an `ENNReal` codomain for the full objective is the
   wrong final target,
4. the missing proof step is a duality theorem about a functional on the simplex, not merely an
   optimizer characterization for normalized laws.

### 3C. Phase 2D/2E proof-shape decision

The exact missing proof step has been implemented as a **direct discrete convex-duality theorem**,
not by waiting for a generic Banach-space Fenchel-Moreau library theorem to appear upstream.

The implemented Phase 2D/2E route is:

1. define the discrete log-partition functional `H(f) = log ∑_p w(p)e^{f(p)}`,
2. formalize the exact dual representation needed for the simplex specialization,
3. prove the upper bound `D ≤ KL` using Gibbs posteriors,
4. prove the lower bound `D ≥ KL` using the paper's truncation sequence,
5. replace the canonical `SemanticConvergence.lem_kl_necessity`.

No future pass may declare Phase 2 closed while the canonical theorem remains a posterior-gap
surrogate plus a helper discrete Gibbs-attainment lemma.

### 4. Raw two-observer scaffold

Canonical declaration:

- `SemanticConvergence.def_raw_two_observer_functional`

Required mathematical content:

- Domain: a program distribution `q` and a policy-coupled action object.
- Formula:
  `F_t[q; h_t] - β A_t^{ω_A}[π; h_t, q] + γ KL(ν_t^π || \bar w^{ω_A})`.
- This object is auxiliary and policy-coupled, exactly as in the paper.

Lean-side consequence:

- The current per-target divergence term is not the final raw scaffold.

### 5. Two-observer functional

Canonical declarations:

- `SemanticConvergence.def_two_observer_functional`
- `SemanticConvergence.prop_two_observer_minimizer`

Required mathematical content:

- Domain: a program posterior `q` and a distribution `ν` on `C^{ω_A}`.
- Formula:
  `J_t^{ω_B,ω_A}[q,ν; h_t] = F_t[q; h_t] - β E_{C~ν}[G_t^{ω_A}(C; h_t)] + γ KL(ν || \bar w^{ω_A})`.
- Minimizer theorem:
  `q_t*` uniquely minimizes in `q`, and the Gibbs class law
  `ν_t^{G,ω_A}(c | h_t) ∝ \bar w^{ω_A}(c) exp((β/γ) G_t^{ω_A}(c; h_t))`
  uniquely minimizes in `ν`.

Lean-side consequence:

- The canonical theorem may not be phrased as "functional value is zero iff weights agree."

### 6. Kernel lift

The finite/countable kernel lift and the compact-action kernel lift are now separated. This section
continues to govern the countable finite-action surface. The measure-theoretic compact-action
target is additionally frozen in `compact_kernel_exactness_lock.md`; that file is authoritative for
what must eventually occupy the paper-facing compact theorem name.

Canonical declarations:

- `SemanticConvergence.def_raw_kernel_functional`
- `SemanticConvergence.def_kernel_functional`
- `SemanticConvergence.prop_kernel_functional_minimizer`
- `SemanticConvergence.prop_kernel_functional_minimizer_compact`

Required mathematical content:

- Domain: a program posterior `q` and a distribution `κ` on `C^{ω_A} × A`.
- Formula:
  `J_{t,ker}^{ω_B,ω_A}[q,κ; h_t] = F_t[q; h_t] - β E_{(C,A)~κ}[B̄_t^{ω_A}(C,A; h_t)] + γ KL(κ || \bar w^{ω_A} ⊗ λ)`.
- Minimizer theorem:
  `q_t*` uniquely minimizes in `q`, and the Gibbs kernel
  `κ_t^{G,ω_A}(c,a | h_t) ∝ \bar w^{ω_A}(c) λ(a) exp((β/γ) B̄_t^{ω_A}(c,a; h_t))`
  uniquely minimizes in `κ`.

Lean-side consequence:

- The canonical finite/countable kernel theorem may not remain a finite-chart zero-crossing
  statement.
- The compact theorem may not remain a finite-action specialization under a compact-action name.
  Any such specialization must be demoted to a helper such as `_finiteAction` or `_finiteChart`
  before the compact-action theorem is counted as closed.

## Representation choice

The variational rewrite will use the following representation.

### Countable paper-facing distributions

- Program beliefs `q` are normalized distributions on `U.Program`.
- Action-side class laws `ν` are normalized distributions on the observer codomain `ω_A.Ω`.
- Kernel laws `κ` are normalized distributions on `ω_A.Ω × A`.

The preferred implementation vehicle is a normalized probability object (`PMF` or an equivalent
bundled probability distribution type with explicit normalization proofs). The point of the choice
is that the canonical paper-facing declarations must quantify over actual probability
distributions, not over arbitrary weight functions plus later equality checks.

### Canonical codomain for the variational functionals

The canonical paper-facing functionals are to be `Real`-valued on explicit admissible domains.

Reason:

- the paper defines `F_t[q; h_t]` only for admissible `q` with finite expectation and finite KL;
- the two-observer and kernel functionals include subtractive terms, so `ENNReal` is the wrong
  codomain for the canonical statements;
- using `Real` on bundled admissible domains is closer to the paper than encoding the whole object
  as a proxy divergence in `ENNReal`.

Accordingly, the rewrite should bundle the required finiteness hypotheses into the variational
domain objects rather than encoding the canonical functionals as proxy zero-crossings.

### Concrete finite-support realization

The concrete finite-support layer must be an exact finite realization of the same formulas.

- No canonical concrete variational declaration may depend on `Float` approximation.
- Existing finite-support laws should be bridged to exact probability objects using the
  `ConcreteLaw.HasPMFMass` / `toPMF` infrastructure where appropriate.

## Migration rules

1. The canonical names listed in the Scope section are reserved for exact paper-level objects.
2. Any current simplified or proxy implementation that remains useful must move behind helper
   names such as `_legacy`, `_chart`, `_finiteChart`, or an internal namespace.
3. Finite target lists and finite action charts may remain as auxiliary approximation or compact
   reduction tools, but not as the canonical meaning of the paper-facing declarations.
4. During the rewrite it is acceptable for audit closure to regress temporarily. It is not
   acceptable to preserve semantic mismatch for the sake of keeping the current audits green.

## Phase ordering constraint

No further contraction-side overhaul is to begin until the following are true:

- `def_afe` matches Definition 6 exactly;
- `lem_variational` and `lem_kl_necessity` match the paper's belief-side statements;
- `def_two_observer_functional` / `prop_two_observer_minimizer` match the paper's exact Gibbs
  two-observer object;
- `def_kernel_functional` / `prop_kernel_functional_minimizer` match the paper's exact Gibbs
  kernel lift.
- `prop_kernel_functional_minimizer_compact` is either replaced by the measure-theoretic compact
  theorem locked in `compact_kernel_exactness_lock.md`, or explicitly demoted so it is no longer
  presented as the compact-action paper theorem.

## Phase 1 acceptance conditions

Phase 1 is complete only if all of the following are true:

1. This file records a one-to-one target map from each paper variational formula to its canonical
   Lean declaration.
2. The distribution and codomain representation choices are fixed here, not left ambiguous.
3. The core variational modules point to this lock so future edits cannot silently treat the
   current proxy objects as semantically closed.
