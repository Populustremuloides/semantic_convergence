# Formalization Target

This document fixes the target meaning of "first-principles formalization" for
`semantic_convergence_interactive_learning.tex`.

It is intentionally stricter than the current paper-to-Lean coverage notion.
The current repo already has exact Lean counterparts for all core manuscript
items. That does **not** yet mean those items are reduced to a concrete
foundational stack.

## Current distinction

There are now two separate closure notions in the repo:

- `paper-complete`
  Every manuscript definition/result has an exact Lean counterpart, and every
  counterpart is proved relative to the currently exposed Lean API.
- `first-principles-complete`
  Every manuscript definition/result is proved directly over a concrete semantic
  stack, without relying on theorem-carrying abstract `...Model` interfaces as
  part of the mathematical trust boundary.

The live status for both notions is tracked in:

- [formalization_manifest.md](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/formalization_manifest.md)
- [formalization_audit.md](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/formalization_audit.md)
- [Manifest.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Manifest.lean)

## Target concrete foundation

The target first-principles stack for this project is:

- Actions: a finite type `A` with decidable equality.
- Observations: a countable type `O` with decidable equality.
- One-step events: pairs `(a, o) : A × O`.
- Length-`t` histories: `Hist t := Fin t → (A × O)`.
- Full histories: `Σ t, Hist t`.
- Policies: discrete stochastic kernels `Hist t → PMF A`.
- Environment semantics: chronological kernels `Hist t → A → PMF O`.
- Programs: concrete codes for a prefix-free universal machine producing
  environment semantics.
- Universal prior: a concrete prefix-machine prior induced by code lengths and
  machine decoding, not an abstract weight function.
- Finite-horizon path laws: recursively defined from the concrete policy and
  environment kernels.
- Reachability/support: defined from those concrete path laws.
- Semantic equivalence: equality of environment behavior on reachable
  history-action pairs.
- Semantic classes: the quotient by that concrete equivalence relation.
- Class posterior and class-complement laws: concrete pushforwards and
  normalized mixtures induced by the concrete posterior.
- Information objects: concrete Bhattacharyya affinity/separation, KL
  divergence, posterior odds, log-odds drift, and concentration statements.
- Self-reference objects: concrete finite-time observers and induced
  self-referential policies built from the same concrete policy/history stack.

## Legacy abstract compatibility APIs

The repo still contains the older theorem-bearing abstract interfaces in files
such as:

- [Functional.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Functional.lean)
- [Belief.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Belief.lean)
- [Semantic.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Semantic.lean)
- [Rates.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Rates.lean)
- [Noise.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Noise.lean)
- [SelfReference.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/SelfReference.lean)
- [Boundary.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Boundary.lean)
- [Surrogate.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Surrogate.lean)

Those interfaces are now retained only for archival comparison and
backward-compatibility. As of the Phase 10 closure pass, no manifest-tracked
paper declaration depends on them anymore. The active trust boundary is the
concrete stack recorded in the generated manifest and audit, not these retained
legacy APIs.

## Phase 1 concrete core

The first concrete reduction layer now lives in
[ConcreteCore.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteCore.lean).

That file introduces:

- concrete finitely supported discrete laws
- concrete policies and one-step environment kernels
- concrete finite-horizon path laws by recursion
- concrete history reachability and reachable history-action pairs
- a concrete reachable-pair equality convention as a setoid over kernels relative
  to a fixed reachable-pair predicate

This is not yet the full terminal foundation for the paper. In particular, the
paper-facing theorem modules still prove most results relative to abstract
`...Model` interfaces. But the repo now has a real concrete interaction core for
later phases to build on, instead of only abstract placeholders.

## Phase 2 concrete machine/prior layer

The second concrete reduction layer now lives in
[ConcretePrior.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcretePrior.lean).

That file introduces:

- concrete binary codewords
- prefix and prefix-free code-domain structure
- a concrete finite-domain prefix machine with explicit semantics on accepted codes
- a concrete universal prior on machine-domain programs from code lengths
- concrete machine mixtures under a fixed policy
- concrete class prior mass and semantic-complexity scaffolding
- prefix-extension structure for machine-to-machine re-encodings

This still does not make the paper first-principles complete. The paper-facing
belief theorems in [Belief.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Belief.lean)
remain stated over the abstract `BeliefModel`. But the repo now has a real
prefix-machine/prior layer for those later phases to target, rather than only a
symbolic prior API.

## Phase 3 concrete hierarchy layer

The third concrete reduction layer now lives in
[ConcreteHierarchy.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteHierarchy.lean).

That file introduces:

- concrete encoded programs as explicit code/kernel pairs
- concrete policy observers and policy-indexed history observers
- concrete interventional semantic equivalence as equality of policy views under
  all policies
- a concrete semantic quotient and observable-quotient theorem
- concrete nesting and refinement-chain theorems
- a concrete exact-recoverability-to-quotient-factorization theorem
- witness-driven concrete fit-gap / policy-gap / syntactic-gap / strict-hierarchy
  statements

This is a real first-principles hierarchy layer, but it has not yet been used to
rewrite the paper-facing entries in the generated manifest. So the current
manifest still records the hierarchy labels as `abstract-interface` until the
paper-facing wrappers are migrated onto this concrete layer.

## Phase 4 concrete functional layer

The fourth concrete reduction layer now lives in
[ConcreteFunctional.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteFunctional.lean).

That file introduces:

- concrete restriction and total-mass operations on finitely supported laws
- a source-type-independent finite-support mixture operator
- concrete support-union, overlap, and Bhattacharyya-style score definitions for
  finitely supported observation laws
- concrete observer fibers and fiber masses over encoded programs
- concrete fiber/complement observation mixtures at a fixed history-action pair
- concrete `bhatOmega`, raw two-observer, two-observer, and kernel-lift
  functionals over the concrete hierarchy stack
- a finite-list argmin witness API (`MinimizesOnList`, `argminOnList`) for the
  later minimizer phases

This still does not make the paper-facing functional entries
`concrete-stack`. The generated manifest continues to classify the functional
labels as `abstract-interface` until [Functional.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Functional.lean)
is rewritten to target these concrete objects directly. But the repo now has a
real first-principles functional substrate instead of only theorem-carrying
abstract functional interfaces.

## Phase 5 concrete belief layer

The fifth concrete reduction layer now lives in
[ConcreteBelief.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteBelief.lean).

That file introduces:

- finite machine-domain enumeration as an actual list of programs
- concrete encoded-program forgetful maps from machine-domain programs
- concrete prior laws, Bayes numerator laws, evidence, and normalized posteriors
  on the finite machine domain
- concrete class posterior mass, posterior restriction/renormalization, and
  class-complement posterior objects
- concrete observer-fiber predicates and observer-fiber posterior masses
- concrete posterior pushforwards through encoded-program observers
- concrete class-side and complement-side predictive observation laws, including
  observer-fiber specialization
- representative-independence at the observer-fiber level via
  `observerFiber_eq_of_sameView` and
  `observerFiberPosteriorMass_eq_of_sameView`

This is the concrete Bayesian engine the later first-principles semantic and
rate phases will target. It still does not migrate the paper-facing belief or
semantic wrappers to `concrete-stack`; those remain `abstract-interface` until
[Belief.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Belief.lean)
and [Semantic.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Semantic.lean)
are rewritten to use these concrete posterior and class-complement objects
directly.

## Phase 6 concrete semantic layer

The sixth concrete reduction layer now lives in
[ConcreteSemantic.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteSemantic.lean).

That file introduces:

- concrete class-complement posterior masses and class posterior odds on the
  finite machine domain
- concrete observer-fiber posterior odds through encoded-program observers
- concrete observer-fiber class-vs-complement predictive law pairs
- concrete semantic separation and semantic gain at a fixed history-action pair
- concrete separating-action predicates and separating-action sets
- explicit finite-action support predicates and separating-support predicates
- a simple full-support finite action law scaffold for later support theorems
- same-view invariance for observer-fiber class-complement laws, posterior odds,
  semantic separation, and semantic gain
- finite-action witness lemmas showing how full support converts a separating
  action witness into separating support

This is the first concrete semantic core in the repo: the class-vs-complement
objects, semantic information quantities, and separating-support notions are now
defined directly over the finite machine-domain posterior rather than only
through the abstract [Semantic.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Semantic.lean)
API. The paper-facing semantic wrappers still remain `abstract-interface`,
because the convergence, rate, and converse theorems have not yet been migrated
onto this concrete layer. Those migrations are the work of the later
first-principles phases.

## Phase 7 concrete rates and noise layers

The seventh concrete reduction layer now lives in two files:

- [ConcreteRates.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteRates.lean)
- [ConcreteNoise.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteNoise.lean)

`ConcreteRates.lean` introduces:

- concrete log-odds proxies from finite machine-domain posterior odds
- a concrete one-step log-odds drift between finite histories
- expected semantic gain under a local action law
- separating-support weights and lower-bound predicates on finite action lists
- same-view invariance for log-odds, drift, and expected semantic gain

`ConcreteNoise.lean` introduces:

- concrete discrete observation channels and their pushforwards on finitely
  supported observation laws
- deterministic and identity channels
- concrete decodable and support-left-invertible channel predicates
- noisy observer-fiber class-complement laws and noisy semantic separation
- same-view invariance for the noisy class-complement and noisy semantic
  separation objects
- identity-channel sanity theorems for decodability and support-left-invertibility

This phase does not yet migrate the paper-facing [Rates.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Rates.lean)
or [Noise.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Noise.lean)
wrappers to `concrete-stack`. But the repo now has concrete rate-side and
corrupted-observation objects defined directly over the finite machine-domain
semantic core, so the remaining first-principles work is no longer blocked on a
missing quantitative or noisy substrate.

## Phase 8 concrete self-reference layer

The eighth concrete reduction layer now lives in
[ConcreteSelfReference.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteSelfReference.lean).

That file introduces:

- concrete finite-time policy views and finite-time policy observers
- concrete finite-time observer fibers through a target program
- concrete eventual-isolation and isolation-obstruction predicates
- a concrete one-step split predicate on explicit finite action lists
- concrete observer-driven and exploration-completed policy rules
- monotone-refinement and fiber-antitonicity facts for finite-time observers
- same-view invariance for finite-time observer fibers
- witness-driven eventual-isolation, obstruction, separating-support, and
  sharpened self-reference theorems

This phase gives the repo a real finite-time observer and self-referential rule
substrate over the concrete semantic core, rather than only the abstract
[SelfReference.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/SelfReference.lean)
API. The paper-facing self-reference wrappers still remain
`abstract-interface`, because the manuscript theorems have not yet been
migrated onto these concrete observers and policy rules directly. But the
remaining first-principles work is no longer blocked on a missing concrete
self-reference layer.

## Phase 9 concrete boundary and surrogate layers

The ninth concrete reduction layer now lives in two files:

- [ConcreteBoundary.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteBoundary.lean)
- [ConcreteSurrogate.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/ConcreteSurrogate.lean)

`ConcreteBoundary.lean` introduces:

- concrete rational boundary risk, information-gain, and expected-free-energy
  terms on observer fibers
- a concrete information decomposition pairing posterior odds with the local
  information term
- a finite-list concrete AFE minimizer and induced singleton-support action law
- same-view invariance for the boundary quantities
- witness-driven near-miss, observer-promotion-failure, and promotion-contrast
  predicates and theorems

`ConcreteSurrogate.lean` introduces:

- concrete surrogate information scores and regularized surrogate energies
- a finite-list concrete amortized-surrogate minimizer
- a concrete singleton-support action law induced by the surrogate minimizer
- same-view invariance for surrogate energies
- witness-driven separating-support theorems for the surrogate minimizer

This phase gives the repo a concrete boundary/AFE and implementation-facing
surrogate substrate over the earlier semantic, rate, noise, and self-reference
layers. The paper-facing [Boundary.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Boundary.lean)
and [Surrogate.lean](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/SemanticConvergence/Surrogate.lean)
wrappers still remain `abstract-interface`, because the manuscript-level
theorems have not yet been rewritten to target these concrete objects directly.
But the repo now has concrete boundary and surrogate objects in place, so the
first-principles campaign is no longer blocked on missing end-of-paper
infrastructure.

## Phase 10 trust-boundary closure audit

The tenth phase is not another substrate-building phase. At this point the repo
already contains concrete modules for every major mathematical layer used by the
paper-facing development.

Phase 10 therefore closes the bookkeeping and trust-boundary audit:

- the generated manifest/audit pipeline now distinguishes paper-complete
  derivation from first-principles migration status
- the repo now emits a generated bridge report,
  [formalization_bridge.md](/Users/brianbrown/Documents/Claude/Projects/algorithmic_free_energy/formalization_bridge.md),
  which maps each paper-facing abstract theorem module to the concrete substrate
  modules already present in the repo
- the former migration boundary has now been closed: every paper-facing wrapper
  is migrated onto the concrete modules listed in that bridge report
- any retained abstract `...Model` / `...Theory` APIs in the source tree are
  now legacy compatibility scaffolding only and are outside the mathematical
  trust boundary

So after Phase 10, the project should be read as follows:

- the concrete first-principles substrate is present through the full paper
- the paper-facing development is entirely `concrete-stack`
- the remaining abstract interfaces in source files are legacy compatibility
  layers, not active proof dependencies

## Migration bookkeeping

The generated manifest pipeline now tracks three distinct notions for every
paper-facing declaration:

- paper-facing derivation status: `derived / wrapped / declared`
- first-principles trust-boundary status: `concrete-stack / abstract-interface`
- migration status: `migrated-to-concrete / pending-concrete-migration`

The generated audit and bridge reports also expose module-level closure checks.
A paper-facing module is considered first-principles closed exactly when its
pending concrete migration count is zero.

## Status interpretation

The manifest now uses a second status axis:

- `concrete-stack`
  The manuscript item is proved directly over the concrete foundational stack.
- `abstract-interface`
  The manuscript item is still proved relative to one or more abstract
  `...Model` interfaces.

This axis is independent of the paper-facing status axis
`derived / wrapped / declared`.

## Definition of done

The project is `first-principles-complete` only when all of the following hold:

1. Every core manuscript declaration is still covered 1-to-1 in Lean.
2. `declared = 0`.
3. `wrapped = 0`.
4. `abstract-interface = 0`.
5. The generated Lean manifest reports `fullyFirstPrinciples = true`.
6. `lake build` passes.
7. The repo contains no `sorry`, `admit`, or placeholder `axiom`.

At that point it is fair to say the manuscript is mechanically verified from the
explicit concrete formal foundation adopted by this repo, rather than merely
relative to an abstract axiomatization.
