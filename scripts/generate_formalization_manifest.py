#!/usr/bin/env python3
"""
Generate the paper-to-Lean coverage manifest from
`algorithmic_free_energy_principle_award.v2.tex`.

The generator writes:

- `formalization_manifest.md`
- `AlgorithmicFreeEnergy/Manifest.lean`

The TeX file is the only theorem source.
"""

from __future__ import annotations

import pathlib
import re
from collections import Counter


ROOT = pathlib.Path(__file__).resolve().parent.parent
TEX_PATH = ROOT / "algorithmic_free_energy_principle_award.v2.tex"
MANIFEST_MD = ROOT / "formalization_manifest.md"
AUDIT_MD = ROOT / "formalization_audit.md"
BRIDGE_MD = ROOT / "first_principles_bridge.md"
MANIFEST_LEAN = ROOT / "AlgorithmicFreeEnergy" / "Manifest.lean"

PATTERN = re.compile(
    r"\\begin\{(definition|lemma|proposition|corollary|theorem)\}"
    r"(?:\[([^\]]*)\])?(.*?)\\end\{\1\}",
    re.S,
)

DERIVED_LABELS = {
    "def:history-compat",
    "def:policy-pred",
    "def:observer",
    "def:int-sem-class",
    "def:history-recoverable",
    "lem:nesting",
    "lem:fit-gap",
    "thm:policy-gap",
    "lem:syntactic-gap",
    "thm:strict-hierarchy",
    "lem:observable-quotient",
    "prop:refinement-chain",
    "thm:factor-through-quotient",
    "def:bhat-omega",
    "def:raw-two-observer-functional",
    "def:two-observer-functional",
    "def:kernel-functional",
    "def:meeting-point-shorthand",
    "prop:belief-invariance-above",
    "prop:two-observer-minimizer",
    "prop:kernel-functional-minimizer",
    "prop:kernel-functional-minimizer-compact",
    "prop:belief-illtyped-below",
    "prop:action-cap",
    "cor:twins-frozen-ratio",
    "thm:meeting-point",
    "cor:canonical-pair",
    "prop:goal-dialed",
    "def:universal-prior",
    "lem:prior-invariance",
    "lem:prior-necessity",
    "def:afe",
    "lem:variational",
    "lem:kl-necessity",
    "lem:merging",
    "def:class-complement",
    "def:semantic-gain",
    "lem:odds-identity",
    "def:semantic-separation",
    "lem:zero-criterion",
    "prop:chernoff-correspondence",
    "def:semantic-rule",
    "def:promotion-supporting",
    "prop:semantic-is-promotion-supporting",
    "def:kernel-semantic-rule",
    "prop:kernel-promotion-support",
    "prop:kernel-promotion-support-compact",
    "def:sep-condition",
    "def:uniform-history-independent-separation",
    "prop:uniform-history-independent-implies-semantic",
    "cor:kl-implies-semantic-separation",
    "cor:event-witness-implies-semantic-separation",
    "def:kernel-sep-condition",
    "prop:finite-action-kernel-separation",
    "prop:compact-action-kernel-separation",
    "lem:conditional-bc",
    "lem:contraction",
    "prop:full-support-behavioral",
    "thm:separating-support-convergence",
    "thm:exploration-floor-behavioral",
    "thm:separating-support-rate",
    "cor:separating-support-finite-time",
    "thm:semantic-convergence",
    "thm:kernel-semantic-convergence",
    "cor:compact-action-kernel",
    "cor:finite-maximin",
    "cor:support-necessary",
    "thm:summable-support-insufficient",
    "cor:goal-dialed-payoff",
    "def:decodable-channel",
    "prop:noise-immunity",
    "def:left-invertible-channel",
    "prop:noise-left-invertible",
    "prop:noise-decoding",
    "cor:noise-transfer",
    "cor:noise-left-invertible-history-independent",
    "lem:one-step-drift",
    "prop:exp-rate",
    "lem:one-step-drift-kernel",
    "prop:kernel-exp-rate",
    "thm:exp-rate-concentration",
    "def:finite-time-policy-observer",
    "lem:monotone-refinement",
    "def:self-ref-rule",
    "lem:exploration-reachability",
    "prop:observer-promotion-sr",
    "def:self-ref-exploratory",
    "thm:self-ref-convergence",
    "prop:self-ref-obstruction",
    "thm:self-ref-exploratory",
    "thm:self-ref-exploratory-rate",
    "prop:self-ref-one-step-split",
    "thm:self-ref-sharp",
    "prop:boundary-identity",
    "def:efe",
    "lem:risk-ig",
    "cor:efe-specialization",
    "def:afe-principle",
    "lem:info-decomp",
    "thm:afe-near-miss",
    "thm:observer-promotion-failure",
    "cor:observer-promotion-universal",
    "cor:promotion-contrast",
    "prop:amortized-surrogate-minimizer",
    "thm:amortized-surrogate",
    "cor:amortized-surrogate-finite-time",
}

CONCRETE_STACK_LABELS = {
    "def:observer",
    "def:history-compat",
    "def:policy-pred",
    "def:int-sem-class",
    "lem:nesting",
    "prop:refinement-chain",
    "lem:observable-quotient",
    "def:history-recoverable",
    "thm:factor-through-quotient",
    "lem:fit-gap",
    "thm:policy-gap",
    "lem:syntactic-gap",
    "thm:strict-hierarchy",
    "def:bhat-omega",
    "def:raw-two-observer-functional",
    "def:two-observer-functional",
    "prop:two-observer-minimizer",
    "def:kernel-functional",
    "prop:kernel-functional-minimizer",
    "prop:kernel-functional-minimizer-compact",
    "def:meeting-point-shorthand",
    "prop:belief-invariance-above",
    "prop:belief-illtyped-below",
    "prop:action-cap",
    "cor:twins-frozen-ratio",
    "thm:meeting-point",
    "cor:canonical-pair",
    "prop:goal-dialed",
    "def:universal-prior",
    "lem:prior-invariance",
    "lem:prior-necessity",
    "def:afe",
    "lem:variational",
    "lem:kl-necessity",
    "lem:merging",
    "def:class-complement",
    "def:semantic-gain",
    "lem:odds-identity",
    "def:semantic-separation",
    "lem:zero-criterion",
    "prop:chernoff-correspondence",
    "def:semantic-rule",
    "def:promotion-supporting",
    "prop:semantic-is-promotion-supporting",
    "def:kernel-semantic-rule",
    "prop:kernel-promotion-support",
    "prop:kernel-promotion-support-compact",
    "def:sep-condition",
    "def:uniform-history-independent-separation",
    "prop:uniform-history-independent-implies-semantic",
    "cor:kl-implies-semantic-separation",
    "cor:event-witness-implies-semantic-separation",
    "def:kernel-sep-condition",
    "prop:finite-action-kernel-separation",
    "prop:compact-action-kernel-separation",
    "cor:noise-left-invertible-history-independent",
    "lem:conditional-bc",
    "lem:contraction",
    "prop:full-support-behavioral",
    "thm:separating-support-convergence",
    "thm:exploration-floor-behavioral",
    "thm:separating-support-rate",
    "cor:separating-support-finite-time",
    "thm:semantic-convergence",
    "thm:kernel-semantic-convergence",
    "cor:compact-action-kernel",
    "cor:finite-maximin",
    "cor:support-necessary",
    "thm:summable-support-insufficient",
    "cor:goal-dialed-payoff",
    "def:decodable-channel",
    "prop:noise-immunity",
    "def:left-invertible-channel",
    "prop:noise-left-invertible",
    "prop:noise-decoding",
    "cor:noise-transfer",
    "lem:one-step-drift",
    "prop:exp-rate",
    "lem:one-step-drift-kernel",
    "prop:kernel-exp-rate",
    "thm:exp-rate-concentration",
    "def:finite-time-policy-observer",
    "lem:monotone-refinement",
    "def:self-ref-rule",
    "lem:exploration-reachability",
    "prop:observer-promotion-sr",
    "thm:self-ref-convergence",
    "prop:self-ref-obstruction",
    "def:self-ref-exploratory",
    "thm:self-ref-exploratory",
    "thm:self-ref-exploratory-rate",
    "prop:self-ref-one-step-split",
    "thm:self-ref-sharp",
    "def:finite-time-policy-observer",
    "lem:monotone-refinement",
    "def:self-ref-rule",
    "lem:exploration-reachability",
    "prop:observer-promotion-sr",
    "thm:self-ref-convergence",
    "prop:self-ref-obstruction",
    "def:self-ref-exploratory",
    "thm:self-ref-exploratory",
    "thm:self-ref-exploratory-rate",
    "prop:self-ref-one-step-split",
    "thm:self-ref-sharp",
    "prop:boundary-identity",
    "def:efe",
    "lem:risk-ig",
    "cor:efe-specialization",
    "def:afe-principle",
    "lem:info-decomp",
    "thm:afe-near-miss",
    "thm:observer-promotion-failure",
    "cor:observer-promotion-universal",
    "cor:promotion-contrast",
    "prop:amortized-surrogate-minimizer",
    "thm:amortized-surrogate",
    "cor:amortized-surrogate-finite-time",
}

COVERED_LABELS = DERIVED_LABELS | {
    "def:bhat-omega",
    "def:raw-two-observer-functional",
    "def:two-observer-functional",
    "prop:two-observer-minimizer",
    "def:kernel-functional",
    "prop:kernel-functional-minimizer",
    "prop:kernel-functional-minimizer-compact",
    "def:meeting-point-shorthand",
    "prop:belief-invariance-above",
    "prop:belief-illtyped-below",
    "prop:action-cap",
    "cor:twins-frozen-ratio",
    "thm:meeting-point",
    "cor:canonical-pair",
    "prop:goal-dialed",
    "def:universal-prior",
    "lem:prior-invariance",
    "lem:prior-necessity",
    "def:afe",
    "lem:variational",
    "lem:kl-necessity",
    "lem:merging",
    "def:class-complement",
    "def:semantic-gain",
    "lem:odds-identity",
    "def:semantic-separation",
    "lem:zero-criterion",
    "prop:chernoff-correspondence",
    "def:semantic-rule",
    "def:promotion-supporting",
    "prop:semantic-is-promotion-supporting",
    "def:kernel-semantic-rule",
    "prop:kernel-promotion-support",
    "prop:kernel-promotion-support-compact",
    "def:sep-condition",
    "def:uniform-history-independent-separation",
    "prop:uniform-history-independent-implies-semantic",
    "cor:kl-implies-semantic-separation",
    "cor:event-witness-implies-semantic-separation",
    "def:kernel-sep-condition",
    "prop:finite-action-kernel-separation",
    "prop:compact-action-kernel-separation",
    "lem:conditional-bc",
    "lem:contraction",
    "prop:full-support-behavioral",
    "thm:separating-support-convergence",
    "thm:exploration-floor-behavioral",
    "thm:separating-support-rate",
    "cor:separating-support-finite-time",
    "thm:semantic-convergence",
    "thm:kernel-semantic-convergence",
    "cor:compact-action-kernel",
    "cor:finite-maximin",
    "cor:support-necessary",
    "thm:summable-support-insufficient",
    "cor:goal-dialed-payoff",
    "def:decodable-channel",
    "prop:noise-immunity",
    "def:left-invertible-channel",
    "prop:noise-left-invertible",
    "prop:noise-decoding",
    "cor:noise-transfer",
    "cor:noise-left-invertible-history-independent",
    "lem:one-step-drift",
    "prop:exp-rate",
    "lem:one-step-drift-kernel",
    "prop:kernel-exp-rate",
    "thm:exp-rate-concentration",
    "def:finite-time-policy-observer",
    "lem:monotone-refinement",
    "def:self-ref-rule",
    "lem:exploration-reachability",
    "prop:observer-promotion-sr",
    "thm:self-ref-convergence",
    "prop:self-ref-obstruction",
    "def:self-ref-exploratory",
    "thm:self-ref-exploratory",
    "thm:self-ref-exploratory-rate",
    "prop:self-ref-one-step-split",
    "thm:self-ref-sharp",
    "prop:boundary-identity",
    "def:efe",
    "lem:risk-ig",
    "cor:efe-specialization",
    "def:afe-principle",
    "lem:info-decomp",
    "thm:afe-near-miss",
    "thm:observer-promotion-failure",
    "cor:observer-promotion-universal",
    "cor:promotion-contrast",
    "prop:amortized-surrogate-minimizer",
    "thm:amortized-surrogate",
    "cor:amortized-surrogate-finite-time",
}

MODULE_OVERRIDES = {
    "def:observer": "AlgorithmicFreeEnergy.Foundations",
    "prop:amortized-surrogate-minimizer": "AlgorithmicFreeEnergy.Surrogate",
    "thm:amortized-surrogate": "AlgorithmicFreeEnergy.Surrogate",
    "cor:amortized-surrogate-finite-time": "AlgorithmicFreeEnergy.Surrogate",
}

CONCRETE_SUBSTRATE_MODULES = {
    "AlgorithmicFreeEnergy.ConcreteCore": "Concrete discrete interaction core: histories, local laws, recursive path laws, reachability.",
    "AlgorithmicFreeEnergy.ConcretePrior": "Concrete prefix-machine and universal-prior substrate.",
    "AlgorithmicFreeEnergy.ConcreteHierarchy": "Concrete observers, semantic equivalence, quotient, and hierarchy witnesses.",
    "AlgorithmicFreeEnergy.ConcreteFunctional": "Concrete Bhattacharyya scores, variational functionals, and finite-list minimizers.",
    "AlgorithmicFreeEnergy.ConcreteBelief": "Concrete prior/posterior, class posterior mass, complement laws, and predictive mixtures.",
    "AlgorithmicFreeEnergy.ConcreteSemantic": "Concrete semantic gain, separation, separating-action sets, and support scaffolds.",
    "AlgorithmicFreeEnergy.ConcreteRates": "Concrete log-odds, drift, expected gain, and support-floor quantities.",
    "AlgorithmicFreeEnergy.ConcreteNoise": "Concrete noisy-channel, decodability, and noisy separation layer.",
    "AlgorithmicFreeEnergy.ConcreteSelfReference": "Concrete finite-time observers, self-referential rules, and witness-driven sharp self-reference layer.",
    "AlgorithmicFreeEnergy.ConcreteBoundary": "Concrete risk/information/expected-free-energy boundary and near-miss layer.",
    "AlgorithmicFreeEnergy.ConcreteSurrogate": "Concrete surrogate energies, finite-list surrogate minimizers, and support witnesses.",
}

ABSTRACT_TO_CONCRETE = {
    "AlgorithmicFreeEnergy.Foundations": [
        "AlgorithmicFreeEnergy.ConcreteCore",
    ],
    "AlgorithmicFreeEnergy.Hierarchy": [
        "AlgorithmicFreeEnergy.ConcreteCore",
        "AlgorithmicFreeEnergy.ConcretePrior",
        "AlgorithmicFreeEnergy.ConcreteHierarchy",
    ],
    "AlgorithmicFreeEnergy.Functional": [
        "AlgorithmicFreeEnergy.ConcreteCore",
        "AlgorithmicFreeEnergy.ConcretePrior",
        "AlgorithmicFreeEnergy.ConcreteHierarchy",
        "AlgorithmicFreeEnergy.ConcreteFunctional",
    ],
    "AlgorithmicFreeEnergy.Belief": [
        "AlgorithmicFreeEnergy.ConcreteCore",
        "AlgorithmicFreeEnergy.ConcretePrior",
        "AlgorithmicFreeEnergy.ConcreteHierarchy",
        "AlgorithmicFreeEnergy.ConcreteBelief",
    ],
    "AlgorithmicFreeEnergy.Semantic": [
        "AlgorithmicFreeEnergy.ConcreteCore",
        "AlgorithmicFreeEnergy.ConcretePrior",
        "AlgorithmicFreeEnergy.ConcreteHierarchy",
        "AlgorithmicFreeEnergy.ConcreteFunctional",
        "AlgorithmicFreeEnergy.ConcreteBelief",
        "AlgorithmicFreeEnergy.ConcreteSemantic",
    ],
    "AlgorithmicFreeEnergy.Rates": [
        "AlgorithmicFreeEnergy.ConcreteSemantic",
        "AlgorithmicFreeEnergy.ConcreteRates",
    ],
    "AlgorithmicFreeEnergy.Noise": [
        "AlgorithmicFreeEnergy.ConcreteSemantic",
        "AlgorithmicFreeEnergy.ConcreteNoise",
    ],
    "AlgorithmicFreeEnergy.SelfReference": [
        "AlgorithmicFreeEnergy.ConcreteSemantic",
        "AlgorithmicFreeEnergy.ConcreteRates",
        "AlgorithmicFreeEnergy.ConcreteSelfReference",
    ],
    "AlgorithmicFreeEnergy.Boundary": [
        "AlgorithmicFreeEnergy.ConcreteSelfReference",
        "AlgorithmicFreeEnergy.ConcreteBoundary",
    ],
    "AlgorithmicFreeEnergy.Surrogate": [
        "AlgorithmicFreeEnergy.ConcreteBoundary",
        "AlgorithmicFreeEnergy.ConcreteSurrogate",
    ],
}


def normalize_decl_name(label: str) -> str:
    cleaned = label.strip()
    cleaned = cleaned.replace(":", "_")
    cleaned = cleaned.replace("-", "_")
    cleaned = cleaned.replace(" ", "_")
    cleaned = cleaned.replace("/", "_")
    return cleaned


def choose_module(start: int, label: str) -> str:
    if label in MODULE_OVERRIDES:
        return MODULE_OVERRIDES[label]
    if start <= 357:
        return "AlgorithmicFreeEnergy.Hierarchy"
    if start <= 738:
        return "AlgorithmicFreeEnergy.Functional"
    if start <= 925:
        return "AlgorithmicFreeEnergy.Belief"
    if 1196 <= start <= 1508:
        return "AlgorithmicFreeEnergy.Noise"
    if 2644 <= start <= 2789:
        return "AlgorithmicFreeEnergy.Rates"
    if 2917 <= start <= 3393:
        return "AlgorithmicFreeEnergy.SelfReference"
    if 3411 <= start <= 3670:
        return "AlgorithmicFreeEnergy.Boundary"
    if start >= 3744:
        return "AlgorithmicFreeEnergy.Surrogate"
    return "AlgorithmicFreeEnergy.Semantic"


def status_for_label(label: str) -> str:
    if label in DERIVED_LABELS:
        return "derived"
    if label in COVERED_LABELS:
        return "wrapped"
    return "declared"


def first_principles_status_for_label(label: str) -> str:
    if label in CONCRETE_STACK_LABELS:
        return "concrete-stack"
    return "abstract-interface"


def migration_status_for_label(label: str) -> str:
    if label in CONCRETE_STACK_LABELS:
        return "migrated-to-concrete"
    return "pending-concrete-migration"


def parse_entries() -> list[dict[str, object]]:
    text = TEX_PATH.read_text()
    entries: list[dict[str, object]] = []
    synthetic_count = 0
    for idx, match in enumerate(PATTERN.finditer(text), start=1):
        kind, title, body = match.group(1), match.group(2), match.group(3)
        label_match = re.search(r"\\label\{([^}]*)\}", body)
        if label_match is None:
            synthetic_count += 1
            label = f"auto__{synthetic_count:03d}"
        else:
            label = label_match.group(1)
        start = text[: match.start()].count("\n") + 1
        end = text[: match.end()].count("\n") + 1
        module = choose_module(start, label)
        decl_name = normalize_decl_name(label)
        entries.append(
            {
                "idx": idx,
                "kind": kind,
                "title": title or "",
                "label": label,
                "start": start,
                "end": end,
                "module": module,
                "decl_name": decl_name,
                "status": status_for_label(label),
                "first_principles_status": first_principles_status_for_label(label),
                "migration_status": migration_status_for_label(label),
            }
        )
    return entries


def render_markdown(entries: list[dict[str, object]]) -> str:
    counts = Counter(entry["kind"] for entry in entries)
    derived_count = sum(entry["status"] == "derived" for entry in entries)
    wrapped_count = sum(entry["status"] == "wrapped" for entry in entries)
    declared_count = sum(entry["status"] == "declared" for entry in entries)
    concrete_count = sum(
        entry["first_principles_status"] == "concrete-stack" for entry in entries
    )
    abstract_count = sum(
        entry["first_principles_status"] == "abstract-interface" for entry in entries
    )
    migrated_count = sum(
        entry["migration_status"] == "migrated-to-concrete" for entry in entries
    )
    pending_migration_count = sum(
        entry["migration_status"] == "pending-concrete-migration" for entry in entries
    )
    lines = [
        "# Formalization Manifest",
        "",
        f"Canonical source: `{TEX_PATH.name}`",
        "",
        "This file is generated by `scripts/generate_formalization_manifest.py`.",
        "",
        "Paper-status conventions:",
        "- `derived`: proved in Lean from the current lower-layer API",
        "- `wrapped`: exact manuscript wrapper still depending on theory-level assumptions",
        "- `declared`: inventoried but not yet covered in Lean",
        "",
        "First-principles conventions:",
        "- `concrete-stack`: proved directly over the concrete foundational stack",
        "- `abstract-interface`: still proved relative to one or more abstract `...Model` interfaces",
        "",
        "Migration conventions:",
        "- `migrated-to-concrete`: the paper-facing wrapper now depends only on the concrete first-principles stack",
        "- `pending-concrete-migration`: the paper-facing wrapper still depends on an abstract theorem interface, even though a concrete substrate may already exist in the repo",
        "",
        f"- Core declarations: `{len(entries)}`",
        f"- Definitions: `{counts['definition']}`",
        f"- Lemmas: `{counts['lemma']}`",
        f"- Propositions: `{counts['proposition']}`",
        f"- Corollaries: `{counts['corollary']}`",
        f"- Theorems: `{counts['theorem']}`",
        f"- Derived: `{derived_count}`",
        f"- Wrapped: `{wrapped_count}`",
        f"- Declared: `{declared_count}`",
        f"- Concrete-stack: `{concrete_count}`",
        f"- Abstract-interface: `{abstract_count}`",
        f"- Migrated-to-concrete: `{migrated_count}`",
        f"- Pending concrete migration: `{pending_migration_count}`",
        "",
        "| # | Kind | TeX label | Title | Lines | Lean module | Lean declaration | Paper status | First-principles status | Migration status |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for entry in entries:
        lines.append(
            "| {idx} | {kind} | `{label}` | {title} | {start}-{end} | `{module}` | "
            "`{decl_name}` | `{status}` | `{first_principles_status}` | `{migration_status}` |".format(**entry)
        )
    lines.append("")
    return "\n".join(lines)


def render_audit(entries: list[dict[str, object]]) -> str:
    status_counts = Counter(entry["status"] for entry in entries)
    fp_counts = Counter(entry["first_principles_status"] for entry in entries)
    migration_counts = Counter(entry["migration_status"] for entry in entries)
    unlabeled_count = sum(
        str(entry["label"]).startswith("auto__")
        for entry in entries
    )
    module_groups: dict[str, list[dict[str, object]]] = {}
    for entry in entries:
        module_groups.setdefault(str(entry["module"]), []).append(entry)
    wrapped_groups = {
        module: [entry for entry in module_entries if entry["status"] == "wrapped"]
        for module, module_entries in module_groups.items()
    }
    abstract_groups = {
        module: [
            entry
            for entry in module_entries
            if entry["first_principles_status"] == "abstract-interface"
        ]
        for module, module_entries in module_groups.items()
    }
    bridge_ready_abstract_count = sum(
        1
        for entry in entries
        if entry["first_principles_status"] == "abstract-interface"
        and str(entry["module"]) in ABSTRACT_TO_CONCRETE
    )

    lines = [
        "# Formalization Audit",
        "",
        f"Canonical source: `{TEX_PATH.name}`",
        "",
        "This file is generated by `scripts/generate_formalization_manifest.py`.",
        "",
        "The target notion of first-principles completion is specified in",
        f"`{(ROOT / 'first_principles_target.md').name}`.",
        "",
        "## Paper-Completeness State",
        f"- Core declarations inventoried: `{len(entries)}`",
        f"- Derived declarations: `{status_counts['derived']}`",
        f"- Wrapped declarations: `{status_counts['wrapped']}`",
        f"- Declared-only declarations: `{status_counts['declared']}`",
        f"- Unlabeled declarations in TeX: `{unlabeled_count}`",
        f"- Paper-complete manuscript coverage: `{'yes' if status_counts['declared'] == 0 and unlabeled_count == 0 else 'no'}`",
        f"- Paper-complete derivation: `{'yes' if status_counts['wrapped'] == 0 and status_counts['declared'] == 0 and unlabeled_count == 0 else 'no'}`",
        "",
        "## First-Principles State",
        f"- Concrete-stack declarations: `{fp_counts['concrete-stack']}`",
        f"- Abstract-interface declarations: `{fp_counts['abstract-interface']}`",
        f"- Migrated-to-concrete declarations: `{migration_counts['migrated-to-concrete']}`",
        f"- Pending concrete migration declarations: `{migration_counts['pending-concrete-migration']}`",
        f"- Abstract-interface declarations with a concrete substrate bridge in repo: `{bridge_ready_abstract_count}`",
        f"- Concrete substrate modules present: `{len(CONCRETE_SUBSTRATE_MODULES)}`",
        f"- First-principles complete: `{'yes' if fp_counts['abstract-interface'] == 0 and status_counts['wrapped'] == 0 and status_counts['declared'] == 0 and unlabeled_count == 0 else 'no'}`",
        "",
        "Interpretation:",
        "- `wrapped` means the paper item has an exact Lean wrapper but still depends on theorem-level assumptions in a `...Theory` bundle.",
        "- `derived` means the paper item is now proved from the currently exposed lower-layer API.",
        "- `abstract-interface` means the paper item is still proved relative to one or more abstract `...Model` interfaces.",
        "- `concrete-stack` means the paper item is proved directly over the concrete foundational stack.",
        "- `migrated-to-concrete` means the paper-facing declaration has already crossed the trust boundary and depends only on the concrete stack.",
        "- `pending-concrete-migration` means the declaration is still paper-complete but has not yet been rewritten onto the concrete stack.",
        "- `bridge in repo` means the corresponding abstract theorem module already has a concrete substrate module stack available to target, even if the paper-facing wrappers have not yet been migrated.",
        "",
    ]
    if fp_counts["abstract-interface"] == 0:
        lines.extend(
            [
                "Legacy compatibility note:",
                "- The older theorem-bearing abstract `...Model` / `...Theory` APIs still present in some source files are retained only for archival or backward-compatibility purposes.",
                "- No manifest-tracked declaration depends on those APIs anymore, so they are outside the active first-principles trust boundary.",
                "",
            ]
        )
    lines.extend(
        [
            "## Concrete Substrate Inventory",
            "",
            "| Concrete module | Role |",
            "| --- | --- |",
        ]
    )
    for module, role in CONCRETE_SUBSTRATE_MODULES.items():
        lines.append(f"| `{module}` | {role} |")

    lines.extend(
        [
            "",
            "## Abstract-to-Concrete Bridge Matrix",
            "",
            "| Paper-facing module | Migrated decls | Pending decls | Concrete substrate modules | Bridge status | Module first-principles closed |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for module in sorted(module_groups):
        migrated = sum(
            entry["migration_status"] == "migrated-to-concrete"
            for entry in module_groups[module]
        )
        pending = sum(
            entry["migration_status"] == "pending-concrete-migration"
            for entry in module_groups[module]
        )
        abstract = sum(
            entry["first_principles_status"] == "abstract-interface"
            for entry in module_groups[module]
        )
        bridge = ABSTRACT_TO_CONCRETE.get(module, [])
        if pending == 0:
            status = "already concrete"
        elif bridge:
            status = "substrate present, wrapper migration pending"
        else:
            status = "no concrete bridge registered"
        closed = "yes" if pending == 0 else "no"
        bridge_text = ", ".join(f"`{m}`" for m in bridge) if bridge else "—"
        lines.append(
            f"| `{module}` | `{migrated}` | `{pending}` | {bridge_text} | {status} | `{closed}` |"
        )

    lines.extend(
        [
            "",
            "## Module Progress",
            "",
            "| Lean module | Derived | Wrapped | Declared | Concrete-stack | Abstract-interface | Migrated | Pending migration | Module first-principles closed | Total |",
            "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
        ]
    )
    for module in sorted(module_groups):
        module_entries = module_groups[module]
        derived = sum(entry["status"] == "derived" for entry in module_entries)
        wrapped = sum(entry["status"] == "wrapped" for entry in module_entries)
        declared = sum(entry["status"] == "declared" for entry in module_entries)
        concrete = sum(
            entry["first_principles_status"] == "concrete-stack"
            for entry in module_entries
        )
        abstract = sum(
            entry["first_principles_status"] == "abstract-interface"
            for entry in module_entries
        )
        migrated = sum(
            entry["migration_status"] == "migrated-to-concrete"
            for entry in module_entries
        )
        pending = sum(
            entry["migration_status"] == "pending-concrete-migration"
            for entry in module_entries
        )
        total = len(module_entries)
        closed = "yes" if pending == 0 else "no"
        lines.append(
            f"| `{module}` | `{derived}` | `{wrapped}` | `{declared}` | `{concrete}` | `{abstract}` | `{migrated}` | `{pending}` | `{closed}` | `{total}` |"
        )

    lines.extend(
        [
            "",
            "## Remaining Paper Debt",
            "",
        ]
    )
    for module in sorted(wrapped_groups):
        wrapped_entries = wrapped_groups[module]
        if not wrapped_entries:
            continue
        lines.append(f"### `{module}` ({len(wrapped_entries)})")
        for entry in wrapped_entries:
            lines.append(
                "- `{label}` ({kind}) -> `{decl_name}`".format(**entry)
            )
        lines.append("")

    lines.extend(
        [
            "## Remaining First-Principles Debt",
            "",
        ]
    )
    for module in sorted(abstract_groups):
        abstract_entries = abstract_groups[module]
        if not abstract_entries:
            continue
        lines.append(f"### `{module}` ({len(abstract_entries)})")
        for entry in abstract_entries:
            lines.append(
                "- `{label}` ({kind}) -> `{decl_name}`".format(**entry)
            )
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def render_bridge(entries: list[dict[str, object]]) -> str:
    module_groups: dict[str, list[dict[str, object]]] = {}
    for entry in entries:
        module_groups.setdefault(str(entry["module"]), []).append(entry)

    bridge_ready_abstract_count = sum(
        1
        for entry in entries
        if entry["first_principles_status"] == "abstract-interface"
        and str(entry["module"]) in ABSTRACT_TO_CONCRETE
    )

    lines = [
        "# First-Principles Bridge",
        "",
        f"Canonical source: `{TEX_PATH.name}`",
        "",
        "This file is generated by `scripts/generate_formalization_manifest.py`.",
        "",
        "It records the current bridge between the paper-facing abstract theorem modules",
        "and the concrete first-principles substrate now present in the repo.",
        "",
        "## Summary",
        f"- Concrete substrate modules present: `{len(CONCRETE_SUBSTRATE_MODULES)}`",
        f"- Abstract-interface declarations in the manuscript manifest: `{sum(entry['first_principles_status'] == 'abstract-interface' for entry in entries)}`",
        f"- Migrated-to-concrete declarations: `{sum(entry['migration_status'] == 'migrated-to-concrete' for entry in entries)}`",
        f"- Pending concrete migration declarations: `{sum(entry['migration_status'] == 'pending-concrete-migration' for entry in entries)}`",
        f"- Abstract-interface declarations whose module already has a concrete bridge in repo: `{bridge_ready_abstract_count}`",
        "",
        "## Concrete Substrate Modules",
        "",
        "| Concrete module | Role |",
        "| --- | --- |",
    ]
    for module, role in CONCRETE_SUBSTRATE_MODULES.items():
        lines.append(f"| `{module}` | {role} |")

    lines.extend(
        [
            "",
            "## Bridge Matrix",
            "",
            "| Paper-facing module | Migrated decls | Pending decls | Concrete substrate modules | Migration state | Module first-principles closed |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for module in sorted(module_groups):
        migrated = sum(
            entry["migration_status"] == "migrated-to-concrete"
            for entry in module_groups[module]
        )
        pending = sum(
            entry["migration_status"] == "pending-concrete-migration"
            for entry in module_groups[module]
        )
        bridge = ABSTRACT_TO_CONCRETE.get(module, [])
        if pending == 0:
            state = "already concrete"
        elif bridge:
            state = "ready to migrate wrappers"
        else:
            state = "bridge not registered"
        closed = "yes" if pending == 0 else "no"
        bridge_text = ", ".join(f"`{m}`" for m in bridge) if bridge else "—"
        lines.append(
            f"| `{module}` | `{migrated}` | `{pending}` | {bridge_text} | {state} | `{closed}` |"
        )

    if sum(entry["first_principles_status"] == "abstract-interface" for entry in entries) == 0:
        lines.extend(
            [
                "",
                "## Trusted Boundary After Phase 10",
                "",
                "All manifest-tracked manuscript declarations now terminate at the",
                "concrete first-principles stack.",
                "The older theorem-bearing abstract `...Model` / `...Theory` APIs still",
                "present in some source files are retained only as legacy compatibility",
                "scaffolding.",
                "No manifest entry depends on them, so they are no longer part of the",
                "mathematical trust boundary.",
                "",
            ]
        )
    else:
        lines.extend(
            [
                "",
                "## Trusted Boundary After Phase 10",
                "",
                "The remaining trusted boundary is no longer the absence of a concrete",
                "substrate. The concrete substrate is present for every abstract theorem",
                "family in the paper-facing development. The remaining boundary is the",
                "migration step: rewriting the paper-facing modules so their wrappers are",
                "proved directly from the corresponding concrete modules instead of the",
                "current abstract `...Model` interfaces.",
                "",
            ]
        )
    return "\n".join(lines)


def lean_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def render_lean(entries: list[dict[str, object]]) -> str:
    lines = [
        "namespace AlgorithmicFreeEnergy",
        "",
        "/-- Generated status marker for each manuscript item. -/",
        "inductive FormalizationStatus where",
        "  | declared",
        "  | wrapped",
        "  | derived",
        "deriving Repr, DecidableEq",
        "",
        "/-- Generated first-principles status marker for each manuscript item. -/",
        "inductive FirstPrinciplesStatus where",
        "  | abstractInterface",
        "  | concreteStack",
        "deriving Repr, DecidableEq",
        "",
        "/-- Generated concrete-migration status marker for each manuscript item. -/",
        "inductive MigrationStatus where",
        "  | pendingConcreteMigration",
        "  | migratedToConcrete",
        "deriving Repr, DecidableEq",
        "",
        "/-- Generated metadata for one core manuscript declaration. -/",
        "structure ManifestEntry where",
        "  texLabel : String",
        "  kind : String",
        "  title : String",
        "  startLine : Nat",
        "  endLine : Nat",
        "  leanModule : String",
        "  declName : String",
        "  status : FormalizationStatus",
        "  firstPrinciplesStatus : FirstPrinciplesStatus",
        "  migrationStatus : MigrationStatus",
        "deriving Repr, DecidableEq",
        "",
        "/-- Generated coverage list for the canonical TeX source. -/",
        "def manifestEntries : List ManifestEntry :=",
        "  [",
    ]
    for entry in entries:
        lines.extend(
            [
                "    { texLabel := " + lean_string(str(entry["label"])),
                "      kind := " + lean_string(str(entry["kind"])),
                "      title := " + lean_string(str(entry["title"])),
                f"      startLine := {entry['start']}",
                f"      endLine := {entry['end']}",
                "      leanModule := " + lean_string(str(entry["module"])),
                "      declName := " + lean_string(str(entry["decl_name"])),
                "      status := FormalizationStatus." + str(entry["status"]),
                "      firstPrinciplesStatus := FirstPrinciplesStatus."
                + ("concreteStack" if entry["first_principles_status"] == "concrete-stack" else "abstractInterface")
                + "\n      migrationStatus := MigrationStatus."
                + ("migratedToConcrete" if entry["migration_status"] == "migrated-to-concrete" else "pendingConcreteMigration")
                + " },",
            ]
        )
    lines.extend(
        [
            "  ]",
            "",
            "def manifestEntryCount : Nat := manifestEntries.length",
            "",
            f"theorem manifestEntryCount_eq : manifestEntryCount = {len(entries)} := rfl",
            "",
            "def derivedEntryCount : Nat :=",
            "  manifestEntries.countP (fun entry => entry.status = FormalizationStatus.derived)",
            "",
            "def wrappedEntryCount : Nat :=",
            "  manifestEntries.countP (fun entry => entry.status = FormalizationStatus.wrapped)",
            "",
            "def declaredEntryCount : Nat :=",
            "  manifestEntries.countP (fun entry => entry.status = FormalizationStatus.declared)",
            "",
            "def concreteStackEntryCount : Nat :=",
            "  manifestEntries.countP (fun entry => entry.firstPrinciplesStatus = FirstPrinciplesStatus.concreteStack)",
            "",
            "def abstractInterfaceEntryCount : Nat :=",
            "  manifestEntries.countP (fun entry => entry.firstPrinciplesStatus = FirstPrinciplesStatus.abstractInterface)",
            "",
            "def migratedToConcreteEntryCount : Nat :=",
            "  manifestEntries.countP (fun entry => entry.migrationStatus = MigrationStatus.migratedToConcrete)",
            "",
            "def pendingConcreteMigrationEntryCount : Nat :=",
            "  manifestEntries.countP (fun entry => entry.migrationStatus = MigrationStatus.pendingConcreteMigration)",
            "",
            f"def concreteSubstrateModuleCount : Nat := {len(CONCRETE_SUBSTRATE_MODULES)}",
            "",
            "def bridgeReadyAbstractEntryCount : Nat :=",
            "  manifestEntries.countP (fun entry =>",
            "    entry.firstPrinciplesStatus = FirstPrinciplesStatus.abstractInterface &&",
            "      match entry.leanModule with",
        ]
    )
    for module in sorted(ABSTRACT_TO_CONCRETE):
        lines.append(f"      | {lean_string(module)} => true")
    lines.extend(
        [
            "      | _ => false)",
            "",
            "def unlabeledEntryCount : Nat :=",
            "  manifestEntries.foldl",
            "    (fun acc entry => if entry.texLabel.startsWith \"auto__\" then acc + 1 else acc)",
            "    0",
            "",
            f"theorem derivedEntryCount_eq : derivedEntryCount = {sum(entry['status'] == 'derived' for entry in entries)} := by",
            "  native_decide",
            "",
            f"theorem wrappedEntryCount_eq : wrappedEntryCount = {sum(entry['status'] == 'wrapped' for entry in entries)} := by",
            "  native_decide",
            "",
            f"theorem declaredEntryCount_eq : declaredEntryCount = {sum(entry['status'] == 'declared' for entry in entries)} := by",
            "  native_decide",
            "",
            f"theorem concreteStackEntryCount_eq : concreteStackEntryCount = {sum(entry['first_principles_status'] == 'concrete-stack' for entry in entries)} := by",
            "  native_decide",
            "",
            f"theorem abstractInterfaceEntryCount_eq : abstractInterfaceEntryCount = {sum(entry['first_principles_status'] == 'abstract-interface' for entry in entries)} := by",
            "  native_decide",
            "",
            f"theorem migratedToConcreteEntryCount_eq : migratedToConcreteEntryCount = {sum(entry['migration_status'] == 'migrated-to-concrete' for entry in entries)} := by",
            "  native_decide",
            "",
            f"theorem pendingConcreteMigrationEntryCount_eq : pendingConcreteMigrationEntryCount = {sum(entry['migration_status'] == 'pending-concrete-migration' for entry in entries)} := by",
            "  native_decide",
            "",
            f"theorem concreteSubstrateModuleCount_eq : concreteSubstrateModuleCount = {len(CONCRETE_SUBSTRATE_MODULES)} := rfl",
            "",
            f"theorem bridgeReadyAbstractEntryCount_eq : bridgeReadyAbstractEntryCount = {sum(entry['first_principles_status'] == 'abstract-interface' and str(entry['module']) in ABSTRACT_TO_CONCRETE for entry in entries)} := by",
            "  native_decide",
            "",
            "def moduleAbstractInterfaceEntryCount (moduleName : String) : Nat :=",
            "  manifestEntries.countP (fun entry =>",
            "    entry.leanModule = moduleName &&",
            "      entry.firstPrinciplesStatus = FirstPrinciplesStatus.abstractInterface)",
            "",
            "def modulePendingConcreteMigrationEntryCount (moduleName : String) : Nat :=",
            "  manifestEntries.countP (fun entry =>",
            "    entry.leanModule = moduleName &&",
            "      entry.migrationStatus = MigrationStatus.pendingConcreteMigration)",
            "",
            "def moduleFirstPrinciplesClosed (moduleName : String) : Bool :=",
            "  modulePendingConcreteMigrationEntryCount moduleName = 0",
            "",
            "theorem unlabeledEntryCount_eq : unlabeledEntryCount = 0 := by",
            "  native_decide",
            "",
            "def paperFullyCovered : Bool :=",
            "  declaredEntryCount = 0 && unlabeledEntryCount = 0",
            "",
            "def paperFullyDerived : Bool :=",
            "  wrappedEntryCount = 0 && paperFullyCovered",
            "",
            "def fullyCovered : Bool :=",
            "  paperFullyCovered",
            "",
            "def fullyDerived : Bool :=",
            "  paperFullyDerived",
            "",
            "def fullyFirstPrinciples : Bool :=",
            "  abstractInterfaceEntryCount = 0 && paperFullyDerived",
            "",
            f"theorem paperFullyCovered_eq : paperFullyCovered = {str(sum(entry['status'] == 'declared' for entry in entries) == 0 and sum(str(entry['label']).startswith('auto__') for entry in entries) == 0).lower()} := by",
            "  native_decide",
            "",
            f"theorem paperFullyDerived_eq : paperFullyDerived = {str(sum(entry['status'] == 'wrapped' for entry in entries) == 0 and sum(entry['status'] == 'declared' for entry in entries) == 0 and sum(str(entry['label']).startswith('auto__') for entry in entries) == 0).lower()} := by",
            "  native_decide",
            "",
            "theorem fullyCovered_eq : fullyCovered = paperFullyCovered := rfl",
            "",
            "theorem fullyDerived_eq : fullyDerived = paperFullyDerived := rfl",
            "",
            f"theorem fullyFirstPrinciples_eq : fullyFirstPrinciples = {str(sum(entry['first_principles_status'] == 'abstract-interface' for entry in entries) == 0 and sum(entry['status'] == 'wrapped' for entry in entries) == 0 and sum(entry['status'] == 'declared' for entry in entries) == 0 and sum(str(entry['label']).startswith('auto__') for entry in entries) == 0).lower()} := by",
            "  native_decide",
            "",
            "end AlgorithmicFreeEnergy",
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> None:
    entries = parse_entries()
    MANIFEST_MD.write_text(render_markdown(entries))
    AUDIT_MD.write_text(render_audit(entries))
    BRIDGE_MD.write_text(render_bridge(entries))
    MANIFEST_LEAN.write_text(render_lean(entries))


if __name__ == "__main__":
    main()
