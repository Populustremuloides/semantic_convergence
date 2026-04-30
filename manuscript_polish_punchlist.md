# H10 manuscript polish punchlist

Date: Apr 30, 2026.

## Summary

The manuscript contains approximately 60 instances of problematic language across all eight categories of concern. The most prevalent issues are: (1) persistent use of "H10" versioning nomenclature in the title, status box, and throughout the paper (critical); (2) self-aware meta-commentary about the paper's own structure and what routes/sections "remain" or are "kept" (substantive); (3) embedding of Lean theorem paths inside assumption statements and definition text rather than only in proof captions (substantive); (4) references to "this copy" and "consolidated assumptions" that signal draft-awareness (critical); (5) extensive use of "records," "identifies," and "routes" as structure-description verbs that dominate the introduction and sections roadmap (cosmetic but pervasive). The paper reads as highly conscious of its own H10-to-previous iteration path and the Lean formalization—both valuable intellectually but problematic for a polished manuscript. A focused revision pass removing all H10 labels, consolidating Lean references into proof captions, and replacing meta-structural language with direct mathematical exposition would substantially professionalize the voice.

---

## Category 1: Versioning and draft-history language

| Line | Current text | Problem | Suggested replacement |
|------|--------------|---------|----------------------|
| 48 | `\large H10 Lean-Verified Interface Draft}` | Title explicitly labels version; "Draft" is draft-aware | `\large Lean-Verified Interface}` |
| 57–69 | Entire "H10 status" box | Self-conscious status/version box explaining what this copy is, mentions "Older drafts are archived", the H10 is a version marker; not in a published paper | Delete entirely or replace with brief, non-self-aware note if needed |
| 80 | "The verified positive theorem of this H10 copy answers the boxed problem" | References "this H10 copy" explicitly—says this is an instance of something versioned; breaks fourth wall | Replace "The verified positive theorem of this H10 copy" with "The verified main theorem" |
| 114 | "This H10 copy answers the boxed problem through the exact kernel-functional route." | Same self-referential "this H10 copy" issue | Replace with "The main theorem answers the boxed problem through the exact kernel-functional route." |
| 1372 | "Earlier drafts used KL and event-witness inequalities as informal sufficient conditions" | Explicitly references earlier drafts of this paper | Replace "Earlier drafts used" with "Prior work has used" or delete entirely if it doesn't matter |
| 1515 | "The package is H10-verified when:" | "H10-verified" is version terminology; confuses which is the formal standard | Replace "H10-verified" with "verified" throughout (H10 removed) |
| 1582 | "the canonical predictive-kernel observer and the consolidated assumptions above." | "consolidated" implies assembly from pieces; reads like internal nomenclature | Replace "consolidated" with "stated" or delete |

---

## Category 2: Meta-commentary about the paper's structure and evolution

| Line | Current text | Problem | Suggested replacement |
|------|--------------|---------|----------------------|
| 80 | "The older support/rate route is retained as a stronger zero-out special-case companion" | Describes paper structure in self-aware terms: the "older" route is "retained"; implies previous version and editorial decision | Replace with "The support/rate theorem specializes to the zero-out case and supplies finite-horizon rate bounds." |
| 114 | "The key upgrade over the previous interface is that the semantic-to-true-law calibration step is no longer a free-standing coherence assumption" | "key upgrade over the previous interface" is meta-commentary about version changes; inappropriate for published paper | Replace with "A key feature is that the semantic-to-true-law calibration step is internal to the theorem." |
| 116 | "Section~\ref{sec:main} states the consolidated H10 coupling conditions on the package" | "consolidated" reads as internal assembly language; also "H10" version label | Replace "consolidated H10 coupling conditions" with "formal coupling conditions" |
| 864 | "The formal meeting-point block is intentionally conservative: it records the refinement predicates used by the verified H10 package." | "intentionally conservative" is self-aware editorial justification | Soften to "The formal meeting-point block is a refinement-predicate wrapper" or delete the editorial comment |
| 891 | "The remainder of the paper identifies the canonical Bayes/Gibbs-plus-separation structure singled out by the observer analysis" | Section-forward roadmap language; structure-referential | Replace with "The analysis of observer structure singles out a canonical Bayes/Gibbs-plus-separation form." |
| 1620 | "The older support-floor calculations remain useful as sufficient checks for the package assumptions" | "older" implies version history; "remain useful" implies retention decision | Replace with "The support-floor calculations serve as sufficient-condition checks for the package assumptions." |
| 2041 | "The self-referential section is now a proxy layer." | "is now" signals a recent revision; meta-commentary about structure | Replace with "The self-referential section provides a proxy-layer interface." |

---

## Category 3: Lean references in inappropriate places (inside assumptions, definitions, or theorem statements)

| Line | Current text | Problem | Suggested replacement |
|------|--------------|---------|----------------------|
| 1506 | End of Definition: `\noindent\emph{Lean: \path{SemanticConvergence.Ontology.Coupling.def_semantic_learning_package} and \path{SemanticConvergence.Ontology.Coupling.predictiveKernelSemanticLearningPackage}.}` | Lean paths in definition body is OK in this location (end of def); acceptable | No change—this is in a proof-caption slot |
| 1532 | Inside Assumption (M6): "This is the manuscript form of \path{CountablePrefixMachine.HasTrueLawHellingerPrefixKernelObligations}." | Lean path embedded inside assumption statement text; breaks mathematical exposition | Replace "This is the manuscript form of \path{...}" with "See the Lean development for the formal predicate." or move to proof caption |
| 1557 | Proof caption (OK) | Lean path in proof caption is standard; no issue | No change |

---

## Category 4: Apologetic, hedging, and transitional filler

| Line | Current text | Problem | Suggested replacement |
|------|--------------|---------|----------------------|
| 1372 | "Earlier drafts used ... The Lean-facing H10 route does not use those analytic inequalities." | Hedging/contrastive language about what this version does vs. earlier; implies draft history | Replace with "The formal route uses Definition~\ref{def:sep-condition} and the bundled class-predictive separation field." |
| 2041 | "The self-referential section is now a proxy layer. It defines finite-time observer interfaces and records the exact local witnesses Lean currently proves." | "now" and "currently" are hedge words; "currently proves" suggests incompleteness or draft state | Replace with "The self-referential section provides a proxy-layer interface. It defines finite-time observer predicates the formal development proves." |

---

## Category 5: Internal-process and retained-structure language

| Line | Current text | Problem | Suggested replacement |
|------|--------------|---------|----------------------|
| 66 | "The Lean development now derives the semantic calibration/coherence bridge internally from the canonical predictive-kernel observer. The remaining load-bearing premises are..." | "now derives" signals a change (draft history); "remaining" implies something was removed | Replace "now derives" with "derives" and "remaining" with "load-bearing" |
| 80 | "The older support/rate route is retained as a stronger zero-out special-case companion" | "retained" implies an editorial decision to keep something old | Replace with "The support/rate theorem specializes to the zero-out case" |
| 1299 | "the channel witness is retained and the posterior mass..." | "retained" in a corollary statement; reads like internal bookkeeping | Replace "is retained and" with "holds and" |
| 1324 | "the separate concrete zero-out stack tracked in the Lean manifest." | "manifest" is internal-process vocabulary; sounds like an audit/ledger | Replace "tracked in the Lean manifest" with "formalized in the Lean development" |
| 1586 | "tracked in the Lean manifest." | Same "manifest" issue | Replace with "formalized in the Lean development" |
| 2041 | "records the exact local witnesses Lean currently proves" | "currently proves" implies this is a snapshot of an ongoing development; draft language | Replace with "proves" (drop "currently") |
| 2313 | "The concrete surrogate assumptions \textup{(A1)--(A3)} remain the verified deployment-side route" | "remain" implies retention from prior version; internal structure decision | Replace with "The concrete surrogate assumptions \textup{(A1)--(A3)} provide the verified deployment-side route" |
| 2318 | "remain separately formalized" | Same "remain" issue | Replace with "are separately formalized" |

---

## Category 6: Personality, informal voice, and over-explanation

| Line | Current text | Problem | Suggested replacement |
|------|--------------|---------|----------------------|
| 2346 | "The boxed problem has two logically distinct parts." | Informal, conversational opening to discussion; "the boxed problem" is colloquial | Replace with "The main result addresses two logically distinct components." |
| 2354 | "First, when do generic information gain and semantic gain coincide? The boundary proxy makes this the right comparison question, but this copy does not prove a full structural equivalence or a constructed counterexample." | Self-aware "this copy does not prove" — acknowledges limitation in terms of this version; reads like defending a draft | Replace with "A full structural equivalence or constructed counterexample would clarify when these coincide." |
| 2358 | "What remains open is the harder approximation question: for which model classes, training procedures, and amortized inference schemes can one prove those assumptions from the optimization itself rather than impose them as deployment-side hypotheses?" | Informal question-statement; "what remains open" is more draft-like than "open problems are" | Rephrase to "Open problems include: deriving those assumptions from the optimization itself rather than imposing them as deployment-side hypotheses." |
| 2365 | "\emph{Observer promotion} is the organizing informal concept:" | "informal concept" is hedging; signals the concept is not formally defined (true, but hedge language) | Replace with "Observer promotion is the organizing principle:" or delete the editorial note |

---

## Category 7: Self-aware forward/backward references and roadmaps

| Line | Current text | Problem | Suggested replacement |
|------|--------------|---------|----------------------|
| 116 | "Section~\ref{sec:main} states the consolidated H10 coupling conditions on the package $\mathfrak K=(\mathcal I,\mathcal J,\Scal)$ and proves the verified main theorem from them, then keeps the stronger support/rate stack as an explicit zero-out special-case route" | Excessive detail about what sections do; "keeps the stronger support/rate stack" is meta-structural | Simplify: "Section~\ref{sec:main} proves the main theorem from the coupling conditions and provides the support/rate specialization." |
| 806 | "Proposition~\ref{prop:belief-invariance-above} says that belief-admissible observers are fine enough to determine the behavioral view. Proposition~\ref{prop:belief-illtyped-below} records the corresponding formal failure predicate when belief admissibility is absent." | Two sentences of structure-description; "records the corresponding formal failure predicate" is explanatory rather than mathematical | Replace with direct statement: "Proposition~\ref{prop:belief-illtyped-below} supplies the formal failure predicate: belief admissibility fails when..." |
| 893 | "Section~\ref{sec:belief} identifies the \emph{belief-side minimizer} of $\mathcal J_t^{\omega_B,\omega_A}$ at the canonical belief observer $\omega_B=\omega_{\mathrm{syn}}$: the Bayes/Gibbs posterior under the universal prior." | Sentence explaining what a section does, then restates its content; redundant structure-commentary | State once: "At the canonical belief observer $\omega_B=\omega_{\mathrm{syn}}$, the belief-side minimizer is the Bayes/Gibbs posterior (Section~\ref{sec:belief})." |

---

## Category 8: Unusual structural elements and diagnostics

| Line | Current text | Problem | Suggested replacement |
|------|--------------|---------|----------------------|
| 57–69 | Status box with "H10 status" header | Structural element that reads like an internal memo or draft status; not appropriate for published paper | Delete or replace with a brief non-self-aware note if necessary information is vital |
| 2027 | Remark title: "[Finite-time proxy and remaining gap]" | "remaining gap" frames an incompleteness in draft terms; sounds like a to-do | Rephrase: "[Finite-time proxy and open gap]" or "[Finite-time proxy interface]" |
| 2156 | "The formal theorem here is a witness package: if a boundary action preference witness and a frozen-posterior-through-horizon predicate are supplied, Lean packages them into the near-miss conclusion below." | "Lean packages them" is implementation-level language; "witness package" is jargon for "interface that requires external predicates" but reads like internal tool talk | Replace with "The formal theorem packages supplied witness predicates into the near-miss conclusion." |
| 2190 | "The formal near-miss statements in this copy are witness predicates." | "in this copy" is explicit draft-awareness marker (similar to "this H10 copy") | Replace with "The formal near-miss statements are witness predicates." |
| 2354 | "but this copy does not prove a full structural equivalence" | "this copy" again—explicit version self-reference | Replace with "The paper does not prove a full structural equivalence" or simply remove clause |

---

## Recommended priority

### Critical (visible to any reviewer; remove immediately)

1. **Line 48**: Remove "H10 Lean-Verified Interface Draft" from title; simplify to "Lean-Verified Interface".
2. **Lines 57–69**: Delete entire "H10 status" box or replace with non-self-aware, essential information only.
3. **Line 80**: Remove "The verified positive theorem of this H10 copy" → "The verified main theorem".
4. **Line 114**: Remove "This H10 copy answers" → "The main theorem answers".
5. **Line 2190**: Remove "in this copy" from "The formal near-miss statements in this copy are".
6. **Line 2354**: Remove "this copy does not prove" → rephrase without version reference.

### Substantive (noticeable but not embarrassing; remove for polish)

7. **Line 80**: Replace "The older support/rate route is retained as a stronger zero-out special-case companion" with "The support/rate theorem specializes to the zero-out case and supplies finite-horizon rate bounds."
8. **Line 114**: Replace "The key upgrade over the previous interface" with "A key feature is".
9. **Line 116**: Replace "consolidated H10 coupling conditions" with "formal coupling conditions".
10. **Line 864**: Remove "intentionally conservative" editorial comment.
11. **Line 1515**: Change "H10-verified" to "verified" throughout (appears ~25 times; see list below).
12. **Line 1582**: Replace "consolidated assumptions" with "stated assumptions".
13. **Line 1620**: Replace "The older support-floor calculations remain useful" with "The support-floor calculations serve as sufficient-condition checks".
14. **Line 2041**: Replace "The self-referential section is now a proxy layer" with "The self-referential section provides a proxy-layer interface."
15. **Line 1324 and 1586**: Replace "tracked in the Lean manifest" with "formalized in the Lean development" (appears 2 times).

### Cosmetic (minor; fold into next revision)

16. **Line 66**: Change "now derives" to "derives" and "remaining" to "load-bearing" for clearer exposition.
17. **Line 1299**: Replace "is retained and" with "holds and".
18. **Line 891**: Simplify excessive section-forward roadmap.
19. **Line 806**: Replace structure-commentary with direct mathematical statement.
20. **Line 893**: Rewrite to avoid redundant section-explanation.
21. **Line 2041**: Drop "currently" from "currently proves".
22. **Line 2313** and **2318**: Replace "remain" with "provide" and "are" respectively.
23. **Line 2027**: Rephrase remark title "[Finite-time proxy and remaining gap]" to "[Finite-time proxy interface]".

### Defensible (arguably OK; flag for author judgment)

24. **Line 1372**: "Earlier drafts used..." vs. "Prior work used..." — arguably OK in context of explaining why Lean uses a different route, but "drafts of this paper" is self-referential.
25. **Line 2346**: "The boxed problem" is informal but memorable; could stay if voice is intentionally accessible.
26. **Line 2365**: "informal concept" — hedging, but accurately describes observer promotion (not formally defined, used as organizing principle).

---

## Complete list of "H10" removals

The term "H10" appears in the following locations and should be removed or renamed:

- Line 48: Title
- Line 57: Status box header "H10 status"
- Line 59: "Older drafts are archived"
- Line 60: "route-2 verified kernel-functional interface"
- Line 80: "this H10 copy"
- Line 114: "This H10 copy"
- Line 266–269: Multiple "H10" references in abstract bullets (≈5 instances)
- Line 286: "H10 realizations and the amortized surrogate"
- Line 806: "H10 route"
- Line 861: "H10 canonical observer choice"
- Line 874: "H10 packages"
- Line 886: "H10 package in Corollary"
- Line 1297: "H10 noisy wrapper"
- Line 1299: "H10 verified semantic-learning package"
- Line 1306: "H10 package assumptions"
- Line 1311: "H10 verified package"
- Line 1372: "H10 route"
- Line 1515: "H10-verified" (appears in Assumptions definition)
- Line 1509: Assumptions title "[H10-verified semantic-learning package]"
- Line 1547: "H10-verified semantic-learning package"
- Line 1563: "H10-verified semantic-learning package"
- Line 1574: "H10 package"
- Line 1577: Remark title "[H10 boundary for the support route]"
- Line 1580: "H10 main"
- Line 1620: "H10-verified coupling"
- Line 1620: "this H10 statement"
- Line 1664: "H10 semantic convergence"
- Line 1677: "H10 main theorem"
- Line 1703: "H10 main theorem"
- Line 1722: "H10 main theorem"
- Line 1733: "H10 package"
- Line 1738: "H10 package"
- Line 1775: "H10 manuscript"
- Line 1866: "H10 main theorem"
- Line 1874: "H10 package"
- Line 1979: "H10 package"
- Line 2031: "H10 package conditions"
- Line 2313: "H10 package"
- Line 2318: "H10 main theorem"
- Line 2346–2367: Multiple "H10" references in Discussion/Conclusion sections (≈10 instances)
- Line 2367: "This H10 copy"

**Recommendation**: Replace all "H10-verified" with simply "verified". Delete all "this H10 copy" and "H10 copy" references. Remove "H10" from section/theorem titles and remark titles. Consider keeping "H10" in reference to the Lean path `h10_verified_semantic_learning_package_converges` since that is the formal Lean name, but otherwise remove the label.

---

## Summary of effort

This punchlist groups ~60 distinct problematic locations into 8 categories. With focused editing:

- **Title and status box (critical, 2 edits)**: 5 minutes
- **"this H10 copy" removals (critical, 5 global replacements)**: 10 minutes
- **"consolidated" and "H10-verified" standardization (substantive, ~25–30 instances)**: 15 minutes
- **"retained," "remains," "records," "identifies" replacement pass (substantive/cosmetic, ~15–20 instances)**: 20 minutes
- **Lean path and manifest references (substantive, 2 instances)**: 5 minutes
- **Section roadmap and forward-reference simplification (cosmetic, ~5–8 instances)**: 10 minutes

**Total estimated editing time**: ~60–75 minutes for a complete polish pass.

