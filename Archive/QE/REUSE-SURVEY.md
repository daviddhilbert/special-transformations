# Existing formalizations relevant to ACVF quantifier elimination

Initial search date: November 4, 2026, America/Los_Angeles. Updated below with
the subsequent successful Palomar source retrieval and local integration.

The external result now used is a countably saturated elementary-extension
construction from Elliot Glazer's Palomar-listed `definable-saturated` project.
Other matches include valuation amalgamation in Tau Ceti, generic QE criteria
in an unmerged Mathlib development, RV algebra in Lean Pool, and a
residue-field algebraic-closedness theorem in NYLL. No external proof of ACVF
QE in our exact frozen RV language was found in the searches below. This is
a bounded search result, not a claim of nonexistence.

The original survey was read-only. The subsequent Palomar follow-up produced
an actual source adaptation, described below. **The complete parameter-free
RV integration PASSED by 2026-11-05 at 05:45 UTC** (November 4 at 21:45
America/Los_Angeles): all 86 modules and a fresh combined import exited 0.
The exact closed theorem was checked, with all headline audits listing only
`propext`, `Classical.choice`, and `Quot.sound`. The previous 78-module,
three-hypothesis run remains a historical result. Upstream catalog labels do
not constitute a local compiler or axiom audit.

## The actual local reuse boundary

The project pins Lean and Mathlib 4.33.1. The current entry point is
`QE/LocalQE/Theorem23.lean`; its latest type has no extra mathematical
hypotheses. Its complete 86-module verification and fresh import passed. The earlier
version took `MarkerBridge.MarkerProposition4328`,
`ResidueEmbeddingExtension.EPAlgebraicallyClosedResidue`, and
`ResidueEmbeddingExtension.MarkerACFSaturatedEmbeddingExtension`, and passed
the 78-module check on 2026-11-05 at 05:11 UTC. See `QE/LocalQE/STATUS.txt` for
the current records.

Ordinary ACVF QE already has a local Johnson proof. Accordingly, an external ordinary valued-field QE proof would be an alternative implementation, not an automatically missing ingredient.

Residue algebraic closedness already exists locally:
`ValOneEC.Johnson.isAlgClosed_residueField`, in
`QE/LocalJohnson/JohnsonGeometry.lean` and the assembly snapshot.
`ResidueTranscendentalTransport.Residue v` is definitionally
`IsLocalRing.ResidueField v.valuationSubring`; the production wrapper is now
`QE/LocalQE/ProvedResidueClosure.lean`. No NYLL dependency is needed.
Pure ACF QE also already existed in `QE/ACF_HasQE.lean`; the new
`JohnsonACFGeometry`, `JohnsonACFPrime`, and `JohnsonACFMain` modules extract
its distinct ingredients while reusing the local generic Johnson criterion.
`ProvedACFExtension` combines that result with the checked generic
QE-to-saturated-extension proof. These individual local proofs supply the
algebraic inputs of the verified parameter-free endpoint.

Preserve the frozen tagged `L_RV` encoding. Our `RV` is the nonzero multiplicative quotient with one absorbing element, `rv(0)`. Preserve the distinction between `pK` and `pInK`. Mathlib's valuation order is reversed relative to the paper's `vv` order; every proposed bridge must explicitly account for it. Independent copies of a language in standalone snapshots require translation, even when their definitions look identical.

## Candidate comparison

### Palomar: countably saturated elementary extensions — adapted locally

- [Entry `PALOMAR-2026-09-19-000005`, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-09-19-000005&version=1)
  led to Elliot Glazer's
  [`definable-saturated`](https://github.com/elliotglazer/definable-saturated)
  repository, revision `e683bba9e758323b43dd1d6206ed2f6fc9510f06`.
- Sources reused: `Scotts/ModelTheory/CountableSaturation.lean`,
  `CountableParameterSaturation.lean`, and `SaturatedExistence.lean`.
  They define actual first-order partial types with named parameters and
  prove countable saturation of a nonprincipal ultrapower on the naturals
  by diagonalization and Łoś's theorem.
- Local adaptation: `QE/LocalQE/CountableSaturatedExtension.lean`, ported
  from Lean 4.34.0-rc1 to 4.33.1, with an explicit bridge to the existing
  `MarkerBridge.SatAt`. Countability of the language and the parameter set
  makes every partial type countable; neither formulas nor parameter maps
  are weakened or restricted to a quantifier-free fragment.
- **No CH is used.** The retained existence proof imposes no cardinality
  bound on the elementary extension. The upstream CH hypothesis is used
  only in omitted results identifying its cardinality with aleph one;
  its forcing and arithmetic applications are also omitted.
- `CountableQECriterion` combines this construction with Mathlib's downward
  Löwenheim–Skolem theorem and the repository's existing compactness argument.
  It supplies the final QE criterion for the countable RV language, rather
  than assuming the previous unrestricted-language Marker proposition.
- Apache-2.0. The original license, NOTICE, and pinned provenance are retained
  in `QE/LocalQE/vendor/definable-saturated/`. The upstream README records
  Glazer's mathematical direction and agent-assisted implementation.
  The port and full local integration passed the 86-module compiler and
  axiom check; the Palomar listing alone was not treated as verification.

### NYLL residue algebraic closedness

- Repository revision inspected: `n-yamaguchi-0729/NYLL`, `2e9f92dc5fbeacd17189dcf0cdb499f528dfd77c`.
- [Source](https://github.com/n-yamaguchi-0729/NYLL/blob/2e9f92dc5fbeacd17189dcf0cdb499f528dfd77c/Nyll/ValuedFieldTheory/Valuation/ResidueAlgebraicClosedness.lean): `ValuationSubring.isAlgClosed_residueField`.
- Actual statement: for any algebraically closed field `Ω` and valuation subring `A`, `IsAlgClosed (IsLocalRing.ResidueField A)`; no rank, characteristic, or nontrivial-valuation restriction.
- The small proof imports only Mathlib. It lifts a monic residue polynomial, finds an ambient root, uses integral closedness to put the root in the valuation ring, and reduces it. No visible `sorry` in this source file. Header license: Apache-2.0; author Naganori Yamaguchi, assisted by OpenAI Codex. Its toolchain and complete transitive axiom audit were not checked here.
- **Fit:** exact mathematical match for `EPAlgebraicallyClosedResidue` at `A := v.valuationSubring`. However, our local Johnson result already supplies it. Keep NYLL as independent proof reference; no external dependency is needed for this input.

### Generic QE criteria outside merged Mathlib

- [Original PR 40561](https://github.com/leanprover-community/mathlib4/pull/40561), head `095ae36e89f0eb4a0a5444a9144ef6e508d797d2`, contains definitions and embedding/extension-pair criteria. Live GitHub API reports it **closed, unmerged**; a cached web page still described it as open.
- The split stack [41111](https://github.com/leanprover-community/mathlib4/pull/41111), [41112](https://github.com/leanprover-community/mathlib4/pull/41112), [41113](https://github.com/leanprover-community/mathlib4/pull/41113), [41114](https://github.com/leanprover-community/mathlib4/pull/41114), [41115](https://github.com/leanprover-community/mathlib4/pull/41115), and [41116](https://github.com/leanprover-community/mathlib4/pull/41116) is open and unmerged in the API snapshot.
- Source inspected at PR 41115 head `d77f9b9a45970de8cd6294ae767e967a855eeaaf`: `Mathlib/ModelTheory/QuantifierElimination.lean`.
- Relevant declarations in `FirstOrder.Language.Theory`: `HasQuantifierElimination`, `isQFEquivalent_iff_realize_iff_of_embeddings`, `hasQuantifierElimination_of_exists_realize_of_embeddings`, and `hasQuantifierElimination_of_isElementaryExtensionPair` (plus finitely/cardinally generated variants).
- **Fit:** useful alternative generic machinery. These statements use witness transfer or elementary extension pairs; they are not literally our `MarkerProposition4328`, which is phrased using `SatAt`. Reuse needs a proved interface bridge, supporting extension-pair files, a pinned-version port, and conversion from ordinary QE to our sorted target. It does not by itself discharge ordinary ACF saturated embedding extension. Header license: Apache-2.0; authors Yağız Kaan Aydoğdu, Yusuf Demir, Salih Erdem Koçak. Not locally compiled.

### Tau Ceti valuation amalgamation

- Revision: `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`; toolchain `leanprover/lean4:v4.36.0-rc2`.
- [Source](https://github.com/TauCetiProject/TauCeti/blob/e8758b7b2f82b9b1c3f33b992ab8f499b510240f/TauCeti/RingTheory/Valuation/Amalgamation.lean): `ValuationSubring.exists_comap_eq_of_comap_eq`.
- Given valuation subrings of two field extensions with identical restriction to the common field, produces a prime of their field tensor product and a valuation subring of its residue field restricting to both original subrings.
- Supporting files include `ValuationSubring.lean`, `AlgebraicExtension.lean`, and `RootMonic.lean`. The latter contains `Valuation.le_one_of_root_monic`. Header licenses: Apache-2.0; retain each file's provenance when adapting.
- **Fit:** substantial overlap with the algebraic amalgamation in our Johnson proof. This is a candidate to shorten or replace that component after a bridge from valuation-subring equality to our valuation predicate. It does not prove first-order QE or RV embedding extension. Because our ordinary QE is already implemented, replacing it now is optional refactoring. The newer toolchain prevents treating this as an immediately checked dependency.

### Lean Pool RV and residue algebra

- Revision: `de237ae89555e2abebcd8e7ca91058acaee4fe45`; toolchain `leanprover/lean4:v4.35.0`.
- [RV source](https://github.com/LeanPool/lean-pool/blob/de237ae89555e2abebcd8e7ca91058acaee4fe45/LeanPool/ConwayRefinement/ConwayRefinement/Algebra/Valuation/RV.lean), namespace `MaxAddDegree`: `RVRel`, `RV`, `rv`, `rv_eq_iff`, `rvEquivHomogeneous`.
- Companion sources: `OfValuation.lean` (`ofValuation`) and `ResidueMathlib.lean` (`nonpositiveSubring_ofValuation_eq_integer`, `nonpositiveEquivInteger`).
- **Fit:** alternative RV/associated-graded algebra and comparison patterns. This is a max-additive-degree framework for general commutative rings, allowing a nonzero support ideal; its zero RV class collapses the entire kernel. It is not definitionally our field quotient `Option (Kˣ / (1 + m))`, and its source does not supply our first-order QE theorem. Reuse requires specialization, an order/convention comparison, and an actual quotient equivalence.
- The project card credits Dan Abramov and upstream `gaearon/conway-refinement`, commit `264445c93b78554c408e99e4e7f663693b4e91ab`, Apache-2.0. Candidate for later algebraic simplification, not an immediate missing QE dependency.

### Many-sorted valued-field model theory

- Discovered directly in Reservoir's package metadata: [Mathias-Stout/many-sorted-model-theory](https://github.com/Mathias-Stout/many-sorted-model-theory).
- Revision `4d15933b1441d955dc0d6bffb4dd0b341eec5149`; toolchain `leanprover/lean4:v4.33.0-rc1`; Apache-2.0.
- `MultisortedLogic/Examples/ValuedFields.lean` develops `VFL`, `CompatibleVFL`, valued-ring/field axioms, `ValuedFieldTheory`, and a three-sorted language `L₃`. Its sort schema also names leading-term sorts.
- **Fit:** relevant language/semantics infrastructure and future design reference. The inspected valued-field file has six `sorry` occurrences, including in the three-sorted model construction. No ACVF QE proof was identified. It uses native many-sorted syntax, so replacing our tagged encoding would require an independently justified translation and author approval; it is not a shortcut permitted by the frozen specification.

## Catalog coverage and search limitations

- **Reservoir:** inspected public search implementation and downloaded the current client metadata bundle. Extracted 894 package name/description records; searching these for `ACVF`, `quantifier`, `valued field`, and `many-sorted` found the many-sorted project above. This is metadata search, not full-text theorem search. The rendered `/packages?q=...` pages returned an unfiltered initial list, so their apparent counts were not used as negative evidence.
- **Lean Pool and Tau Ceti:** downloaded complete, nontruncated GitHub path trees at the revisions above. Inspected selected valuation and model-theory sources. Successfully retrieved 237 of 326 Lean Pool project cards; the remaining 89 downloads failed. Therefore the project-card search was incomplete. No ACVF/QE headline was identified in the inspected cards and paths.
- **Mathlib:** inspected its complete path tree at `805bbc496804387c2c87f9773b149ddd3a5286d2`, selected source files, the installed pinned source, and the QE PR stack. The external QE criteria remain outside the inspected master tree.
- **Formalpedia:** direct `q=ACVF` search returned zero results. `q=quantifier elimination` returned 69 results; the visible initial results concerned real QE rather than ACVF. Broader valued-field terms produced noisy matches. Not every result page was audited, and definitions/open entries were not treated as completed proofs.
- **TheoremSearch:** API searches for ACVF QE and residue algebraic closedness returned relevant informal literature; an expanded 20-result ACVF query returned arXiv results, not a reusable Lean declaration. This does not rule out formal results elsewhere in its index. A supplied `source` parameter did not produce a formal-only result set and was not treated as a verified filter.
- **Project intentions:** GitHub issue searches found zero `ACVF` and zero `quantifier` hits. `valued` found the masures/Kac–Moody project, issue 34, not an ACVF QE claim.
- **Palomar:** the initial public-root access failed in both web and direct retrieval, and indexed site searches produced no relevant hit. **That access limitation is superseded by the successful follow-up:** entry `PALOMAR-2026-09-19-000005`, version 1, and its full proof sources were retrieved and audited, producing the adaptation above. The catalog was not exhaustively searched. **Papers With Lean:** indexed topic searches yielded no usable candidate; its visible home page is a paper feed, not evidence of exhaustive theorem coverage.
- **NYLL:** followed a valued-field residue-field lead from its public documentation to the pinned source above. This broader GitHub follow-up found a useful theorem that catalog keyword searches had missed.

Initial downloaded indexes, selected sources, API responses, and failed-download
lists are in `.scratch/catalog-audit/`, excluded from version control. The
later Palomar source audit is in `.scratch/palomar-proof-audit/`; the adapted
proof and its licensing records are included in the local source tree as
described above. The other candidates remain comparison sources.

## Recommended next use of these findings

1. Preserve the completed 86-module check, fresh combined import, and transitive axiom audit as the baseline for the parameter-free endpoint, including the local ACF/residue wrappers and Palomar-derived saturation construction. Rerun the dedicated verifier when its dependencies change.
2. Keep the split Mathlib QE stack as an alternative reference. The current route uses the local compactness proof and the explicit countable-language saturation bridge.
3. Keep the local Johnson ordinary-QE proof as the working baseline. Consider Tau Ceti's amalgamation only if it reduces maintenance enough to justify the port.
4. Retain Lean Pool RV and the many-sorted development as comparison references. Neither warrants changing the frozen encoding.

The reusable policy for future repositories is `FORMALIZATION-REUSE-GUIDELINES.md` at the project root.
