# Section 5 reuse survey

Date: November 5, 2026. Source: arXiv:1006.2467v1, Section 5.
Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`;
ACVF-QE `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`. No dependency upgrades.

The author explicitly permits material from Sections 2–4 as given. Missing
earlier results may be exact theorem hypotheses; this permission does not
permit assuming Section 5's own conclusions or its uniform construction.

## Source comparison

| Candidate | Actual scope | Decision |
| --- | --- | --- |
| `Section5/Sec5.lean` | Legacy standalone quotient RV model, hull identities, injectivity and set-theoretic contraction; 5.2, 5.4, 5.5 are definitions of propositions | Reuse arguments, preserve the snapshot. Do not import its second RV implementation. Its canonical step is identity, its special-bijection data lack definability, and its frozen 5.4/5.5 use the wrong transformed domain. |
| `Section3/MixedRV.lean`, `BallGeometry.lean`, `DiscCentres.lean`, `BallTranslation.lean` | The actual released sorted RV carrier, RV fibres, valuation order reversal and translated balls | Direct imports and small tuple bridges. |
| `Section3/Barycentre.lean`, `FiniteBarycentricCode.lean`, `DefinableMeans.lean`, `RawBarycentricCode.lean` | Means, strict splitting of finite root clusters, recursive finite codes, and full uniform original-base definability | Preferred unary induction; extend the code control theorem to arbitrary field points. Do not replace centres by named roots. |
| `Section3/PolynomialRVConstant.lean` | Factorization proves polynomial RV constancy from constancy of all linear root factors, and on root-free balls | Direct reuse. |
| `Section3/FiniteGluing.lean`, `DefinableLocalChoice.lean`, `TupleCompactness.lean` | Original-base definable partial functions, finite gluing, actual small-parameter saturation | Reuse for uniform families. These do not already prove that local special bijections glue. |
| `Section4/DefinableGeometry.lean`, `Products.lean`, `CodeMaps.lean`, `Spaces.lean` | Full-graph definable maps on actual real and imaginary presentations, products and coordinate-code constructors | Direct reuse of these narrow interfaces, without importing Section 4 dimensions or Grothendieck constructions. |
| Pinned Mathlib model theory, valuations, finite tuples and polynomials | `Term.definableFun_realize`, `DefinableFun.ite`, finite quantification, `Fin.append`, polynomial roots and splitting | Reuse generic syntax, tuple and algebraic machinery. |

Local project sources retain their existing licenses and author credit.
Mathlib is Apache-2.0; ACVF-QE is MIT with its separately credited ports.
No external source was copied into Section 5 in this work.

## External discovery

Focused web queries used `Lean "special bijections" "RV"`,
`site:github.com Lean "RV-pullback"`,
`site:github.com/TauCetiProject/TauCeti "valuation" "definable"`, and
`Lean formalization algebraically closed valued fields special transformations`.
Further index queries targeted Reservoir, Palomar, Lean Pool and the Lean
community project registry for ACVF and valued fields. These searches did
not find an importable special-bijection or RV-pullback formalization.
Search-index coverage is incomplete; this is not a claim of nonexistence.

The broader current-upstream, Tau Ceti, Mathlib PR and registry comparison is
recorded in `Section4/REUSE-SURVEY.md`; its generic algebra and category ports
do not implement the Section 5 transformations. The specialized target search
returned the original paper and valued-field developments with different
scope. TheoremSearch and Formalpedia were not directly queried in this pass.
No external candidate is claimed as compiler-verified reuse.

Section 5 source and axiom checks are recorded separately in `STATUS.md`.
The implemented inverse-ball argument uses the elementary translation
description on fixed final RV labels. It reuses `VFValued`'s actual compatible
valuation; it does not import the legacy quotient RV model or assume an
inverse-ball conclusion as a primitive property of special bijections.

The unary construction directly reuses `Barycentre.mean_definable`,
`mean_mem_openDisc`, `fibre_card_lt`, `PolynomialRoots.term` and
`CanonicalStructure.term_normalize`. A proved identity ring equivalence
bridges original and normalized VF means. Mathlib's `RingEquiv` and
finite-average transport are used at the pinned revision; no external
implementation is copied. The iteration and boundary alternation argument
are new Section 5 proofs, rather than assumptions of an earlier input.

The higher-dimensional continuation reuses the Section 4 map graph,
image, composition, extension and corestriction interfaces. Its vertical
root-count and VF-dimension inductions are new Section 5 constructions.
`PolynomialExpression.lean` reuses the finite expression and evaluation
proof from `Section4.PolynomialZero` in an isolated import boundary, with
explicit source credit. This avoids importing its unrelated zero-set and
definable-closure development. The polynomial construction then reuses `RingSyntax`
and `CanonicalStructure.term_normalize`.
The lift construction directly uses Section 4's `RVObject`, `RVFiniteObject`,
`rvLift`, `VFObject`, `VFFiniteObject` and the full-subcategory isomorphism
constructor. It retains the actual mixed RV key as the object domain.
The real-sort reduction consequence of 4.2 and finite-fibre invariance
from 4.13 are explicit given interfaces in the category statements.
The named-Gamma construction uses the actual `GammaParameters.Base` and
full invariant preimages from `GammaParameters`. Ordinary invariant
image/restriction laws are explicit earlier interfaces, together with QE
finite-polynomial support and finite-code specialization. No chosen
representative is added to the named base. Focus restriction, polynomial
preparation and lift assembly are Section 5 constructions.
`GammaLift` retains the same Section 4 RV object and actual lift and uses
Mathlib equivalences for full-graph isomorphisms. It introduces no second
RV language or standalone quotient implementation.

## November 6 audit reuse

The audit compared the actual definitions with Section 5 of the same paper
version and the updated WORKFLOW.md. No substantial prerequisite was rebuilt.
The diagnostic zero-fibre counterexample directly reuses the current
`FocusGeometry`, `CanonicalRV.encodedRv_zero_iff`, `RVCalc.rv_zero_eq`, and
`RVCalc.le_refl_rv` in the pinned released language. It was compiler-checked
separately in scratch, with its headline types and permitted-axiom audits.
Earlier-section mathematics remained given. STATUS.md records the resulting
Definition 5.1 fidelity issue and the concrete normalization/clarification
options; the prior existence constructions were preserved.

## November 6 normalization bridge

The authorized follow-up uses a small bridge inside the existing model and
transformation API. Local candidates compared were `Focus.restrict` (changes
the source and intersects its hull, so unsuitable for preserving endpoints),
`FocusGeometry.eta_target_strict` (directly reusable on nonzero fibres),
`rv_eq_zero_iff`, `FocusGeometry.center_sameRV`, `isRVPullback_inter`, and the
real/Gamma graph restriction laws (directly reusable). The earlier external
special-bijection search above found no importable replacement; no substantial
prerequisite is rebuilt and no external source is copied for this bridge.

`ZeroNormalization` intersects the old locus with the parameter-free retained
tag condition `tag != rv(0)`. It proves definability and pullback saturation,
identity on deleted fibres, equality of actual images, the printed C-sharp
target, preservation of primitive kinds, arbitrary-boundary alternation,
chain maps and inverses, length, and original-base invariant Gamma graphs.
It uses the same pinned ACVF-QE and Mathlib revisions recorded above. The
compiler and axiom verification status is recorded separately in STATUS.md.

### Kernel replay for provenance renewal

The pinned Lean 4.33.1 distribution already supplies `leanchecker` and
`Lean.Replay` (Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`).
The installed `src/LeanChecker.lean` was inspected, alongside the official
[checker documentation](https://github.com/leanprover/lean4checker/blob/master/README.md).
Its default mode replays a module's declarations into its imported environment;
`--fresh` would also recheck earlier imports and is unnecessary here.

The local verification harness adapts that small driver to load the accepted
earlier boundary once and replay the 26 unchanged Section 5 modules in dependency
order. It starts without importing a Section 5 module, so Section 5 lemmas are
checked rather than taken as given. The imported earlier boundary remains given.
The original source-compiler exit-zero receipts, exact source and compiled-file
identities, a successful current kernel replay and the current provider manifest
are all required before issuing a new cache certificate. Replay source, log and
receipt are themselves hashed in the cache. New mathematical source and the
combined headline audit still require fresh source compilation.

The driver is credited to Kim Morrison and Sebastian Ullrich under Apache-2.0,
following the pinned source header. It is retained under `.scratch/` as verification
evidence, not imported into the mathematical library. No extra dependency, language
or proof assumption is introduced. STATUS.md records the completed check's scope.
