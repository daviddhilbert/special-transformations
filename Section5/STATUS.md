# Section 5 proof status

The author authorizes the needed Sections 2–4 as given. The statements below
keep unfinished earlier interfaces as explicit hypotheses. No Section 5
existence theorem, induction conclusion, or special-bijection construction
is assumed as an input. On November 6 the author authorized publishing this
Section 5 checkpoint so the dependency of Section 6 is available remotely.
Unrelated workspace edits remain outside the publication.

## November 6 normalization and verification

The completed verifier reports PASS. The authorized follow-up proves the
zero-fibre normalization, adds Section 5 to CI and replaces source-only cache
reuse with compiled-import provenance. No Section 5 mathematical obligation
remains under the accepted Sections 2–4 inputs and the proved normalization
bridge. The separate consumer integration check also passed with compiler
exit 0 and 39 permitted-axiom audits. The final checkpoint has 28 modules
and 282 headline audits, with Sections 2–4 treated as given. The final verifier
reuses 26 matching artifacts after re-certification and freshly compiles
`ZeroNormalization` and `Library`. A fresh ordered kernel replay checked all
1,186 declarations in those 26 unchanged modules, beginning with the accepted
earlier environment and without importing Section 5 as given. Original
source-compiler exit-zero receipts and exact source/artifact identities are
retained. This is kernel re-certification of existing proofs, not a claim that
all 28 modules were freshly elaborated from source.

`ZeroNormalization` constructs a nonzero active locus for every focus. It
proves the locus remains definable over the same parameters, remains an
RV-pullback, and has the same centre and the same transformation on the source.
Its actual image is unchanged. `eta_printedTarget` proves the paper's strict
C-sharp codomain for these representatives; `printedTarget_disjoint` proves
that its two pieces are disjoint. Points whose targeted VF coordinate is zero
are inactive.

Every primitive and alternating chain is normalized without changing source,
target, primitive kind, length, forward map or inverse map. Alternation is
preserved at every initial boundary. Original-Gamma locus and complete centre
graph certificates are preserved; `GammaSpecialBijection.withoutZero_spec`
also keeps the same internal code set and source/target presentations. Thus
all existing preparation, contraction, inverse-fibre and lift results keep
their actual functions and can use the normalized paper representatives.

The literal printed formula for the *old* zero-active locus still fails on
the singleton counterexample below. The bridge resolves this by choosing an
equivalent legitimate locus, without changing the paper's RV convention or
introducing an additional RV element. It does not assume a codomain exception.

The new cache schema records Lean-resolved provider paths for the complete
given import closure, plus SHA256 identities of the .olean, split private and
server parts, and interpreter artifacts where present. Reuse also binds the
compiled Section 5 dependency closure, source/dependency fingerprints, pinned
versions and compiler log. Old source-only cache entries are rejected by the verifier. The unchanged
checkpoint artifacts earned new certificates only after the separate kernel
replay, exact-identity checks and provider-manifest check. Source changes and
provider replacement during verification fail the run; a fresh final provider
probe checks resolution again. Earlier mathematical interfaces are imported
as given and are not rebuilt or certified.

Evidence: `.scratch/section5-verified/` contains `results.json`,
`import-providers.json`, `resolved-imports.json`, `given-inputs.json`,
`cache.json`, the two provider-probe logs and the full library audit.
`KernelReplay.lean`, `KernelReplay.log`, `KernelReplayReceipt.json`, the
original compiler receipts and `RenewProvenanceDriver.txt` document the
one-time provenance renewal; their identities are bound into the cache.
`NormalizationAudit.lean` additionally imports the finished library, checks
all 37 bridge headlines and constructs normalized Corollary 5.6 witnesses
for both real and Gamma bases in every mixed arity. Its compiler and axiom
results are recorded separately from the 282 library headlines in
`NormalizationAudit.result.json` and `NormalizationAudit.log`: compiler exit 0,
all 39 expected full types present, and every axiom list contained only
`propext`, `Classical.choice`, and `Quot.sound`. The two consumer proofs use
only the already accepted earlier interfaces and construct the normalized
witnesses; neither assumes the desired normalization or preparation result.
The completed source and evidence snapshot is `.scratch/section5-checkpoint282/`.
The next step is to use `Section5.Library` in subsequent sections; there is
no further Section 5 proof obligation under the accepted earlier inputs.

The CI workflow invokes the Section 5 verifier, reports its separate outcome,
retains its logs, manifests, source probes and status, and runs the provenance
regression checks. Those checks cover unchanged reuse, changed provider
location, changed artifact content, split/interpreter artifacts, old cache
schema rejection, changed fingerprints, changed output, changed logs and
tampered replay evidence. A regression runs the actual verifier cache-hit
path twice and checks that replay evidence remains in both memory and the
saved cache. Valid reused entries are retained unchanged.
The YAML structure and step/evidence wiring are checked locally. These local
checks do not claim a remote Actions result. The publication includes the
Section 5 sources, library registration and verifier/CI wiring; scratch
compiler artifacts remain local. The existing Section 4 cache regression
coverage is retained.

Publication checks matched all 28 Lean sources to the completed certificate
and all 77 recorded earlier source identities to the published checkout.
The updated coordination-root import passed a fresh pinned compiler check
using accepted earlier compiled interfaces, with source and imported
artifacts unchanged. The four shared cache tests passed for both Sections
4 and 5, and the 183-module repository dependency closure has no missing
source imports. These are source/import checks, not a new full-project rebuild.

## November 5 checked checkpoint

The completed November 5, 2026 check reports PASS for all 27 modules under
pinned Lean 4.33.1, including a fresh combined-library compilation. All 245
headline types and their explicit hypotheses were checked. Every headline
axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
All recorded source hashes matched at completion. Fifteen matching compiled
modules were reused and twelve modules were freshly compiled. The completed
source and certificate snapshot is `.scratch/section5-checkpoint245/`;
the earlier 87-, 111-, 122- and 155-headline checkpoints remain preserved.

The verifier records compiler exit codes and source hashes in
`.scratch/section5-verified/results.json`, compiled-artifact hashes in
`cache.json`, earlier source/import fingerprints in `given-inputs.json`,
and actual headline types, explicit input definitions and axiom lists in
`Section5.Library.log`. It always freshly compiles the library audit.
The accepted headline axioms are only `propext`, `Classical.choice`,
and `Quot.sound`. Earlier-section source fingerprints and imported compiled
interfaces are recorded separately; this is not a rebuild of Sections 2–4.

## Paper coverage

Numbering follows [Section 5 of arXiv:1006.2467v1](https://arxiv.org/html/1006.2467v1#S5).
The checked source modules implement the main constructions for real VF/RV
and named-Gamma bases under the explicit accepted earlier-section inputs.
The audit found no missing construction proof in 5.2–5.7 under the accepted
earlier inputs. The normalization bridge above identifies their actual maps
with representatives satisfying the printed Definition 5.1 codomain.

| Target | Implementation and actual conclusion |
| --- | --- |
| Preamble and 5.1 | `Geometry`, `Core`: shared released sorts, hulls, label-appending canonical maps, full-graph focus maps, injectivity, inverses, alternation and length; `ZeroNormalization` supplies equivalent nonzero-locus representatives and the printed disjoint C-sharp target |
| Preservation after 5.1 | `TransformGeometry`: special bijections preserve RV-pullbacks, including zero fibres; strict-radius target description has its necessary nonzero premise |
| Lemma 5.2 | `RootConstruction`, `UnarySets`: finite original-base root families, actual mean foci, strict root-count iteration and restriction; the named-Gamma instance also follows from `corollary_5_6_gamma` |
| Remark 5.3 | `TransformGeometry`: an entire nondegenerate unary output fibre has an open-polydisc inverse inside an original RV fibre; no inverse-ball conclusion is assumed |
| Contraction paragraph | `Core`: actual unique definable contraction on mixed key images; `GammaContraction`: actual function, commuting identity, full invariant graph and uniqueness over the original Gamma base |
| Theorem 5.4 | `PolynomialPreparation.theorem_5_4` and `GammaExistence.theorem_5_4_gamma`: every finite VF dimension, the specified original RV fibre, arbitrary initial special bijection, zero polynomials included |
| Theorem 5.5 | `PolynomialPreparation.theorem_5_5` and its Gamma version: arbitrary definable original domain, contraction and an RV-pullback target; finite simultaneous versions retain genuine concatenation alternation |
| Corollary 5.6 | `GeneralExistence.corollary_5_6`, `GammaExistence.corollary_5_6_gamma`: actual special-bijection existence for every finite mixed VF/RV arity, including empty and degenerate cases |
| Corollary 5.7 | `CategoryLift`: actual Mathlib isomorphisms to Section 4 lifts in both real-base category variants; `GammaLift`: original-Gamma-base bijections and inverses to the same actual lift objects, with invariant domain and volume graphs and finite volume in the finite variant |

## Construction and parameter scope

The unary construction centres finite root families using their means and
iterates the strict decrease in nonzero root count. The higher-dimensional
construction in `Assembly`, `Centering`, `GeneralAssembly` and
`GeneralExistence` prepares vertical loci, transports finite root bounds,
uses compatible coordinate lifts, descends head-key graphs, and discharges
the VF-dimension induction. The final general-map theorem has no remaining
dimensional induction hypothesis. It implies the exact polynomial wrappers
and the real-base deformation theorem.

`ParameterExtension`, `GammaGraphs`, `GammaLogic`, `GammaRestriction` and
`GammaExistence` use the actual `Section3.GammaParameters.Base` and its full
invariant graph preimages. QE supplies finite occurring VF polynomials.
Their preparation over the real base is restricted to the Gamma-definable
source using actual restricted focus geometries and full centre graphs.
Internal real presentations do not replace the original named base by
chosen RV representatives. Every primitive has an invariant certificate.
`GammaSpecialBijection` stores an actual alternating chain, not an assumed
existence predicate. `GammaIso` stores an actual equivalence with its full
original-base graph; its inverse graph is proved by swapping that graph.

`PullbackLift` constructs the actual Section 4 RV object from the full mixed
key, retaining all old RV labels. Its volume is the projection to the VF
RV coordinates. A canonical map gives the bijection to its actual lift.
`GammaLift` certifies the object's domain and volume over the original Gamma
base and composes actual bijections. Its `GammaIso` witness expresses the
isomorphism directly; it does not introduce a separate Lean Gamma category.

The higher-dimensional results visibly assume the earlier uniform vertical
obstacle interface. The Gamma results also expose ordinary invariant logic,
finite QE polynomial support and finite presentation specialization. The
category results expose the dimensional reduction after 4.2 and finite-fibre
invariance from 4.13. These are accepted earlier inputs, not independently
verified here. Their exact scope is listed in [INPUTS.md](INPUTS.md) and
printed in the library audit. No saturation package bundles Section 5 lemmas.

## Build boundary

Only `Section5.Library` is the new section library. The legacy `Sec5.lean`
and `LegacyScaffold/` remain unimported reference snapshots. Their historical
headers and theorem totals are not evidence for the current library.

The pinned portable invocation is `lake env python3 Section5/verify.py`,
with the accepted earlier compiled interfaces on the import path. Local
checking uses the existing pinned Linux environment; the given-import
inventory and compatibility records remain under `.scratch/`.

## Earlier November 6 audit and its resolution

The comparison used arXiv:1006.2467v1, Section 5, including its standing
parameter conventions. The published language, single absorbing RV element,
valuation-order reversal, full RV-class equality, characteristic (0,0),
finite tuple arities, original-base graphs and arbitrary initial chains were
reviewed. The real-category exports use actual Section 4 objects and lifts.
The Gamma exports give actual equivalences with full invariant graphs and
proved definable inverse graphs; this supplies the isomorphism content
without constructing a second Gamma category.

### F1: Definition 5.1 zero-fibre codomain — normalized

Take the definable singleton `A = C = {(0, rv(0))}` with constant focus zero.
It is an RV-pullback and satisfies the focus conditions. Subtraction fixes
its point. In the printed C-sharp formula the retained value is infinity,
so the strict-radius part is empty; `hull(A) \ C` is empty as well. Thus the
displayed ambient codomain does not contain the output.

The current code targets the actual image. Its `eta_target_strict` theorem
explicitly assumes a nonzero targeted coordinate, and the preservation proof
handles zero as a singleton. Those are sound statements but do not prove
the unrestricted printed codomain clause. This is a mathematical
specification issue, separate from the author-approved RV-inversion erratum.

The diagnostic source `.scratch/section5-audit-20261106/PaperAudit.lean`
constructs this focus geometry and proves `zeroCell_pullback`,
`zeroFocus_eta`, `zero_not_printedSharp`, and
`zeroFocus_not_printedCodomain`. Its displayed sets and constant focus are
definable by ground-language formulas. The diagnostic uses the existing
absorbing point and introduces no second RV element.

Resolution: `ZeroNormalization.lean` implements the original-base-preserving
normalization described above. `Focus.withoutZero_eta` and
`Focus.withoutZero_image` prove equality of the old and new actual maps and
images. `SpecialBijection.paper_representative` and
`paper_representative_gamma` supply normalized chains with the same maps,
inverse maps and lengths. The Gamma wrapper preserves the exact presentation.
The counterexample remains a diagnostic for the unnormalized printed clause;
it is not an outstanding Section 5 construction obligation after this bridge.

### W1: Section 5 CI coverage — implemented

`.github/workflows/lean.yml` now invokes `Section5/verify.py` after Section 4,
includes a Section 5 summary row and retains its evidence. With the project
built, the Section 5 step runs independently of earlier audit outcomes. It also runs the
cache regression checks. The workflow is locally validated; no remote run or
publication is claimed under the instruction not to push.

### W2: Given-artifact cache binding — implemented

The new schema binds cache reuse to the actual Lean-resolved earlier import
providers and their compiled contents, and to the compiled Section 5 imports.
The source-only cache format cannot be reused. Before/after provider probes,
content identities, stability guards and the regression checks supply the
new evidence. The old audit did not detect stale theorems; this fixes the
provenance gap and makes future acceptance depend on the actual imports.

### Fresh audit evidence

`PaperAudit.lean` compiled with exit 0 under pinned Lean 4.33.1. It freshly
imports `Section5.Library`, prints the 245 existing headline types and axioms
with readable arguments, and checks the four diagnostic theorems above.
All 249 printed axiom lists contain only the three permitted axioms.
The initial attempt failed in its metadata-export helper, not its theorem
proofs; that failed attempt is preserved in `attempt1/`.

Evidence is under `.scratch/section5-audit-20261106/`: `command.json`,
`compiler.json`, `PaperAudit.log`, `before.json`, `imports.json`,
`import-artifacts.json`, `axioms.json` and `result.json`. The final driver
status is PASS. This is a fresh consumer and counterexample check, with
matching prior source evidence, rather than a fresh rebuild of all 27 modules
or an independent check of Sections 2–4.

That earlier audit changed no implementation source or paper convention.
The subsequent authorized normalization and verification changes are recorded
above. Earlier-section proofs and dependency pins are unchanged by this work.
No commit or push was made.
