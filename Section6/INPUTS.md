# Accepted earlier and standard inputs

## Current paper exports

[PaperResults.lean](PaperResults.lean) supplies the assumptions of the
earlier conditional helpers through checked proofs. Earlier preparation
comes from Section 3's RV normal form and Section 5's uniform obstacles.
The expanded literal normal form follows from the constructed native
envelopes. The common envelope uses elementary amalgamation and the
released countable saturation result. Native field and valuation
extraction, the simple-root scheme, and the concrete RV quotient give
`nativeEnvelopes` and `ordinaryRecognition`. In the algebraic closure,
the characteristic-zero valuation invariance follows from the checked
coprime factor-lifting argument.

The generic saturated-extension quotation, native envelopes, ordinary
recognition, and the other preparation interfaces remain visible in
the appropriate lower-level or historical statements. The paper
headlines 6.4 and 6.5 take none of these as inputs. The standalone Lemma
6.3 uses the same checked providers. The standalone Lemma 6.2 constructs
the valued algebraic closure in the given ambient model and invokes the
proved valuation invariance. The lower-level envelope form retains its
explicit valuation-invariance input.
See [STATEMENT-REVIEW.md](STATEMENT-REVIEW.md) and [STATUS.md](STATUS.md).

## Earlier input record

This records the published inputs. The local proof
`EnvelopeUniformity.earlierPreparation` discharges the ambient pure-RV
definition and uniform-obstacle inputs. See [STATUS.md](STATUS.md) for
the local verification and remaining hypotheses.

The author expressly permits the needed materials in Sections 2–5 as
given. This does not authorize assuming Lemmas 6.2 or 6.3, Proposition 6.4,
or Corollary 6.5. The old `HenselAclStep` and
`hensel_qe_lemma_statement` are not used.

`FunctionallyClosedOver S X` retains the paper's original named base S,
separate from the substructure carrier X. The fixed-field argument proves
the stronger parameter-closed `FunctionallyClosed X`; the proved
`FunctionallyClosed.over` bridge gives the literal original-base statement
for every S contained in X. All finite input and output arities are retained.

* Released LRV, its ACVF model and canonical normalization, VF and RV
  carriers, and `ValuedModelMap.toCanonicalEmbedding` come from the pinned
  ACVF-QE release. VF inversion is unnamed; RV inversion follows the
  author's documented language correction. There is one absorbing point.
* For the syntactic continuation, the author again takes earlier sections
  as given. The pure-RV consequence of earlier ACVF QE and the RV-literal
  normal form is exposed as `RVGraphLanguage.RVQFDefinitions`: a pure RV
  definable set in the **ACVF ambient model** has a QF definition in the
  genuine RV reduct with RV parameters from the original substructure S.
  This earlier input makes no assertion about henselian models, RV
  expansions or relative elimination. Section 6 proves its transfer to
  substructures by an actual QF embedding. It is an accepted earlier input,
  not a new Section 6 proof of the Section 3 normal form. The author's
  latest clarification leaves "occurring
  polynomials" unchanged, since `rv(f/g) = rv(f)/rv(g)`.
* Corollary 3.14 supplies an elementary algebraic envelope over the
  substructure, with the VF field its algebraic closure. The interface in
  `lemma_6_2` displays the normalized elementary embedding, its exact base
  image and the `IsGalois` instance. Pure characteristic zero ensures the
  required separability. The envelope is not silently identified with the
  whole monster field.
* Lemma 3.13 supplies `DefinableRVLifting`: each singleton RV element
  definable over the VF-generated base has a VF representative definable
  over the same base. This is an explicit accepted earlier input. Surjective
  rv on the substructure, including zero, is retained separately.
* Engler–Prestel, [Valued Fields](https://link.springer.com/book/10.1007/3-540-30035-X),
  Theorem 4.1.3 (the uniqueness characterization of henselian valuations),
  supplies `HenselianAutomorphismInvariance`: every base-field automorphism
  of the algebraic closure preserves the valuation preorder. Henselianity
  itself is the actual Mathlib `HenselianLocalRing` property of the
  restricted valuation ring. The permitted standard input says nothing
  about definable closure, functional closure or QE. The Galois fixed-field
  step is proved by Mathlib's `InfiniteGalois.mem_range_algebraMap_iff_fixed`.
  The quotation is used under the exported theorem's displayed `IsGalois`
  hypothesis for the algebraic envelope, not for a transcendental extension.
* Sections 4–5 supply the actual complete-graph definable maps, special
  bijections and definable inverses, RV hulls, key images, contractions,
  and `map_preparation`. The latter's uniform root-free obstacle input
  remains an explicit earlier hypothesis, with the scope already documented
  in Section5/INPUTS.md. It is not rebuilt in Section 6.

`PreparedDescent` proves the restriction of the maps and the realization
of RV keys over the substructure. These are Section 6 constructions, not
fields of an assumed saturation structure. Its arbitrary final RV predicate
is evaluated on the substructure's RV points, so extra RV quantifiers are
never transferred to the algebraically closed overfield.

The syntactic henselian theory, arbitrary RV language expansion and
Denef–Pas translation are constructed in the continuation. STATUS.md
separates assembled-source, development and integration evidence. The
conditional reduction in `RelativeSyntax` alone is not their proof.

The new HenselianTheory specification separates the ordinary henselian
scheme (hen00) from its canonical tagged presentation (canonicalHen00).
The latter fixes native evaluations at wrongly sorted tuples to the
existing result-sort zero, and makes relations false off their declared
sorts, matching the shared CanonicalStructure.normalize convention. Added
RV symbols have the same canonical sort discipline. No symbol is added
to published LRV and no new RV absorbing element is introduced. The named
theory uses this canonical presentation. Its identification with ordinary
henselian valued fields and the standard small-model/envelope test cover
are separate standard inputs; defining this theory does not certify
those facts or any elimination statement. A raw one-sorted theory with
unconstrained native junk would not justify an elementary test cover by
substructures of a fixed canonical ambient model.

`NativeAmalgamation.SaturatedElementaryExtensionAt` states the authorized
generic saturated-model existence input from Marker, Chapter 4: for every
first-order language, nonempty structure and cardinal, there is an actual
elementary embedding into a model satisfying the released genuine `SatAt`
predicate at that cardinal. It does not assert an embedding extension, a
valued-field amalgamation, functional closure or relative QE. The common
native ACVF envelope is constructed with the already checked released
`LocalAssembly.fullQE`, `QESaturatedExtension.extension_of_fullQE` and
`HQEDerive.termSubEmb`. Those QE proofs are reused as given.

The model-uniform continuation displays its inputs separately.
`EnvelopeUniformity.EarlierPreparation` supplies only the earlier
`RVQFDefinitions` and `UniformVerticalObstacles` interfaces and an actual
compatible valuation on finite generated bases in a genuinely saturated
ACVF(0,0) model. It contains no henselian elimination conclusion.
`UniformNormalizedElimination.NativeEnvelopes` records ordinary native
algebraic representation for a model of the encoded henselian theory.
Its constructor supplies an actual native embedding into canonical
ACVF(0,0) and the independent algebraic/henselian/earlier witnesses in
`HenselianInputs.of_envelope`. No expanded isomorphism, definable closure,
fragment type invariance or QE is assumed. The image isomorphism, Lemma 6.2,
common envelope and comparison are proved separately. Recognition of the
encoded Hensel scheme as this ordinary representation remains an explicit
standard-reference/encoding boundary.

The generated-base interface uses the native term closure of the original
tuple. Its application with a named base S must retain S's constants in
the free context or prove the corresponding constant-language adapter.
Check the standing nontrivial valuation of S when discharging the earlier
preparation input; that input's definition does not prove nontriviality
for a trivially valued generated base.

The native henselian theory retains axNontrivialRV from the pinned repair
axioms. The Denef-Pas corollary handles its trivial-valuation branch
separately using the proved angular-component field equivalence and an
actual uniform formula translation. No DP QE statement or model-specific
translation dictionary is an input. The actual three-sort signature and
strict RF/Gamma binder class are in DenefPasLanguage.

The nontrivial DP wrapper now names the standard ordinary-field representation boundary as DenefPasHenselianModels.OrdinaryRecognition. Its exact content is: an actual valued field with ac data, CharZero on VF and its actual residue field, a HenselianLocalRing valuation ring, and nontrivial valuation satisfies canonicalHen00 in the displayed native tagged structure. This is retained as an explicit standard representation input under the author's authorization, not presented as a checked proof or a Section6/QE conclusion. The arbitrary relational Morley expansion is proved from the base model.

For genuinely sorted auxiliary expansions, `AuxiliarySorts` specifies each
symbol's RF/Gamma argument and result sorts. `AuxiliaryStructure` supplies
ordinary functions between those carriers and relations on their products.
The canonical tagged interpretation and all primitive DP symbol typing and
off-sort laws are proved in `DenefPasCanonical` and
`DenefPasAuxiliaryStructure`. These are language presentation data, not
additional elimination hypotheses. `DenefPasTheorem.corollary_6_5` chooses
one properly sorted output before all actual models, auxiliary structures
and original free assignments. It assumes neither `Canonical` nor an
interpretation dictionary.
