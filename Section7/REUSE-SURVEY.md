# Section 7 reuse survey

November 6, 2026; Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, ACVF-QE
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`. No pin changes.

## Local source comparison

| Source | Finding and decision |
| --- | --- |
| `Sec7Gamma.lean` | Useful elementary power/product estimates, adapted with attribution into `GammaPolynomial`. Its `IsResidueRoot` existential quantifies over a value fibre, without fixing an RV class; do not reuse that predicate. Its collected-coefficient definition discards the paper's extra summand index. |
| `Sec7GammaHensel.lean` | Diagonal substitution, chain rule and determinant arguments were adapted with attribution into `JacobianNormalization` and checked freshly. Its duplicate RV, collected-coefficient predicate, `NormalizedHensel` and full value-carrier surjectivity remain excluded. |
| `Sec7Lift.lean` | Old finite `SP` parameters and a `Sec7Prereq.localLift` hypothesis containing the core Section 7 task. Set-theoretic assembly is a candidate; the theorem assuming 7.6 is not a proof of 7.6. |
| `Sec7Cor77.lean` | Assumes lifting and surjectivity, uses underlying rather than definable isomorphisms, and a free commutative monoid instead of the paper's scissors semigroup. Reuse only independently checked elementary fibre arguments, if needed. |
| `LegacyScaffold/Hensel.lean` | TODO-only scaffold; no proof input. |
| Released `ResidueTransportCore`, `RVClassEquality`, `RVValueMap` | Direct import of actual RV, rv, vrv, quotient surjectivity and RV equality iff strict closeness. Avoid a competing quotient or language. |
| Released `CanonicalRV` | Direct import of the proved equivalence with encoded RV and its compatibility with `encodedRv`; used by `EncodedResidueRoots`. |
| Released `RVHenselLifting.exists_root_of_eval_lt_one` | Checked-source candidate for monic univariate lifting over algebraically closed fields; not a multivariate simple-system theorem. It does not close 7.2. |
| Section 3 `ModelContext`, Gamma parameter, compactness and gluing modules | Actual small-parameter saturation and homogeneity interfaces. Use later for 7.4/7.6; do not introduce a saturation structure with lifting conclusions as fields. |
| Section 4 residue interpretation, categories and canonical lift; Section 5 preparation | Candidates for 7.5/7.7 integration. Their actual source and verification boundaries must be checked before use; they are not silently assumed as entire sections. |

The estimate adaptation is from this repository's existing Yimu Yin source
under MIT. ACVF-QE is MIT, with its existing separately credited adaptations;
Mathlib is Apache-2.0. The Tau Ceti existence port described below retains
its own Apache-2.0 copyright, authorship and license.

## Mathematical definition review

The paper writes coefficients as `a_{ij}`, allowing multiple summands of the
same degree. Sums, derivatives and determinants can exhibit coefficient
cancellation. A property requiring every *collected* nonzero coefficient to
have value exactly alpha is therefore unsuitable for the intended closure
arguments. `PolynomialPresentation` retains a finite family of exponents and
coefficients, with the associated genuine `MvPolynomial`. This is a direct
representation of the printed sum, not an author-approved alteration of the
paper. No claim of uniqueness of residue value after cancellation is made.

## External discovery

The paper's [Section 7](https://arxiv.org/html/1006.2467v1#S7), including its
7.2 proof and 7.4/7.6 statements, was inspected directly. Current upstream
[Mathlib Henselian](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/RingTheory/Henselian.lean)
and pinned `Mathlib/RingTheory/Henselian.lean` provide ordinary univariate
lifting predicates. Neither inspected file supplies the required RV-relative
multivariate theorem. No newer Mathlib code was adopted or compiled.

Queries included `Lean Gamma polynomial residue root hensel Yin`,
`mathlib multivariate hensel`, `mathlib pull henselian multivariate`, and
targeted Reservoir, Lean Pool, Palomar, Tau Ceti and community-project
searches. Existing `.scratch/catalog-audit/` catalog trees, Reservoir package
summaries and TheoremSearch/Formalpedia residue/valued-field searches were
also consulted. Those are earlier discovery snapshots, not fresh verification.
Several Tau Ceti Henselian-source fetches in that snapshot failed, as recorded
in its `download-errors.json`; coverage is incomplete.

A live primary-source hit was
[NYLL's monic-factorization documentation](https://n-yamaguchi-0729.github.io/NYLL/modules/Nyll.ValuedFieldTheory.Valuation.Henselian.MonicFactorization/).
The local catalog identifies NYLL revision
`2e9f92dc5fbeacd17189dcf0cdb499f528dfd77c`; the live documentation is not
bound to that revision. This is a univariate valuation/factorization candidate,
not an inspected multivariate proof, and is not a dependency.

No importable proof of the required multivariate RV lifting theorem was found
in these searches. The least costly sound start is the attributed elementary
estimate port plus direct use of the released quotient/encoded-sort bridge.
Before tackling multivariate Hensel, repeat a focused source-level search for
simple systems over henselian local rings; absence of a search hit is not
evidence that no such formalization exists.

## Focused multivariate-Hensel reuse, November 6 continuation

The local catalog contains a substantially better candidate than the
univariate hits above: Tau Ceti's
`TauCeti/RingTheory/Henselian/Etale.lean` at
`e8758b7b2f82b9b1c3f33b992ab8f499b510240f`. The local file's Git blob was
recomputed and matches the catalog exactly:
`79fbca52ee56d6c9984bb8d04e0c46f85da7fb10`. A live fetch of that exact raw
URL failed with a cache miss; the source inspection is of this identified
local snapshot, not a claim about current upstream.

`TauCeti.HenselianLocalRing.comp_bijective` lifts residue-field points of
etale algebras over a genuine `HenselianLocalRing`. Its standard-etale
existence proof and the general surjectivity half use APIs already found
in pinned Mathlib `RingTheory/Henselian.lean`, `Etale/StandardEtale.lean`
and `Unramified/LocalStructure.lean`, including
`Algebra.IsEtaleAt.exists_isStandardEtale`. Its uniqueness half uses a
separate Tau Ceti unramified-diagonal theorem that has not been adopted.

`Imported/EtaleLifting.lean` is a small attributed port of the two existence
proofs. Other Tau Ceti imports, tensor-product variants, split-algebra
results and uniqueness are excluded. The original copyright and authors
are preserved and `Imported/TauCeti-LICENSE` retains Apache-2.0. This port
has passed fresh pinned source compilation and its headline axiom audit;
the combined verification and integration evidence is recorded in STATUS.md.

Proposed bridge: present a polynomial system with invertible Jacobian as
an etale algebra after localizing its Jacobian determinant; lift the
residue point with this generic theorem. Then prove uniqueness and the
valuation/RV normalization bridges. This could remove the unproved
`NormalizedHensel` input without citing Bourbaki as an authorized hypothesis.
The RV/Jacobian normalization part is now proved below. The ordinary
polynomial-system-to-etale bridge and uniqueness remain open; the port
alone does not prove Lemma 7.2.

`ValuationHenselian.lean` supplies a second, small bridge: the released
`RVHenselLifting.exists_root_of_eval_lt_one` is used to construct the actual
Mathlib `HenselianLocalRing` of an algebraically closed field's valuation
ring. Integrality of the lifted root and the original valuation-ring
polynomial equation are proved explicitly. Fresh pinned compilation and its
headline axiom audit passed; its `IsAlgClosed` hypothesis is visible. It does not assume
ordinary or multivariate henselian lifting as an additional reference input.

Pinned Mathlib also supplies the proposed system bridge's structural pieces:
`Algebra.PreSubmersivePresentation.naive`, `localizationAway`, `comp`,
`comp_jacobian_eq_jacobian_smul_jacobian` in
`RingTheory/Extension/Presentation/Submersive.lean`, and the instance
`IsStandardSmoothOfRelativeDimension 0 R S -> Algebra.Etale R S` in
`RingTheory/Smooth/StandardSmoothCotangent.lean`. The naive square-system
presentation can be composed with localization at its Jacobian to make
that Jacobian a unit; equal variable/relation counts give dimension zero.
These APIs were source-inspected. The required construction, residue-point
map, polynomial evaluation bridge and uniqueness proof have not been
implemented or verified by this inspection.

The pinned Tau Ceti unramified-diagonal source was subsequently fetched
successfully by direct read-only download and its Git blob checked against
the catalog: `19673df2b1f9907b76e83839e40345295bb3e214`, SHA-256
`72a7bed473dcdbad52f2214097366bb933393b1004a7aeeef35be124402b9734`.
The source and receipt are `.scratch/section7-reuse/UnramifiedDiagonal.*`.
`TauCeti.Algebra.FormallyUnramified.ext_of_quotient_eq` gives the desired
uniqueness over a Jacobson-radical ideal without completeness or nilpotence.
Its proof uses the idempotent generator of the kernel of multiplication on
the self tensor product and a further `TensorProduct/Maps` helper. These
are source-inspected candidates, not new imports or verified dependencies.
PLAN.md records the exact bridge and the reason not to assume adic
separatedness of a nondiscrete valuation ring.

## RV/Jacobian bridge continuation

The next target is Definition 7.1's genuine simple-common-residue-root
predicate and the normalization calculation in Lemma 7.2. The paper text
and the local MIT `Sec7GammaHensel.lean` diagonal chain rule and determinant
identity were re-read. These algebraic calculations are suitable for an
attributed port; its duplicate RV, collected-coefficient predicate,
surjectivity and `NormalizedHensel` assumption remain excluded.

Pinned Mathlib `Algebra/MvPolynomial/PDeriv.lean` supplies
`pderiv_monomial` and `X_mul_pderiv_monomial`; determinant expansion,
evaluation and diagonal/product identities come from its matrix library.
No applicable general diagonal-substitution chain rule was found in the
inspected PDeriv file; the local structural-induction proof is small and
fits the current pins without upgrades. The prior external Section 7 and
Henselian surveys remain relevant; this continuation builds the RV-specific
bridge, not another ordinary Henselian implementation.

`GammaPolynomialAlgebra.lean` is new project code. It converts finite
families to the existing presentations and proves sum/product/derivative
closure. A derivative multiplicity is represented as repeated summands,
so no extra hypothesis that integer valuations equal one is introduced.
In particular coefficient cancellation is preserved. All four continuation
modules passed fresh pinned compilation in the expanded eleven-module
library. All 64 headline types, explicit hypotheses and defining predicates
were reviewed; their axioms are contained in the permitted three. The
resolved external inputs remained unchanged and the combined ACVF-QE import
passed. STATUS.md records source/certificate identities and the separate
project-root check. The genuine simple-root predicate, scalar construction,
Jacobian normalization and integral-system/unit-Jacobian bridge are proved;
ordinary multivariate root existence and uniqueness are still open.

## Ordinary multivariate Hensel continuation

The focused search was extended to the exact Tau Ceti snapshot's
`Henselian/Lifting.lean` and `Henselian/Section.lean`. The first transports
univariate simple roots along injective maps; the second proves general
etale-section lifting over henselian pairs with a much larger dependency
graph. Neither is adopted for the square-system construction.

A direct download of `RingTheory/Smooth/Jacobian.lean` was checked against
catalog Git blob `d93a555d3d7e595becbd8c8a5203197179270aca` at the same
revision. Its finite-presentation Jacobian-localization theorem exactly fits
the remaining construction. `Imported/JacobianEtale.lean` ports only that
theorem, retaining Apache-2.0 notices and the existing license. Its selected
pinned compilation passed. The unrelated smooth cotangent-basis theorem is
excluded. Fetches of `MvPolynomial/Jacobian.lean` and `TensorProduct/Maps.lean`
failed; these files are not dependencies.

`PolynomialSystemEtale` constructs the square-system quotient and selected
Jacobian presentation in the actual pinned Mathlib interfaces. The planned
uniqueness port `Imported/UnramifiedUniqueness` retains the three inspected
diagonal arguments, replacing its missing tensor-product helper by a local
tensor-induction proof. New compiled and audited scopes are recorded only
after their checks; no ordinary multivariate result is yet certified.

That ordinary continuation has since passed the eighteen-module verifier,
all 90 permitted-axiom audits, full type and explicit-hypothesis review, and
the combined ACVF-QE import. `MultivariateHensel`, `GeneralizedHensel` and
`EncodedHensel` close Lemma 7.2 at the library boundary. No reference
hypothesis beyond the ordinary checked Mathlib and published ACVF inputs
was added. STATUS.md records the current certificate and separate root check.

## Residue constructibility continuation

The exact Remark 7.5 target is constructibility over the original residue
parameter field, including the residue zero. Section 4's checked
`ResidueNormalization.normalizedResidueSet_definable` supplies pure ring
definability over `residueParameterField B` by taking all anchors equal to
one. No new VF or RV representative is named in that coefficient field.
The actual field's algebraic closedness follows from the released
`VFAlgClosed.isAlgClosed_vfType` and
`ValOneEC.Johnson.isAlgClosed_residueField`.

The released `ProvedACFExtension.fullQE` already proves pure ACF QE with
arbitrary parameter types. Pinned Mathlib
`ModelTheory/Algebra/Ring/Definability.lean` proves polynomial zero sets
definable, the opposite direction of the needed bridge.
`RingTheory/Spectrum/Prime/ConstructibleSet.lean` and
`Topology/Constructible.lean` supply actual constructible sets and Boolean
closure. These definitions and declarations were read locally. Current
[ring-definability documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Algebra/Ring/Definability.html)
and
[prime-spectrum documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/ConstructibleSet.html)
were also inspected for discovery; current upstream is not a build input.

Focused searches on November 6 used `Lean algebraically closed field
definable constructible quantifier elimination MvPolynomial PrimeSpectrum`,
Tau Ceti `constructible ACF`, Mathlib `constructible IsQF`, and Reservoir
`algebraic geometry model theory ACF constructible`, together with the
existing catalog's quantifier/constructibility entries. No directly reusable
Lean theorem of this exact coefficient-preserving converse was found in
these searches. The prior broad catalog survey remains discovery evidence,
not an assertion of exhaustive coverage or current upstream verification.

The selected bridge evaluates each ring term in the polynomial ring over
the original subfield and interprets Boolean combinations of equations as
constructible subsets of its prime spectrum. An ambient tuple is compared
through the kernel of its actual evaluation homomorphism: the tuple is not
identified with a prime ideal. Only this small syntax/geometric bridge is
new; QE and residue purity are reused. The bounded-formula conversion is
adapted from local MIT `Section4/PureFieldAlgebraicity.lean` with credit in
the module header. `FieldConstructibility` and `ResidueConstructibility`
passed selected pinned source checks. The 35-module entry-point audit,
full statement review and fresh root check verify Remark 7.5.

## Original-base representatives and integer coefficients

For the next 7.4 bridge, the checked Section 3 modules were read at source:
`GeneratedBaseLifting.algebraic_rv_closure_generated_lifts`,
`GammaFiniteMeans.finite_mean_definable_base`,
`GeneralBallCenters`'s `OpenBallCodes.normalized_mean_mem`,
`RVUnaryLift.DefinableAt.rv_preimage`, and the genuine generated-base
closure laws. Together they give an economical route to representatives
of named nonzero RV elements inside the original generated base's VF part.
Filter a finite algebraic witness by the named RV class and take its mean.
Pure characteristic zero keeps that mean in the same actual open RV ball;
its same-base definability and closure give the required VF membership.
`GeneratedRVRepresentatives` verifies this bridge with the genuine saturation,
real-base smallness, ACVF00 and generation assumptions visible. This is not
yet the polynomial or derivative conclusion of 7.4.

For 7.6's integer choices, pinned
`Mathlib/Algebra/MvPolynomial/Funext.lean` already supplies `funext_set` on
boxes with infinite sides. Its proof and exact hypotheses were inspected;
rebuilding a Schwartz-Zippel or genericity theorem is unnecessary. The
integer image is infinite in a characteristic-zero field. Applying this
existing theorem to the product of the two row-combination determinant
polynomials supplies one common integer choice. `IntegerAvoidance` verifies
this small bridge, including the empty square matrix. The two hypotheses
are the original nonzero determinants; genericity is a conclusion. The
subsequent valuation, coefficient-scope and local-system arguments of 7.6
remain unverified. Both supporting modules passed the 35-module entry-point
audit and full statement review.

The next finite-fibre bridge reuses pinned `Polynomial.finite_setOfPred_isRoot`
and the root-multiplicity/iterated-derivative results in
`Mathlib/Algebra/Polynomial/FieldDivision.lean`. A small specialization lemma
uses `MvPolynomial.induction_on` and the checked Leibniz rules. No new
separability assumption is required in residue characteristic zero. The
leading-term comparison uses actual `RVCalc.rv_eq_iff` and Mathlib valuation
subtraction estimates. Clearing integer exponents uses the already checked
`PolynomialPresentation.ofFamily` constructor over the original coefficient
field. The supporting specialization, derivative and weighted leading-term
exports passed the expanded audit. Selected source checks also passed for
the finite-pattern extraction and the parameter assignment; their later
guarded-clause assembly is still being checked.

The verified local system for Theorem 7.6 reuses pinned multivariate polynomial
renaming, partial derivation, valuation-ring reduction, determinant maps
and the verified generalized Hensel theorem. The balancing multiplier is
the opposite simple derivative times its variable; it needs no external
result or new coefficient. Section 3's actual tuple compactness and finite
Gamma specialization supply the cover. The only added logic is the
first-order description of fibrewise existence and uniqueness and the
finite first-piece restriction.

The earlier Corollary 7.7 checkpoint uses Section 4's volume relation, zero-coordinate
deletion, canonical lift, complete graph maps and actual positive
presentations. It reuses the two Section 5 category representation
exports with their exact previously accepted earlier inputs. The uniform
obstacle condition remains explicit in both versions; the general version
also retains the dimensional presentation condition.
The finite version has source-checked presentation and invariance proofs using
`finite_map_to_vf_of_dimension_and_finite_rv_fibres` and
`dimension_and_finite_rv_fibres_of_finite_map_to_vf` from the checked
Section 4 library, together with `injection_refinement`.
The Section 5 raw presentation map preserves the point
and both of its blocks. No companion-paper result or new axiom is adopted.
The lift isomorphism uses the existing `Section4/FunctionalRelations.lean`
constructor. Its input is the complete definable relation with totality
and uniqueness proofs, and its output is a map with that graph. The helper
is built from the existing source against the checked Section 4 artifacts
for this integration boundary.

The November 7 repair uses the proved Section 5 representations to
discharge the obstacle, presentation and finite-fibre inputs of the
real-parameter surjections. The named-Gamma continuation uses the
original-base graph operations from Section 5, the balanced correspondence
lift from Theorem 7.6, and the existing positive additive presentation from
Section 4. It keeps the isomorphism graph over the original named base
while obtaining the VF fibre bijections over the real part of that base.
