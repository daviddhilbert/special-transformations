# Reuse survey for Sections 2–3

Search date: November 4, 2026 (America/Los_Angeles). This is a record of
discovery and source inspection; compiler evidence is recorded separately.

## Pinned, directly reused dependency

- ACVF-QE, `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`, MIT (with its separately
  attributed Apache adaptations). Lean 4.33.1; Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474` (Apache-2.0).
- Read `Proofs/Enc.lean`, `VFField.lean`, `VFValued.lean`, `RVCalc.lean`,
  `CanonicalRV.lean`, `CanonicalQF.lean`, and the verification script.
- `HasQE` preserves well-sortedness and the original parameter type.
  `theorem_2_3_quantifier_elimination` supplies it without additional premises.
- `CanonicalRV.encoded_eq_iff_close` supplies **both directions** of the
  leading-term equivalence; `rv_eq_of_close` alone supplies only one.
- Focused follow-up inspection found `ValOneEC.atomGood_of_isAlgClosed`,
  `good_solSet`, ball comparability and Swiss-cheese decomposition in
  `Proofs/JohnsonGeometry.lean`. These are proved, not merely the earlier
  `AtomGood`/`GoodMeetsBase` interface definitions in that file. Reusing these
  plus `hasQEb_ACVF_val` gives the new checked valued-language C-minimality
  theorem. Transferring arbitrary RV formulas still requires an interpretation
  bridge; the old C-minimality placeholder is not used.
- `LocalAssembly.fullQE` and `CanonicalStructure.sortedQF_*` provide the
  raw-to-sorted unary definability bridge on canonical tagged structures.
  This avoids rebuilding QE or assuming a closure-identification principle.
- Do not use `Enc.theorem_2_8_c_minimal`: its proof contains `sorry`.
- Existing package verification artifacts have matching source and the pinned
  checkout is clean. A fresh root import passed locally in WSL this session.
  This is not a fresh build of all 81 package modules.

## Local candidates

- `Sec3Average.lean`: port the valuation argument, derive the natural-number
  unit premise from the actual ACVF(0,0) theory, and add RV nonconstancy.
  Its old header wrongly describes that conclusion as a paper error and
  wrongly calls `vrv` injective. Use mutual preorder inequalities for values.
- `Archive/Milestone0/Saturation.lean`: genuine small-parameter saturation and
  homogeneity; useful interface. Its `MonsterACVF` specializes only ACVF,
  not ACVF(0,0). New context must retain the stronger theory and small base.
- `Sec3_frozen.lean` and its dependents: finite `SP` parameter pairs are useful
  witnesses, but cannot replace the arbitrary base S. Some targets are
  placeholders. Do not import them into the new section entry point.
- `UniformCover.lean`, `Sec3Count.lean`: formula constructions for the uniform
  cover step; they do not discharge saturation/compactness for Lemma 3.1.
- `Sec3FunIntoPower.lean`: useful set-theoretic descent proof; its
  identification of the additive maximal-ideal quotient with `ker rv` is
  incorrect. The equivalence relations must remain separate.

`Archive/audit_section3.py` stages exact sources under historical module
aliases and records all compiler exits, occurrences of `error`, and local
placeholder counts. Scratch logs are not proof certificates for paper items.

## Mathlib and external discovery

Pinned Mathlib source inspected: `Mathlib/ModelTheory/{Definability,Syntax,
Semantics,Complexity}.lean`, the ModelTheory file inventory, and valuation
modules. `BoundedFormula.restrictFreeVar` and `realize_restrictFreeVar`
provide the finite-support syntax bridge; `Set.Definable` gives the usual
arbitrary-base definition for the raw language. Sortedness still needs its
own bridge. No direct proof of C-minimality or sorted acl was found in these
searches. `Nat.recOnMul` is available for the residue-characteristic argument.

Web queries included “Lean C minimality algebraically closed valued fields
formalization”, “mathlib4 CMinimal algebraicClosure model theory”, “Reservoir
valued field quantifier elimination”, and “LeanPool Palomar TauCeti valued
fields C minimal”. Inspected the community projects/intentions registry,
LeanPool repository, Tau Ceti repository, Palomar landing page, and
TheoremSearch API documentation. Reservoir timed out; Formalpedia returned
an error. Palomar's landing page did not expose searchable results without
its runtime database. GitHub's direct ACVF-QE and current-upstream
AlgebraicClosure URL fetches missed the web cache. No additional importable
target proof was found; catalog and open/closed-PR coverage is incomplete.
No external candidate code was copied from these searches.

November 5 follow-up: inspected Mathlib's `Polynomial.continuous_eval₂`,
`Valued.mem_nhds`, `Valued.locally_const`, `Valuation.restrict_lt_iff` and
`ValueGroup₀.restrict₀_surjective`. These support the checked polynomial
leading-term stability and neighbourhood-infinitude prerequisites for 3.3.
`PolynomialSyntax.realizes` is a new bridge to the released LRV terms.

Links: [paper](https://arxiv.org/pdf/1006.2467v1),
[Mathlib](https://github.com/leanprover-community/mathlib4),
[community registry](https://leanprover-community.github.io/lean_projects.html),
[LeanPool](https://github.com/LeanPool/lean-pool),
[Tau Ceti](https://github.com/TauCetiProject/TauCeti),
[Palomar](https://palomar-registry.org/),
[TheoremSearch](https://www.theoremsearch.com/).

Polynomial-root and finite-image follow-up: reused Mathlib's
`FirstOrder.Ring.termOfFreeCommRing`, its realization theorem,
`Polynomial.eval₂_eq_sum_range`, `Polynomial.finite_setOfPred_isRoot`,
`Set.Definable.image_comp` and `Set.Finite.pi'`. New syntax bridges use the
released LRV language. `FiniteImage` proves the compactness step from the
genuine saturation API; it does not reuse the contrary legacy header claim.

C-minimality bridge follow-up: checked the released `CanonicalRV`,
`CanonicalResidueOperations`, `ValuedModelMap` and `VFAlgClosed` interfaces.
Reused their actual RV/residue arithmetic identities and the Mathlib definable
function composition, inverse-graph, case-split and preimage APIs. The new
representative and formula translations are proved, rather than assumed as
an interpretation premise. `GeometryBridge` transports Johnson's finite
Boolean ball representation to the exact frozen encoded ball definitions.
No call to the inherited Theorem 2.8 placeholder is used. Also inspected
Mathlib's algebraic matroid, its closure characterization and transcendence
basis interfaces as candidates for the remaining field-closure consequences;
that inspection alone does not prove those paper targets.

Closure and transcendence follow-up: used Mathlib's finite-parameter
character theorem and definable-map preimages to eliminate parameters
already definable over the base. Reused its relative algebraic closure,
`trdeg_add_eq`, `trdeg_eq_zero`, `isAlgebraic_algHom_iff`,
`IntermediateField.adjoin_toSubfield`, the checked fraction-field instance
in `IntermediateField.algebraAdjoinAdjoin`,
`AlgebraicIndependent.matroid_closure_eq` and `Matroid.closure_exchange`.
The new bridges identify the actual sorted closures and coefficient fields;
the generic field/matroid facts are not substituted for those bridges.

Normalization and closure follow-up (November 5, 2026): searched the pinned
Mathlib ModelTheory sources and the QE package for definable reducts,
interpretation of case-defined functions, definable choice/Skolem functions,
and saturation transfer. The existing TermDefinable.trans handles term
substitution, while canonical totalization uses cases on sort predicates.
A focused primary-source web search of Mathlib's Definability documentation
and FormalizedFormalLogic/Foundation found no directly importable theorem
for this transfer in those searches. The new DefinableReduct bridge proves
function/relation interpretation and induction on every bounded formula,
including universal quantification. NormalizationReduct checks every symbol
of the released encoding; NormalizationSaturation translates over the same
small parameter set. No new theory or model-theoretic hypothesis is introduced.
The sorted parameter bridge preserves the original arbitrary base.

For finite gluing, searched the pinned ModelTheory library, local section
files and the same primary-source documentation for definable choice,
Skolem functions and definable graphs with unique fibres. Reused the checked
finite-subcover proof and finite-fibre counting machinery; the new gluing
proof resolves overlaps by the domains of the partial graphs. It does not
replace definable choice by an arbitrary chosen function. Primary discovery
sources: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Definability.html>
and <https://github.com/FormalizedFormalLogic/Foundation>. This was a focused
follow-up, not a fresh exhaustive survey of every registry listed above.
Compilation and headline audit status are recorded separately.

Finite-coding follow-up (November 5): inspected Mathlib's finite-set cardinality,
finite sums, `Equiv.sum_comp`, term-definable function composition, definable
images and finite quantification. The construction uses the audited Lemma 3.8
and iterated centering at the mean of each RV fibre. Every child fibre is
strictly smaller when the parent has at least two points. A fixed bound on
finite-family size gives a uniformly definable mean via complete injective
enumerations and the term k*z-sum(c_i). The empty case is handled separately.
This permits an explicit recursive code in all VF tuple arities without
naming an enumeration of A as extra base parameters. The canonical model is
internal; `CanonicalContext` transfers ACVF(0,0) using the package's checked
well-sortedness audits of both characteristic-zero axiom schemes.

For the next center proofs, inspected the actual type of
`ValOneEC.Johnson.ne_finite_union_of_proper_subballs` in pinned
`Proofs/JohnsonGeometry.lean` (around line 2747): an algebraically closed field,
a nontrivial valuation, a nonempty ball, and finitely many proper subballs
cannot give a cover. This is a checked package dependency, not a hypothesis
assuming Yin's center theorem. Its reuse in Section 3 still needs a proved
bridge. Also inspected Mathlib's Antisymmetrization before defining the direct
RV same-value quotient; its equality and infinity class are proved from the
released RV preorder. Ordered-group operations and imaginary base-generation
interfaces are separate remaining tasks. Compilation and complete headline
audits are recorded in STATUS.md and verification/, not inferred from this survey.

Closed-ball centers follow-up (November 5): reused the pinned Mathlib
`Polynomial.Splits.eval_eq_prod_roots`, finite minima and minimal elements,
valuation sums, and the previously audited definable-mean construction.
The actual package declarations are
`ValOneEC.Johnson.ne_finite_union_of_proper_subballs`,
`ValOneEC.Johnson.isValBall_subset_or_subset` and
`ValOneEC.Johnson.exists_val_between'`; the earlier missing `Johnson`
namespace in this survey is corrected. The first two are included directly
in the fresh headline axiom audit. No copy of the finite-cover proof is made.

The new bridge extracts an actual finite unary polynomial support, proves
root-free RV constancy by factorization, and defines its finite root set over
the original base. Minimal ball values are finite even when their real-code
preimage is infinite. The same-base definable mean is invariant under equality
of balls, so it descends to the actual closed-ball quotient. The code coverage
theorem includes singleton and whole-field radii. The center convention is
the function/graph definition in Yin's companion paper, Definition 4.14
(<https://arxiv.org/pdf/1006.1393>), rather than a stronger requirement that one
point set meet every nested ball in exactly one point. The companion center
theorem is not used as an unproved input. The exact 94-module certificate
and 172 actual headline types/axiom checks are recorded separately in
verification/ and STATUS.md.

Definable-point and uniform-support follow-up (November 5): reused pinned
Mathlib's `Finset.exists_min_image`, `Valuation.map_sub_le`, `map_sub_lt`,
`map_add_le`, `map_add_lt`, finite first-order quantification and the audited
mean construction. The new nearest-root selection is definable from the
original sets R and A, so the containing ball and its center are never named.
The proof handles open and closed special radii and transfers the frozen
ball predicates by correctly sorted normalization. It does not assume the
companion paper's positive-component/positive-closure construction.

For Corollary 3.12, adapted this repository's unary polynomial syntax/support
proofs to one VF variable and any finite RV tuple in the same released Enc
language. Correctly sorted VF terms cannot contain those RV variables. One
root set is therefore uniform in all RV outputs; each exceptional RV fibre
must contain a root. No auxiliary definable choice, saturation or extra
characteristic assumption is used. Full compiler/type/axiom records now cover
102 modules and 198 headlines. The remaining K-term normal form, RV exchange
and Gamma-generation obligations are not supplied by these syntax lemmas.

Value-fibre follow-up (November 5): re-audited `InfRVDefGam.lean` before reuse.
Its uniform bound and C-minimality consequence are explicit hypotheses, so it
is not imported as a proof of Lemma 3.15. Its generic counting construction
had already been attributed and ported in `Counting`. The new proof derives
both missing inputs: a finite Boolean ball basis has only finitely many
balls avoiding zero, each contained in one RV class; zero-containing balls
are radial. Positive natural multiples give infinitely many distinct RV
classes at each nonzero value using the audited residue-characteristic-zero
unit theorem. Pinned Mathlib finite images, cardinality comparisons and
first-order finite counting finish the proof. The actual Gamma quotient and
full representative preimage supply imaginary-set definability without a
named section. `Sec3Fibre.fibre_one_infinite` concerns a VF-to-RV fibre, not
an RV-to-Gamma fibre, and was unsuitable for the latter requirement.

Remark 3.19 was checked against arXiv:1006.2467v1, printed page 7, lines
411–414 in the extracted primary PDF. `Remark319Audit.signs` is an actual
multiplicative subgroup of VF units, with point image {1,-1}; the complete
original-base definability, non-ball assertion and inequality with the full
valuation-unit group have checked types and only standard axioms. This is
an obstruction to the printed unrestricted statement. No silent corrected
classification or claim that Remark 3.19 is complete is introduced.
The certificate now covers 111 integrated modules and 226 headlines.

Additive-subgroup follow-up search (November 5, work still in scratch): native
pinned Mathlib searches for valuation/AddSubgroup/ball and finite initial-set
APIs, plus web discovery queries `Lean formalization C-minimal definable
additive subgroups valued field balls`, `site:github.com lean4 valuation
definable AddSubgroup ball` and the corresponding Mathlib GitHub query, found
no directly usable formal proof in these searches. Mathematical expositions
and unrelated discrete valuation formalizations are not checked dependencies.
The existing broad catalog survey remains applicable; this focused pass did
not repeat every catalog. The intended small bridge uses our already checked
finite Boolean ball basis, natural-number units and RV equality criterion,
plus Mathlib `Set.Finite.exists_minimal`/`exists_maximal`; the subgroup theorem
is not assumed as a standard input. Compilation of these scratch additions
will be recorded separately when available.

Additive subgroup and coset follow-up (November 5): implemented the focused
route described above in the released Enc language. The affine sequence
c+(n+1)b has pairwise distinct RV classes when v(c)<=v(b); pairwise differences
have value v(b), using residue-characteristic-zero natural units. At most one
term has a smaller absolute value. A finite ball basis then proves subgroup
downward closure. The endpoint argument ports no external proof: it uses
Mathlib's finite minimal/maximal elements and the elementary nesting of initial
sets. No classification hypothesis is left in the exported theorem.
Uniform polynomial support gives finite varying fibres for any partition into
balls, then a checked translation/actual-additive-quotient bridge proves 3.18(1).

For Gamma comparison, inspected pinned Mathlib
`Algebra/GroupWithZero/Range.lean` (`ValueGroup₀.restrict₀_surjective`) and
`RingTheory/Valuation/Basic.lean` (`restrict_inj`, `restrict_le_iff`,
`restrict_eq_zero_iff`), and reused the pinned ACVF-QE
`CanonicalRV.equivOfSameFibers`/`equivOfSameFibers_apply`. The resulting
comparison and units equivalence are on the actual value quotient. The
compatibility of RV multiplication and the reversal of inequalities are
proved. The comparison is not used as a substitute for the still-open
imaginary-parameter and Gamma-generation interfaces. All seven new modules
have fresh compiler checks; the combined certificate covers 118 modules,
251 actual headline type/axiom checks and a fresh root import.

Closed quotient representatives follow-up (November 5): reused the checked
full-code center theorem and uniform polynomial root support, plus pinned
Mathlib definable preimages, finite-coordinate existential/universal
quantification and finite images. The quotient relation is the full real
kernel over S. Classes meeting the finite original-base root set have a
family of ALL proper real closed-ball codes; only distinct ball values are
finite. Its definability is proved by equality of complete membership sets,
not by naming an enumeration or choosing representative parameters.
The center relation inherits ball invariance and is functional on a class
partition. Explicit finite-coordinate profile composition preserves the
complete sorted graph. Outside its domain, closed-ball root-free constancy
supplies class invariance. Arbitrary quotient representatives are used only
inside the proof; the invariant graph is proved equal to the original-S
constructed relation, and a realizing representative is proved for each class.
The final additive-quotient wrapper derives the closed-partition premises by
translating a code of an actual closed-ball imaginary, including zero-radius
and whole-field flags. No companion center theorem or quotient choice result
is assumed. The fresh record covers 125 modules, 284 headline type/axiom checks
and the root import. The VF,Gamma-generated alternative of 3.18(2) remains open.

For the next Gamma operations bridge, inspected Mathlib's Apache-2.0
`Algebra/Group/TransferInstance.lean`, `Algebra/GroupWithZero/InjSurj.lean`,
`Algebra/GroupWithZero/TransferInstance.lean`, `Order/Lattice.lean` and
`Algebra/Order/Monoid/Basic.lean`. Equiv transfers commutative groups and
linear orders; a group-with-zero transfer can use the checked injective
pullback API. This is a small extension of the already checked actual-quotient
comparison. Drafts remain in scratch and have not been compiler-certified.
In particular the reversed top order must not acquire an incorrect
zero-minimal ordered-group-with-zero instance. The imaginary-parameter and
Gamma-generation interfaces are separate outstanding obligations.


## Retraction of Remark 3.19 (November 5, 2026)

The author retracted the whole remark, conditional on its not being used later.
A complete arXiv v1 HTML search found one visible occurrence of “3.19” (its own
heading), no links to its anchor, and no other “multiplicative subgroup” phrase.
Sections 4–10 have no reference to `fun:quo:rep:mult`, `FunQuoRepMult` or
`Remark319Audit`, and no imports of `Sec3Tail` or `Sec3TailGamma`.
See [RETRACTIONS.md](RETRACTIONS.md) for the precise scope and decision.
The checked counterexample remains imported as an audit result; no replacement
classification or theorem is assumed. This documentation change does not alter
Lean source or the existing 125-module / 284-headline certificate.


## Actual Gamma parameters and consequence audit (November 5, 2026)

Completed the small transfer bridge surveyed above using pinned Mathlib's
Apache-2.0 Equiv/injective pullback APIs. `GammaOperations` credits the
GroupWithZero transfer pattern (Johannes Hoelzl). Ordered comparisons and
multiplication are proved to coincide with the actual released RV quotient.
The infinity class is maximal, so the implementation avoids an incompatible
zero-minimal ordered-group-with-zero instance. Divisibility uses the checked
ACVF-QE `VFAlgClosed.isAlgClosed_vfType` and Mathlib
`IsAlgClosed.exists_pow_nat_eq`; density uses a square root of b/a. No new
algebraic-closure assumption is imported.

For parameters, reused the already checked raw/sorted normalization bridges,
Mathlib first-order definable preimages and finite-support semantics, and the
existing actual quotient. `GammaParameters.Relation` requires a normalized
LRV first-order full preimage and global invariance on every pair of proper
RV code tuples with equal values. Choosing a representative is confined to
proofs of surjectivity and specialization. The real base is not enlarged in
the definition. An empty Gamma base is proved equivalent to the existing
real-base API in every finite arity. Constructor types, not only wrappers,
are included in the explicit headline audit. No standard-input structure
bundles a paper conclusion. Closure and generated-base predicates are only
definitions; their algebraic laws are still obligations.

`AlgebraicUniformCover` adapts the already checked tuple-descent finite-cover
proof: temporary domain parameters may appear in compactness, but the finite
relation remains over the original S. `SmallFiniteParameters` iterates the
checked cardinal bound for finite insertions. VF algebraicity after Gamma
specialization then follows by the checked RV-parameter independence theorem.
C-minimality, finite images and finite exceptions transfer through explicit
specialization; all representative parameters are visible in intermediate
types, and are not silently retained in base-sensitive conclusions. The
remaining base-sensitive Gamma extensions are listed separately in STATUS.md.

All fourteen added modules have compiler exit 0. The combined record covers
139 modules, 386 actual headline type/axiom checks and a fresh root, with only
the three allowed standard axioms. The pinned source commits and licenses
are unchanged. The newly documented RV-inversion language erratum changes
attribution, not these definitions or proofs. Scratch Gamma descent and finite
coding extensions are not included in this certificate.


## Gamma fibre descent, coding and closed-ball centers (November 5, 2026)

Reused the checked tuple finite-cover proof, generic first-order finite
quantification, Gamma quotient/full-preimage interface, and RV-parameter
independence. `GammaFamilyIntersection` takes the intersection along the entire
Gamma-definable real family. Compactness may temporarily name RV codes, but
the covering relation and final invariant intersection remain over the
original real S. This supplies the RV-to-Gamma-fibre part of 3.2 for real
outputs, as well as arbitrary nonempty Gamma-definable indexing families.
It does not establish Gamma-output or full imaginary ambient-base descent.

For 3.9, a finite set of algebraic real elements is covered by a finite set
definable over the original base. RV independence then covers any finite VF
tuple set with temporary RV names by such a real-base tuple set. Reusing the
checked real-base coding on that cover and restricting its graph proves the
full genuine Gamma-base version. This avoids an unnecessary second port of
the uniform barycentric-code construction. Every retained parameter is
visible in the graph type; the chosen temporary coding graph is not claimed
to descend by arbitrary choice.

For 3.10, reused `ClosedBallCentres`' finite-hitting-set mean construction,
extracted as `centers_of_finite_hitting_set`. The finite center image obtained
with temporary RV names is algebraic over real S; its finite definable cover
is an S-definable hitting set. The resulting total function on real ball
codes has a real-S-definable graph and is invariant under equality of balls.
Restricting it to the Gamma-base family and descending the actual closed-ball
quotient gives the full same-base center graph. Whole-field and singleton
cases are included. Neither representatives nor selected centers are named
as S parameters. This does not prove 3.13 for open balls.

The ten added modules have compiler exit 0. The combined record covers
149 modules, 420 actual headline type/axiom checks and a fresh root import.
All headline axioms are among the three permitted standard axioms. Sources,
dependency pins and licenses of reused components remain unchanged.

## Imaginary expansion: focused reference check (November 5, 2026)

[Pillay's author-hosted Stability Theory notes](https://academicweb.nd.edu/~apillay/pdf/lecturenotes.stability.pdf)
(September 29, 2003), Proposition 1.9 and Corollary 1.10 on printed pages 6–7,
give formula pullback to real representatives and preservation of saturation
and strong homogeneity under the imaginary expansion. Independently,
[Chernikov's author-hosted notes](https://www.math.ucla.edu/~chernikov/teaching/StabilityTheory285D/StabilityNotes.pdf)
(updated August 27, 2017), Lemma 1.19(2),(6),(7), printed pages 7–8, give
the corresponding formula, saturation and automorphism statements.
These are mathematical proof references; no source code has been imported.

[Marker's official contents](https://homepages.math.uic.edu/~marker/mtcont.html)
locates interpretability in Chapter 1 and saturation in Chapter 4. This search
did not verify a precise Marker statement covering the full imaginary bridge.
No additional hypothesis has been introduced on that basis. The remaining
Lean work includes a genuine interpreted carrier/language, parameter-size
bounds, and a proved equivalence with this library's invariant full-preimage
Gamma definitions. Assuming those Gamma closure or descent conclusions as
an interface would not complete their proofs. The current direct coded
descent remains the implemented route; a generic quotient interpretation is
a possible later reuse target, not a checked imported result.


## Gamma-output descent and support calculus (November 5, 2026)

Reused the checked real-tuple parameter-promotion theorem, genuine normalized
small-parameter saturation, finite-subcover proof, and actual Gamma quotient.
Raw RV preimages of finite Gamma sets are infinite: they cannot be passed to
the real finite-fibre descent theorem. `GammaCounting` instead counts pairwise
value-inequivalent nonzero RV codes. The finite-set cardinality argument is
adapted from local `Counting.lean`, with its unused LRV-structure argument
removed, so no language structure is assigned to the Gamma imaginary.

`GammaGoodRelations` universally intersects a promoted predicate over all
equivalent output codes, restoring global value-class invariance. At the
designated real tuple it remains the entire preimage of the original finite
Gamma witness. A first-order count/cut makes every Gamma row finite. The
finite union supplied by genuine saturation stays over the original real S;
intersecting it along the nonempty Gamma-definable family is definable via
the checked `GammaFamilyIntersection`. Its actual Gamma witness is finite
because it is contained in one chosen finite Gamma row. Temporary RV names
from compactness are absent from the final defining relation.

The resulting theorems cover Gamma outputs in 3.1 and both cases of 3.2 over
real ambient S, with finite tuple inputs and the intended nonempty condition.
This is not full ambient-imaginary-base descent. `GammaSupport` joins finite
supports using finSumFinEquiv and proves properness, reparameterization,
intersections and monotonicity without representative names in the base.
Closure idempotence and generated-base laws are separate obligations.

All five added modules compile with exit0. At that checkpoint, the certificate covered
154 modules, 454 actual headline type/axiom checks and a fresh root import;
all axiom sets are contained in the three allowed standard axioms. New checks
use one Lean worker; matching earlier checked compiler artifacts are reused.

## Focused follow-up for 3.17 (November 5, 2026)

A focused external search for Lean RV-valued monomial formalizations found
no additional importable proof of 3.17. This is a search result, not a claim
of exhaustive absence. The current [Mathlib ordered-group API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/GroupWithZero/Basic.html)
exposes the needed integer-power inequalities. Implementation uses the
matching declarations inspected in the pinned local revision
`0df444a360eaa60ab8c11dca51a86af692955474`, without upgrading Mathlib.

The checked semantic proof reuses the released canonical RV quotient,
residue operations, the checked mixed-polynomial realization theorem, and
local polynomial RV constancy. Integer powers and bounded nonzero coefficient
functions give uniform small-variable estimates using ordered-group laws;
no Archimedean hypothesis is introduced. Residue operations require explicit
zero and junk-zero branches. These ingredients now give the checked semantic proof of 3.17 in
`SmallFamilyConstancy`. The author's rational-function normal form in 2.4
remains an independent open obligation.


## Structural checkpoint: Gamma bases and small families (November 5, 2026)

Reused the checked finite real-base algebraic covers, nearest-root geometry,
uniform finite means and RV independence of VF algebraicity. The Gamma-base
3.11 proof names no containing ball. A globally bounded filtered finite set
has a full invariant mean graph, and the original/normalized interpretations
are explicit. Gamma-base 3.15 counts actual RV points within each value class;
specialization supplies only a natural-number bound, with no retained names.

For 3.17, the released canonical RV and residue equivalences provide the
actual RV group with zero and its residue operations. Polynomial trailing
degree and local RV constancy give rv(P(x))=rv(x)^m*rv(c) near zero. Integer
powers, products and inverses preserve bounded coefficient functions.
Nonzero exponents eventually force nonzero inputs outside the residue subset;
the checked residue junk-zero branches then produce coefficients independent
of x. Atomic equality, unit membership and value comparisons are independent
of sufficiently small nonzero x on the bounded output box. Quantifier-free
induction and released QE prove the complete set-valued statement, with actual
Gamma thresholds and all larger thresholds. Zero RV coordinates and arity0
are included. No Archimedean or new mathematical input is assumed.

Closely related semantic components were assembled into a coherent module to
avoid repeated compiler startup during proof development. Development-server
checks were followed by actual standalone compiler checks of every module,
the full headline/axiom audit and a fresh root import. The published combined
certificate covers 167 modules and 570 headline checks. Only the three permitted
standard axioms occur. Matching earlier artifacts are explicitly reused.

`GammaBaseTools` retains full code invariance under Boolean operations and
real-parameter promotion, without adding representative names to conclusions.
It does not settle full ambient-Gamma-base descent or closure/generation laws.
The verifier now hashes artifacts in small chunks after a memory-allocation
failure; matching checked cache hashes remain unchanged.

Further local reuse for 3.14: `ValOneEC.IsKBall`, `Good`, `good_solSet` and
`atomGood_of_isAlgClosed` in the pinned JohnsonGeometry preserve both centers
and radii in the algebraically closed coefficient field's image. The new
`AlgebraicBaseGeometry` lemma extends the existing valued C-minimality wrapper
to an arbitrary coefficient-field embedding. The ambient valuation is
nontrivial; the coefficient field's restricted valuation may be trivial.
RV lifting is now checked in `AlgebraicRVLifting`; full acl modelhood remains open.


## Coefficient lifting and ambient-base descent (November 5, 2026)

Reused the pinned `ValOneEC.Good`/`IsKBall` coefficient geometry and the
released RV and residue interpretations, extending the latter's definability
proofs to arbitrary named coefficient subfields. If a finite RV set failed
to lift in the coefficient field, one of its angular classes would avoid all
finitely many coefficient centers. The ball tests there are uniform on its
value fibre. Angular infinitude in residue characteristic zero contradicts
finiteness. The proof needs no nontrivial valuation on the coefficient field.
An independent valued-subfield elementary embedding uses released valued QE;
its nontrivial restricted-valuation hypothesis is explicit.

For the exchange route, the checked local RV-fibre exception theorem yields
finite/cofinite traces. Genuine saturation supplies uniform finite-side bounds,
and elementary order arguments supply finite images under bounded cuts and
canonical endpoints for finite-threshold sets. The bridge from actual Gamma definability to finite thresholds and the
Gamma-independence consequence are now checked below; RV exchange remains open. No conditional stability or exchange premise is imported.

For real-output descent over Gamma-named ambient bases, reused the checked
proper-code counting, support hull, tuple promotion and common-name cardinal
bounds. Finite row cuts preserve the original invariant relation. Saturation
is used only for the uniform finite subcover after temporary specialization;
the final universal intersection is definable over exactly the original base.
Both real and Gamma parts of the ambient base have explicit smallness bounds.

The combined certificate covers 170 modules and 640 actual headline type/axiom
checks, plus a fresh root import. The three new modules passed standalone Lean
compilation; matching earlier compiler artifacts are reused explicitly. Only
`propext`, `Classical.choice` and `Quot.sound` occur. The root's concurrent
Section 4 and Section 5 imports are consumer checks using the recorded matching
artifacts, including individual Section 4 compiler records. They do not certify
those sections. Full types were reviewed for the coefficient
lifting, valued elementary embedding, finite-side and endpoint tools, and
ambient-Gamma-base real-output descent.


## Actual Gamma/RV separation and 3.7 (November 5, 2026)

A focused external follow-up searched for Lean ACVF RV/value-group exchange,
strong minimality and orthogonality, including the upstream Mathlib GitHub
repository. No additional importable Lean proof was found in those searches.
They returned mathematical expositions, including
[Kamensky's ACVF notes](https://mkamensky.github.io/teaching/2015s/acvf/notes.pdf)
and [Rideau's valued-field notes](https://www.math.ens.psl.eu/~rideau/teaching/val/vf.pdf).
These are reference hits, not imported theorem dependencies. The earlier
catalog/registry survey and exact pinned local source inspection remain the
reuse basis; no dependency upgrade or new mathematical hypothesis was added.

Reused the checked C-minimality theorem, arbitrary-coefficient ball geometry,
angular infinitude, actual Gamma order, finite/cofinite RV fibres, genuine
saturation and 3.15. A radial Boolean combination of VF balls has a finite
actual threshold basis: angular representatives avoid its finite set of
centers, so ball tests depend only on the finite collection of radii. The
intrinsic endpoint is the set's infimum when bounded below and otherwise the
complement's infimum. Finite thresholds prove that this endpoint exists in
the actual Gamma group, without order completeness.

The endpoint's full graph is first-order on all proper RV codes, using lower
bounds and greatest lower bounds. Thus its order cuts retain exactly the
original real parameters. Uniform finite-side bounds on each angular fibre
force finite endpoint image; uniformly finite original rows force finite
endpoint inverse fibres. Checked 3.15 then gives finite total RV projection.
No desired finite-image or orthogonality conclusion is supplied as a premise.

Existential Gamma-coordinate projection preserves full code invariance. After
temporarily specializing the other coordinates, the one-Gamma result applies
at each induction step. A checked globally finite scalar-row cut then removes
all finite Gamma support from an RV algebraic witness. The final finite set is
definable over exactly the original real base. This proves the Gamma assertion
of 3.7 even with arbitrary existing Gamma names, requiring no bound on that
entire Gamma set. RV exchange remains a separate unfinished step.

The combined checkpoint certifies 173 Section 3 modules, 722 actual headline
type/axiom checks and a fresh root import. The three new modules passed actual
standalone Lean compilation. Only `propext`, `Classical.choice` and `Quot.sound`
occur. Full types were reviewed for finite thresholds, endpoint-cut
definability, the genuine family constructor, Gamma/RV separation, Gamma tuple
projection, algebraic closure equivalence and 3.7. Earlier matching compiler
artifacts and the recorded external root-consumer interfaces are reused;
this is not an audit of Sections 4 or 5.


## RV exchange completed (November 5, 2026)

Reused the checked parameter-promotion/finite-row cut in
`GammaBaseDescent.good_base_relation_of_algebraic`, the new Gamma-name removal
in `RVGammaAlgebraicity`, and the checked finite/cofinite RV geometry and 3.15.
The legacy `Exchange.lean` contains conditional reductions; its exchange or
reverse-finiteness premise is not assumed or imported as a proof.

On each actual RV value fibre, genuine saturation supplies a uniform bound
on finite reverse fibres. First-order counting above this bound defines a
bad-output relation, invariant on every Gamma representative. The pure
cofinite intersection argument makes its fibre finite. Thus a bad output is
algebraic over the original real base plus that Gamma value; the proved Gamma
independence removes it. A nonalgebraic output therefore has finite reverse
fibres in every value class. Checked 3.15 makes the entire reverse relation
finite. The final exchange theorem constructs its forward relation from the
given algebraic witness, so no conditional finite-relation interface remains
in the headline. A wrapper uses the checked Gamma-name equivalence to retain
arbitrary existing Gamma names, without bounding that whole name set.

The combined certificate covers 174 modules, 743 actual headline type/axiom
checks and a fresh root import. The new coherent `RVExchange` module passed
standalone Lean compilation. Only `propext`, `Classical.choice` and `Quot.sound`
occur. Full types were reviewed for both exchange headlines, the complete
bad-output relation, the actual uniform finite-side bound and the reverse
finiteness theorem. ACVF(0,0), genuine saturation, the countable lower bound
and real-base smallness are explicit; there is no VF-field-base or homogeneity
premise. Other sections' root-consumer artifacts remain separately recorded.


## Full acl modelhood and Corollary 3.14 (November 5, 2026)

Reused the checked coefficient-preserving RV lifting and valued-subfield
elementary embedding from `AlgebraicRVLifting`, together with sorted parameter
elimination, relative field algebraic closure and canonical normalization.
The legacy `M3AclField.lean` proves only field closure and was not treated as
full LRV modelhood. No result from the cited companion paper is assumed.

Focused source inspection in the unchanged Mathlib pin
`0df444a360eaa60ab8c11dca51a86af692955474` found the needed generic bridges:
`Mathlib/ModelTheory/ElementarySubstructures.lean`,
`ElementarySubstructure.meetsDefinable`, `MeetsDefinable.closure_eq_self`, and
`MeetsDefinable.isElementary_closure`; and
`Mathlib/ModelTheory/ElementaryMaps.lean`,
`ElementaryEmbedding.liftWithConstants` (Apache-2.0, Aaron Anderson).
The former are directly imported. `ModelTheory.elementaryEmbeddingWithNames`
is an attributed adaptation of the latter to an arbitrary original name
type, rather than only a subset of the embedding's source. Relative algebraic
closedness uses the pinned `IsAlgClosure.isAlgClosed` projection; that
projection is not itself registered as a typeclass instance. No dependency
upgrade or new standard-reference hypothesis is introduced.

Over VF generators, actual RV acl is the rv-image of the relative algebraic
closure F of the generated VF field. Thus every real acl parameter is
definable over VF names in F. The complete decode-preimage of any sorted
definable set is valued-language definable over F. The checked valued QE
embedding makes F elementary when its restricted valuation is nontrivial.
Mathlib's definable-set Tarski-Vaught criterion then gives the full LRV
elementary submodel on the actual acl carrier, including RV surjectivity and
all theory axioms. Naming is by the literal inclusion of the original base.
For arbitrary original models, canonical normalization is internal and
explicit; its correctly sorted operations and original acl carrier agree.

Full invariant Gamma fibres also prove name elimination: quantified codes
are restricted to their entire original-base definable value fibres, and
then projected. For a VF-generated imaginary base this preserves precisely
its real part's definable sets and acl. Elementarity meets each named Gamma
value fibre inside the acl model, with no externally chosen representative
named in the conclusion. General Gamma closure laws remain separate.

The six new modules passed standalone pinned Lean compilation. The combined
certificate covers 180 modules, 786 actual headline type/axiom checks and a
fresh root import; only `propext`, `Classical.choice` and `Quot.sound` occur.
Every new full headline was reviewed, including original versus normalized
structure arguments, genuine Gamma bases, named atomic diagrams and the
nontrivial actual-value hypothesis. There is no saturation or cardinality
premise. Matching earlier compiler artifacts and the 69 separately recorded
external root-consumer interfaces are reused; this does not audit Sections 4
or 5. The compiler and ACVF-QE revisions remain unchanged.


## Genuine Gamma closure laws and generated-base lifting (November 5, 2026)

Reused `GammaBaseTools.promote_gamma_relation`, its universal invariant hull,
finite Gamma-support joins, original-base Boolean operations and real
projection, plus Mathlib's finite parameter support theorem. A finite tuple
of real definable names has a definable singleton over exactly the original
base. A tuple of Gamma definable names has its full product of nonzero RV
value fibres definable over that base. Intersecting these with the promoted
relation and projecting all input names proves general dcl transitivity.
Applying this to the actual `closureBase` proves its closure laws, without
saturation or desired-conclusion hypotheses. The earlier real-only closure
tools were used through bridges, rather than silently reinterpreted as
imaginary-base theorems.

The generated-base laws then combine the checked real/Gamma algebraicity
equivalences with `rv_algebraicClosure_iff_lift` from `AclFieldImages`. For RV, the
genuine saturation and small-real-generator assumptions come from the proved
Gamma independence theorem. There is no bound on all Gamma generators or on
the cardinality of their whole definable closure. Coefficient valuations may
be trivial. This supplies an actual RV lift for the proposed general-center
argument; it does not itself finish Lemma3.13.

Focused pinned Mathlib valuation source inspection found `Valuation.map_sub_swap`,
`map_add_lt` and `ne_zero_iff` in
`Mathlib/RingTheory/Valuation/Basic.lean` at the unchanged Mathlib pin.
Elementary ball geometry then compares two strict disc radii by taking the
VF boundary point of the smaller radius. Equal proper open discs therefore
have the same-radius closed hull. No value-group density or order completeness
is assumed, and this hull is not topological closure. Existing local
`BallTranslation` and the pinned Johnson ball geometry remain the intended
bridges to complete ball-code families. Legacy conditional center reductions
are still not treated as proofs.

The three new modules passed standalone pinned Lean compilation. The combined
certificate covers 183 modules, 809 actual headline type/axiom checks and a
fresh root import. Only `propext`, `Classical.choice` and `Quot.sound` occur.
Full new headline types were reviewed, including finite input arities,
imaginary parameter scope, actual closure definitions, generator cardinal
bounds and nonzero actual VF radii. Matching prior compiler artifacts and 69
recorded external root-consumer interfaces are reused; this is not a proof
audit of Sections 4 or 5. No dependency revision or mathematical assumption was
added. General Gamma acl transitivity and other base-sensitive extensions
remain separately open.


## Gamma-base VF fields and proper open-ball coding (November 5, 2026)

Reused the checked general dcl-parameter elimination in `GammaClosureLaws`
to transfer original real-name function and inverse definitions over exactly
the same genuine Gamma base. The existing `VFDefinableClosure` field proof
was adapted to the actual `DefinableClosureAtBase` carrier. The algebraic
field is linked to `AlgebraicAtBase` by the checked Gamma/VF algebraicity
equivalence. Thus neither field is merely a renamed raw-real object without
its required membership bridge. Existing `TranscendenceDegrees`,
`SubfieldTrdeg` and RV-independence prove all three transcendence-degree
equalities in the full Gamma-base scope, with the paper's standing VF-field
base convention retained. No desired field-closure or trdeg equality is
assumed, and no saturation or characteristic restriction is introduced.

For proper open balls, reused the checked `ClosedBallCodes` evaluation and
quotient schemes, recording that source in the new file. A strict disc is
defined by negating the reverse weak RV-value comparison on correctly sorted
terms. Its nonzero actual VF radius is part of the real-code guard. Ordinary
valuation semantics is proved from the compatible valuation bridge, with
the paper/Mathlib order reversal explicit in the proof. `OpenBallHullGeometry`
then makes the same-radius closed hull independent of the code. The map is
descended to actual ball imaginaries, and inclusion in the hull is proved.
The full definable-family hull bridge and the finite-family center argument
are still separate work; the new quotient alone is not Lemma3.13.

The two new modules passed standalone pinned Lean compilation. The combined
certificate covers 185 modules, 843 actual headline type/axiom checks and a
fresh root import. Only `propext`, `Classical.choice` and `Quot.sound` occur.
Full new headline types were reviewed, including actual Gamma-base field
membership, original parameter sets, all finite VF tuple arities, arbitrary
RV names, standing VF-field base convention, nonzero radii and actual ball
quotients. Matching prior compiler artifacts and 69 recorded external
root-consumer interfaces are reused; this is not a source/headline audit of
Sections 4 or 5. No dependency revision or accepted input was added.


## Finite Gamma order and complete hull-family graphs (November 5, 2026)

Reused `GammaClosureLaws`, `GammaBaseTools`, `GammaProjection` and the actual
Gamma order bridge from `GammaRVSeparation`. Minimum selection uses the
negated RV-order predicate with the paper's order convention. Erasing the
definable minimum then isolates each member of a finite actual Gamma set.
The induction scheme was inspected in the concurrent local
`Section4/GammaFiniteDefinablePoints.lean`; the new module credits that source
and implements the arbitrary genuine Gamma-base version on checked Section3
interfaces, without importing Section4. Pinned Mathlib's
`Data/Finset/Max.lean` supplies finite minima and strong induction. Its
Apache-2.0 dependency pin is unchanged. This proves Gamma acl equals dcl;
it does not claim full mixed acl transitivity.

For hull families, reused the complete closed-code membership graph and the
quantified equality-kernel scheme in `ClosedClassCodes`. The full hull graph
quantifies over every equivalent closed-ball code, rather than recording only
the direct image of one code. Normalization preserves the radius guard and
the VF-one flag. Intersecting this graph with the original open family's full
preimage and projecting gives exactly the full closed-family preimage over
the original base. This works for infinite families as well as finite ones.
The existing closed-center theorem is the intended next reuse; a hull center
need not belong to the original open ball, so this bridge alone is not3.13.

Both new modules passed standalone pinned Lean compilation. The combined
certificate covers 187 modules and 864 actual headline type/axiom checks,
plus a fresh root import. All21 new full types were reviewed, including
the actual Gamma quotient, full value-class preimages, genuine base scope,
normalization and absence of extra finiteness or saturation hypotheses.
Only `propext`, `Classical.choice` and `Quot.sound` occur. Matching earlier
compiler artifacts and69 recorded external root-consumer interfaces are
reused; this is not a source/headline audit of Sections4 or5. No dependency
revision or authorized reference input was added.


## Proper-open-ball centers over generated Gamma bases (November 5, 2026)

Reused `GammaClosedBallCenters`, `OpenBallFamilyHulls`, `GeneratedBaseLifting`,
`AclFieldImages`, `FiniteAlgebraicCover`, `MeanInBalls` and the complete graph
schemes in `ClosedCentersFromFiniteSet`. The raw-map pullback in
`GammaRealMap` retains all Gamma support invariance; its hypothesis concerns
globally definable maps in the normalized real structure. The hull-code map
uses only projections and the VF-one constant, with normalization proved.
Original off-sort field-operation totalizations are not silently transferred.

The original closed-hull center need not lie in the open ball. For a center
outside its ball but inside the same-radius closed hull, the distance to any
ball point equals its actual VF radius. This makes the translated RV fibre
exactly that ball. Finite actual ball families have finite RV offset images,
whose full graphs remain definable over the original B. The checked generated
base lifting theorem places these RV offsets in the relative VF algebraic
closure of the pure VF generators; trivial coefficient valuations are allowed.
Adjoining the algebraic hull center gives a VF-algebraic point in the ball.

The checked VF/Gamma algebraicity equivalence then removes Gamma names from
these finitely many VF points. `finite_definable_cover` constructs a finite
cover over B.real. The original raw finite-family mean graph and the checked
open-disc mean containment give an invariant function on every proper code,
then on actual open balls. This avoids assuming an algebraic hitting set or
a definable choice theorem. Namespace isolation in the standalone check
caught a missing Transfer open in an initially split membership component;
the coherent construction is consolidated in `OpenBallCenters` and checked
as its own module. No mathematical statement was weakened.

The two new modules passed standalone pinned Lean compilation. The combined
certificate covers 189 modules, 898 actual headline type/axiom checks and a
fresh root import. All34 new full types were reviewed, including actual
imaginary bases, true saturation, exact generator cardinality scope, proper
open-ball radii, algebraic-point witnesses and full quotient graphs. Only
`propext`, `Classical.choice` and `Quot.sound` occur. The mixed-family form of
3.13 and the generated 3.18(2) consequence are still separate obligations.

The shared QE scratch directory disappeared during verification. A private
clone at the unchanged release pin was restored; all81 shipped proof sources
match the retained release snapshot byte for byte. The earlier86-module
cache's exact source/recursive-dependency/compiler fingerprints were checked,
and80 relevant artifacts have identical Lean code to the pinned sources.
The QE root and its three exact headline audits were checked afresh with
exit zero and standard axioms. The published record embeds all recovery
identities and distinguishes reused proofs from fresh imports. This is build
dependency recovery, not a restart of QE or a new accepted input. The69
source/cache-matched external root consumers remain import checks only.


## Full mixed-family Lemma 3.13 (November 5, 2026)

Reused the compiler-checked proper-open algebraic-point theorem in
`OpenBallCenters` and full Gamma-base closed centers in `GammaClosedBallCenters`.
The actual all-ball sort is the quotient of the closed/open charts by equality
of their point sets, including equality across charts. Each chart embeds
injectively, so a finite family pulls back to finite actual chart families;
raw real code sets themselves are not counted as finite. Explicit code
coverage handles arbitrary actual VF radii, radius-zero closed balls and the
whole field, using the checked ordinary-valuation semantics.

Definability of a family and of its center function is specified by the full
real preimage in both charts over the same genuine Gamma base. Algebraic
points in each ball give one finite real-base definable hitting cover. The
center is the normalized mean of that same finite set intersected with the
actual ball, so chart aliases have exactly the same value. The finite-family
mean definability proof was extracted from the checked closed/open hitting-set
construction and bridged to both complete quotient graphs. `GammaFiniteMeans`
supplies the actual normalized mean; `MeanInBalls` proves containment. The
normalization bridge transfers point-set membership, rather than equating
two field instances. Restoring the original structure as the local instance
after binding its normalization resolves the model-instance elaboration.

The new coherent module passed standalone pinned Lean compilation. The
combined certificate covers 190 modules, 940 actual headline type/axiom
checks and a fresh root import. All42 new full types were reviewed, including
the quotient kernel, code coverage, full two-chart graphs, genuine imaginary
bases, true saturation and exact cardinality scope. Only `propext`,
`Classical.choice` and `Quot.sound` occur. There is no new standard-reference
input, center/choice hypothesis or Gamma-generator size bound. The pinned
QE recovery and69 external consumer identities remain recorded separately.
The generated3.18(2) application and other remaining targets are not counted
as proved by this center theorem.


## Full quotient selection, Lemma 3.18(2) (November 5, 2026)

Reused checked `DefinableCosets` subtraction and its normalization bridge,
`GammaRealMap` full-preimage pullbacks, the genuine Gamma-base Boolean and
projection calculus, and `GammaBaseFiniteExceptions.lemma_3_18_1_gamma_base`.
The real-base `ClosedClassCodes` and `ProfileComposition` constructions were
inspected and adapted over the same imaginary base. The profile variation
relation is the projection of the symmetric difference of the two full
profile graphs, retaining every finite RV arity. Universal membership
comparison defines equality of a real-coded ball with an entire coset.
Intersecting with variation defines both full exceptional chart preimages;
finiteness counts actual cosets and ball point sets rather than real codes.

`EncodedBallGeometry` supplies the actual-radius conversion proof, now with
explicit coverage in the all-ball quotient. Translation preserves these
actual discs; closed cosets reuse `ClosedCosetChoice.closed_cosets_of_code`,
including singleton and whole-field cases. Closed-family centers come from
checked Gamma-base3.10, a real-base finite hitting cover and a common mean;
they require no saturation. Generated-base centers use the proved full3.13.
Both chart graphs give one point/center relation. Its functionality and
constancy on cosets follow from the actual quotient kernel. Composing with
the original powerset-valued graph, and using the definition of exceptional
cosets on the complement, gives both quotient definability and a realizing
representative for every selected profile. Final paper headlines discharge
all intermediate center and code-coverage data.

The coherent new module passed standalone pinned Lean compilation. The
combined certificate covers191 modules,983 actual headline type/axiom checks
and a fresh project root import. All43 new full types were reviewed for
sorts, tuple arities, full parameter scope, genuine saturation and cardinal
bounds. Only `propext`, `Classical.choice` and `Quot.sound` occur. No new
standard-reference input or extra mathematical hypothesis was introduced.
The two remaining work blocks are Gamma closure/descent extensions and the
author-approved rational guarded normal form2.4.
