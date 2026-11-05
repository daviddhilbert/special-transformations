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
