# Section 4 formalization plan

The Section 4 milestones have been implemented and checked relative to the
accepted inputs. [STATUS.md](STATUS.md) is the current verification record;
the original implementation plan below is retained for provenance.
The earlier sections have since been completed in their approved scope;
Section 4 now consumes their checked exports.

Prepared November 5, 2026. The objective is the whole of Section 4, including
its unnumbered consequences and Grothendieck constructions. Numbering follows
[arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1).

The author has authorized using the material in all previous sections as
given while Section 3 continues separately, and has explicitly instructed
that those dependencies need not be reverified. Section 4 proofs will be
checked relative to those inputs. This authorization does not extend to
assuming a Section 4 conclusion or its principal proof step.

## Shared context and assumptions

Keep Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and
ACVF-QE `f3ef4ee679f921079aa8f742a2807a9cc724d2d6` unchanged. Reuse the
released language and the new Section 3 model, parameter, closure, coordinate,
and definability interfaces.

Use ACVF(0,0), genuine small-parameter saturation and homogeneity, and the
original small named base. Preserve the single absorbing RV element and the
reversal of the valuation order. State any stronger generation condition only
where its proof needs it.

Create a narrow `Inputs.lean` interface for the Section 3 statements actually
used. Use existing exports as given. Supply an unfinished Section 3 result
as a theorem hypothesis with its precise arities and parameter scope, without
introducing an axiom. Keep a dependency ledger so that each such hypothesis
can later be replaced by its completed Section 3 theorem.

The initial dependency groups are:

| Section 3 input | Section 4 use |
| --- | --- |
| 3.9, with tuple and parameter extensions | Uniform coding of finite fibres |
| 3.3 and 3.4 | VF algebraicity and transcendence degree |
| 3.5 | RV-to-VF finite images and fibre invariance |
| RV exchange in 3.6 | RV dimension calculus |
| Gamma independence in 3.7 and 3.15 | Value-group fibre argument |
| 3.2 and 3.3 | Morphisms detected by lifts |

Compactness and finite gluing should come from the existing saturation API.
Any additional standard model-theoretic or valued-field hypothesis must have
its full type and its authorized Marker or Engler--Prestel citation. A missing
bridge from pure ordered-group facts to the induced Gamma structure remains
a mathematical task.

## Reuse before implementation

Follow [the reuse guidelines](../FORMALIZATION-REUSE-GUIDELINES.md) at each
substantial prerequisite. The initial comparison is in
[REUSE-SURVEY.md](REUSE-SURVEY.md). Search current external developments and
unmerged work as well as the pinned library; the old cached survey misses
substantial newer Tau Ceti material.

Use Mathlib's categories, functors, isomorphisms, full subcategories and full
and faithful functors. Its categorical Grothendieck construction is already
available if an indexed-category construction becomes useful. The algebraic
Grothendieck semigroup in this section needs a separate comparison.

Two particularly useful external candidates are Tau Ceti's generic presented
categorical group and its ring structure on additive group completion. The
latter imports only Mathlib modules. Both need a checked port to the pinned
environment; the current Tau Ceti toolchain cannot be imported wholesale.
Compare the open Mathlib additive-localization proposal and the smaller
Bridgeland presentation as alternatives before choosing the port.

## Milestone 1 Statements and definable maps

Freeze a target checklist for 4.1--4.23, including the surrounding prose.
Add a separate Section 4 library entry point and verifier when proof work
starts. Preserve the legacy files as candidates and keep the active Section 3
working tree untouched.

Build the common interface for definable sets and maps on finite mixed
tuples. Maps should have their complete graphs definable over the original
base. Prove identity, composition, restriction, pairing, coordinate changes,
images and preimages, finite gluing, and parameter extension. Reuse the new
Section 3 bridges before porting the older formula manipulations.

Treat Gamma as the actual imaginary quotient. The older claim that a Gamma
tuple can simply be replaced by a definably chosen RV tuple is insufficient.
Retain mixed RV/Gamma targets, or prove the exact dimension-preserving
elimination of those targets. No definable section of the quotient is presumed.

Settle empty sets, zero arities, empty maxima, and absorbing coordinates at
this stage. In particular, use an explicit nonemptiness condition or an
extended dimension convention where the zero-dimensional polydisc statement
requires it. Compare the empty-set convention separately with Krull dimension.

**Deliverable:** a checked interface in which the paper's dimension witnesses
can be stated without arbitrary-function or finite-base substitutes.

## Milestone 2 VF dimension

Address 4.1--4.8 in dependency order.

First define dimension by the least admissible finite-to-one witness and prove
that the minimum is attained. Derive the injection characterization using
Section 3 finite coding, uniformization by genuine saturation, and finite
gluing. The auxiliary coding dimension must be uniform; independently chosen
maps on individual fibres do not establish this.

Next prove the fibre calculation, with the fibre parameter explicitly adjoined
when needed. Establish the comparison with actual field transcendence degree
over the VF part of the base. Use it for the geometric consequences and
parameter invariance under allowed small extensions.

For the polydisc argument, prove all dimensions by induction, using the
existing ball geometry and C-minimality interfaces. Account explicitly for
the Gamma radius-selection step. The one-coordinate legacy result is useful
but does not close the general induction.

A second route is now available for comparison: generalize the accepted
Section 3 univariate `PolynomialSyntax`, `RVTermLocal`, and `QFLocal` to
finite VF tuples. At a tuple algebraically independent over the coefficient
field, a nonzero polynomial stays nonzero locally, and its RV value is
locally constant. Released QE then gives a neighbourhood in the fixed RV
fibre. For the reverse implication, genuine saturation and definability of
polynomial zero sets reduce generic-point existence to finite polynomial
avoidance on an infinite-sided box. Mathlib's `MvPolynomial.funext_set`
already proves the needed algebraic avoidance. Compare this route before
building the induction's separate Gamma-radius selection layer. Neither
route may assume the polydisc-dimension conclusion.

After the local route is checked, parameter invariance can be obtained
without first completing 4.8. Choose a coordinate projection of A whose
image has an algebraically independent tuple of length dim(A). Its image
contains an open polydisc in an RV fibre. The same image remains definable
over an enlarged small base, so the polydisc lower bound and 4.5 give the
reverse dimension inequality. Extending an existing finite-to-one witness
gives the forward inequality. Coordinate indices add no model parameters;
the enlarged base must retain its explicit smallness bound.

For the Zariski comparison, use the actual Zariski closure and its dimension.
Inspect the pinned transcendence-basis, finite-generation, Noether-normalization
and Krull-dimension APIs before building a missing algebraic bridge. The pinned
library already contains `Algebra.IsAlgebraic.trdeg_le_cardinalMk`; the old
file's claim about a missing generator bound needs reassessment.

**Deliverable:** 4.1--4.8 with explicit Section 3 inputs and no assumed
straightening, transcendence-degree comparison, or polydisc-dimension result.

## Milestone 3 RV and fibre dimensions

Address 4.9--4.13. Develop the finite-tuple rank calculus from RV exchange and
relate it to the dimension witnesses. Prove the necessary uniformity and
parameter statements using small extensions of the base.

Use residue-field normalization for the Zariski comparison, separating any
absorbing coordinates before division. For the value-group fibre argument,
make the descending RV arity explicit and retain original-base definability
through the construction. Audit the final selection of a definable Gamma
point against the precise induced ordered-group structure.

Define the dimension of RV fibres and prove its invariance using the
Section 3 finite-image theorem. Include the uniform finite-to-one maps needed
in that proof. Check the precise finite-image scope of the unnumbered
set-valued image assertions against the source before freezing them.

**Deliverable:** the full RV dimension layer and the exact finite-fibre
criterion used by the categories.

## Milestone 4 Categories and padding

Address 4.14--4.17 using Mathlib's category interfaces. Define the VF
categories by the dimension conditions first, then prove the alternative
finite-to-one descriptions. Audit the old `VFObj` interface before reuse;
its finite-relation presentation cannot silently replace these objects.

Define RV objects and the paper's morphism condition, and prove identities,
composition, restriction inclusions and the characterization of isomorphisms.
Keep the finite-image condition on images of label fibres distinct from
finite-to-one behavior of the whole morphism.

Prove that padding is a genuine full and faithful functor, with the required
object and subcategory properties. Represent the graded collections using
finite families in the appropriate degrees. Keep VF unions and RV degree
tags distinct in the implementation. A zero-length tuple is a singleton
product, and introduces no new RV absorbing point.

**Deliverable:** genuine categories and functors with checked equivalences
to the paper's descriptions.

## Milestone 5 Canonical lifts

Address 4.18--4.20. Prove definability, category membership, companion identities
and compatibility with padding. Prove the complete morphism criterion,
including the passage from algebraicity to finite images. The legacy file
currently gives a conditional algebraicity reduction, which needs that last
step and a full audit of its input types.

Use the dimension layer to establish the bijective variant. At this stage
the lift is an object construction; producing lifts for arbitrary RV
isomorphisms belongs to Section 7. Keep that later dependency visible when
discussing induced maps on Grothendieck classes.

**Deliverable:** all lift properties asserted within Section 4, with no
assumed Section 7 lifting theorem.

## Milestone 6 Grothendieck semigroups and rings

Address Section 4.3, including 4.21--4.23 and the final padding assertion.
Choose the algebraic implementation after the external reuse comparison.

Construct the positive scissor quotient first, with its class map, additive
universal property, and disjoint-union description. Prove compatibility with
products and the degree-zero multiplication convention. Then obtain the
group and ring by checked general completion machinery. If a generic
presented-group API is used as an alternative presentation, prove its
equivalence with the completion of the positive object.

Do not use additive-category biproduct infrastructure as a substitute for
disjoint unions of definable sets. The inspected Tau Ceti object-code monoid
has biproduct hypotheses that these categories do not satisfy automatically.

Prove the quotient and congruence properties, universal maps, and the induced
padding homomorphism. Its injectivity must survive the scissor relations;
full faithfulness alone is not the complete quotient argument. Establish
restriction and finite-partition compatibility, or an equivalent reflection
argument.

**Deliverable:** the positive and groupified constructions required later in
the paper, with their operations and universal properties.

## Verification and first proof session

For each target record the source number, full Lean type, original-base
definability, Section 3 inputs, authorized standard hypotheses, compiler exit,
and headline axioms. Compile and audit the new Section 4 work; do not make
earlier-section verification a prerequisite. Accept only `propext`, `Classical.choice`, and
`Quot.sound`; a clean audit does not discharge explicit premises. Distinguish
proofs relative to the authorized Section 3 inputs from unconditional
integration after those inputs are proved.

The first proof session should complete Milestone 1 and the basic dimension
definitions, then attempt the uniform finite-fibre coding step for 4.2. That
gives a substantive first checkpoint and exercises the interface needed by
the rest of the section. Keep compile output and experiments in
`.scratch/section4-*`. Preserve source credits on any ports. Make all changes
locally; pushing requires a new explicit instruction.
