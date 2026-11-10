# Section 6 statement and hypothesis review

Updated November 10, 2026. This reviews mathematical scope separately from compiler
and axiom evidence. See [STATUS.md](STATUS.md) for the current verification.
All names below are under `SpecialTransformations.Section6`.

## Lemma 6.2

The November 10 standalone `Paper.lemma_6_2` takes the ambient
ACVF(0,0) model, the substructure and its actual VF subfield, and the
valuation compatible with the ambient comparison. The inherited
valuation is nontrivial and henselian, and every RV element of the
substructure has a representative in its field. The conclusion is
functional closure over the substructure in the normalized ambient
model. The valued algebraic closure, elementary embedding, Galois
property and henselian valuation invariance are supplied by the proof.

## Lemma 6.3

The November 10 standalone `Paper.lemma_6_3` starts with an arbitrary
well-sorted VF-quantifier-free formula with finitely many original free
VF and RV variables and a finite VF tuple to eliminate. It chooses one
equivalent formula with only RV quantifiers before the model and sorted
assignments. It uses the same preparation and native envelopes as 6.4.

### Lower-level statements

`syntactic_lemma_6_3` in SyntacticLemma63.lean starts with an actual
RV-fragment formula, arbitrary original VF/RV base names, a finite tuple of
existential VF variables, and arbitrary remaining RV names. It constructs
an actual formula with an `RVQuantified` syntax witness. That formula is
chosen before the henselian substructure and its arbitrary extra RV
interpretation. The left side binds the actual original FV tuple; an
empty polynomial-occurrence list does not erase the prepared graph domain.

This local theorem fixes the ambient ACVF(0,0) model and compatible actual
valuation. It displays earlier RV QF definitions and vertical obstacles,
base inclusion, and `HenselianInputs` explicitly. The model-uniform step
is constructed separately in `UniformNormalizedElimination.eliminate`,
then generalized by `HenselianElimination.finite_oneStep` and `hasVFQE`.
Free VF parameters are retained in that uniform statement.

## Proposition 6.4

`Paper.proposition_6_4` proves the defined `NamedLogic.HasVFQE`
property for `HenselianTheory.named E S`. Unfolding that property gives
every arbitrary free-variable type, every finite bound context and every
properly sorted formula an equivalent properly sorted formula with no VF
binders. Original constants for S are opened and reclosed using Mathlib's
actual syntax equivalence. Their sorts come from the original atomic
diagram. No finiteness restriction is imposed on the named base.

The encoded native theory uses the paper's nontrivially valued named
setting. Canonical values on wrongly sorted tuples implement the
many-sorted presentation. The proof constructs the algebraic envelope,
ordinary henselian valuation-ring interpretation, countable elementary
comparison, earlier preparation and expanded literal normal form.

## Corollary 6.5

`Paper.corollary_6_5` chooses one formula before all actual fields,
valuations, angular components, sorted auxiliary interpretations and
original free assignments. Its field and actual residue field have
characteristic zero; its valuation ring satisfies Mathlib's
`HenselianLocalRing`. Both trivial and nontrivial valuations are covered.
Gamma is the actual valuation-image group with its infinity point.

The conclusion includes `WellSorted` for every term and atom and
`IsFieldQF`, whose only binder constructors are RF and Gamma. The output
uses exactly the original free-variable type, without a finite-type
restriction. `AuxiliaryStructure` consists only of ordinary symbol maps
between the declared auxiliary sorts and relations on those products.
Its interpretation and all primitive sort laws are constructed. Neither a
DP dictionary nor `Canonical` nor an elimination statement is assumed.

The nontrivial branch uses the proved identification of the
angular-component splitting with the concrete leading-term model and its
henselian axioms. The trivial branch uses the separate formula translation.
[INPUTS.md](INPUTS.md) records which earlier proofs are used.

## Language conventions

The published ACVF-QE language is reused. RV inversion is named and VF
inversion remains unnamed. `rv(P/Q) = rv(P)/rv(Q)` is proved, including
totalized zero cases, in RVQuotients. Ordinary occurring polynomials remain
P and Q, recursively through RV inversion. Rational pole guards remain
separate. RV has a single absorbing zero/infinity, residue units are not
arbitrary nonzero RV classes, and value comparisons reverse Mathlib's
multiplicative valuation order as required by the paper.

The final exports are in [PaperResults.lean](PaperResults.lean).
The earlier elimination and translation statements remain available as
helpers with their explicit interfaces.
