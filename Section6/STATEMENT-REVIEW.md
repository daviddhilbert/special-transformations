# Section 6 statement and hypothesis review

November 6, 2026. This reviews mathematical scope separately from compiler
and axiom evidence; the final pinned Library check passed 78 modules and
444 full headline audits, including the printed hypothesis definitions.
See STATUS.md for the exact evidence.
All names below are under `SpecialTransformations.Section6`.

## Lemma 6.3

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

`NamedLogic.proposition_6_4` proves the defined `NamedLogic.HasVFQE`
property for `HenselianTheory.named E S`. Unfolding that property gives
every arbitrary free-variable type, every finite bound context and every
properly sorted formula an equivalent properly sorted formula with no VF
binders. Original constants for S are opened and reclosed using Mathlib's
actual syntax equivalence. Their sorts come from the original atomic
diagram. No finiteness restriction is imposed on the named base.

The displayed inputs are Marker's genuine saturated elementary-extension
existence, earlier preparation, ordinary native envelopes, and earlier
RV-literal normalization. No one-step or relative-QE premise remains.
The encoded native henselian theory retains nontrivial valuation.

## Corollary 6.5

`DenefPasTheorem.corollary_6_5` chooses one formula before all actual fields,
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

The four preceding standard/earlier inputs remain explicit, specialized
to the constructed relational RV expansion. There is also the authorized
standard `OrdinaryRecognition` input: an actual nontrivially valued
pure-characteristic-zero henselian field with angular component satisfies
the displayed native tagged henselian axioms. It asserts no elimination,
definability or Section 6 conclusion. The trivial branch does not use it.
INPUTS.md records these boundaries; axiom audits do not discharge them.

## Language conventions

The published ACVF-QE language is reused. RV inversion is named and VF
inversion remains unnamed. `rv(P/Q) = rv(P)/rv(Q)` is proved, including
totalized zero cases, in RVQuotients. Ordinary occurring polynomials remain
P and Q, recursively through RV inversion. Rational pole guards remain
separate. RV has a single absorbing zero/infinity, residue units are not
arbitrary nonzero RV classes, and value comparisons reverse Mathlib's
multiplicative valuation order as required by the paper.

The final theorem bodies are in DenefPasConclusion and the ordinary-model
bridge is in DenefPasInterpretation. Their old helper paths are compatibility
imports. Public names and the hypothesis scopes reviewed above are unchanged.
