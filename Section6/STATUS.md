# Section 6 status

Updated November 6, 2026 (America/Los_Angeles). The requested syntactic
Lemma 6.3, Proposition 6.4 and Corollary 6.5 are proved and integrated with
the explicit authorized earlier and standard-reference inputs below.
Earlier sections are accepted as given and were not rederived. The author
authorized committing and pushing this Section 6 checkpoint on November 6.
Unrelated workspace edits are outside this publication.

## Current proof scope

- `syntactic_lemma_6_3` in SyntacticLemma63 constructs the actual finite
  ordinary-polynomial occurrence tuple and an existential FV formula over
  arbitrary original parameter names. The output is chosen before the
  substructure and its arbitrary RV interpretation.
- `UniformNormalizedElimination.eliminate` constructs one formula across
  the henselian models for normalized finite input, retaining free VF
  parameters. Common envelopes and their comparisons are proved using the
  pinned ACVF-QE dependency and the displayed earlier/standard inputs.
- `HenselianElimination.hasVFQE` proves the one-step interface and extends
  it to all formulas. `NamedLogic.proposition_6_4` opens and recloses the
  original named base, retaining arbitrary free and bound contexts.
- `DenefPasTheorem.corollary_6_5` handles actual pure-characteristic-zero
  henselian valued fields with angular component, including trivial and
  nontrivial valuations. One output formula retains arbitrary original
  free names, is properly sorted, and has only RF/Gamma binders.

The forward/return dictionaries, RV pair-code normalization, polynomial
leaves, finite-support restriction, original-parameter substitution,
trivial-valuation branch and proper-sort normalization are constructed.
`AuxiliaryStructure` supplies ordinary typed functions and relations.
Their tagged interpretation and all DP sort laws are proved. Neither a
translation dictionary nor `Canonical` nor a QE conclusion is assumed by
the final theorem.

The explicit mathematical inputs are `OrdinaryRecognition`, Marker's
genuine saturated elementary-extension existence, `EarlierPreparation`,
`NativeEnvelopes`, and earlier `RVLiteralNormalForm`. INPUTS.md and
STATEMENT-REVIEW.md display their exact scopes. In particular ordinary
henselian fields' recognition as models of the tagged theory remains an
authorized standard representation hypothesis. An axiom audit does not
discharge any explicit theorem hypothesis.

## Final verification

The pinned Lake verification passed: **78 source modules, 444 full
headline type/axiom audits, and the combined ACVF-QE + Section5 + Section6
import**, compiler exit 0. This is the actual library import graph, not
an assembled-source substitute. Matching checked dependencies were reused;
the consolidated modules, named-base wrapper, final Library and combined
import were checked from their actual source paths. No earlier source was
rebuilt.

The fresh Library audit includes the full types and axioms of syntactic
6.3, henselian VF-QE, named 6.4, DP 6.5 and `rv_division`, together with
the printed conclusion and hypothesis definitions. Its compiler exit is 0.
All headline axioms lie in `propext`, `Classical.choice`, `Quot.sound`.
The statement/hypothesis review is recorded separately in
STATEMENT-REVIEW.md.

The immutable certificate is `.scratch/section6-final78-444/`. It retains
exact sources, compiler logs, full type/axiom output, compiled artifacts,
source/cache/provider identities, native-build and transport receipts,
integration evidence and the fragment-to-module identity map. The earlier
inputs are byte-identical attested copies; their identities were checked
again at closure. The 56 old helper paths are compatibility imports and
are outside the 78-module active graph.

Historical certificates remain separate: assembled444 checked a frozen
assembled continuation; checkpoint61 checked 15 modules/61 headlines; the
old 73-module/211-headline run and fragment-by-fragment run were intentionally
stopped for Section5 priority. Those incomplete runs are superseded by
the final integrated certificate and are not counted as passed runs.

## Fixed conventions and exclusions

Definition 2.4 does not change occurring polynomials:
`rv(P/Q) = rv(P)/rv(Q)`. RVTermSupport recursively collects ordinary
polynomial leaves through RV inversion, including both P and Q. Pole guards
and zero branches are retained. VF inversion remains unnamed. RV has one
absorbing zero/infinity; residue units are distinguished from arbitrary
nonzero RV classes. Value comparisons respect the reversed multiplicative
valuation order.

Lean is 4.33.1; Mathlib is
`0df444a360eaa60ab8c11dca51a86af692955474`; ACVF-QE is
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`. No pins were upgraded.
Legacy Sec6.lean, Sec6QE.lean and the unselected PolynomialNormalForm.lean
draft are outside this certificate.

## Publication boundary

This Section 6 commit does not include the separately maintained Section 5
work. Reproducing the recorded verification requires its accepted compiled
interfaces on the import path, or its separately published sources.
