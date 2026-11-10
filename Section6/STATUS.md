# Section 6 status

## Paper results

On November 7, 2026, the pinned Lean source check of
[PaperResults.lean](PaperResults.lean) passed with exit zero. The full types
of `Section6.Paper.proposition_6_4` and `Section6.Paper.corollary_6_5`
contain the paper's named-base and ordinary henselian assumptions,
respectively. Both axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The source check and headline
output are in `.scratch/section6-paper-results-v1.log`. The revised
`Section6.Library` compiled with exit zero and 481 permitted-axiom
reports in `.scratch/section6-final-library.log`. This checked the new
sources and the library entry point in the pinned environment, with
matching earlier compiled imports reused. The combined library check
through Section 8 passed in `.scratch/section-through8-audit-v3.log`.
The kernel replay and provider identities are recorded in
`.scratch/section-through8-audit-evidence.json`.

The named theorem allows arbitrary RV-only added symbols and keeps every
original constant. The Denef–Pas theorem allows arbitrary sorted
auxiliary symbols, chooses its formula before the valued field and
interpretation, and covers trivial and nontrivial valuations. It uses
the actual henselian valuation ring, field and residue characteristic
zero, and an angular component. The extra preparation, expanded
normal-form, saturation, algebraic-envelope and ordinary-recognition
inputs of the earlier wrappers are supplied by proofs.

The standalone Lemma 6.2 already takes the ambient ACVF model and the
henselian substructure as given. Its additional input is an elementary
algebraic envelope inside the ambient model, corresponding to the algebraic
closure of the substructure's valued field there. The proof uses finite
Galois orbits in that algebraic part to descend definable elements.
Corollary 3.14 proves that the model-theoretic algebraic closure is an
elementary submodel. The remaining connection for the standalone export
is to use that result and identify the inherited valued-field and RV
structures with the inputs to the descent proof.

The same algebraic-closure argument applies when starting with a
henselian field on its own. In the quantifier elimination proof, no
ambient ACVF model is given. The native construction extends the field
and valuation to an algebraic closure and supplies the envelope there.

`NativePresentation` recovers the concrete valued field and RV quotient
from the native model. `NativeEnvelopeConstruction` extends the valuation
to an algebraic closure, using the proved valuation invariance there.
`DenefPasRecognition` identifies the angular-component interpretation with
the concrete henselian model. `ElementaryAmalgam` and `CountableEnvelope`
use the pinned countable saturation theorem. The separate provider checks
are recorded in `.scratch/section6-native-presentation-v6.log`,
`.scratch/section6-native-envelope-v1.log`,
`.scratch/section6-recognition-v2.log` and
`.scratch/section6-countable-integration.log`.

## Earlier checkpoints

November 7 local repair. The verified `EnvelopeUniformity.earlierPreparation`
now supplies both previously assumed parts. `RVReductQE.lean` obtains
RV-only quantifier-free definitions over the original substructure.
`EarlierPreparation.lean` derives uniform vertical obstacles using
genuine small-parameter saturation and the repaired Section 5 theorem.
The pinned target and `Section6.Library` checks exited zero. The latter
prints the full types and permitted axioms in
`.scratch/section5-repair-section6-preparation-root.log`.
Syntactic Lemma 6.3 keeps the henselian-substructure input.
Proposition 6.4 and Corollary 6.5 use the proved preparation and
display their remaining inputs.
For Lemma 6.2, `Section6.Paper.lemma_6_2_of_algebraic_envelope` proves
functional closure over the original base. Averaging the finite Galois
orbit of an RV representative supplies the descent inside the pure
characteristic zero envelope. The theorem retains the algebraic envelope
and the authorized henselian valuation invariance. Its full type and
permitted axioms passed in
`.scratch/section5-repair-section6-henselian-rv-source-v2.log`.
The checked `ExpandedNormalForm` proof derives the RV literal normal
form from the native envelopes. Its source and full type/axiom audit
passed in `.scratch/section5-repair-section6-expanded-normal-source.log`.
The revised 6.4 and 6.5 wrappers use this proof internally. General
native-envelope construction and ordinary recognition remain open.
The final source, Section 6 library, and combined ACVF-QE, Section 5
and Section 6 import checks exited zero. The full revised types and
450 permitted axiom reports are in
`.scratch/section5-repair-section6-final-library.log`.
The publication record below describes the earlier conditional snapshot.

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

The Section 6 checkpoint was published separately as commit 4f93a69. The
author subsequently authorized publishing Section 5 in the same repository,
supplying the source dependency for this library. Its mathematics remains
an accepted earlier input; the Section 6 proof sources are unchanged.
