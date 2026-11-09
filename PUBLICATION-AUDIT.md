# Publication audit

## Lean 4.35.0 migration review

The QE package builds with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The fresh QE scope audit checked 13 complete types and axiom reports. The
declaration-wide audit checked 3,998 declarations across all 85 package
modules against the three permitted axioms. The ordinary and RV languages
each have separate trivial and nontrivial valuation results. The audit
unfolded the theories and checked the quantifier order of `HasQE`.

The package removes the old unused C-minimality placeholder. The checked
theorem is in Section 3. The two `ValOneEC` polynomial interfaces retain
their types and use Mathlib's `Polynomial.monic_of_natDegree_le_of_coeff_eq_one`
and `Polynomial.lifts_and_natDegree_eq_and_monic`. These are small adapters
to the existing Mathlib results.

The eleven licensed Section 9 Stacks files were compared with upstream
revision `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` and compiled on the matching
pins. The two index changes restore the upstream calls to Mathlib's
one-based `TFAE.out`. The types and axiom reports of the 04GN existence result
and the 04GS map, locality, and uniqueness were checked. The finite henselian
extension premise used by Section 9 remains a separate Engler–Prestel input.
See [Section 9 status](Section9/STATUS.md).

The QE Lake build recorded 344 warning lines, including module-system,
deprecation, and other linter diagnostics. These warnings are a separate
quality measure from the compiler exit and axiom checks. The review covered
the two reused Mathlib polynomial results and the two imported Stacks tags.
[Kim Morrison's critique](https://kim-em.github.io/blog/2026-11-5-axioms-formalization-of-the-stacks-project/)

## Library through Section 8

The current library imports the active Section 3 through Section 8
entry points. The pinned local audit replayed 12,302 declarations in
680 modules and checked 3,336 full headline types and axiom reports.
The declaration-wide axiom check also passed. The revised Section 6
paper exports construct their representation and saturation inputs.
[Section 6 status](Section6/STATUS.md) and [Section 8 status](Section8/STATUS.md)
record the current verification and scope.

## Historical checkpoint reviewed on November 7, 2026

The audit records the published state independently of local repairs.
Remote branch enumeration on November 7, 2026 identified
[ACVF-QE main](https://github.com/daviddhilbert/ACVF-QE/tree/f3ef4ee679f921079aa8f742a2807a9cc724d2d6)
and
[special-transformations main](https://github.com/daviddhilbert/special-transformations/tree/e4ece39cba56540ef7f2be4fa21b365b640a8c7f).
The paper repository also publishes
[codex/section4-verification](https://github.com/daviddhilbert/special-transformations/tree/93166e6779094bcc85ea3753fefc70e8e220008e).
That revision is an ancestor of main. The remote enumeration returned no tags.
The paper repository pins the named ACVF-QE main revision.

## Findings

### Section 5 claims more coverage than the published theorem types support

The paper's Corollary 5.7 asks for surjectivity on isomorphism classes of
both VF categories under the standing conventions. The published real
theorem takes `UniformVerticalObstacles` and a same-base dimensional
presentation as explicit premises. The finite theorem also takes invariance
of finite RV fibres. The earlier unary obstacle theorem has no uniformly
definable family over complementary VF coordinates. The earlier
dimension theorem has a target allowing the actual Gamma quotient. One
cannot turn its Gamma coordinates into RV representatives by choice and
preserve definability. See
[published CategoryLift](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section5/CategoryLift.lean#L88)
and [published inputs](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section5/INPUTS.md).

The same obstacle premise reaches general Theorems 5.4 and 5.5 and
Corollary 5.6. The named-Gamma variants of these results additionally
take `GammaLogicInput`, `GammaPolynomialSupportInput` and, for existence,
`GammaPresentationInput`. The named-Gamma Corollary 5.7 statements also
take reduction and, for the finite variant, finite-fibre invariance.
These inputs are listed in the published input table. The status and
handoff treated their proof as outside the remaining work, which
overstated paper-level completion. See
[GammaExistence](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section5/GammaExistence.lean#L242)
and [GammaLift](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section5/GammaLift.lean#L184).

The polynomial-support interface quantifies over an arbitrary `Base`,
yet requires all coefficients to lie in its real part. The intended
proof uses a VF coefficient field. Over an empty real base a nonempty
polynomial list cannot meet the published coefficient condition at
even one coefficient index. An empty list cannot control the
parameter-free relation (x = 0). An implementation must supply the
paper's field-base convention or use same-base definable coefficients.

The zero-coordinate issue in Definition 5.1 was disclosed. The literal
strict-radius target can miss the image at the absorbing coordinate.
The published proof replaces the focus by an equivalent nonzero-active
representative and proves equality of maps and inverse maps. That is a
statement reconciliation with a proof, distinct from assuming a needed
existence theorem. See
[published Section 5 status](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section5/STATUS.md).

### Section 6 headlines retain several independent mathematical inputs

The published statement review discloses these. The root README compresses
them into “explicit accepted earlier/standard inputs.” The distinction
matters because an earlier proof can supply a component without supplying
the exact new uniform interface.

| Export | Published boundary |
| --- | --- |
| Lemma 6.2 | A normalized elementary algebraic envelope with exact base image, Galois structure, earlier definable RV lifting and henselian automorphism invariance. The last input is the authorized Engler–Prestel uniqueness consequence. |
| Syntactic Lemma 6.3 | The actual ambient model, compatible valuation, `RVQFDefinitions`, uniform vertical obstacles, base inclusion and `HenselianInputs`. |
| Proposition 6.4 | Genuine saturated elementary-extension existence, `EarlierPreparation`, `NativeEnvelopes` and `RVLiteralNormalForm`. |
| Corollary 6.5 | Those same four interfaces specialized to the relational expansion and `OrdinaryRecognition` for the nontrivially valued branch. The trivial branch is separate. |

`EarlierPreparation` includes both the Section 5 obstacle premise and
same-base quantifier-free definitions in the actual RV reduct.
`NativeEnvelopes` is an algebraic embedding and input-transport
requirement over each native model. `RVLiteralNormalForm` is an interface
for the expanded language, distinct from the checked Section 3 normal
form for the released ACVF language. The publication displays these
conditions separately. They remain theorem premises even with clean
axiom output. See the
[published Section 6 statement review](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section6/STATEMENT-REVIEW.md)
and [input definitions](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section6/INPUTS.md).

### QE's theory definition is stronger than the literal printed list

The RV headline takes no additional mathematical argument. Unfolding
`HasQE` gives one well-sorted quantifier-free formula, chosen before the
model and all sorted free assignments. Unfolding `Axioms.ACVF` matters.
In addition to the tagged sort axioms and named inversion, the theory
includes `repairRV`. This explicitly imposes a nontrivial valuation,
the leading-term equivalence for RV fibres, the addition and negation
links with the residue field, the totalization of residue operations,
and additional group and order compatibility laws.

The printed Definition 2.2 does not explicitly exclude a trivial
valuation. For instance, take an algebraically closed field with the
trivial valuation, take its nonzero multiplicative group for nonabsorbing
RV, take the same field for the residue field, and send each nonzero
element to its own class. All finite values agree and the composite is
the trivial valuation. This meets the printed trivial-valuation case
and fails `axNontrivialRV`. Thus the released QE and the active Theorem
2.8 apply to the encoded nontrivially valued theory. The ordinary-valued
QE README already names nontriviality. The RV headline description
does not spell it out. The precise relationship between the remaining
linkage laws and the intended concrete RV construction should be kept
separate from a claim about the literal printed axioms. See
[paper Definition 2.2 and Theorem 2.3](https://arxiv.org/html/1006.2467v1#S2)
and [published Enc](https://github.com/daviddhilbert/ACVF-QE/blob/f3ef4ee679f921079aa8f742a2807a9cc724d2d6/Proofs/Enc.lean#L1478).

The paper's introduction defines the intended RV sort as the quotient by
`1 + 𝔪` and identifies its residue-field part. Those concrete
definitions justify the linkage axioms. The six clauses alone allow
other interpretations even in pure characteristic zero with a
nontrivial valuation. Starting with the usual RV sort, replace the
map by `x ↦ rv(x)²`. Squaring is surjective on
the divisible nonzero RV group and the induced additive valuation
is doubled. The valuation ring and maximal ideal are unchanged.
The modified map identifies `1` and `−1`, which have distinct
classes in the actual quotient. The author confirmed that clause (6)
should specify `ker(rv : VFˣ → RVˣ) = 1 + 𝔪`. The released
`rvEqLink` implies this kernel condition when its second argument is
`1`. Independently, transporting residue
addition by inversion on the nonzero residue elements preserves the
residue multiplication and algebraic closedness but changes `1 + 1`
from `2` to `1/2`. This violates the residue addition link with
the usual RV map. These are mathematical examples about the literal
list, separate from the intended semantics of the introduction.
[Paper introduction](https://arxiv.org/html/1006.2467v1#S1)
[Local errata](LANGUAGE-ERRATA.md#kernel-of-the-rv-map-in-definition-22)

The author also confirmed that the intended QE coverage is split into
two cases. The published RV headline supplies the nontrivially valued
case. The trivially valued RV case reduces to ACF and is missing as a
separate Lean theorem in the published release. Uniform QE for their
union in the current language would force
the embedding of a trivially valued algebraically closed constant field
in a nontrivially valued model to be elementary. The sentence asserting
valuation nontriviality witnesses the failure. See the
[trivial-valuation scope and example](LANGUAGE-ERRATA.md#trivial-valuations-and-qe).

Definition 2.1 also prints separate symbols for residue zero and RV
infinity. The released encoding uses the project's single absorbing RV
element, `rv(0)`, and the residue-field predicate includes this element
as its zero. The exact QE statement is for that encoding.
[Paper Definition 2.1](https://arxiv.org/html/1006.2467v1#S2)
[Project conventions](AGENTS.md)

The published QE README attributes the omission of inversion to the
Lean transcription. The author clarified that it was a correction to
the explicit inverse-free language in the paper. QE for the named
language is the released result. Downstream results about definability
can use a definable inverse without enlarging same-base definable sets
or closures. See
[published QE README](https://github.com/daviddhilbert/ACVF-QE/blob/f3ef4ee679f921079aa8f742a2807a9cc724d2d6/README.md)
and [local erratum](LANGUAGE-ERRATA.md).

### Section 4 retains an earlier exchange premise at the 4.13 export

The published `lemma_4_13` takes `RVExchangeInput`, uniformly over
arbitrary parameter sets. Section 4 documents that assumption and
contains `rvExchangeInput_of_earlier`, which constructs it from checked
Section 3 RV exchange by finite formula support under the standing
saturation and pure-characteristic-zero conditions. The 4.13 export
itself does not apply the constructor. This is a missing application
at that headline, unlike the absent Section 5 obstacle construction
at publication. The 4.10 and 4.11 headline chains apply the earlier
inputs internally. Canonical-encoding and RV-coded representation
premises in generic Section 4 declarations are supplied for the
actual Gamma quotient by the normalization and coding theorems.
See [published 4.13](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section4/RVFibreInvariance.lean#L45)
and [checked exchange adapter](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section4/EarlierRVInputs.lean#L23).

### Known Section 2–4 changes and publication boundaries

- The active Theorem 2.8 is the Section 3 proof for the published
  ACVF theory. The same-named declaration in QE's `Enc` is the
  separately documented C-minimality placeholder. These declarations
  have different fully qualified names.
- Section 2's guarded rational normal form follows the author's
  documented correction to Definition 2.4. Section 3's published
  handoff excludes all of Remark 3.19 by the author's explicit
  retraction and retains the checked counterexample.
- The unnumbered Section 4 image inequality uses finite-valued
  outputs and their full union, following the author's recorded
  clarification. The dimension files also state their empty-set and
  maximum conventions. Proposition 4.8 and Lemma 4.10 explicitly use
  nonemptiness to compare natural-valued dimension with actual Krull
  dimension. The zero coordinate ring has bottom Krull dimension.
- Lemma 4.11 uses `GammaTop` so it can return infinity when an RV
  coordinate is absorbing. With literal finite Gamma coordinates,
  a positive-dimensional RV set with a fixed absorbing coordinate
  has empty intersection with every such fibre. The Section 4
  status records that its theorem includes the absorbing case.
- Section 6 has a separate local verification certificate. The
  published default root and workflow cover QE and Sections 3–5.
  Passing that workflow is not evidence of a Section 6 verifier run.
- No active Section 7 library or Corollary 7.7 proof is present in
  the reviewed public refs. The pushed Section 7–10 material is
  historical source, with scope determined by the legacy inventory.

## Audit evidence and limits

The source inventory was taken from Git objects rather than the dirty
worktrees. It enumerated every file, its SHA-256 and every Lean source
under each live ref. The source scan found 12 placeholder tokens in
682 Lean files at the paper main revision, all outside the combined
default root and Section 6 closure of 538 local Lean modules. It found
the same 12 on the Section 4 branch, all outside that branch's default
root closure. It found one placeholder in 81 QE Lean files, the
disclosed `Enc` C-minimality declaration.

The source inventory and numbered headline locations are in
`.scratch/publication-audit-20261107/`. Source scans classify
placeholder locations. They do not determine theorem dependence or
validate the mathematical meaning of theorem hypotheses. The
published and saved full-type and axiom records are separate evidence.
The saved Section 5 and Section 6 source snapshots match the published
Git blobs for all 28 and 134 snapshot Lean files respectively, allowing
the Windows line-ending conversion. The 134 Section 6 files include
compatibility imports. The Section 6 proof certificate covers 78 active
modules. The published source hashes match all 197 Section 3 and
234 Section 4 modules in their checked library records. Section 3
records two generated consumer files separately.
The published QE, Section 3 and Section 4 axiom records and the
matched local Section 5 and Section 6 logs contain 7, 1,393, 967, 282
and 444 axiom reports respectively. All reported axioms are among
`propext`, `Classical.choice`, and `Quot.sound`. The axiom transcript
checks reuse the recorded proof evidence for the published revisions.
A fresh pinned consumer check imported the QE library and printed the
types and axioms of all four public QE headlines, plus the definitions
of `HasQE`, `ACVF`, `ACVFpaper` and `repairRV`. It exited zero and
all four axiom lists were permitted. This check used existing compiled
dependencies. The standalone QE publication recorded a fresh root and
combined import with verified reuse. The paper repository's CI prepares
the sibling module registrations before its clean build.

This review concerns the current published trees and the distinct
Section 4 branch. Superseded historical work was classified by its
publication and import status. A theorem-by-theorem replay of each
historical commit is outside that review.

## Local follow-up before the Section 8 checkpoint

The two local checkouts now record the kernel condition and separate
QE cases. The local kernel identity and its elementwise criterion both
passed Lean's full type and axiom checks in
`.scratch/section5-repair-qe-rv-kernel-v2.log`.
The local QE checkout retains the C-minimality definitions
and removes the unused placeholder. The focused encoding check and a
fresh consumer check of the four released QE headlines exited zero.
The consumer check used the changed encoding and the pinned compiled
proof dependencies. The checked C-minimality theorem remains in
Section 3 of the paper repository.

The local QE checkout now also contains a checked separate theorem for
the canonical RV structure of a trivially valued algebraically closed
field in every characteristic. The proof interprets the two sorts in
the field, uses the checked ACF theorem, and translates the resulting
quantifier-free formula into the corrected RV language. Its headline
and axiom audit are in `.scratch/section5-repair-trivial-qe-standalone.log`.
The separate ordinary trivially valued theory has both bounded and
formula QE in the ring language with comparison. The common sentence
theory of the canonical trivial RV models also satisfies `HasQE`.
The combined QE entry point check exited zero in
`.scratch/section5-repair-qe-final-root.log`.
The revised Lemma 4.13 applies checked Section 3 RV exchange in its
proof. Its fresh type and axiom check is in
`.scratch/section5-repair-paper-4-13-audit.log`.

The real-parameter Corollaries 5.7 and 7.7 are checked locally in both
the general and finite forms, using the actual Gamma quotient for
VF dimension. Corollary 5.7 constructs the three witnesses previously
assumed in the published statements. See
[Section 5 status](Section5/STATUS.md) and [Section 7 status](Section7/STATUS.md)
for the separate scope involving named Gamma parameters.
Both named-Gamma forms of Corollary 5.7 also have checked proofs,
with the result and isomorphism definable over the original named base.
Both named-Gamma forms of Corollary 7.7 use those results and the
original-base lift of an RV isomorphism. Their full types, 277 permitted
axiom reports, and successful library and project exits are in
`.scratch/section5-repair-gamma-scissors-source.log`.

Section 6 now has checked proofs of both parts of `EarlierPreparation`.
The Section 6 library check confirms the pure RV reduct definition
theorem and the construction of the uniform obstacle input. The
pure-characteristic-zero form of Lemma 6.2 now also constructs the RV
descent inside the algebraic envelope. The RV literal normal form
follows from the native envelopes and the revised 6.4 and 6.5 wrappers
use it internally. General native-envelope construction and
ordinary-model recognition remain open. The revised Section 6
library and combined import passed with 450 permitted axiom
reports in `.scratch/section5-repair-section6-final-library.log`.
