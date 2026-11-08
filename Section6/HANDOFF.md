# Section 6 handoff

The paper-level exports are in [PaperResults.lean](PaperResults.lean).
Both headline types and their axiom audits passed the pinned source check
in `.scratch/section6-paper-results-v1.log`. The algebraic-envelope provider
is `UniformNormalizedElimination.nativeEnvelopes`. The ordinary
nontrivial-valuation interpretation is
`DenefPasHenselianModels.ordinaryRecognition`. Both compile, and the
trivial-valuation Denef–Pas branch uses the checked separate translation.
Use [STATUS.md](STATUS.md) and [STATEMENT-REVIEW.md](STATEMENT-REVIEW.md)
for the current verification and exact scope.

## Earlier checkpoints

November 7 audit. The published Section 6 headlines are conditional on
the displayed preparation, native-envelope and expanded normal-form
interfaces. Corollary 6.5 also takes ordinary recognition for the
nontrivial branch. See [publication audit](../PUBLICATION-AUDIT.md)
and [statement review](STATEMENT-REVIEW.md).

The local repair proves `EnvelopeUniformity.earlierPreparation`.
`RVReductQE.lean` derives the required pure RV definitions from the
pinned sorted QE theorem. `EarlierPreparation.lean` proves the bridge
from Marker's one-variable saturation to finite tuple types and uses
countability of a finitely generated LRV substructure to apply the
checked Section 5 uniform-obstacle theorem. The target and Section 6
library checks both exited zero. `ExpandedNormalForm.lean` proves
the RV normal form from the native envelope. `HenselianRVClosure.lean`
supplies the RV descent inside a pure-characteristic-zero algebraic
envelope, and `PureHenselianInputs.lean` uses it to construct the
earlier RV centre input. The remaining general native-envelope and
ordinary-recognition obligations are separate.

For the next proof, establish the representation of
`HenselianTheory.canonicalHen00`. Start with the recognition of the
actual tagged structure in `DenefPasHenselianModels.nativeStructure`,
including the translation between `henselScheme` and
`HenselianLocalRing`. In the converse direction, extract the field and
valuation from a native model and construct its compatible embedding
into an algebraically closed valued extension. The checked pure
algebraic-envelope adapter supplies the RV centre input once the
valuation, embedding, Galois extension and base image are available.

Updated November 6, 2026. The requested syntactic Lemma 6.3, Proposition
6.4 and Corollary 6.5 are complete within their displayed authorized inputs.
The active entry point is Section6.Library. Earlier sections were accepted
as given, with no QE or earlier-section proof campaign restarted. The author
authorized publishing this Section 6 checkpoint on November 6. Unrelated
workspace edits, including the separate Section 5 work, remain outside it.

## Entry points and scope

- SyntacticLemma63.syntactic_lemma_6_3 constructs the finite occurrence tuple
  and the actual FV existential formula before substructure/RV interpretation.
- UniformNormalizedElimination.eliminate proves the uniform normalized step;
  HenselianElimination.hasVFQE proves full native relative elimination.
- NamedLogic.proposition_6_4 retains the original named base and arbitrary
  free/bound contexts.
- DenefPasTheorem.corollary_6_5, in DenefPasConclusion, chooses one properly
  sorted formula with only RF/Gamma binders over the original arbitrary free
  names. It covers actual pure-characteristic-zero henselian fields with
  angular component, for both valuation branches and genuine sorted
  auxiliary expansions.

The dictionaries, code normalization, trivial branch and sort laws are
constructed. The final theorem assumes no translation dictionary, Canonical
law package or Section6 elimination conclusion. The explicit authorized
inputs remain OrdinaryRecognition, Marker saturated-extension existence,
EarlierPreparation, NativeEnvelopes and earlier RVLiteralNormalForm. Read
INPUTS.md and STATEMENT-REVIEW.md before changing those interfaces. Their
presence must remain visible when reporting the result.

The author's settled convention is `rv(P/Q) = rv(P)/rv(Q)`: occurring
polynomials are the ordinary leaves P and Q, recursively through RV inverse.
Retain denominator guards, zero branches, the single absorbing RV point and
the reversed multiplicative valuation order. Do not add named VF inverse.

## Verification and organization

The final pinned Lake run passed **78 modules / 444 full headline audits**
and the combined ACVF-QE + Section5 + Section6 import. The fresh Library
audit checked the five main headlines and printed all conclusion/hypothesis
definitions alongside the complete 444-headline audit. Compiler exits are 0; headline axioms are confined to propext,
Classical.choice and Quot.sound. STATEMENT-REVIEW.md records the semantic
review separately. These are conditional theorems with the explicit inputs
above, not proofs discharging the standard representation boundaries.

`.scratch/section6-final78-444/` is the immutable final certificate. It holds
exact active sources, logs, full types/axioms, compiled-artifact archive,
provider/cache identities, integration results, native receipts and source
mapping. Sources are the actual repository paths; earlier imports are
attested byte copies, not newly compiled earlier proofs. The certificate
records which modules were freshly checked and which matching checks were
reused. Previous assembled and paused-run evidence remains separate.

The new DP continuation is in DenefPasAlgebra, DenefPasInterpretation,
DenefPasTrivialBranch and DenefPasConclusion; MODULES.md gives the mapping.
The 56 previous helper paths are import-only compatibility files. The
historical Library audit body is also retained by the identity map. Exported
names and theorem statements are unchanged by grouping.

To verify again, run `lake env python3 Section6/verify.py` in the pinned
environment with the earlier compiled interfaces on LEAN_PATH. Optional
SECTION6_BUILD_DIR relocates only the output directory. The exact final
launcher/environment and logs are preserved in .scratch. Before using the
current WSL setup, verify dependency revisions and remote URLs using
`.scratch/preflight-section6-lake.py`; never refresh unchecked dependencies.
An earlier symlinked-QE dependency incident was fully restored and isolated;
`.scratch/section6-dependency-restore.json` records that recovery. No new QE
recovery or proof is needed.

The Section 6 checkpoint was published as commit 4f93a69. The author's
subsequent Section 5 publication supplies its source dependency in this
repository. Those interfaces remain accepted earlier inputs. This
dependency publication changes no Section 6 proof source or theorem scope.

There is no remaining Section6-specific obligation for the three requested
targets within the displayed accepted-input scope. Preserve the author's
unrelated concurrent edits. Any later publication requires a new explicit
instruction. A new session should select its next mathematical target
before expanding the current scope.
