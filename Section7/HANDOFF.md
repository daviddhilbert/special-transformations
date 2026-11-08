# Section 7 continuation

Updated November 7, 2026. Read root WORKFLOW.md, AGENTS.md and Section3/HANDOFF.md,
then Section7/STATUS.md, TARGETS.md and REUSE-SURVEY.md. Section 3 and QE
must not be restarted. No publication is authorized.

The November 7 Section 5 repair removes the extra real-parameter
surjectivity inputs from both fixed-degree Section 7 headlines. The
objects and maps are definable over `B.real`. Genuine named-Gamma
definability is also covered by the two checked `Section7.Paper` exports
in `GammaScissors.lean`. Both preserve the original named base.
See [STATUS.md](STATUS.md) and the [publication audit](../PUBLICATION-AUDIT.md).

Continue the authorized Section 7 objective across verified checkpoints.
Ordinary multivariate Hensel and both versions of Lemma 7.2 are verified
in the pinned library. Eighteen fresh compilations, 90 headline axiom and
full-type reviews, stable resolved dependencies and the combined ACVF-QE
import passed. The separate fresh project-root check also passed with no
diagnostics. The matching source and evidence snapshot is
`.scratch/section7-hensel-certified/`. The targeted 35-module/137-headline
entry-point audit, full type review and fresh root check also passed;
Definition 7.1's residue projection and Remark 7.5 are verified in that
expansion. Its matching sources and evidence are preserved in
`.scratch/section7-expansion-certified/`. The 41-module/168-headline
checkpoint verifies Lemma 7.4 and the ambient pullback extension of
Definition 7.3. Full type review and the fresh project-root check passed.
Matching evidence is in `.scratch/section7-74-certified/`. The subsequent
47-module/233-headline checkpoint verifies Theorem 7.6 with full type review
and a fresh root import. Matching evidence is in
`.scratch/section7-76-certified/`. The final 53-module/276-headline
checkpoint verifies both Corollary 7.7 statements in the recorded scope.
Full type review and the final project-root check passed. Matching evidence
is in `.scratch/section7-77-certified/`. PLAN.md and TARGETS.md record the
exact route and hypotheses.

The current work replaces the legacy-only Section 7 starting point with
shared-dependency source modules. The numbered Section 7 targets are verified
in the scope recorded in STATUS.md. The source entry point is
`Section7/Library.lean`, registered explicitly in
Lake and imported by the project root. The legacy snapshots remain excluded.

The RV/Jacobian continuation is proved through construction of the ordinary
valuation-ring system with zero residue and unit Jacobian. Eleven fresh
module compilations, 64 headline audits, full type review and the combined
ACVF-QE import passed. The fresh project-root check also passed. The earlier
seven-module checkpoint is preserved separately with matching source.
See STATUS.md for exact evidence for the completed ordinary multivariate
step and full Lemma 7.2.

## Mathematical decisions

`PolynomialPresentation` retains repeated monomials, reflecting the extra
summand index in Definition 7.1. The legacy collected-coefficient predicate
does not support cancellation in the way needed by sums and determinants.
The new definitions use the actual released quotient RV. A fixed value
fibre is not an RV fibre. The encoded bridge uses `CanonicalRV.equiv` and
the actual VF type. There is one absorbing RV element, `none = rv(0)`, and
paper strict increase of valuation is Mathlib strict decrease.

`GammaPolynomial` develops the elementary bound and representative
independence. `PolynomialNormalization` develops the initial normalization
in 7.2, including the normalizing scalar from an actual nonzero polynomial
term instead of ambient value-carrier surjectivity. `EncodedResidueRoots`
transports the statement to the released model's sorts. `LiftRelations`
implements the full-ambient-space instance of 7.3 and its genuine fibre
equivalence. No theorem assumes a Section 7 headline and counts it as proved.

`GammaPolynomialAlgebra` proves derivative closure using repeated summands,
so no integer-unit premise is needed. `JacobianNormalization` proves the
genuine polynomial Jacobian's gamma structure and exact value at all
representatives of a simple common residue root. Its simple-root definition
contains the paper's non-residue-root condition, not the desired value identity.
`SimpleRootNormalization` derives row nonzeroness, chooses common field
representatives and row scalars, and proves simple-root and exact-solution
transport. `IntegralNormalization.lean` exports `exists_integral_simpleRoot_normalization`
in the Section7 namespace, constructing an actual valuation-ring system with
zero residue and a genuine ring-unit Jacobian at the all-one point.

## Verification checkpoint

All ten proof modules and `Library.lean` have passed fresh pinned source
compilation. The 64 exported headline types, defining predicates and explicit
hypotheses were reviewed; their axioms are contained in `propext`,
`Classical.choice`, `Quot.sound`. The full verifier exited zero, including
the resolved-dependency comparison and combined ACVF-QE import. The separate
fresh project-root import check also passed with exit zero and no diagnostics.
STATUS.md records the exact evidence and remaining paper obligations.

WSL connections recovered without intervention. The user lifted the temporary
wait for other Lean checks. Compile independent modules concurrently and
sequence modules that consume each other's compiled outputs. Do not restart
Linux or stop a running proof job.

The focused reuse search found Tau Ceti's actual etale residue-point lifting
proof at catalog revision `e8758b7b2f82b9b1c3f33b992ab8f499b510240f`. The
local Git blob was verified. `Imported/EtaleLifting.lean` ports only the
existence proof using pinned Mathlib APIs, preserving Apache-2.0 notices and
license. `ValuationHenselian.lean` bridges the released monic root-lifting
theorem to the actual henselian valuation ring. Both have passed fresh
compilation, type review and headline axiom audits.
The checked polynomial-system-to-etale presentation discharges the
normalized Hensel step without an assumed `NormalizedHensel` input.

## Verification and next proof

1. Inspect Git status and preserve unrelated edits. Confirm the shared Linux
   environment is accessible. No dependency refresh or toolchain change.
2. Preserve the successful verifier and root-check evidence in
   `.scratch/section7-verified/`; the complete first fresh run, whose axiom
   name parser rejected universe annotations, is preserved separately in
   `.scratch/section7-first-full-run/`. No source theorem failed that run.
3. The portable verifier is `lake env python3 Section7/verify.py`. It freshly
   compiles the active import graph, fingerprints Lean's complete resolved
   earlier compiled closure before/after, audits all 137 current headlines and
   checks ACVF-QE + Section7. It treats earlier compiled mathematics as given, not
   re-certified. Local launchers select the existing attested native copies
   under `/tmp/section6-fast-01a1/v3`; current Section 4 output is selected
   separately for the root compatibility check. Restore inputs from their
   existing evidence if temporary storage is lost; do not accept unbound caches.
4. `HenselHeadlineReview.log` and its receipt record the separately compiled
   full type review. `HenselStatementReview.json` binds the manual scope and
   hypothesis review to source and certificate hashes. The Jacobian-only
   review and earlier certificates remain archived. Preserve the full 7.2
   source and evidence snapshot before another run replaces its output.
5. The etale algebra, residue lift and unramified uniqueness argument are
   implemented and verified. The attributed Tau Ceti port retains its
   license, with the missing tensor-product helper proved locally. No
   adic separatedness, maximal-ideal nilpotence or normalized-Hensel premise
   was used. Do not restart this proof.

The archived surjectivity types retained uniform obstacles and, in the
general variant, dimensional presentation. The November 7 entry-point
check supersedes those types for the categories over `B.real`. The
named-Gamma categories still need full invariant graph and quotient
integration.
