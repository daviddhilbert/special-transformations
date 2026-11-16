# Section 10 status

The target is [Section 10 of arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1#page=27),
with the author's finite-volume `RV[n]` and `VF[n]` scope. The two legacy
proof files and the scaffold remain historical material.

| Paper target | Current scope |
| --- | --- |
| Definitions 10.1 and 10.3 | The [VF](MeasuredVFCategory.lean) and [RV](MeasuredRVCategory.lean) groupoids are implemented in positive degree. The [graded categories](GradedCategories.lean) now retain actual forms in degree zero for both scales, including neutral forms. [WeightedZero](WeightedZero.lean) keeps the full ordinary VF zero presentations and exact form-preserving bijections. |
| Remark 10.2 | [Almost-everywhere agreement](EssentialVFGerms.lean) is equivalent to equality on independent VF tuples. [The quotient](MeasuredVFCategory.lean) is equivalent to the type of measured germs. Identity, composition and inversion use [actual chart Jacobians](EssentialVFMeasure.lean). |
| Theorem 10.4 | Both positive-degree cases, [RV-valued](RVVolumeSurjectivity.lean) and [Gamma-valued](GammaVolumeSurjectivity.lean), pass the pinned checks. The positive [constant-volume](UnitVolume.lean) specializations and both [weighted degree-zero](WeightedZeroResults.lean) variants are checked; [ordinary zero](ZeroDegree.lean) remains separate. |
| Theorem 10.5 | Both positive-degree cases, [RV-valued](RVVolumeRepresentative.lean) and [Gamma-valued](GammaVolumeLift.lean), pass the pinned checks. They preserve the given label map and satisfy the measure equation on the actual restricted VF chart. They apply to the constant-volume subcategories. Both [weighted zero cases](WeightedZeroResults.lean) retain exact weights and the supplied label map; the old [ordinary zero](ZeroDegree.lean) result is preserved. |
| Corollary 10.6 | The [RV-valued and Gamma-valued additive lifts](MeasuredPositiveLift.lean) preserve the class of every generator and are surjective. The positive [constant-volume](UnitVolume.lean) variants and both [weighted zero](WeightedZeroResults.lean) additive lifts are checked; [ordinary zero](ZeroDegree.lean) remains separate. |

Both cases of 10.5 use the released ACVF language, the paper's
pure-characteristic-zero setting through `BaseContext`, and the explicit
`VFGammaGeneratedBase` condition on the original parameter base. Both
volume maps are finite-to-one. The essential RV isomorphism is between
the parts whose volume tuples have no absorbing coordinate. The VF
representative has complements of dimension strictly below the degree
`k + 1` in the full source and target lifts. Its measure equation uses
the determinant on its own fixed-label VF chart.

The RV form takes values in nonzero RV. Its input isomorphism satisfies
both the pointwise Gamma condition and the actual Section 9 RV Jacobian
condition outside a definable RV-small set. The only external premise is
the authorized `FiniteHenselianExtensionReference`. It supplies
henselianity of a finite extension and equality of residue and field
degrees for an unchanged value group in residue characteristic zero.
The Section 9 adapter constructs the graph-field input to 9.16 from
this premise.

The Gamma form is a definable map into the actual Gamma imaginary,
presented by all nonzero RV codes. Its input isomorphism satisfies the
pointwise Gamma condition. Its proof uses the checked weighted lift and
the definable product-value test, with no external mathematical premise.
Both cases use [EssentialVFMap.lean](EssentialVFMap.lean) to transfer
the Jacobian across a restriction to the complement of the closure of
the exceptional VF projection.

For Remark 10.2, the independent tuples are taken over the VF parameter
field of the original small base. Agreement on these tuples is equivalent
to agreement on a same-base definable set with VF-small complement. The
VF groupoid uses the measured representative on each actual composable
overlap. After applying Lemma 9.12, it restricts away from the closure of
the exceptional VF projection. The RV groupoids use the pointwise Gamma
equation and the checked RV chain rule on a definable RV co-small locus.

For Corollary 10.6, [MeasuredScissors](MeasuredScissors.lean) defines the
positive additive presentations using measured isomorphisms, the empty
object and restrictions of the same form. Lift preserves all three
relations. Theorem 10.4 gives a preimage for every VF generator and
Theorem 10.5 gives invariance under the source isomorphisms. The RV-valued
lift retains `FiniteHenselianExtensionReference` from 10.5. The Gamma
lift has no external mathematical premise. The constant-volume proofs
restrict the forms to their neutral values and reuse the same lift.

## Corrected measured degree zero

The author-approved [erratum](WEIGHTED-ZERO-ERRATUM.md) replaces the
unweighted exceptions in Definitions 10.1 and 10.3. The six new modules
retain actual same-base RV or Gamma forms and total exact weight-preserving
bijections. VF zero objects retain arbitrary mixed presentations of the
ordinary dimension-zero category. No nonempty locus is discarded. The
existing positive-degree APIs and their hypotheses are preserved.

`theorem_10_4_rv_zero` and `theorem_10_4_gamma_zero` transport the actual
form through the checked ordinary finite lift presentation. Their concrete
wrappers retain `BaseContext`, including pure characteristic zero, genuine
saturation and smallness. The generic `theorem_10_4_weighted_zero` states
these assumptions explicitly for an arbitrary form scale and small real
base. It introduces no paper-specific reference premise.

`theorem_10_5_rv_zero` and `theorem_10_5_gamma_zero` use the total lifted
bijection `MeasuredRVZero.liftMap`. `liftMap_labels` preserves the supplied
label map and `liftMap_measure` checks determinant one at every point.
These elementary zero results require only the canonical ACVF structure
and the supplied same-base objects/isomorphism. They need no saturation,
generation or finite-extension reference beyond those already in an input
object. The positive RV results retain `FiniteHenselianExtensionReference`.

`MeasuredRVZero.liftHom_generator` identifies every actual weighted
lift generator. `corollary_10_6_rv_zero` and `corollary_10_6_gamma_zero`
prove surjectivity after weighted isomorphism, empty and same-form scissors
relations. The generic result also applies to `VolumeScale.unit`.
Neutral embeddings recover ordinary **isomorphisms**; ordinary
noninvertible maps are not made into measured arrows. Every neutral-form
zero object is isomorphic to the neutral embedding of its own underlying
object. Gamma neutral weight is multiplicative one.

`ZeroForm.rvProduct_weight` and `ZeroForm.gammaProduct_weight` retain both
pointwise factors on arbitrary definable domains, including zero-degree
factors. `gammaZeroForm_weight_eq_iff` identifies represented-weight
equality with exact Gamma equality. No Gamma-to-RV section is assumed.

## Verification

The weighted-zero change was checked locally on November 15, 2026,
starting at published main `f76d100e07c0a791259244fc7fdf06f4dfaaf8ae`,
with its exact Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and ACVF-QE
`939346b0a99899e22a873479364e3cc5d142731c` pins. The complete
`lake -R build Section10` exited 0. The Section 10 verifier exited 0
for all **68** paired headline types and axiom reports. Every axiom set
is contained in `{propext, Classical.choice, Quot.sound}`. The parser now
accepts Lean's omission of `@` for declarations without implicit parameters;
it still requires every selected type and exact axiom coverage.

The additional `.scratch/weighted-zero/FullTypes.lean` check exited 0.
Its log expands the actual object/arrow definitions and fully explicit
weighted theorem types, including the concrete RV/Gamma additive maps.
Source/hypothesis review confirms the full ordinary zero VF family,
nonzero RV forms, exact Gamma equality, total zero isomorphisms, actual
label preservation and both product densities. No open mathematical
obligation is supplied as a theorem hypothesis.

Evidence: `.scratch/weighted-zero/verification.json`,
`section10-build.log`, `FullTypes.log`, and
`.scratch/section10-verified/{HeadlineAudit.log,headlines.json,status.txt}`.
The project-root `lake -R build` also exited 0 (10,042 jobs), including
`Section10.Library` and `SpecialTransformations`. It reuses the just-built
Section 10 artifacts with matching sources; uncached earlier modules were
compiled in this root build. This is an integration build, not a new full
mathematical audit of unchanged earlier sections. Existing import/module
style, tactic and deprecation warnings remain; no compiler error or proof
placeholder occurs in the passing checks. The historical evidence below
concerns earlier types.


The standalone `lake -R build Section10` and headline audit passed with
Lean 4.35.0 on November 9, 2026. All 29 printed types match the Lean
4.33.1 output up to whitespace. Every report lists `propext`,
`Classical.choice` and `Quot.sound`.
[Verified checkpoint](https://github.com/daviddhilbert/special-transformations/commit/7f2e697c8cfcb2702504f78ef3cc79289f040179),
[Actions run](https://github.com/daviddhilbert/special-transformations/actions/runs/42738182685),
[verification artifact](https://github.com/daviddhilbert/special-transformations/actions/runs/42738182685/artifacts/13728552237).

`SpecialTransformations.lean` imports `Section10.Library`, and the full
project workflow includes the Section 10 audit. The local evidence below
comes from the original Lean 4.33.1 checkout.

The final local check of `Section10/Library.lean` through pinned
`lake env lean` exited 0. All 18 active Section 10 modules have matching
source and artifact fingerprints. The final log prints the full types
and axiom reports for 29 declarations. Every report lists exactly
`propext`, `Classical.choice` and `Quot.sound`. The type review checked
the same-base finite-volume objects, the original label map in both
positive-degree 10.5 conclusions, the equivalence of measured germs with
the quotient by almost-everywhere agreement, and the generator and
surjectivity statements for the additive lifts. The unmeasured
degree-zero statements keep the normalized model, saturation and
smallness hypotheses of the Section 5 and 7 results they specialize.

The final evidence is in `.scratch/section10/Library-local.log`,
`Library-local.exit` and `section10-local-audit.json`. The individual
`*-local.exit` and `*-local.sha256` receipts record the fresh source
checks. The earlier checks below supply the fingerprints for the five
unchanged proof modules reused in the final run.

Both cases of 10.4 start with a same-base definable set with `k + 1` VF
coordinates and finite RV fibres. They construct a finite-volume RV
object and an essential VF bijection to its lift. The shared proof
constructs a representative with Jacobian one. The RV form is nonzero.
The Gamma form uses the imaginary presentation, and
`RVPreparationData.lean` determines its graph by a finite same-base RV
tuple. The two statements retain `BaseContext`, `CharZero`, canonicality
and the paper's `VFGammaGeneratedBase` scope. Neither needs an external
reference hypothesis.

Fresh Linux checks through pinned `lake env` compiled
`RVPreparationData.lean`, the refactored `RVVolumeSurjectivity.lean`,
`GammaVolumeSurjectivity.lean`, and `Section10/Library.lean`. Each exited
0. The library printed the full types of both 10.4 headlines and reported
`[propext, Classical.choice, Quot.sound]` for each. The `*-gamma.log` and
`*-gamma.exit` files and `theorem-104-gamma-fingerprints.sha256` are in
`.scratch/section10/`. The earlier standalone RV check and its Section 5
prerequisite are recorded in the `*-linux` receipts.

`Section10.Library` is the active entry point of the `Section10` Lake
target. Fresh pinned `lake env` source checks ran
`lean -j 1 -DElab.async=false -o …` on `EssentialVFMap.lean`,
`RVVolumeRepresentative.lean`, `GammaVolumeLift.lean` and
`Library.lean`. All four exited 0. The library imported both theorem
modules and printed the full types and axioms for the two Theorem 10.5
statements, their restriction and Gamma locus helpers, and the earlier
almost-everywhere RV theorem. Each axiom list is exactly
`[propext, Classical.choice, Quot.sound]`. The type and source review
checked the two small complements, same-base bijection, original label
graph, the pointwise volume laws, and the explicit hypotheses above.

The checks used Lean 4.33.1 (compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and ACVF-QE
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`. Linux recovered briefly
and the proofs were checked in an isolated Windows Lake project with
the same pins after further Linux timeouts. The Mathlib umbrella
artifact matches the pinned Linux cache hash. All 513 restored project
providers matched the earlier source and artifact records. The
already source-checked Linux builds of `RVVolumeLift.lean` and
`WeightedJacobianLocus.lean` were reused with matching fingerprints.

The local evidence is under `.scratch/section10/windows/` in
`Library.log` (full type and axiom output), the individual compiler logs
and exit-code files, `provider-check-final.log` and
`final-fingerprints.sha256`. The earlier Linux proof receipts are under
`.scratch/section10/` in `RVVolumeLift.log` and
`WeightedJacobianLocus.log`, with their respective exit-code files.

See [handoff](HANDOFF.md) for the proof routes and
[reuse survey](REUSE-SURVEY.md) for the source audit.
