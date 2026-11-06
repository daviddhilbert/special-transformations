# Section 4 status

Updated November 6, 2026. The active [library](Library.lean) formalizes
Section 4 of arXiv:1006.2467v1, including its unnumbered dimension,
Grothendieck-construction, and padding assertions. Sections 2--3 are
completed in their approved scope and supplied as checked imports. The
precise interfaces are in [INPUTS.md](INPUTS.md).

## Verification

The publication audit passed against completed Section 3 from publication
base `9ee0027`. It covers 234 active Section 4 modules and 967 distinct
headline declarations. All final compiler checks exited zero. Complete
headline types and explicit hypotheses were reviewed separately from the
axiom checks. Every headline uses only `propext`, `Classical.choice`, and
`Quot.sound` (or a subset).

The audit matched the current compiled Section 3 providers to its successful
compiler receipts and published sources. It then rechecked all Section 4
mathematical declarations with Lean's kernel replay against that completed boundary,
preserving the actual prior source-compilation records. The replay rejects
own axioms, explicit unsafe/partial source declarations, unexpected unsafe or
partial constants, and non-identical preloaded declarations. An already loaded
theorem is reused only when its full type, proof, universe parameters and
mutual-theorem group are identical. Generated executable
`_unsafe_rec` helpers are excluded only when their safe parent is present;
all mathematical declarations must kernel-check without those helpers.
The final run used a temporary Linux copy of the publication project, with
all 653 source and support files matched byte for byte. Its actual exit-zero
compiler evidence was preserved without rewriting recorded native paths.
The local run used byte-checked, read-only native import replicas to avoid
mounted-file failures. Individual artifact aliases were restored as ordinary
files with identical contents after verification. No native input was modified.
The library entry point, complete headline audit, combined released-QE import,
and published `SpecialTransformations.lean` root were checked afresh. The
published root imports QE and Sections 3--4.

The prior verifier's source-only earlier-section cache key was insufficient
for this audit. The public verifier now records Lean's actual resolved
compiled provider closure and hashes all present module parts and interpreter
code. Reuse also binds source, own compiled dependencies, lookup order,
compiler, pins, verifier, outputs, logs and any kernel-replay evidence. The
four cache-provenance regression tests pass. Earlier sections are not
re-proved by this Section 4 verifier.

The full-type review is linked to the inspected checkpoint by unchanged
serialized declaration types and successful kernel replay; no new display
variant is marked inspected automatically. Counts and identities are in the
curated [publication audit](verification/AUDIT.json), with the method and
reproduction commands in [verification/README.md](verification/README.md).
Raw logs, provider manifests and generated harnesses remain under `.scratch/`.
The static inventory and dependency planner are separate from compiler evidence.

The unchanged pins are Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and ACVF-QE
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.

## Mathematical coverage

| Targets | Checked content |
| --- | --- |
| 4.1--4.2 | Least finite-to-one dimension witnesses, attainment, and the injective characterization, including actual Gamma coordinates. |
| 4.3--4.5 | Fibre maximum, actual VF field transcendence degree, and the full finite-valued relation image inequality. |
| 4.6--4.8 | Open polydiscs, the RV-polydisc bound, parameter invariance, and actual coordinate-ring Krull dimension and Zariski closure. |
| 4.9 | RV algebraic-closure matroid, coordinate bases, attained maximal rank, finitary images, and parameter invariance. |
| 4.10 | Exact-base residue interpretation, field/RV algebraicity, tuple rank, normalization, and actual Krull/Zariski dimension. |
| 4.11 | An original-base definable value tuple whose full RV fibre has the original RV dimension, including absorbing coordinates. |
| 4.12--4.14 | RV-fibre dimension, its finite-fibre criterion and bijection invariance, VF categories, and their alternative finite-map characterizations. |
| 4.15--4.17 | Weight, both RV categories and morphism conditions, finite graded families, coproducts, and full and faithful padding with injective object maps. |
| 4.18--4.20 | Canonical lifts, category membership, finite graded lifts and bounds, padding compatibility, the volumetric commuting-lift criterion, and its bijective variant. |
| 4.21 | Actual products and units, both VF and both graded RV positive commutative semirings, and their ring completions. |
| 4.22--4.23 | Additive and semiring congruences and the commutative-semiring congruence criterion. |
| Unnumbered constructions | Positive scissor quotients and actual isomorphism classes, groupification and universal properties, bounded completions and exhaustive multiplicative filtrations, and both positive padding injections. |

The image inequality following Definition 4.9 uses the paper's earlier
definition of a **finitary** function: every set-valued output is finite.
Its formal image is the union of the complete finite outputs.

## Premises and conventions

The model-theoretic proofs state their canonical-structure, pure
characteristic-zero, genuine small-parameter saturation and homogeneity,
and small-base assumptions explicitly where needed. The final 4.10 and
4.11 statements use the genuine standing `BaseContext` and derive the purity,
rank and definable-point conclusions from its assumptions. Generic category
and quotient constructions retain their weaker model/base premises.
`BaseContext` also displays the paper's standing nontriviality condition on
the named value group; it imposes no VF/Gamma-generation assumption.

For 4.10, the RV set uses the original base, the normalizing tuple is
arbitrary with the specified values, and zero coordinates are fixed at
zero before division. Nonemptiness is explicit for the Krull comparisons
and the polydisc or attained-point statements that require it. VF and RV
dimensions use zero for the empty set. For 4.11,
definability is over the original base and retains complete Gamma
pullbacks; no definable section is assumed. RV has its single absorbing
element, and valuation comparisons track the reversed multiplicative order.

Injectivity of finite-volume forgetting concerns the positive quotients.
Canonical lifting here covers objects and the stated commuting-map
criteria; constructing lifts of arbitrary RV isomorphisms belongs to
Section 7, as recorded in [TARGETS.md](TARGETS.md).

## Source and layout

[REUSE-SURVEY.md](REUSE-SURVEY.md) records the reused Mathlib and external
algebra developments. Their licenses and source credit remain in the
ported files. The common language and field/valuation interfaces come from
the pinned ACVF-QE release. Legacy snapshots are excluded from the active
library, as explained in [README.md](README.md). The original implementation
plan is retained in [PLAN.md](PLAN.md); this status is the verification record.

This publication contains only the active Section 4 sources and their
verification, attribution and integration support. Legacy snapshots remain excluded.
