# Section 9 status

## Scope

Started November 7, 2026 from the published Section 8 checkpoint
[`32d7815`](https://github.com/daviddhilbert/special-transformations/tree/32d7815b7a58624a620abb9d6423721b7e094520).
The new Lake target is `Section9`, with entry point `Section9.Library`.
The legacy snapshots are outside this entry point.

The active Jacobian targets use `RV[n]`: both volume maps are finite-to-one.
The author agreed to leave the broader `RV[n,·]` version outside the Section 9
scope. Theorem 9.16 already has these hypotheses. The corrected 9.15 retains
its comparison for arbitrary definable lifts of essential `RV[n]` isomorphisms.

The author approved the [replacements for 9.11 and 9.12](DIFFERENTIATION-ERRATA.md#approved-replacement-statements)
on November 7, 2026. The formalization keeps the paper's algebraic
scope. `BaseContext` spells out genuine small-parameter saturation and
strong homogeneity as separate assumptions of the monster model. It
also records the nontriviality of `Γ(S)`, which the paper assumes
immediately before Convention 2.5.
The audited arbitrary-lift comparison, the positive-arity prescribed
lift, and the intrinsic Gamma polydisc
descent take `HenselizedGaussGraphInput` as an explicit proof input.
`GraphReferenceAudit.log` checks the library construction of that input
from `FiniteHenselianExtensionReference`. This names the authorized
Engler–Prestel facts that henselianity persists in a finite extension
and that the residue degree equals the field degree in residue
characteristic zero when the values are unchanged. The ACVF adapter
uses the algebraic closedness theorem from the published library.
The positive-arity statements use `ℵ₀ ≤ κ` and `|S| < κ` to express the
paper's sufficiently saturated small-base setting. The `(VF, Γ)`-generated
base used for finite-head representatives is the explicit hypothesis of 9.16.
The intrinsic Gamma proof uses `ℵ₀ < κ` for its small algebraic extensions.
This follows from the paper's standing smallness assumption when the base
contains its characteristic-zero VF field.
The proofs establish the algebraic conditions of their local lemmas,
including nonzero specializations, simple-root equations and invertible
reduced blocks. The intrinsic descent argument chooses an auxiliary field with
nontrivial value group inside the monster, even when the original base
has trivial valuation. This choice does not strengthen the original
parameter assumptions.

| Target | Current state |
| --- | --- |
| Definition 9.1 | `Limits.lean` defines limit sets and minimality using the released VF type and actual Gamma quotient, including the formal infinity in the auxiliary codomain. `IsLimitSet.mono` proves monotonicity in the candidate limit set. The model-theoretic limit statements below record the definability hypotheses. |
| Lemmas 9.2–9.5 | `FinitePointLimits.lean` and `LimitTopology.lean` give the finite-point statements and closure bridge. `FiniteLimitSeparation.lean` proves uniqueness and the union rule for finite limits with infinity coordinates. `LimitCardinality.lean` and `LimitDefinability.lean` give the 9.4 cardinality bound and 9.5 finite minimal limit with same-base definability. The 9.5 source allows an arbitrary unary domain and measures the limit at zero. All these headlines have passed the checks below. |
| Definition 9.6, Lemma 9.7, Definition 9.10 | `Differentiation.lean`, `VFJacobian.lean` and `MixedJacobian.lean` passed the type and axiom audits for the arbitrary-rank derivative, chain rule, partial Jacobian and fixed-label version. |
| Lemma 9.8 and Corollary 9.9 | The headlines in `PartialDerivativesAE.lean` passed the post-restart compiler, full type and axiom checks. They include the same-base dimension bound and continuity of partial derivatives, with one exceptional set for all partial derivatives. |
| Lemma 9.11 and Lemma 9.12 | The approved positive-arity and zero-arity headlines passed their full type and axiom audits. `SpecialJacobianAE.lean` proves 9.11 for the actual special chain and inverse. |
| Definitions 9.13–9.14 | The essential restriction, arbitrary-degree essential isomorphism and dimension bound for the discarded degeneracies passed the checks. The scaled residue tangent determinant, uniqueness and projection to the paper Gamma quotient passed the audit. `GenericRVJacobian.lean` passed the full audit for the definable generic value. `GenericRVJacobianChain.lean` passed the audit for the proposed generic chain rule, with a same-base exception of dimension below `n` in both the labels and their source volume image. Its arity-zero result is pointwise. The printed pointwise RV chain rule has an obstruction in `RV[1]`. See [RV-CHAIN-ERRATUM.md](RV-CHAIN-ERRATUM.md). |
| Lemma 9.15, RV clause | `PaperLiftComparison.lean` passed the full audit for arbitrary definable lifts with a same-base exception in the source volume image and only the graph-field construction as an explicit reference input. It supplies the definable candidate from 9.14. The arity-zero comparison also passed and needs no graph-field input. |
| Lemma 9.15, Gamma clause | The withdrawn assertion and the proposed agreement on a full-dimensional part of each fibre fail in arity two. `GammaObstruction.lean` proves the group-level bijection and the change in the sum of valuations. The mathematical counterexample uses its rational branches on the maximal ideal and translates into a singleton RV polydisc. The author accepted this documented counterexample and its group-level Lean audit as the scope for the withdrawn clause on November 9, 2026. |
| Theorem 9.16 in RV[n] | The zero-arity case and the full positive-arity theorem conditional on `HenselizedGaussGraphInput` passed their type and axiom audits. The positive-arity type keeps both paper compatibility conditions and returns a same-base definable lift off a VF-small exception. The graph-field construction has a separate audit under the named finite-extension reference. See [RV-CATEGORY-AUDIT.md](RV-CATEGORY-AUDIT.md). |
| Gamma descent for a volume-preserving lift | `GammaPolydiscDescent.lean` passed the full type and axiom audit for bijections of polydiscs with a fixed finite Jacobian value outside a same-base VF-small set. It uses the intrinsic coarsening and takes `HenselizedGaussGraphInput` explicitly. |

See [LEMMA-9.15.md](LEMMA-9.15.md) for the mathematical arguments and
[REUSE-SURVEY.md](REUSE-SURVEY.md) for the checked dependencies and candidates.

The graph construction imports eleven licensed Stacks proof modules.
The local valuation-ring argument and the Gauss value-group calculation
are proved in the library. The explicit finite-extension reference is
the remaining external mathematical input for positive-arity 9.15,
9.16 and intrinsic Gamma descent. The model and lift assumptions are
listed separately above.

Five earlier support files expose choices, algebraic representatives,
weighted polynomial systems, and definable lift maps to Section 9.
The publication audit compared the original theorem signatures with
the staged sources and found them unchanged.

## Verification

Run the project through the pinned Lake environment.

```sh
lake exe cache get
python3 scripts/prepare_ci.py
lake -R build
lake env python3 scripts/verify_ci.py section9
```

The last command imports `SpecialTransformations`, prints the definitions
and full headline types, and checks the axiom allowlist. GitHub Actions
retains the compiler and audit logs.

The local publication audit compiled `Section9.Library` with exit zero.
It rebuilt ten active modules and reused checked artifacts for the other
imports. The 596 local sources in this import closure match the staged Git
blobs. `CompleteSection9Audit.log` exited zero and records 25 Section 9
headlines and ten supporting headlines, including both versions of each
earlier helper interface. A scan of all 2,151 declarations in the 189
Section 9 modules and eleven vendored Stacks modules found only the
permitted axioms. The logs and source and artifact hashes are in
`.scratch/section9/publication/`. The clean repository-wide build is a
separate GitHub Actions check.

The original Section 9 publication used Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`, and ACVF-QE at
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`. The library import and
headline checks passed on November 8 under these pins. The local
development receipts are in `.scratch/section9/post-restart/`.
`FinalSection9Audit.log` checks the generic RV Jacobian and chain rule,
corrected 9.15, 9.16, Gamma descent, and the ACVF graph adapter.
`GraphReferenceAudit.log` prints the finite-extension reference.
`LimitAndDerivativeAudit.log`, `DifferentiationAndLiftAudit.log`,
`SpecialJacobianAudit.log`, and `MixedAndResidueAudit.log` cover
the earlier Section 9 statements and the shared lifting interfaces.
All headline reports use only `propext`, `Classical.choice`, and
`Quot.sound`.
