# Measured degree zero

The author-approved convention removes the degree-zero exceptions in
Definitions 10.1 and 10.3 of arXiv:1006.2467v1. The comparison is HK,
arXiv:math/0510133v3, Definitions 8.10 and 8.13. This is a correction to
the paper convention. It does not import any unproved HK theorem.

An object of measured RV[0] is an ordinary finite-volume RV[0] object
with a same-base definable nonzero RV form. Measured VF[0] retains the
same form on the full ordinary VF[0] object, including arbitrary mixed
presentations of VF dimension zero. The Gamma variants retain their
actual Gamma-valued forms. An arrow is a total definable bijection
preserving the exact form value at every point. Same valuation is weaker
than same RV class. There is one absorbing RV element; weights exclude it.

The empty-coordinate determinant is one. No nonempty zero-degree locus
can be removed as a lower-dimensional exceptional set. Ordinary categories
are unchanged. Their isomorphisms embed into the neutral-form measured
categories; ordinary noninvertible maps are not measured arrows. Gamma
neutral weight is multiplicative one (additive zero in the paper).

The implementation starts at published main
`f76d100e07c0a791259244fc7fdf06f4dfaaf8ae`, in an isolated worktree to
preserve the migrated checkout's uncommitted work. Existing positive-degree
indices still mean degree `k + 1`. The positive RV lift retains its explicit
`FiniteHenselianExtensionReference`; zero lifts require no such premise.

`WeightedZero.lean` supplies objects, exact arrows, pullback/restriction,
and the form-preserving zero lift. `WeightedZeroRepresentation.lean`
transports the supplied form through Section 5's ordinary finite lift
presentation. `WeightedZeroScissors.lean` descends this lift through
weighted isomorphism, empty and scissors relations. `WeightedZeroUnit.lean`
identifies the neutral subcategories, `WeightedFormProducts.lean` retains
both product densities, and `WeightedZeroResults.lean` exports concrete
RV/Gamma versions of 10.4–10.6. `GradedCategories.lean`
uses weighted zero families for both form scales, including neutral forms.

The complete `lake -R build Section10` and
`lake env python3 scripts/verify_ci.py section10` exited 0 under the
published Lean 4.35.0 pins. All 68 headline reports have allowed axiom
sets; the separate full explicit-type check also exited 0. The old
29-headline receipt certifies the old convention only. The current receipt
is in `.scratch/weighted-zero/verification.json`, with the full type log
and `.scratch/section10-verified/` headline audit. The complete project-root
`lake -R build` also exited 0 (10,042 jobs). These are local checks of the
corrected source; no new GitHub Actions run or remote publication is claimed.

RES, pure value-group categories, tensor decompositions, and the sequel's
Section 7 integration/kernel work are outside this task. No change to the
sequel's dependency pin or paper-repository push is authorized here.
