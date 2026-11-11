# Open-disc radius correction

Author-approved correction, November 9, 2026.

A proper open disc has a finite valuative radius. In the existing reversed,
multiplicative encoding this is `OpenRadius Γ := OrderDual Γˣ`. `openDisc`
and `openPolydisc` take that type; multiplicative valuation zero (the paper's
radius infinity) cannot be passed to either definition. `openRadius` packages
an actual nonzero value. The singleton at infinity is `closedDisc_infinity`.
The former `openDisc_infinity`, `openPolydisc_infinity` and open whole-field
radius declarations have been removed. The whole field remains a separate
case in the closed code chart.

The ordinary finite-radius inequalities are unchanged. The ball representation
now gives either an open radius or a closed radius, instead of sharing an
extended radius across both alternatives. Centres, means, nearest roots,
RV-fibre constancy, radial geometry and polynomial-constancy proofs have been
updated accordingly. The six direct Section 5 consumers also use finite open
radii. No language symbol, ACVF axiom, parameter base, saturation condition or
headline polynomial-preparation conclusion is changed by this correction.

The correction was developed against
`9cc9760892092dd34cfad4a6dee655843c52f30c`. This publication applies the same
30 source-module changes on top of `ff2c999c6946a2b200f8778384c847f58e4ed521`,
preserving the later Section 6 and Section 10 work, blueprint and limit-set
correction. The `diamond-integral` consumer keeps its existing dependency pin
and portable source-matched patch; publishing this change does not upgrade
that consumer's dependency. Its preparation script checks the base and the
complete effective source identities.

Verification uses Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and ACVF-QE
`939346b0a99899e22a873479364e3cc5d142731c`. The corrected sources are byte-matched
between this checkout and the consumer's dependency before checking them.
The consumer builds `Section3.Library`, `Section5.Library` and its own
`DiamondIntegral` entry point. The standalone library audit prints full types
and axioms for all 250 public declarations in the 28 changed source modules.
It allows only `propext`, `Classical.choice` and `Quot.sound`; explicit theorem
hypotheses remain visible. This is not a fresh complete audit of Sections 6–9
or a replacement for the wider historical section verification records.

The subsequent §2 work in `diamond-integral` found the one direct Section 4
caller, `Section4/PolydiscLocal.lean`. Its carrier-to-paper-disc bridge now
packages the already nonzero step values with `Balls.openRadius`. The old
unreachable infinity branch is removed. The polydisc carrier and its existing
nonzero-step hypotheses are unchanged. The consumer's portable patch now
covers 29 modules and 258 public declarations, while the original standalone
250-declaration/28-module record below remains a historical checkpoint for
Sections 3 and 5. The additional Section 4 module has a separate fresh audit
in `../Section4/verification/FiniteOpenRadiusAudit.{lean,txt,json}`; this does
not certify the full Section 4 library.

See `verification/OpenDiscRadiusAudit.lean`,
`verification/OpenDiscRadiusAudit.txt` and
`verification/OpenDiscRadiusAudit.json` for the exact scope, source identities
and compiler results. Runtime build logs remain under `.scratch/`.

## Final consumer integration and publication

The additional direct Section 8 caller, `UnaryBalls.lean`, now also uses a
finite `Balls.OpenRadius`. The complete correction covers **30 source modules**
in Sections 3, 4, 5 and 8. Their contents are byte-identical to the approved
consumer patch. The consumer's final project entry-point build and full type
and logical-dependency audit pass with **850 section theorems and 378 selected
reuse declarations**, allowing only `propext`, `Classical.choice`, and
`Quot.sound`. The nine accepted inputs of the consumer remain explicit.

Consumer evidence is published in
[`diamond-integral` commit 82fe1a1](https://github.com/daviddhilbert/diamond-integral/commit/82fe1a127def2c24ca32a97935ff3de3f732a84c),
under `section 2/verification/` and `section 2/reuse/manifest.json`. Earlier
250/258-declaration standalone records above retain their historical scope.
The publication adds no unrelated local source changes.

The publication also passes a fresh `lake build` of the current complete
`SpecialTransformations` coordination root on the newer remote base. A fresh
combined audit prints all **260 public declaration types and their logical
principles** across the 30 changed source modules, with the same standard-three
allowlist. Exact source hashes, commands and compiler exits are recorded in
`verification/FiniteOpenRadiusPublicationAudit.{lean,txt,json}`. This build
checks later imports for compatibility; the 260-declaration semantic/type
scope remains distinct from a fresh full audit of every unchanged later result.
