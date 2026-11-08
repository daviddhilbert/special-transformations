# Section 7: Lifting functions

The active continuation is described in [STATUS.md](STATUS.md),
[TARGETS.md](TARGETS.md), and [HANDOFF.md](HANDOFF.md). The source entry point
is [Library.lean](Library.lean), registered explicitly in Lake and imported
by the project root. The eighteen-module/90-headline verification, full
type review and combined ACVF-QE import passed, including Lemma 7.2.
The expanded 35-module/137-headline entry-point and root checks passed,
including the residue polynomial projection and Remark 7.5. See STATUS.md
for evidence and the exact remaining scope.

The 41-module expansion and its 168 headline audits also passed, including
Lemma 7.4 and the ambient pullback extension of Definition 7.3. The full
statement review and fresh project-root check passed.

The 47-module expansion verifies Theorem 7.6. Its 233 headline axiom
audits, full type review and fresh project-root check passed.

The final 53-module expansion verifies both variants of Corollary 7.7 in
their stated scope. The 276 axiom audits, full type review and fresh
project-root check passed. STATUS.md records the explicit earlier
inputs to each variant.

New modules retain finite monomial presentations, use the released ACVF-QE
RV quotient and encoded-sort bridge, and develop residue-root independence,
coordinate normalization and fibrewise lift relations. The continuation
constructs normalized valuation-ring systems with zero residue and a unit
Jacobian. Ordinary multivariate lifting and uniqueness give the exact
root in the original RV fibre. See
[REUSE-SURVEY.md](REUSE-SURVEY.md) for source comparison and attribution.

`Sec7Gamma`, `Sec7GammaHensel`, `Sec7Lift`, `Sec7Cor77` and `LegacyScaffold/`
remain historical candidates, excluded from the new entry point. They are not
certificates of Lemma 7.2, Lemma 7.4, Theorem 7.6 or Corollary 7.7.

After pinned dependencies and earlier compiled imports are available, run
`lake env python3 Section7/verify.py`. Logs and generated artifacts belong
under `.scratch/section7-verified/`. This check freshly compiles the new
modules and audits their full headline types and axioms. The legacy files
are outside this entry point.
