# Handoff: Section 3 and post-QE Section 2 complete

November 9 update: the author has corrected open discs to have finite radii.
See [OPEN-DISC-RADIUS-NOTE.md](OPEN-DISC-RADIUS-NOTE.md) for the local changes,
current Lean 4.35.0 verification and consumer patch. The older release details
and dependency versions below belong to the historical completed checkpoint.


Updated November 6, 2026 (America/Los_Angeles). This replaces the November 4
startup handoff. The requested formalization is complete in the author's
approved scope; there is no remaining Section 3 proof campaign to restart.

## Completed scope and entry points

All active targets in Section 3 and all Section 2 material after Theorem 2.3
are proved, with the rational correction to Definition 2.4 and the retraction
of Remark 3.19 described below. The numbering follows
[arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1).

Use [Library.lean](Library.lean) as the checked entry point,
[STATUS.md](STATUS.md) for exact theorem scopes and hypotheses, and
[TARGETS.md](TARGETS.md) for the numbered checklist. The library excludes
legacy snapshots and placeholders; [LEGACY.md](LEGACY.md) records their audit
and reuse history. Genuine real/Gamma parameter bases, finite tuple arities,
and original-base definability are retained where required.

The final proof commit is
[`d466a69`](https://github.com/daviddhilbert/special-transformations/commit/d466a692305bae435cc26954fbae33b435bfbd77).
It was published with the existing remote workflow commits in
[`e032b9a`](https://github.com/daviddhilbert/special-transformations/commit/e032b9a7c96cd8f5ea76d4806be9e8556e1e428e).
These identify the completed proof checkpoint, before this handoff-only update.

## Definition 2.4: approved correction and proved normal form

On November 5, 2026, the author approved **rational VF functions with explicit
domain guards** instead of the strict polynomial-only VF factors. See
[NORMAL-FORM-NOTE.md](NORMAL-FORM-NOTE.md). This is the adopted statement;
no Lean-proved counterexample to the printed polynomial-only form is claimed.

[GuardedRationalNormalForm.lean](GuardedRationalNormalForm.lean) proves
`GuardedRVNormalForm.definition_2_4_guarded_rational_normal_form` and
`DefinableOver.guarded_rational_normal_form`. The supporting modules are
[GuardedRVArithmetic.lean](GuardedRVArithmetic.lean),
[GuardedRVTerms.lean](GuardedRVTerms.lean), and
[GuardedRVLiterals.lean](GuardedRVLiterals.lean).

The finite DNF is chosen before quantifying over models and uses exactly the
original VF and RV slots. It compiles to an actual well-sorted quantifier-free
formula in the released language. Equality literals have coefficient one on
the left and genuine flat K factors with at least two summands. Order
comparisons have no K factors. Every true raw clause establishes all VF pole
guards and residue-summand domains, including residue zero. Zero RV branches
are retained. The definable-set wrapper reuses the original parameter package.
The normal-form theorem holds in every ACVF model, with no saturation,
cardinality, characteristic-zero, or assumed-normalization premise.

VF inversion remains unnamed: rational VF factors compile as
`rv(numerator) / rv(denominator)` using named RV inversion, with nonzero VF
denominators explicitly guarded. Nonunit RV scalars are not distributed
through residue addition without its proved domain conditions.

## Remark 3.19: retracted, not counted as proved

The author retracted the whole remark on November 5, 2026, including its
proposed multiplicative extension of Lemma 3.18. It is excluded from the active
targets. No replacement classification, including one restricted to infinite
definable groups, was adopted. See [RETRACTIONS.md](RETRACTIONS.md).

[Remark319Audit.lean](Remark319Audit.lean) retains the checked obstruction
`{1,-1}` to the printed unrestricted classification. The citation and import
audit found no later citation or identified reliance on the remark; the
retraction note records the precise checks and their limits. Lemma 3.18's
additive conclusions are proved and remain active results.

## Verification and passing GitHub Actions run

The combined local certificate covers **197 integrated modules, 1,393 actual
headline type/axiom checks, and a fresh project-root import**. All compiler
exits are zero; no proof placeholders remain in the checked library. Headline
axioms are contained in `{propext, Classical.choice, Quot.sound}`. Complete
intended theorem types, including parameter scope and explicit hypotheses,
were reviewed. Matching checked caches are identified separately in
[verification/LibraryAudit.json](verification/LibraryAudit.json); the full
headline output is [verification/HeadlineAudit.txt](verification/HeadlineAudit.txt).

The [Lean verification run 42242271465](https://github.com/daviddhilbert/special-transformations/actions/runs/42242271465)
for published commit `e032b9a7c96cd8f5ea76d4806be9e8556e1e428e` completed
**successfully on November 6, 2026**. The pinned project source build,
published QE headline audit, and Section 3 verifier all passed. The Section 4
verifier was skipped because it was absent from that published tree; this
run does not certify the later sections. This is the passing proof-publication
run, not a claim about a future run triggered by this documentation update.

## Fixed dependencies and mathematical conventions

- Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib is pinned to
  `0df444a360eaa60ab8c11dca51a86af692955474`.
- QE is the completed [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE)
  dependency at `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`, imported as
  `ACVFQE`. Use its `theorem_2_3_quantifier_elimination`; do not reprove QE or
  introduce a competing copy of its language. Its inherited C-minimality
  placeholder is not used as a proof of Theorem 2.8; the actual theorem is
  proved in this library.
- The author clarified that naming RV inversion corrects the paper's printed
  inverse-free language specification, not merely a Lean transcription.
  The released implementation already names it. VF inversion stays unnamed.
  Naming a definable inverse changes neither definable sets nor same-base
  acl/dcl; it creates no new downstream language requirement.
- RV has one absorbing element, `rv(0)`, also written infinity. `pK` is the
  nonzero RV group; `pInK` is the residue subset including zero.
- Mathlib's absolute-value valuation order is reversed from the paper's
  value-group order. Equal valuation is not equal RV class.
- Preserve theorem-specific characteristic, genuine saturation, smallness,
  nonemptiness, and VF- or (VF,Gamma)-generation assumptions from `STATUS.md`.
  A real parameter set does not silently include Gamma imaginaries; use the
  explicit `GammaParameters.Base` interfaces for those statements.

## Reproduction and future work

After setting up the pinned dependencies, follow
[the CI workflow](../.github/workflows/lean.yml). On a fresh checkout,
`python3 scripts/prepare_ci.py` registers the pinned QE package's sibling
modules without changing its Lean sources. Then run `lake -R build`,
`lake env python3 scripts/verify_ci.py`, and
`lake env python3 Section3/verify.py` from the repository root. Scratch logs
and verification artifacts belong under `.scratch/`.

No Section 2/3 proof obligation remains in the agreed scope. Further work
should follow a new request, rather than the obsolete instruction to start
formalizing this section. Read the current root instructions and inspect Git
status, remote state, and worktrees before editing. Publication used an
isolated worktree to preserve unrelated local work, including later sections;
do not reset or overwrite that work to synchronize a checkout. Future changes
still require pinned compilation, full headline type/axiom review, and the
affected integration check. Push only within the user's current authorization.
