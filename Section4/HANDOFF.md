# Handoff: Section 4 complete and GitHub-verified

Updated November 6, 2026 (America/Los_Angeles). The active Section 4
formalization is complete in the scope recorded in [STATUS.md](STATUS.md)
and [TARGETS.md](TARGETS.md). There is no remaining Section 4 proof campaign
to restart.

## Entry points and completed scope

Use [Library.lean](Library.lean) as the checked entry point. It covers
the numbered material 4.1--4.23 of arXiv:1006.2467v1, with the unnumbered
dimension properties, positive scissor quotients, Grothendieck group/ring
constructions, universal properties, graded filtrations and positive padding
injections described in the status. Legacy snapshots are excluded.

The checkpoint comprises **234 active modules and 967 distinct headline
declarations**. Compiler checks exited zero; complete headline types and
explicit hypotheses were reviewed separately from their axiom lists. Every
headline uses only `propext`, `Classical.choice` and `Quot.sound`, or a subset.
The curated local certificate is [verification/AUDIT.json](verification/AUDIT.json),
with its method and reproduction commands in
[verification/README.md](verification/README.md). It distinguishes original
source-compilation receipts, kernel replay against completed Section 3, and
fresh headline and integration checks. Raw logs remain under `.scratch/`.

## Published commits and passing GitHub runs

The Section 4 proof-publication commit is
[`93166e6`](https://github.com/daviddhilbert/special-transformations/commit/93166e6779094bcc85ea3753fefc70e8e220008e).
Its [verification run 42303747683](https://github.com/daviddhilbert/special-transformations/actions/runs/42303747683)
completed **successfully on November 6, 2026**. The pinned source build,
cache-provenance regression tests, published QE headline audit, Section 3
verifier and Section 4 verifier all passed. The Section 4 verifier compiled
the active library, checked the complete headline output and allowed axioms,
and checked the combined QE import and project root.

The later published main-branch commit
[`21cff13`](https://github.com/daviddhilbert/special-transformations/commit/21cff13d8f9beb28e6ed84e04242e9deae875cb6)
has a second [passing run, 42303485856](https://github.com/daviddhilbert/special-transformations/actions/runs/42303485856),
including the Section 4 and Section 5 verifiers. Its Section 4 files are
unchanged from `93166e6`. Both runs retained a
`lean-verification-<full commit SHA>` artifact with compiler logs and
headline audits in the run's Artifacts section.

Earlier runs `42297717897` and `42299437473` were cancelled by subsequent
main-branch publications. The passing isolated run used
`codex/section4-verification`, whose separate cancellation group let it
finish. No proof fixes were needed. These are passing proof checkpoints;
they do not claim that a future run for this handoff-only update has passed.

## Inputs, conventions and theorem scope

Sections 2--3 are completed in the approved scope of
[their handoff](../Section3/HANDOFF.md), including the guarded rational
correction to Definition 2.4 and the retraction of Remark 3.19. Use their
checked interfaces as recorded in [INPUTS.md](INPUTS.md). QE is the pinned
completed ACVF-QE dependency; do not restart either earlier proof campaign.

- Lean is pinned to `leanprover/lean4:v4.33.1`, Mathlib to
  `0df444a360eaa60ab8c11dca51a86af692955474`, and ACVF-QE to
  `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`. Keep the common released language
  and existing shared definitions. Attribution and port licenses remain in
  `Imported/`; [REUSE-SURVEY.md](REUSE-SURVEY.md) records their provenance.
- Preserve pure characteristic zero, genuine small-parameter saturation and
  homogeneity, and the stated small base where required. The final 4.10 and
  4.11 statements use the genuine `BaseContext`, including its nontrivial
  named value group, and derive their purity/rank conclusions. They assume
  no VF/Gamma-generation condition or definable RV section.
- RV has one absorbing element, `rv(0)`. Distinguish equal valuations from
  equal RV classes, and track Mathlib's reversed multiplicative valuation
  order in comparisons and balls.
- The image inequality after Definition 4.9 uses the author's clarified
  **finitary** function: each set-valued output is finite, and the image is
  the union of those complete outputs.
- Keep the documented empty-set dimension convention and explicit
  nonemptiness in the Krull, polydisc and attained-point statements that
  require it. In 4.10, normalization is zero-aware and uses arbitrary
  same-value normalizers; 4.11 retains original-base Gamma definability.
- Lemma 4.19 retains its volumetricity premise. Canonical object lifts and
  the stated commuting-map criteria are proved here; lifting arbitrary RV
  isomorphisms belongs to Section 7. Finite-volume forgetting is asserted
  injective on the positive quotients, with the completion scope recorded
  in the status.

## Continue from this checkpoint

Later sections can import `Section4.Library` and use the statements with
their displayed hypotheses. Continue the relevant later-section targets
from their current status rather than reopening the completed Section 4
targets. Preserve unrelated uncommitted work and the fixed dependency pins.

For changes affecting Section 4, use the pinned project and
`lake env python3 Section4/verify.py`; the independent source-build commands
are in [verification/README.md](verification/README.md). Cache reuse must
match actual resolved compiled providers, module parts, lookup order,
sources, dependencies, outputs, logs and any replay evidence. Old
source-only caches are insufficient. Record real compiler exits, inspect
the complete affected theorem types and hypotheses, check the permitted
axioms, and verify the affected integration boundary before updating a
completion claim. Scratch output stays in `.scratch/`; further repository
pushes require the author's explicit instruction.
