# Project workflow

Follow this workflow throughout the paper repository, together with
[AGENTS.md](AGENTS.md) and any applicable section instructions. The current
user's authorization determines the objective, accepted inputs and publication
boundary. Preserve unrelated work and carry the authorized task through its
verification and documentation.

## 1. Orient

Read the section's handoff, targets, plan and current status where available.
Read [Section3/HANDOFF.md](Section3/HANDOFF.md) before the next proof session,
as required by `AGENTS.md`; distinguish its historical checkpoint from later
source and status updates. Inspect `git status`, existing diffs, `lean-toolchain`
and the Lake dependency pins before editing.

QE is a completed dependency in `daviddhilbert/ACVF-QE`. Do not restart it or
duplicate its language. Use [Archive/MOVE-INDEX.json](Archive/MOVE-INDEX.json)
to resolve historical paths. Legacy files and static dependency inventories
are candidates for reuse, not current proof certificates.

## 2. Specify the target

Read the relevant paper version and numbered statement, including standing
assumptions. Record the intended Lean headline and definitions, parameter
base, characteristic, tuple arities, nonemptiness and saturation bounds.
Preserve the author's approved language corrections and the conventions in
`AGENTS.md`, including valuation order reversal and the distinction between
equal valuation and equal RV class.

Classify prerequisites as checked imports, results needing a proved bridge,
explicitly authorized hypotheses, or open obligations. For accepted
earlier-section or standard-reference inputs, record the authorization and
precise scope. Do not assume an entire earlier section without authorization.
Keep remaining mathematical hypotheses visible in the exported theorem type.

## 3. Survey reuse

Follow [FORMALIZATION-REUSE-GUIDELINES.md](FORMALIZATION-REUSE-GUIDELINES.md).
Check local modules, scratch work and legacy candidates as well as external
libraries, catalogs and Mathlib pull requests. Compare actual definitions and
statements. Record substantial findings in the section's `REUSE-SURVEY.md` or
established equivalent, with source revisions, licenses, verification evidence
and the proposed import, bridge or attributed port. Explain a decision to
rebuild. Repeat focused searches when a major blocker or strategy change
warrants it; keep research proportional and continue useful authorized work.

## 4. Implement

Use the portable pinned Lake project, published ACVF-QE modules and retained
`Shared/` helpers. Adapt legacy snapshots into the common language rather than
bulk-importing them. Preserve source attribution and licenses.

Work in coherent modules with explicit dependencies. Add a ready module to
the appropriate library entry point and build configuration. Use genuine
saturation and homogeneity; do not bundle the desired conclusions into their
definitions. Keep scratch sources and logs under `.scratch/`. Do not edit
files during a compiler run that is checking them. Do not silently weaken
targets, change frozen conventions or upgrade dependencies to fit a proof.

## 5. Verify

Run Lean through the pinned Lake environment. For an individual module, use
`lake env lean SectionN/Module.lean` with the actual source path and required
dependencies built. Read the section verifier's invocation and scope before
using it. A verified result requires:

- Compiler exit zero and inspection of complete diagnostics, including parse
  errors and unsolved goals.
- The intended full headline type, including quantifiers, parameter scope,
  definitions and every explicit hypothesis; exclude vacuous substitutes.
- `#print axioms` on the exported headline containing only `propext`,
  `Classical.choice` and `Quot.sound`. A clean audit does not discharge
  explicit mathematical hypotheses.
- A successful check of the affected library import or downstream consumer.

Record commands, compiler and dependency versions, source identity, exit
status, headline type and axiom output. Distinguish fresh builds from reused
artifacts and selected-module checks from wider integration checks. Cached
evidence requires matching source and dependency fingerprints. Broaden checks
when failures, changed interfaces or unresolved concerns justify it.

## 6. Record and hand off

Update the section's status or target table in the same change that establishes
the result. Distinguish statements, partial proofs, conditional theorems,
individually checked modules and integrated results. Separate authorized
reference inputs from open paper-specific obligations. Keep counts tied to
their verified checkpoint; an audit still running is not a passed certificate.

Correct misleading headers and status claims when evidence changes. Update
the handoff when the strategy or next step changes and when a new session is
requested. Include the exact target, entry points, evidence locations,
remaining obstacles and concrete next step. Keep scratch output uncommitted.

## 7. Publish within authorization

Review the final diff and include only intended changes. Follow the current
commit and push authorization separately. Further paper-repository pushes
require an explicit instruction; an earlier publication does not authorize a
new one. When authorized, publish relevant status and attribution updates and
verify the remote revision. Report the result and its verification scope.
Stop at a requested handoff; otherwise continue the authorized objective.

## Automated GitHub checks

[Lean verification](.github/workflows/lean.yml) runs on pushes, pull requests
and manual dispatch after it is published to GitHub. Runs appear under
**Actions**; commits themselves appear in the repository's commit history.

The pinned QE release declares only its root module in Lake, although its
proofs use sibling module names. `scripts/prepare_ci.py` registers all shipped
proof modules as library roots in the CI checkout before the build. It checks
the exact dependency revision, leaves every Lean source unchanged, and saves
source hashes and the configuration change in the verification artifact.
Review this workaround when updating the dependency pin.

The workflow builds the pinned project root and audits the published QE
headline types and axioms. It runs the Section 3 and Section 4 verifiers when
they are present in the checked-out revision. It retains logs, audits and status
records as downloadable artifacts, including available diagnostics on failure.
The run summary records these separate step outcomes.

This checks the current integrated libraries and selected headlines. It does
not certify all of Sections 2–10, legacy snapshots, unimported Section 5 work,
or the semantic fidelity of every statement to the paper. Later integrated
sections need explicit verifier steps and headline audits. The manual source
and hypothesis review above remains required even when CI is green.
