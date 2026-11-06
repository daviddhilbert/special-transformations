# Working agreement and current structure

Read `Section3/HANDOFF.md` before the next proof session. This repository has
been organized by paper section. QE is finished in `daviddhilbert/ACVF-QE`;
do not restart its proof. The author's standing instructions are summarized below; Git history preserves
the previous layout. These current paths supersede older instructions.

## Required project workflow

Read and follow [WORKFLOW.md](WORKFLOW.md) in every substantive proof session:

1. Read applicable instructions, handoff and current status; inspect Git status
   and preserve existing edits.
2. Fix the exact paper target, definitions, parameter scope, prerequisites and
   explicitly authorized hypotheses.
3. Survey local and external reuse before rebuilding a substantial prerequisite;
   follow `FORMALIZATION-REUSE-GUIDELINES.md` and record the decision.
4. Implement a coherent module using pinned ACVF-QE and shared definitions.
5. Compile in the pinned Lake environment, inspect the full headline type and
   axioms, and check the affected integration boundary.
6. Update the section status and, when needed, its handoff with the exact scope,
   evidence, remaining obligations and concrete next step.
7. Publish only within the current authorization; local editing permission does
   not authorize a paper-repository push.

The workflow governs the process. Section handoffs and plans record the
mathematical strategy; old proof orders and status counts are not verification.

## Author's standing instructions

- Work persistently on the authorized objective; do not stop at a partial
  result or ask repeatedly whether to continue. Stop for the requested handoff
  when the user explicitly wants to continue in a new session.
- Preserve the author's work and existing uncommitted edits. Further
  paper-repository pushes require an explicit instruction. The author authorized
  publishing this section layout and ignoring the newer OpenMathOS content;
  earlier commits remain in Git history. The author also requested removal of
  the obsolete QE campaign from the current tree.
- A Lean result is verified only after compiler exit 0 and a checked headline
  type and axiom audit. Accept only `propext`, `Classical.choice`, `Quot.sound`.
  Explicit theorem hypotheses must also be checked. A definition of an open
  obligation or a theorem assuming that obligation is not a completed proof.
- Model theory in Dave Marker's *Model Theory: An Introduction* and valued-field
  results in Engler--Prestel's *Valued Fields* may be used as explicitly stated
  hypotheses under the author's authorization. Do not silently turn citations
  to Yin's other paper into proved inputs. Prefer existing checked proofs.
- Use genuine small-parameter saturation and homogeneity, not a structure
  bundling the desired paper lemmas as its definition of saturation.
- Survey existing formalizations before rebuilding a substantial prerequisite;
  follow `FORMALIZATION-REUSE-GUIDELINES.md`. Preserve licenses and source credit.
- Scratch output goes in `.scratch/`, not into source or version control.

## Fixed conventions

- Use the released ACVF-QE language and theory as the common starting point.
  Its RV inversion captures the author's group-language convention. The missing
  inverse symbol was an error in the Lean transcription, not in the paper.
- RV has one absorbing element, `rv(0)`, written as zero/infinity in the paper's
  conventions. Do not add a second absorbing point. `pK` is the nonzero group;
  `pInK` is the full residue-field predicate including zero.
- Mathlib's multiplicative valuation order is reversed relative to the paper's
  value-group order. Track the reversal in every comparison and ball definition.
- The material after Definition 2.4 works over pure characteristic zero and an
  appropriately saturated model, with the stated small base substructure.
  Preserve theorem-specific scope: Theorem 2.8 is stated for ACVF itself.
- Distinguish same valuation from same RV class. Do not repeat older comments
  attributing defects in a Lean transcription to the paper.

## Layout and verification

- `Section3/` includes the remaining Section 2 tasks. `Section4/` through
  `Section10/` hold the later sections. Existing Lean files there are legacy
  snapshots whose contents were moved unchanged, not automatically imported
  components of the new library.
- `Archive/MOVE-INDEX.json` maps historical paths to current files. The inventory
  and dependency planner are static tools, not Lean verification reports.
- Seven required syntax/parameter helpers are retained in `Shared/`. Shared
  `Enc`, `RVCalc`, `VFField` and `VFValued` modules come from pinned ACVF-QE.
  Older model snapshots remain in `Archive/Milestone0/`; its duplicate encoding
  and the obsolete QE campaign have been removed. Do not introduce competing
  standalone copies of the published language.
- Build new modules through the portable pinned Lake project. Record source,
  target statement, remaining hypotheses, compiler status and headline axioms
  separately. Historical headers and milestone totals are not current evidence.
