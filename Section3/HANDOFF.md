# Handoff: finish Section 2 after QE, then all of Section 3

Prepared November 4, 2026 (America/Los_Angeles), at the author's request.
The user explicitly wants the actual formalization continued in a new session.
This session organized files and prepared the handoff; it did not start new proofs.

## Objective and completed dependency

Formalize all of Section 3 of Yimu Yin, *Special transformations in algebraically
closed valued fields*, and all material in Section 2 after the statement of
Theorem 2.3. The source checked for numbering is
[arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1), printed pages 4--7
(Section 3 starts on printed page 5). Check the author's intended paper version
before freezing any statement whose wording differs.

**QE is done.** The independent [ACVF-QE repository](https://github.com/daviddhilbert/ACVF-QE)
is pinned at `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`. Its root import is
`ACVFQE`; its Lake package name is `acvf_qe`. It exports:

- `JohnsonACF.hasQEb`: pure ACF QE, all characteristics.
- `hasQE_ACVF_val`, `hasQEb_ACVF_val`: ordinary nontrivially valued ACVF QE.
- `SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination`:
  exactly `HasQE Axioms.ACVF`, with no additional mathematical hypotheses.

The initial standalone export checked 81 modules and a fresh combined import.
The final QE axiom audit contains only `propext`, `Classical.choice`, `Quot.sound`.
The subsequent inversion-attribution correction changed documentation/comments
only. Its public verification records are under `verification/` in ACVF-QE.
The inherited C-minimality placeholder in its `Enc` module is **not a proof**
of Theorem 2.8 and is not a QE dependency. Do not use that placeholder.

## What changed in this working copy

The root is now an index and portable build configuration. Existing work is
organized in `Section3/` through `Section10/`. Old QE material and milestone-0
snapshots are preserved in `Archive/`; old root handoffs and plans are in
`Archive/History/`. `Archive/MOVE-INDEX.json` records the 336 unchanged moves.

`Section3/` contains 27 relocated files, including three earlier scaffolds;
`Section4/` contains 15. These counts describe files, not proved paper results.
No legacy Section 3/4 compiler check was performed during relocation. Static
source inventory and dependency planning do not establish Lean correctness.
Use `LEGACY.md` and `TARGETS.md`, not old "green" headers, as the starting map.

Cleanup checks passed: every moved file matches its recorded original hash,
and static dependency plans resolve for all 42 Section 3/4 source files.
The new top-level root source, with fresh QE headline checks appended, also
compiled successfully under the pinned Lake environment; all three QE audits
list only the standard Lean axioms. That check reused the matching installed
Mathlib and previously checked ACVF-QE oleans. It was not a clean rebuild of
all dependencies or a compiler check of the legacy section snapshots.
Records: `Archive/REORGANIZATION-CHECK.json` and `Archive/ROOT-IMPORT-AUDIT.txt`.

The cleanup included substantial pre-existing local work, all preserved in the
relocation. The author subsequently authorized publishing this layout while
ignoring the newer OpenMathOS content. The pre-cleanup remote tip is retained
on `codex/pre-section-layout-06c840f` and in the merge history. Inspect current
`git status` before editing and preserve any new working-copy changes.
The user chose section **subdirectories**, so do not create nested `.git`
directories, GitHub section repositories, or submodules.

## First concrete steps in the new session

1. Read this note, `../AGENTS.md`, `TARGETS.md`, and `LEGACY.md`.
2. Check `git status` and the move index before editing. Keep the exact QE pin.
3. Make the pinned dependency available through Lake; use `import ACVFQE`.
   The root config now uses public Git revisions instead of `/opt/mathlib`.
   Do not upgrade Lean or Mathlib to accommodate a candidate proof.
4. Add a small, separately checked Section 3 library entry point and explicit
   model/base-parameter context. Do not bulk-import the old snapshot collection.
   Reuse the published `Enc` definitions as the one shared language.
5. Audit the raw-parameter/sorted-parameter interfaces, `acl` and `dcl` in VF,
   RV, and the imaginary Gamma sort. The old `SP` API represents finite tuples,
   whereas the paper's ambient base S is a small substructure; provide a proved
   bridge rather than silently replacing the base by a finite tuple.
6. Close the post-QE normal-form/ball/C-minimality layer before relying on it
   in Section 3. Then proceed through the checklist, reusing local candidates.

The source files are ready for inspection; module imports still reflect the
historical staging scheme. `python3 Archive/inspect_legacy.py --plan
Section3/Sec3Count.lean` gives a static dependency order and alias map. It is
not a substitute for a clean compiler run after porting.

## Fixed mathematical and language choices

- RV inversion was omitted from the original **Lean transcription**, not the
  paper. The released function symbol captures the author's group convention;
  generated RV substructures contain inverses. Keep this interpretation.
- The encoding has one absorbing RV element `rv(0)`, identified with the
  zero/infinity notation as already settled by the author. `pK` is the nonzero
  multiplicative group, while `pInK` includes residue zero.
- Track the reversal between Mathlib's absolute-value valuation order and
  the paper's ordered value-group convention. Do not equate the RV preorder
  with antisymmetric Gamma order or an rv-fibre with a closed ball.
- Section 3 uses the standing pure characteristic-zero setting from Section 2,
  a sufficiently saturated model, a small base S with nontrivial Gamma(S), and
  its atomic diagram. Definability is over that named base unless additional
  parameters are explicitly introduced. Preserve the extra VF-generated or
  (VF,Gamma)-generated assumptions exactly where the paper requires them.
- Saturation/homogeneity must have their actual model-theoretic meanings.
  `Archive/Milestone0/Saturation.lean` is a candidate generic interface; audit
  how it instantiates the characteristic-zero theory and parameter sizes.
  ACVF-QE's ultrapower supplies countable-parameter saturation for its QE
  criterion; it does not automatically provide every monster/homogeneity
  hypothesis needed in this section.
- Standard results from Marker's *Model Theory: An Introduction* and
  Engler--Prestel's *Valued Fields* are authorized as explicit hypotheses.
  State their full types and citations. This is not blanket authorization to
  assume the paper's own unproved Section 3 conclusions. For citations to Yin's
  companion paper, identify and formalize the needed result or mark the target
  as still conditional; never call it finished merely because the audit is clean.

## Known transcription and specification traps

Read the actual paper before attributing any defect to it. Several legacy
comments conflate an error in a Lean statement with an error in the paper.

- **Lemma 3.8:** the paper assumes the c_i have the same **valuation**, not the
  same RV class. Retain the residue-characteristic-zero standing context, the
  nondegenerate finite-family conditions, and the zero-average hypothesis.
  `Sec3Average.average_zero_rv_not_constant` is a useful candidate for the
  valuation conclusion; derive the advertised RV nonconstancy as well.
  Do not inherit the `Sec3_sat` header's assertion that the paper's conclusion
  is inconsistent: its earlier transcription used a stronger wrong premise.
- **Lemma 3.1:** inspect the nonempty-domain issue. A universally quantified
  condition over an empty A is vacuous. `AclFibres`, `UniformCover`, and
  `Sec3Corrected` isolate it; verify the paper's intended nonempty application
  and record the exact hypothesis instead of claiming the unrestricted target.
- **Centers:** a definable center function on a family of balls is not the
  stronger requirement that one common set meet every ball in exactly one
  point. `M7Centres`/`BallSec3` diagnose that transcription. Set-theoretic choice
  of arbitrary centers does not prove definable choice.
- **Lemma 3.9:** target some `RV^m`, not necessarily a single RV coordinate.
  Older finite-set constructions name the elements as extra parameters;
  this does not prove a map definable over the original base S.
- **Corollary 3.5:** every function must be definable, with the complete finite
  tuple arities. An arbitrary set-theoretic function cannot replace it.
- **Lemma 3.11:** audit the meaning of a proper definable subset, including
  nonemptiness and the exact parameter set. Avoid a vacuous empty-subset claim.
- **Lemma 3.15:** `InfRVDefGam` still exposes uniform boundedness and a
  C-minimality consequence as hypotheses. They must be proved from the actual
  theory before the paper lemma is reported closed.

## Suggested proof order and completion criteria

First finish the post-QE Section 2 items in `TARGETS.md`; C-minimality is a
central missing dependency. Develop sorted closure and compactness tools,
then 3.1--3.5, exchange and 3.7, the average/coding and center results,
3.12--3.15, and the quotient/set-valued language and 3.17--3.19.
Adjust the order when actual dependencies require it; keep each paper number
and each remaining premise visible in the status table.

For every item, record its precise paper statement, imported definitions,
parameter and characteristic assumptions, remaining standard hypotheses,
compiler exit code, and `#print axioms` on the exported theorem. A wrapper
around an unproved Prop is still conditional. A test of one intended valued
field does not establish the assertion over all models. Do not silently weaken
definability, replace a definable function by arbitrary choice, or narrow tuple
arity to make a target easy. Finish and check one coherent module at a time.

## Prompt for the new session

> Read AGENTS.md and Section3/HANDOFF.md. QE is complete in the pinned ACVF-QE
> dependency. Formalize all of Section 3 and all material in Section 2 after
> Theorem 2.3, following Section3/TARGETS.md. Audit and reuse the relocated
> candidates; old headers are not current proof status. Preserve the author's
> language and parameter conventions, use the completed QE proof directly,
> and keep working locally without pushing the paper repository.
