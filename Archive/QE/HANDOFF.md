# Handoff: the QE thread (state at the six-part frontier, 2026-11-04)

*(Deliverable of swarm `smw2qpqe7` member m8 / direction u8: this text replaces the stale
`QE/HANDOFF.md`, whose "seven hypotheses / FINAL" frontier predates `QE/RouteLedger.lean`. To be
merged as `QE/HANDOFF.md`; the member's file scope is `.ultramath/smw2qpqe7/m8/`, so it sits here
until the judge merges it. The machine-checked detail is in `FRONTIER.md` next to it.)*

Read this first if you are picking up Theorem 2.3. The detail lives in `FRONTIER.md` (endgame list,
per-part status, route equivalences, census), `QE/MATRIX.md` (which hypothesis gives which part),
`QE/SHRINK.md` (why the list cannot be shortened), `QE/RELUNIT.md` (the unit half),
`QE/NonUnitNOTES.md` (the non-unit half), `QE/EP_LEDGER.md` (the Prestel–Engel quotes), and
`MILESTONES.md` (chronology, one section per accepted patch). `QE/README.md` and the
repository-root `HANDOFF.md` are history: their "Status" tables predate the `QE/` campaign.

## The target and the rules that have not changed

`Milestone0/Encoding.lean`'s frozen `theorem_2_3_quantifier_elimination : HasQE Axioms.ACVF`, plus the
frozen `theorem_2_8_c_minimal`. Both stay `sorry`ed on purpose: they are the deliverable, not a gap.
Everything else must compile green, and:

* never leave a file with errors, never add a `sorry`/`admit`/`native_decide`/`axiom`;
* `#print axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound};
* Marker's model theory and Prestel–Engler's valuation theory are QUOTED as `Prop`s and stay
  hypotheses of the final theorem (author ruling);
* never import `QE/Assembly_val.lean` (or `Pre_build`/`Pre2`/`PreC`/`AV`) next to the frozen
  encoding — module-name clash; `lean FILE.lean` writes no olean unless you pass `-o`;
* a hypothesis that is its own conclusion is worse than an open lemma: every new hypothesis gets the
  `⊤`-witness and cardinality stress test before the verdict, and a machine-checked counterexample to
  a tempting stronger form is a deliverable, not a failure.

## The frontier, in one screen

`HasQE Axioms.ACVF` follows from **five parts + one quotation**, at
`relGate M N = M1Fix.SatRel M N ∧ M7Paper.SizeHyp M N` (`QE/RouteLedger.lean`):

```
M5Shoenfield.ShoenfieldTestRel → RelHull → RelSeparated → RelUnit → RelNonUnit → RelNewRV → HasQE
                                 (3.3)      (3.7)          (3.4+3.6)   (3.5)        (3.8)
```

`RouteLedger.paper_theorem_2_3_of_five_rel`. The frozen-gate twin is
`RouteLedger.paper_theorem_2_3_of_five` (`M7Paper.ShoenfieldTestSat`, `M7Paper.PaperHyp`).

**The shape is forced.** `M5Shrink.input5R_iff_relHull_and_fourParts`: the conjunction of the five
parts is *equivalent* to `M5Shoenfield.Input5R` (Marker's saturated realisation), and at a single pair
to `M5Ledger.SaturationRealization` (`M6Matrix.fiveParts_pair_iff_satReal`). So the paper's §3 case
analysis is a rewriting of input 5, not a way around it; and no case slot can discharge `RelHull`
(`M5Shrink.hullExtension_iff_nonStanding`: all four slots assume `Standing S`).

**Status, one line each** (`FRONTIER.md` §2 has the theorem names):

* `RelHull` (3.3) — open. It *is* the frozen `Assembly.PrepStepP` (`M6Matrix.relHull_iff_prepStepP`);
  `M8Hull.standingHull` builds the least `Standing` superstructure inside `M`, so the open content is
  the map, and `M5Shrink.relHull_iff_baseRootResidual` splits it into `D7.HullBaseStep ∧
  D7.RootStepResidual`.
* `RelSeparated` (3.7) — open, and blocked on a defect: the tree's `M5L.OneStepSeparatedP` needs
  `M5L.VFInvClosedOn`, which `Assembly.Standing` does not give (no `VF`-inverse symbol).
  `Bookkeeping.caseSeparated_of_structuralResidual` states the exact residual;
  `Case35Hull.caseSeparated_of_rootHullEmbedding` bypasses it.
* `RelUnit` (3.4 + 3.6) — **assembled** (`QE/RELUNIT.md`). Two residuals: `RouteLedger.RootData`
  (3.4) and `RelUnit.TranscendentalRealisation` (3.6's `f^*`). 3.6's class half is *proved* from the
  paper's hypotheses without EP 3.4.3 (`RelUnit.transcendentalClaimStar_of_residueTranscendental`).
* `RelNonUnit` (3.5) — open, reduced to the realisation row `NonUnitAssembly.SlotTotalExt` /
  `SlotAtomic`; the hull row is `T = ⊤` (`NonUnitAssembly.nonUnitHull_holds`).
* `RelNewRV` (3.8) — open, class half proved (`M5LNewRV.ResidualClassesNew_of_VFGen`); what is missing
  is `Standing T` (the divisible hull, `NewRVGlue.hull_demand_of_standing`) plus the monomorphism.

**One residual closes all four case parts**: `Case35Hull.RootHullRealisation` ("`f` extends to
`rootHull S m`") implies `RelSeparated`, `RelUnit`, `RelNonUnit`, `RelNewRV`
(`Case35Hull.cases_of_rootHullEmbedding`; the `relGate` wiring is compiled in
`.ultramath/smw2qpqe7/m8/Probe.lean`). Its content is atomic realisation — saturation, not algebra.
So the frontier can be read as **2 parts + the quotation**.

## Two shortcuts, and why neither can be taken

* **Granting `QFFinSat`.** `G3.paper_theorem_rel_of_qffinsat : ShoenfieldTestRel → (∀ relGate pairs,
  QFFinSat) → HasQE` is a theorem, and it implies all five parts (`M6Matrix.fiveParts_of_finSat`). But
  the hypothesis is **refutable**: `M6Matrix.not_finSatAtRelGate_of_config` (and
  `G3.not_forall_qffinsat_at_relGate`) — at a `relGate` pair with an Archimedean target carrying an
  infinitesimal over an embeddable substructure, the pushed type is not finitely satisfiable. The
  canonical single-hypothesis form is therefore the split `M6Matrix.paper_theorem_rel_of_finSat_split :
  ShoenfieldTestRel → M8NV.FinSatAtArchimedean → FinSatOffArchimedean → HasQE`, and the case lemmas
  3.4–3.8 need be proved **only at non-Archimedean targets**.
* **The frozen seven-hypothesis route.** `QE/FinalRoute.lean`'s `FinalHyp` and
  `M4Cases.paper_theorem_2_3_sat_of_cases` still compile, but `QE/FinalAudit.lean` collapsed them:
  inputs 1, 2, 3, 4 and the paper-pair one-step are *not used*, and the route is
  `ShoenfieldTestSat → Prop39Sat → HasQE` (`FinalAudit.paper_theorem_FINAL2` / `.paper_theorem_FINAL3`,
  `FinalAudit.FINAL2_iff_FINAL3`, `FinalAudit.ledgerInput5P_iff_prop39Sat`). The seven-hypothesis text
  in the old `HANDOFF.md` is superseded; do not re-derive the collapse.

## Traps that have already cost this project time

* **`M8.Lemma36Hyp` (the merged Lemma 3.6) is inconsistent** — `RouteLedger.lemma36Hyp_false`,
  `.not_exists_lemma36Hyp`. `Assembly.KEqTop S` puts `rv e` itself into `S`, so the polynomial
  `X − rv e` violates `M8.RVTrans`. The repair is `RouteLedger.RVTransVF` (coefficients restricted to
  `rv '' (S ∩ VF)`), and `RelUnit.merged_lemma36_hyp_no_instances` records the consequence. Any
  "wire 3.6 in" plan must start from the repair.
* **`QFFinSat` / `Prop39Sat` / `Input5R` / `LedgerInput5P` are not theorems at every paper pair**
  (`G3.not_prop39Sat_of_archimedean_config`, `G3.not_ledgerInput5P_of_config`,
  `M8NV.refutingConfig_not_input5R`); `∀ N, ¬ SaturatedFS N` is false as written
  (`M5Gate.not_forall_not_saturatedFS`) — the correct form is `M5Gate.NoSatModel`.
* **`M5L.ResidualClasses` cannot be a branch conclusion** — perturbation points satisfy the slot's
  hypotheses and fail it for every `T` (`Case35.not_residualClasses_of_perturbation`); and 3.5's
  `m^n = a` shape is inconsistent at `Standing S` (`Case35.not_rootStepHyp_of_standing`).
* **`M5L.VFInvClosedOn` is not `Standing`-derivable** (`QE/OneStepCases.lean` §2) — the separated
  slot and 3.6 keep inheriting this defect.
* **Units and `X^n − a` roots are never `M5L.Separated`** (`M5P1.not_separated_of_units`,
  `Lemma36AuditACVF.not_separated_of_vpow_mem`): `CaseSeparated` is 3.7's infinite-order regime only,
  and the merged `QE/OneStepCases.lean` docstring that puts 3.4/3.6 there is wrong.
* **The encoding is one-sorted and tagged.** `Substructure.closure` contains ill-sorted applications,
  `Γ(S)` is only a submonoid (no inverse symbol), and `K(Ŝ)` cannot be restricted to `rv '' (S ∩ VF)`.
  Several paper statements have no direct transcription; say so in the header rather than
  strengthening the frozen statement.

## Census and how to re-measure

`make milestones` over `Milestone0/*`, `Milestone0/accepted/*`, `QE/*`:

```
$ cd $R && make milestones                    # HEAD = 9e94ed1, make exit 0
$ wc -l < milestones.out                      # 195 QE/*.lean + 20 Milestone0{,/accepted}/*.lean
215
$ grep -c 'exit=0'   milestones.out ; grep -c 'errors=0' milestones.out
215
215
$ grep 'sorries=[1-9]' milestones.out
Milestone0/Encoding.lean                       exit=0 errors=0 sorries=2
QE/Assembly_val.lean                           exit=0 errors=0 sorries=2
QE/Sec3_frozen.lean                            exit=0 errors=0 sorries=4
QE/Sec3_sat.lean                               exit=0 errors=0 sorries=8
QE/TransferWS.lean                             exit=0 errors=0 sorries=2
                                              # 18 sorrys in 5 files; 0 errors, 0 non-zero exits
```

18 `sorry`s, all of them frozen or pre-repair snapshots: `Milestone0/Encoding.lean` 2 (the two frozen
targets), `QE/Assembly_val.lean` 2 (their copies), `QE/Sec3_frozen.lean` 4, `QE/Sec3_sat.lean` 8,
`QE/TransferWS.lean` 2. `Milestone0/Balls.lean` is sorry-free.

Re-measure with `cd $R && make milestones` (~3 s/file warm; `make enc` builds `Enc.olean` into
`.scratch2/sec3/` first). Work leaves in `.ultramath/<swarm>/m<n>/`; compile with
`LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean FILE.lean` and paste the real `#print axioms` lines in
the header — that is what gets a file accepted.
