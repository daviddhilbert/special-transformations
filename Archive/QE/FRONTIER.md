# FRONTIER — the exact state of Theorem 2.3's reduction

*(Deliverable of swarm `smw2qpqe7` member m8 / direction u8. To be merged as `QE/FRONTIER.md`; the
member's file scope is `.ultramath/smw2qpqe7/m8/`, so this file sits here until the judge merges it.
Same for `HANDOFF.md` next to it, which replaces the stale `QE/HANDOFF.md`.)*

**Target.** `Milestone0/Encoding.lean`'s frozen `theorem_2_3_quantifier_elimination : HasQE Axioms.ACVF`.
**This document** is the endgame list, per-part status, route equivalences, sorry census and the
first moves for a new session. It is written to be *checked*, not believed: every declaration it
names is `#check`ed by `Cites.lean` (same directory), and every structural claim is either a named
theorem here or a `#check` of one.

Baseline of the numbers below: `make milestones` run over the tree at commit `9e94ed1`
(2026-11-04). The tree moves while the swarm runs — **re-measure before quoting**:

```
cd $R && make milestones                      # one line per file: exit / error / sorry counts
ls QE/*.lean | wc -l                          # QE file count
git log --oneline -8                          # what landed since this document was written
```

Declarations are named `<namespace>.<declaration>`, `#check`ed by `Cites.lean`. The namespace is the
file name except for: `M5P1` → `Case34Slot`, `Case35` → `Case35Slot`, `Case35Hull` → `RootHull`,
`D7` → `D7Hull`, `M6Matrix` → `Matrix`, `M5Shrink` → `Shrink`, `M8Hull` → `StandingHull`, `M5Gate` →
`Gate`, `M8NV` → `NonVacuity2`, `M5LNewRV` → `NewRVClaim`, `M2Saturation` → `SatReal`, `M5Shoenfield`
→ `ShoenfieldQuote`, `M7Paper` → `PaperRoute`, `M4Cases` → `OneStepCases`, `M8` →
`Lemma36Statement`/`UnitCase`, `M7` → `UnitTranscend`.

`QE/HANDOFF.md` is the same content in narrative form; the per-direction notes are `QE/MATRIX.md`
(u6), `QE/RELUNIT.md` (u1), `QE/NonUnitNOTES.md` (u2), `QE/SHRINK.md` (the frontier's shape),
`QE/EP_LEDGER.md` (Prestel–Engel quotes). `QE/README.md` and the repository-root `HANDOFF.md`
predate the `QE/` campaign: read them as history, not as status.

---

## 1. The frontier: five parts + one quotation, at `relGate`

`relGate M N = M1Fix.SatRel M N ∧ M7Paper.SizeHyp M N` (`QE/ShoenfieldQuote.lean`) is Marker's
`‖M‖⁺`-saturation read pair-relatively, plus `#M ≤ #N`. Everything below is stated at that gate, in
the vocabulary the merged files already use.

```
QE/RouteLedger.lean
  paper_theorem_2_3_of_five_rel :
    M5Shoenfield.ShoenfieldTestRel      -- the QUOTATION (Marker's test; author ruling: stays a hypothesis)
    → RouteLedger.RelHull               -- L33  Lemma 3.3, hull form   = frozen Assembly.PrepStepP
    → RouteLedger.RelSeparated          -- 3.7  e:transc, M5L.Separated
    → RouteLedger.RelUnit               -- 3.4 + 3.6, the ¬Separated UNIT half = RouteLedger.UnitSlot
    → RouteLedger.RelNonUnit            -- 3.5  lift:divisible:hull, the non-unit half
    → RouteLedger.RelNewRV              -- 3.8  lift:value:full = M4Cases.CaseNewRV = M5.OneStepRVNew
    → HasQE Axioms.ACVF
```

Definitions: `RouteLedger.RelHull`, `.RelSeparated`, `.RelUnit`, `.RelNonUnit`, `.RelNewRV`,
`.RelCases`, `.UnitSlot`, `.NonUnitSlot`; frozen-gate twins `RouteLedger.GatedHull`,
`.GatedSeparated`, `.GatedUnit`, `.GatedNonUnit`, `.GatedNewRV` with endgame
`RouteLedger.paper_theorem_2_3_of_five` (quotation `M7Paper.ShoenfieldTestSat` at
`M7Paper.PaperHyp`). `RouteLedger.relCases_of_parts` and `RouteLedger.gatedCases_of_parts`: the four
case parts give `M4Cases.Cases`, slot by slot.

**The list is forced, not chosen.** `M5Shrink.input5R_iff_relHull_and_fourParts` proves

    M5Shoenfield.Input5R  ⟺  RelHull ∧ RelSeparated ∧ RelUnit ∧ RelNonUnit ∧ RelNewRV,

and at a single pair `M6Matrix.fiveParts_pair_iff_satReal` proves the five parts ⟺ that pair's
`M5Ledger.SaturationRealization`. So the conjunction of the five parts *is* Marker's saturated
realisation: slicing §3 into the paper's case lemmas is a rewriting of input 5, not a way around it.
Two further structural facts to know before proposing a restructuring:

* `M5Shrink.hullExtension_iff_nonStanding` — Lemma 3.3's map half costs nothing at `Standing`
  domains (`D7.hullExtensionAt_of_standing`), so `HullExtension` is *equivalent* to its restriction
  to non-`Standing` domains. Every case slot's hypothesis list begins with `Assembly.Standing S`, so
  **no case slot can discharge `RelHull`**; it stays a separate hypothesis (or is proved from
  saturation).
* `M5Shrink.relGate_units_card`, `.relGate_no_card_obstruction` — `relGate`'s size conjunct already
  gives `#Kˣ(M) ≤ #N`, the only cardinality the hull form forces
  (`RouteLedger.gatedHull_forces_units_size`). No size obstruction remains at `relGate` pairs.

## 2. Per-part status

| part | paper | what discharges it (machine-checked) | exact residual |
|---|---|---|---|
| `RelHull` | 3.3 | `M6Matrix.relHull_iff_prepStepP` (it *is* the frozen `Assembly.PrepStepP`); `M5Ledger.prepStepPaper_of_ledger` from ledger inputs 1–5; `M8Hull.standingHull`, `.standing_standingHull`, `.standingHull_le` build the least `Standing` superstructure inside `M`, so Lemma 3.3 = "extend the monomorphism to that fixed hull" | the hull: `M5Shrink.relHull_iff_baseRootResidual` splits it into `D7.HullBaseStep ∧ D7.RootStepResidual` (`D7.extendsHere_iff_steps_and_oneStep`); `D7.not_hullBaseStep_of_cardinality`, `.hullBaseStep_KEqTop_trivial`, `.rootStepResidual_standing_trivial` say which halves are contentful |
| `RelSeparated` | 3.7 | `M6Matrix.relSeparated_of_oneStepSeparatedP`: the tree's `M5L.OneStepSeparatedP` **plus `M5L.VFInvClosedOn`**; `Bookkeeping.caseSeparated_of_structuralResidual`: realisation + `Assembly.IsVFGen T` + `M5L.QuotExpansions S T m` + `VFInvClosedOn S`; `QE/Lemma37.lean` is the Mathlib-level value computation | `M5L.VFInvClosedOn` is **not** derivable from `Standing` (the language has no `VF`-inverse symbol; `M5P1.vfInvClosedOn_top` gives it only at `⊤`); or the embedding into `Case35Hull.rootHull S m`, which bypasses all of it (`Case35Hull.caseSeparated_of_rootHullEmbedding`) |
| `RelUnit` | 3.4 + 3.6 | **assembled** (`QE/RELUNIT.md`): `RelUnit.relUnit_of_gated_parts`, `.relUnit_of_rootHullRealisation`, `.unitSlot_of_34_and_36`, `.paper_theorem_2_3_of_parts`; `M5P1.Slot34` is a theorem (`RelUnit.slot34_holds`), `¬ Separated` is derived not assumed (`RelUnit.unitSlot_iff_no_separated`), and the slot conclusion collapses to the closure embedding (`RelUnit.slotConcl_iff_closureEmbedding`) | two named pieces: `RouteLedger.RootData` (3.4: monic `F` over `O(Ŝ)` with irreducible projection + henselianity) and `RelUnit.TranscendentalRealisation` (3.6's `f^* : ⟨Ŝ,m⟩ → N`). 3.6's *class* half is proved from the paper's hypotheses without EP 3.4.3 (`RelUnit.residualClasses_closure_of_residueTranscendental`, `.transcendentalClaimStar_of_residueTranscendental`, on `QE/UnitTranscend.lean`'s `M7.gamma_step`) |
| `RelNonUnit` | 3.5 | `M6Matrix.relNonUnit_of_branch` (from `Case35.NotSeparatedBranch`); `NonUnitAssembly.nonUnitSlot_of_extAlongStanding` — extension along `Standing` inclusions, a hypothesis that never mentions `m`, `¬iUnits` or `¬Separated`; `NonUnitAssembly.nonUnitHull_holds` (the hull row is `T = ⊤`, costing exactly `relGate`'s size) | the realisation row: `NonUnitAssembly.SlotTotalExt` / `SlotAtomic` (sandwich `slotAtomic_of_qfsat` + `nonUnitSlot_of_slotAtomic_and_closureStanding`). `M5L.ResidualClasses` cannot be the branch's conclusion (`Case35.not_residualClasses_of_perturbation`), and the `m^n = a` shape is inconsistent at `Standing S` (`Case35.not_rootStepHyp_of_standing`, `Case35Hull.lemma35_hyp_is_newRV`) |
| `RelNewRV` | 3.8 | `M6Matrix.relNewRV_iff_oneStepRVNew` (definitional); the class half is a theorem without quotation (`M5LNewRV.ResidualClassesNew_of_VFGen`, `M5LNewRV.claimStarNewRV_holds`); `NewRVGlue.oneStepRVNew_of_total_extension` is the only positive source | `Standing T` (the divisible hull of `Γ(S)+ℤ·vv(m)`: `NewRVGlue.hull_demand_of_standing`, `.hull_demand_of_oneStepRVNew`) together with the monomorphism `T ↪ N`. No value/residue algebra produces it: `NewRVGlue.not_caseNewRV_of_infinitesimal` |

Three attribution facts that keep being mis-stated, all machine-checked in `QE/Case34Slot.lean` and
`QE/Lemma36Audit.lean`: a unit is **never** `M5L.Separated` (`M5P1.not_separated_of_units`,
`Lemma36AuditACVF.separated_not_units`); an `X^n − a` root never is either
(`Lemma36AuditACVF.not_separated_of_vpow_mem`); so `CaseSeparated` is the *infinite-order* regime of
3.7 only and is empty at `VF`-generated substructures (`Lemma36AuditACVF.caseSeparated_empty_of_vfgen`).
3.4, 3.5, 3.6 all live in `¬ Separated`; the unit and non-unit halves are exhaustive
(`M5P1.caseNotSeparated_iff_unit_and_nonunit`, `M6Matrix.unit_nonunit_iff_notSeparated`).

## 3. The three routes, and how they are related

| route | statement | file |
|---|---|---|
| two-hypothesis (quotation + Marker's input 5) | `G3.paper_theorem_rel_two : ShoenfieldTestRel → M5Shoenfield.Input5R → HasQE` | `QE/Prop39Decomp.lean` |
| finite satisfiability | `G3.paper_theorem_rel_of_qffinsat : ShoenfieldTestRel → (∀ relGate pairs, QFFinSat) → HasQE` | `QE/Prop39Decomp.lean` |
| case-lemma ledger (the frontier) | `RouteLedger.paper_theorem_2_3_of_five_rel : ShoenfieldTestRel → RelHull → RelSeparated → RelUnit → RelNonUnit → RelNewRV → HasQE` | `QE/RouteLedger.lean` |

Machine-checked relations:

* `RouteLedger.relHull_and_cases_iff_input5R` and `M5Shrink.input5R_iff_relHull_and_fourParts`:
  route 1 ⟺ route 3 (the hypothesis conjunctions are equivalent, so the endgames are one assertion).
* `G3.input5R_of_relGate_finSat` with `G3.extendsAt_rel_finSat`: route 2 ⇒ route 1; and
  `M6Matrix.fiveParts_of_finSat` gives the five parts from route 2's hypothesis directly.
* `M6Matrix.two_routes_agree`; `M6Matrix.paper_theorem_rel_of_finSat_via_parts` recovers route 2
  *through* the five parts.
* Frozen gate: `RouteLedger.paper_theorem_2_3_of_hull_and_cases` (L33 + L3x + `ShoenfieldTestSat`),
  `RouteLedger.paper_theorem_2_3_of_five`, `M6Matrix.paper_theorem_sat_of_finSat`, and the collapsed
  legacy form `FinalAudit.paper_theorem_FINAL2` / `.paper_theorem_FINAL3` with
  `FinalAudit.FINAL2_iff_FINAL3`, `FinalAudit.ledgerInput5P_iff_prop39Sat`,
  `FinalAudit.reduced_final_is_the_criterion`.
* `RouteLedger.gatedHull_and_cases_iff_ledgerInput5P`: at the frozen gate the five parts are exactly
  `M5Ledger.LedgerInput5P`; at `relGate` exactly `Input5R`. `M5Shoenfield.paperGate_le_relGate`: the
  frozen gate is the smaller one, so honest-gate obligations give frozen-gate ones.

## 4. Two reductions that shorten the list, and one that cannot be made

**(a) The four case parts come from ONE gate-free residual.** `Case35Hull.standing_rootHull` proves
`Assembly.Standing (rootHull S m)` for **every** standing `S` and **every** `m ∈ VF(M)`, inside `M`,
with no saturation. Hence

    Case35Hull.cases_of_rootHullEmbedding :
      (∀ S f, Standing S → ∀ m, iVF m → (f extends to rootHull S m ↪ N)) → M4Cases.Cases

so `Case35Hull.RootHullRealisation` (the named residual: "`f` extends to the root hull") implies all
of `RelSeparated`, `RelUnit`, `RelNonUnit`, `RelNewRV` — `Case35Hull.oneStepVFP_of_rootHullEmbedding`,
`Case35Hull.oneStepPaper_of_rootHullRealisation`, `Case35Hull.paper_theorem_2_3_of_rootHullRealisation`,
`RelUnit.relUnit_of_rootHullRealisation`, and at `relGate` the wiring in `Probe.lean`
(`relCases_of_rootHullRealisation`, `paper_theorem_2_3_of_relHull_rootHull`, compiled and
axiom-clean). So the frontier is **2 parts + the quotation**, and the residual contains no `Γ`-content:
`Case35Hull.standing_iff_rootClosedOn` shows the frozen `Standing` is `KEqTop ∧ RootClosedOn`, the
`Kˣ`-half is monotone (`KEqTop` of a superstructure is free), and
`Case35Hull.oneStepVFP_iff_rootClosed` shows the frozen one-step *is* its root-closed form. What
remains in (a) is the atomic-realisation half of §3 — saturation, not algebra.

**(b) The canonical single-hypothesis form is the Archimedean split.**
`(∀ relGate pairs, QFFinSat)` is **refutable**, not provable: `M6Matrix.not_finSatAtRelGate_of_config`
(the `∀`-form), `G3.not_forall_qffinsat_at_relGate` and `M6Matrix.not_finSat_of_config` (per pair) —
at a `relGate` pair with an Archimedean target carrying an infinitesimal over an embeddable
substructure, the pushed type is not finitely satisfiable. The sharpest surviving statement is

    M6Matrix.paper_theorem_rel_of_finSat_split :
      ShoenfieldTestRel → M8NV.FinSatAtArchimedean → FinSatOffArchimedean → HasQE

whose Archimedean half no refutation touches (`M6Matrix.no_refutingConfig_of_arch_half`), and which
implies the blanket form (`M6Matrix.finSatAtRelGate_of_split`); `M8NV.input5R_of_finSat_split` is the
same split at `Input5R`. So **the case lemmas 3.4–3.8 need be proved for non-Archimedean targets
only**; the Archimedean half is a separate obligation (`M8NV.FinSatAtArchimedean`).

**(c) What cannot be shortened.** The quotation `M5Shoenfield.ShoenfieldTestRel` is irreducible (the
only hypothesis mentioning `HasQE`); by (a)–(b) the rest of the list is exactly input 5.

## 5. Statements that are FALSE as written — do not re-prove them

Each was believed at some point in this project and is refuted machine-checkably. This is the
cheapest thing in the document to read twice.

| tempting statement | verdict | witness |
|---|---|---|
| Lemma 3.6 as merged: `M8.Lemma36Hyp S e` | **inconsistent** — no instances, in any model, at any `S` | `RouteLedger.lemma36Hyp_false`, `.not_exists_lemma36Hyp`, `.not_rvTrans_of_units`, `.not_rvTrans_top`: `Assembly.KEqTop S` puts `rv e` itself in `S`, so `X − rv e` breaks `M8.RVTrans`. Repair: `RouteLedger.RVTransVF` (coefficients restricted to `rv '' (S ∩ VF)`); consequence: `RelUnit.merged_lemma36_hyp_no_instances` |
| `QFFinSat` at every `relGate` pair | **false** at the Archimedean configuration | `M6Matrix.not_finSatAtRelGate_of_config`, `G3.not_forall_qffinsat_at_relGate`, `M8NV.not_finSat_of_satRel_of_archimedean_tiny` |
| `Prop39Sat` / `Input5R` / `LedgerInput5P` as theorems at every paper pair | **false** there (`SaturatedFS` does not exclude the configuration; genuine saturation does) | `G3.not_prop39Sat_of_archimedean_config`, `G3.not_extendsAt_rel_of_archimedean_config`, `G3.not_ledgerInput5P_of_config`, `M8NV.refutingConfig_not_input5R` |
| `QE/ShoenfieldQuote.lean` §5's hypothesis `∀ N, ¬ SaturatedFS N` | **false** (a subsingleton structure satisfies `SaturatedFS`) | `M5Gate.not_forall_not_saturatedFS`, `M5Gate.saturatedFS_of_subsingleton`; correct form `M5Gate.NoSatModel`, with `M5Gate.shoenfieldTestSat_iff_hasQE_of_noSatModel` and `M5Gate.satBridge_dichotomy` |
| `M5L.ResidualClasses S T` as the conclusion of the `¬Separated` branch | **refutable**: perturbations `m = y + ε` satisfy the slot's hypotheses and fail it for every `T` | `Case35.not_residualClasses_of_perturbation`, `Case35Hull.perturbation_notSeparated_without_classControl` |
| the `m^n = a ∈ VF(Ŝ)` shape of 3.5 at `Standing S` | **inconsistent** | `Case35.not_rootStepHyp_of_standing`; the surviving branch is exponent one, and at a `VF`-generated `S` it *is* the new-`rv` slot (`Case35Hull.lemma35_hyp_is_newRV`, `.not_mem_rv_of_separatedBelow`) |
| `M5L.VFInvClosedOn S` from `Assembly.Standing S` | **not derivable** (no `VF`-inverse symbol in the language) | `QE/OneStepCases.lean` §2; `M5P1.vfInvClosedOn_top` (it holds only at `⊤`) |
| `M4Cases.CaseNewRV` / `M5.OneStepRVNew` at an Archimedean configuration | **false** | `NewRVGlue.not_caseNewRV_of_infinitesimal`, `.not_cases_of_infinitesimal` |
| `M1QF.Frozen.StepObligation` (and `M5L.ClassStepP`) on the new-`rv` branch | **unsatisfiable** (it forces `iRv m ∈ S`) | `NewRVGlue.not_stepObligation_of_newRV`, `.not_classStepP_of_newRV` |
| `DivHullCover` (earlier work on 3.5) | **refuted** at `S = ⊤`, `m = 1` | `M5P1.divHullCover_refuted` |
| the frozen `SizeHyp` guard as the paper's hypothesis | **under-powered**: ledger input 1 forces `#K(M) ≤ #N` | `QE/M5Ledger.lean` §11; `M5Shrink.relGate_units_card` |
| `ClassicalProps.DivisibleHullExists` instantiated in the encoding | carries **no** hull information at `Γ(M)` (a hull of a divisible group is an isomorphism) | `HullAudit.divisibleHullExists_at_gammaMk_surjective`; the pinning theorem is `HullAudit.divisibilityStep_pins_hull`; `HullAudit.hull_clamp_not_pinning` shows the clamp alone is not enough |
| Prestel–Engel 3.4.3 as a *necessary* ingredient of 3.6 | **removable** | `M7.gamma_step`, `M7.val_sum_eq_one` (Mathlib level); `RelUnit.residualClasses_closure_of_residueTranscendental` (frozen level); `M7.unit_hypothesis_essential` shows the *unit* hypothesis cannot be dropped |

## 6. Census (real output)

`make milestones` over `Milestone0/*.lean`, `Milestone0/accepted/*.lean`, `QE/*.lean`:

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

Sorry-bearing files are exactly five: `Milestone0/Encoding.lean` 2 (the frozen
`theorem_2_3_quantifier_elimination` and `theorem_2_8_c_minimal`), `QE/Assembly_val.lean` 2 (their
verbatim copies in the `L_val` snapshot), `QE/Sec3_frozen.lean` 4, `QE/Sec3_sat.lean` 8,
`QE/TransferWS.lean` 2 — **18**, and no others. `Milestone0/Balls.lean` is sorry-free (its frozen
target was proved, statement verbatim). Nothing in `QE/` outside those files has a `sorry`, `admit`,
`native_decide` or a new `axiom`; the standing discipline is `#print axioms` ⊆
{propext, Classical.choice, Quot.sound} on every headline theorem.

## 7. What a newcomer should do first

1. **Read in this order**: this file → `QE/RouteLedger.lean` (the frontier; mostly docstrings) →
   `QE/MATRIX.md` → `QE/SHRINK.md` (why the list cannot be shortened) → the two frozen targets in
   `Milestone0/Encoding.lean`. Do not start from `QE-PLAN.md` (chronology) except to look up why
   something is the way it is.
2. **Reproduce the baseline**: `make milestones` (~3 s/file warm) and check §6. A red file blocks
   everybody: fix or revert it before anything else.
3. **Pick a residual, not a restatement.** What is open, ordered by how much of the route it closes:
   * `RelUnit.TranscendentalRealisation` (3.6's `f^* : ⟨Ŝ,m⟩ → N`) and `RouteLedger.RootData` (3.4's
     r1/r2/r3) — see `QE/RELUNIT.md`; a WIP for 3.4's embedding half is
     `.ultramath/smw2ox51x/m4/RootLift.lean` (39 KB, one parse error at :748).
   * `M8NV.FinSatAtArchimedean` — the Archimedean half of §4(b). `QE/NonVacuity2.lean` §2 settles its
     ordinal part (`M8NV.huge_ordinal_atoms_realizable`), so the work is the residue-field/quantifier
     part, which is QE for ACVF itself.
   * the hull base/root steps (`D7.HullBaseStep`, `D7.RootStepResidual`) — the `RelHull` row of §2.
   * `Case35Hull.RootHullRealisation` — one statement closing all four case parts (§4(a)); its
     content is atomic realisation, so it overlaps the second item: do not attack it twice.
4. **Do not**: add a `sorry`, an `axiom`, or `native_decide` in a headline theorem; import
   `QE/Assembly_val.lean` next to the frozen encoding (module-name clash); state a hypothesis that is
   its own conclusion without the `⊤`-witness and cardinality stress tests; or try to prove
   `QFFinSat` / `Prop39Sat` / `Input5R` globally — they are refutable (§5).
5. **When you have a result**: file it in `.ultramath/<swarm>/m<n>/`, compile with
   `LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean FILE.lean`, paste the real `#print axioms` output in
   the header, and say which of the six parts it moves. Partial results count; a red file does not.

## 8. Index of the notes

| file | what it holds |
|---|---|
| `QE/RouteLedger.lean` | the frontier definitions and the endgame theorems; §1 refutes the merged 3.6 |
| `QE/MATRIX.md` + `QE/Matrix.lean` | the per-part matrix: which hypothesis gives which part, and the exactness theorems |
| `QE/SHRINK.md` + `QE/Shrink.lean` | `Input5R ⟺ the five parts`; case slots cannot discharge `RelHull`; `relGate`'s size is the right size |
| `QE/RELUNIT.md` + `QE/RelUnit.lean` | the unit half assembled: 3.4 = `RootData`, 3.6 = class half (proved) + `TranscendentalRealisation` |
| `QE/NonUnitNOTES.md` + `QE/NonUnitAssembly.lean` | the non-unit half: `SlotTotalExt`/`SlotAtomic`, hull row trivial, the missing `GammaHullInitial` clamp |
| `QE/EP_LEDGER.md` | the Prestel–Engel quotes: what each supplies, what is removable |
| `QE/HANDOFF.md` | the same state in prose, with the build/verification discipline |
| `MILESTONES.md` | the chronological ledger, one section per accepted patch |
