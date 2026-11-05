# m2 / u2 — `RelNonUnit`: what the non-unit slot actually costs

File: `NonUnitAssembly.lean` (this directory).  Verified with

    cd $R && LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean .ultramath/smw2qpqe7/m2/NonUnitAssembly.lean

exit 0, 0 `error`, 0 warnings, no `sorry`/`admit`/`native_decide`, no new `axiom`; 26 `#print axioms`
lines, every one ⊆ {propext, Classical.choice, Quot.sound} (see `verify.log`).  Imports: `RouteLedger`, `SatReal`,
`Prop39Decomp`, `InterfaceClosure`, `Case35Slot`, `OneStepCases` (no `Assembly_val`, no `Pre*`).

## The result

`RouteLedger.NonUnitSlot` (Lemma 3.5's surviving branch, exponent-one form) has three rows:
a **pure-`M` hull row** (`T ⊇ S`, `m ∈ T`, `Standing T`), an **`N`-realisation row** (`g : T ↪ N`
extending `f`), and the hypothesis rows (`Standing S`, `iVF m`, `iRv m ∈ S`,
`¬ iUnits (iRv m)`, `¬ M5L.Separated S m`).

1. **The hull row is empty, not residual.**  `NonUnitHull` (the hull row as a `Prop`) is *proved
   unconditionally* — `nonUnitHull_holds`, witness `T = ⊤` (`StandingTree.standing_top`).  So no
   `Γ`-divisibility, no exponent-one normal form, no `m^n = a` construction is needed for `T`.
2. **The whole slot follows from a hypothesis that never mentions `m`**: `nonUnitSlot_of_extAlongStanding`
   — monomorphisms extend along inclusions of `Standing` substructures (`ExtAlongStanding`).
   `M5Ledger.SaturationRealization` (input 5) gives it (`nonUnitSlot_of_satReal`), `QFSat` gives it
   (`nonUnitSlot_of_qfsat`), and at `relGate` (`SatRel ∧ SizeHyp`) `QFFinSat` gives it:
   **`relNonUnit_of_qffinsat : (∀ relGate pairs, QFFinSat) → RelNonUnit`**.
3. **The exact weakest realisation row** is `SlotTotalExt`: total extension of `f` demanded only at
   `Standing S` that carry a slot point (if none, the slot is vacuous at `S`).
   `nonUnitSlot_of_slotTotalExt`; the `⊤`-witness costs `#M ≤ #N` (`slotTotalExt_forces_size`),
   which `relGate`'s `SizeHyp` supplies.
4. **Consequence for the endgame list**: `RelNonUnit` is implied by the input that the alternative
   route already consumes — `paper_theorem_2_3_of_rel_parts_no_nonunit` (the other four parts +
   `QFFinSat` give the frozen target).

## The sandwich: what the slot's `N`-side really is

Two routes bracket the slot exactly:

* **`⊤` route** (`t = ⊤`): needs a *total* extension, hence `#M ≤ #N`.
* **Generated-substructure route** (`T = closure (S ∪ {m})`): needs only *per-element* atomic
  realisation at the slot points (`SlotAtomic`) plus `Standing` of the closure —
  `nonUnitSlot_of_slotAtomic_and_closureStanding` (through `M3Slot.exists_oneStep_closure`).

and atomic realisation is *necessary*: `slotAtomic_of_nonUnitSlot` reads it off the slot's own
witness (`M2Saturation.realizesAtomic_of_extends`).  So the slot's model-theoretic content is
per-element realisation, not saturation (`#M ≤ #N` is only the price of choosing `⊤`), and
`SlotAtomic` is the restricted (`QFSat` ⟹ `SlotAtomic`) form of the realisation row.

## Why the hull row is empty (diagnosis, not accident)

`M5Ledger.DivisibilityStep` — the tree's transcription of the paper's divisible-hull step — carries
`M5Ledger.GammaHullInitial S T` in its conclusion, and its docstring says this clamp is "what forbids
`T = ⊤`".  The four slots of `M4Cases.Cases` (`CaseSeparated`, `CaseNotSeparated`, `OneStepRVNew`,
hence `UnitSlot`/`NonUnitSlot`) carry **no** such clamp, so `T = ⊤` discharges their hull rows.  This
is a property of the *slot statements*, not of `M`: a paper-faithful non-unit slot would have to
carry the clamp.  Recorded here as `ClampedNonUnitHull` (+ `nonUnitHull_of_clamped`,
`gammaHullInitial_top_top` shows the clamp is satisfiable, so a clamped slot is not vacuous).

The same argument applies verbatim to the other three slot rows (`UnitSlot`, `CaseSeparated`,
`CaseNewRV = M5.OneStepRVNew`), all of which have the same `∃ T g, S ≤ T ∧ agree ∧ m ∈ T ∧
Standing T` shape.  I did **not** claim those — they belong to m1/m3/m4 — but they follow by the same
three lines, and the tree already has `M5.oneStepVFP_top` for the shape.

## The paper-shaped route is closed (machine-checked)

The alternative is to extend to the *generated* substructure `closure (S ∪ {m})`
(`nonUnitSlot_of_closureRealisation_and_standing`: per-element atomic realisation + `Standing` of the
closure).  The tree's bridges from class control to `Standing` are `M5L.standing_of_ClassControl` and
`M5.standing_of_RV_le`; both consume class control (`M5L.ResidualClasses`, `RV`-control).  At a
**perturbation point** `m = y + ε` (`y ∈ S ∩ VF` old, `ε` of a class that is no old class):

* `not_residualClasses_of_perturbation_at_slot` — `ResidualClasses S ⊤` fails (Case35's theorem at
  `T = ⊤`; it holds for *every* `T ⊇ S ∪ {m}` by Case35 §3c);
* `not_rvControl_of_perturbation_at_slot` — `RV`-control fails as well (it is stronger);
* `perturbation_rv_mem_at_slot` — and these points *are* slot points (`iRv m ∈ S` by
  `Case35.perturbation_rv_mem`).

So at a sub-regime of the slot the class-control interfaces are not merely unproved: they are false.
`Case35.NotSeparatedBranch` is therefore only a *sufficient* interface, and its hypothesis row adds
nothing: `branch_hypothesis_is_slot_hypothesis` — under `Standing S` and `IsVFGen S`, its
`RVOldClass S m` is *equivalent* to the slot's own `¬ M5L.Separated S m`
(`Case35.notSeparated_iff_RVOldClass`).  Only the branch's conclusion restricts.

## Why the tree's polynomial/ratio assets cannot apply here

`NonUnitSlot`'s hypothesis is `¬ M5L.Separated S m`.  Every one of the tree's expansion/ratio
theorems takes `M5L.Separated S e` as a *hypothesis*:

* `M5L.ResidualClasses_of_VFGen` (QE/M5L34_36.lean) — `hsep : Separated S e`;
* `M3Slot.ResidualClasses_of_poly`, `M3Slot.rv_mem_of_polyExpansions` (QE/InterfaceClosure.lean) —
  same;
* `Bookkeeping.bookkeeping_half` (the Γ/RV half, QE/Bookkeeping.lean §413) — `hsep : Separated S e`.

So none of them can be instantiated at the non-unit slot: they are the *separated / new-`rv`* side
(`CaseSeparated`, `CaseNewRV`), which is why the direction's suggestion to combine them with
`Case35Slot.lean` cannot close this slot, and why the exponent-one form
(`Case35.notSeparated_class_form` / `RVOldClass`) is the only use the tree makes of the non-unit
hypothesis.  The `m^n = a` (RootStepHyp) shape is *inconsistent* at `Standing` VF-generated `S`
(`Case35.not_rootStepHyp_of_standing`), so Lemma 3.5's construction, as transcribed, has no instance
at the slot.

## Non-vacuity (the hypothesis cone is inhabited in every model)

* `exists_nonunit` — **new extraction of the axiom `Axioms.axNontrivialRV`**: every model of `ACVF`
  has `m` with `iVF m`, `m ≠ 0`, `¬ iUnits (iRv m)`.  Read off through `Assembly.real_exSorted_vf`
  and `RVCalc.units_iff_le_one`; the tree had no extraction of this axiom.
* `exists_nonUnit_hyp_top` — at `S = ⊤` **every** `NonUnitSlot` hypothesis holds simultaneously
  (`Standing ⊤`, `iVF m`, `iRv m ∈ ⊤`, `¬ iUnits (iRv m)`, `¬ Separated ⊤ m`); hence the slot is not
  a vacuous implication, and its `∀` is not empty.
* `unit_and_nonunit_both_occur` — both halves of the 3.4/3.6 vs 3.5 split are inhabited.
* `nonUnitSlot_concl_of_mem` — the `m ∈ S` case is trivial, so the slot's content is only at new
  elements.

## What is left for u2 (honest residual)

Exactly one of two rows, depending on the route:

* **`⊤` route**: the realisation row, in any of the forms `ExtAlongStanding` / `SlotTotalExt` /
  `G3.ExtendsHere` / `M5Ledger.SaturationRealization` / `M2Saturation.QFSat` — all implied by
  `QFFinSat` at `relGate` (`relNonUnit_of_qffinsat`).  No pure-`M` content at all.
* **generated-substructure route**: `SlotAtomic` (per-element realisation) + the pure-`M` row
  `Standing (closure (S ∪ {m}))` at slot points.  §5 shows the class-control interfaces cannot
  produce the second row there, so if this route is to be taken the pure-`M` row needs a *new*
  argument (not `ResidualClasses`, not `RV`-control).  If the swarm wants the slot to carry Lemma 3.5's content, the
slot statement must be clamped by `GammaHullInitial` (as `M5Ledger.DivisibilityStep` is); that is a
change to the *frontier's slot statements*, not a proof obligation on `M`.
