/-
# m2 / u2 — `RelNonUnit`: the non-unit half of the not-separated slot, and where Lemma 3.5 lives

Member `m2`, swarm `smw2qpqe7`, direction `d6` (u2).  Target: the frozen frontier of
`QE/RouteLedger.lean`,

    `RelNonUnit` = ∀ `relGate` pairs, `NonUnitSlot`  (= Lemma 3.5's surviving branch,
    `QE/Case35Slot.lean`'s exponent-one form).

`NonUnitSlot` (`QE/RouteLedger.lean` §4) is

    ∀ S f, Standing S → ∀ m, iVF m → iRv m ∈ S → ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
      ∃ T g, S ≤ T ∧ (g extends f on S) ∧ m ∈ T ∧ Standing T,

so it has a **pure-`M` hull row** (`T`, `S ≤ T`, `m ∈ T`, `Standing T`) and an **`N`-realisation
row** (`g`), on top of its hypothesis rows

    H1 `Standing S`,  H2 `iVF m` + `iRv m ∈ S`,  H3 `¬ iUnits (iRv m)`,  H4 `¬ M5L.Separated S m`.

## What this file decides

**§1 The hull row is empty, not residual.**  `NonUnitHull` — the pure-`M` row — is a *theorem*, with
the `⊤`-witness: `Standing ⊤` is `StandingTree.standing_top`.  No `Γ`-divisibility, no exponent-one
form, no `m^n = a` construction enters.  This is not an accident of `M`: the tree's own
`M5Ledger.DivisibilityStep` records that `GammaHullInitial S T` is the clamp that "forbids `T = ⊤`",
and the four slots of `M4Cases.Cases` carry no such clamp.  Hence **the non-unit slot has no
pure-`M` content**: every residual it can have is in the realisation row.

**§2 The two rows, in general.**  `ExtAlongStanding` (extension along inclusions of `Standing`
substructures) + the hull row give `NonUnitSlot`; `M5Ledger.SaturationRealization` (input 5) and
`QFSat` give `ExtAlongStanding` (`nonUnitSlot_of_satReal`, `nonUnitSlot_of_qfsat`).

**§3 The exact (weakest) realisation row.**  `SlotTotalExt`: total extension `M ↪[LRV] N` of `f`,
demanded only at `Standing` `S` that carry a slot point.  `nonUnitSlot_of_slotTotalExt`; the tree's
`G3.ExtendsHere` (Proposition 3.9 at the pair) is such a hypothesis
(`slotTotalExt_of_extendsHere`); and the `⊤`-witness costs `#M ≤ #N` (`slotTotalExt_forces_size`),
which `relGate`'s `SizeHyp` supplies.

**§4 The gate-level deliverable.**  `relNonUnit_of_qffinsat`: **`QFFinSat` at `relGate` gives
`RelNonUnit`** — via `G3.qfsat_of_satRel_of_qffinsat`.  So this row of the six-part list is implied
by the input the alternative route (`G3.paper_theorem_rel_of_qffinsat`) already consumes
(`paper_theorem_2_3_of_rel_parts_no_nonunit`): Lemma 3.5's mathematics belongs to the *hull*
row of the decomposition (Lemma 3.3 / input 5), not to this slot.

**§5 The alternative (paper-shaped) route, and why it is not available.**  The generated
substructure `closure (S ∪ {m})` needs only *per-element* atomic realisation but must be `Standing`
(`nonUnitSlot_of_closureRealisation_and_standing`).  The tree's only bridge from class control to
`Standing` is `M5L.standing_of_ClassControl`, whose input `M5L.ResidualClasses S T` fails for *every*
`T ⊇ S ∪ {m}` at a perturbation point (`Case35.not_residualClasses_of_perturbation`), while the
slot's own hypotheses hold there (`nonUnit_perturbation_cone`, `Case35.perturbation_rv_mem`).  So the
paper-shaped route is closed to this tree, and the `⊤` route of §3 is the only one available — a
statement that is machine-checked here, not a guess.

**§5b The sandwich.**  The slot's `N`-side is *per-element* atomic realisation, not saturation:
`SlotAtomic` (one element of `N` per slot point) is **necessary** for the slot
(`slotAtomic_of_nonUnitSlot`, from the slot's own witness) and **sufficient** together with the
pure-`M` row `Standing (closure (S ∪ {m}))` (`nonUnitSlot_of_slotAtomic_and_closureStanding`), while
`QFSat` gives it (`slotAtomic_of_qfsat`).  So `#M ≤ #N` is only the price of choosing `T = ⊤`
(`slotTotalExt_forces_size`), and on the generated-substructure route the residual is a genuinely
pure-`M` row that §5 shows class control cannot supply.

**§6 Stress tests.**  The hypothesis cone is **inhabited in every model**: `exists_nonunit` extracts a
non-unit from the axiom `Axioms.axNontrivialRV` (the tree had no such extraction), and
`exists_nonUnit_hyp_top` then puts every slot hypothesis at `S = ⊤`.  The `m ∈ S` case is trivial
(`nonUnitSlot_concl_of_mem`), so the slot's content is only at genuinely new elements; and the tree's
branch hypothesis `Case35.RVOldClass` is *exactly* H4 under `Standing` + `VFGen`
(`branch_hypothesis_is_slot_hypothesis`), so `Case35.NotSeparatedBranch`'s only restriction is its
class-control *conclusion*.

No `sorry`, no `axiom`, no `native_decide`; the axiom audit is at the end.
-/
import RouteLedger
import SatReal
import Prop39Decomp
import InterfaceClosure
import Case35Slot
import OneStepCases

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Milestone0.NonUnitAssembly

/-! ## 1. The hull row is empty -/

/-- **The pure-`M` hull row of the non-unit slot**: at the slot's hypotheses there is a `Standing`
substructure `T ⊇ S` containing `m`.  (The realisation `g` is not part of this row.) -/
def NonUnitHull (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
      ∃ T : LRV.Substructure M, S ≤ T ∧ m ∈ T ∧ Assembly.Standing T

/-- **The hull row holds unconditionally**, with the `⊤`-witness (`StandingTree.standing_top`):
nothing about `Γ`-divisibility, the exponent-one normal form or Lemma 3.5's construction is needed
to produce `T`.  Compare `M5Ledger.DivisibilityStep`, whose conclusion carries the clamp
`GammaHullInitial S T` — the tree's own record that without it `T = ⊤` is available. -/
theorem nonUnitHull_holds (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] :
    NonUnitHull M :=
  fun _S _hS _m _hmVF _hmrv _hnu _hns =>
    ⟨⊤, fun _ _ => trivial, trivial, StandingTree.standing_top⟩

/-- The `⊤`-witness, written out: `⊤` is `Standing` and contains `S` and every element. -/
theorem nonUnitHull_witness {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (S : LRV.Substructure M) (m : M) :
    S ≤ (⊤ : LRV.Substructure M) ∧ m ∈ (⊤ : LRV.Substructure M) ∧
      Assembly.Standing (⊤ : LRV.Substructure M) :=
  ⟨fun _ _ => trivial, trivial, StandingTree.standing_top⟩

/-! ## 2. The two rows in general: hull row + extension along `Standing` inclusions -/

section TwoRows
variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- **The realisation row in the form the slot consumes it**: monomorphisms extend along inclusions
of `Standing` substructures.  (`M5Ledger.SaturationRealization` extends along *all* inclusions;
`Standing` is what the hull row produces, so this is the exact shape needed.) -/
def ExtAlongStanding (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S T : LRV.Substructure M) (hST : S ≤ T) (f : S ↪[LRV] N),
    Assembly.Standing S → Assembly.Standing T → ∃ g : T ↪[LRV] N, M5Ledger.Extends hST g f

/-- **The two rows give the non-unit slot.**  This is the exact decomposition of `NonUnitSlot` into
its pure-`M` hull row and its `N`-realisation row. -/
theorem nonUnitSlot_of_hull_and_extAlong [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hhull : NonUnitHull (M := M)) (hext : ExtAlongStanding (M := M) (N := N)) :
    RouteLedger.NonUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnu hns
  obtain ⟨T, hST, hmT, hT⟩ := hhull S hS m hmVF hmrv hnu hns
  obtain ⟨g, hg⟩ := hext S T hST f hS hT
  exact ⟨T, g, hST, hg, hmT, hT⟩

/-- Marker's saturated realisation (input 5) gives `ExtAlongStanding`: it extends along any
inclusion, so in particular along the `Standing` ones. -/
theorem extAlongStanding_of_satReal (h : M5Ledger.SaturationRealization (M := M) (N := N)) :
    ExtAlongStanding (M := M) (N := N) :=
  fun S T hST f _hS _hT => h S T f hST

/-- **The non-unit slot from Marker's saturated realisation at the pair.** -/
theorem nonUnitSlot_of_satReal [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : M5Ledger.SaturationRealization (M := M) (N := N)) :
    RouteLedger.NonUnitSlot (M := M) (N := N) :=
  nonUnitSlot_of_hull_and_extAlong (nonUnitHull_holds M) (extAlongStanding_of_satReal h)

/-- **The non-unit slot from quantifier-free type realisation at the pair** (`M2Saturation.QFSat`),
i.e. from "`N` realises the atomic type of every element of `M` over every substructure". -/
theorem nonUnitSlot_of_qfsat [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : M2Saturation.QFSat M N) : RouteLedger.NonUnitSlot (M := M) (N := N) :=
  nonUnitSlot_of_satReal (M2Saturation.satReal_of_qfsat h)


/-- **The sharpest form**: the non-unit slot follows from a hypothesis that does not mention `m`, the
non-unit condition, the exponent-one form or `¬ Separated` at all.  (Nothing about the slot's
hypotheses is consumed, because the hull row is `⊤` and `⊤` is `Standing`.) -/
theorem nonUnitSlot_of_extAlongStanding [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hext : ExtAlongStanding (M := M) (N := N)) :
    RouteLedger.NonUnitSlot (M := M) (N := N) :=
  nonUnitSlot_of_hull_and_extAlong (nonUnitHull_holds M) hext

end TwoRows

/-! ## 2b. What the paper's Lemma 3.5 would have to carry: the `GammaHullInitial` clamp

`M5Ledger.DivisibilityStep` is the tree's transcription of the paper's divisible-hull step, and its
conclusion carries `M5Ledger.GammaHullInitial S T` — the clamp that "forbids `T = ⊤`" (its own
docstring).  The four slots of `M4Cases.Cases` carry no such clamp, which is exactly why their
pure-`M` rows are trivial (§1).  Recording the clamped row here fixes what a *paper-faithful*
non-unit slot would have to prove. -/

section Clamped
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **The paper-faithful hull row**: `T ⊇ S`, `m ∈ T`, `Standing T`, and `Γ(T)` inside the hull of
`Γ(S)` up to roots and units (`M5Ledger.GammaHullInitial S T`). -/
def ClampedNonUnitHull (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
      ∃ T : LRV.Substructure M, S ≤ T ∧ m ∈ T ∧ Assembly.Standing T ∧
        M5Ledger.GammaHullInitial S T

/-- The clamp only removes the `⊤`-witness: it implies the unclamped row. -/
theorem nonUnitHull_of_clamped (h : ClampedNonUnitHull M) : NonUnitHull M :=
  fun S hS m hmVF hmrv hnu hns =>
    let ⟨T, hST, hmT, hT, _⟩ := h S hS m hmVF hmrv hnu hns
    ⟨T, hST, hmT, hT⟩

/-- The clamp is satisfiable (so a clamped slot is not vacuous): at `S = ⊤` the witness `T = ⊤` works
by `n = 1`, `s = t`, `c = 1`. -/
theorem gammaHullInitial_top_top :
    M5Ledger.GammaHullInitial (⊤ : LRV.Substructure M) (⊤ : LRV.Substructure M) := by
  intro t _ht hrv ht0
  refine ⟨1, t, iRVOne, by norm_num, trivial, hrv, ht0, StandingTree.rv_one_units (M := M), ?_⟩
  show iRVMul (Assembly.rvPow t 0) t = iRVMul t iRVOne
  show iRVMul iRVOne t = iRVMul t iRVOne
  rw [MulNormalForm.rv_mul_one_all hM hrv, MulNormalForm.rv_mul_one_right hM hrv]

end Clamped

/-! ## 3. The exact (weakest) realisation row

With the hull row discharged at `T = ⊤` the realisation row is a *total* extension of `f` — but only
at the `Standing` substructures that carry a slot point.  That is `SlotTotalExt`, and it is the
weakest hypothesis of this shape: if no slot point sits over `S`, the slot demands nothing at `S`. -/

section Exact
variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- **The exact realisation row.** -/
def SlotTotalExt (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S →
    (∃ m : M, iVF m ∧ iRv m ∈ S ∧ ¬ iUnits (iRv m) ∧ ¬ M5L.Separated S m) →
      ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-- **`SlotTotalExt` gives the non-unit slot** (the hull row is `nonUnitHull_holds`). -/
theorem nonUnitSlot_of_slotTotalExt [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hext : SlotTotalExt (M := M) (N := N)) :
    RouteLedger.NonUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnu hns
  obtain ⟨g, hg⟩ := hext S f hS ⟨m, hmVF, hmrv, hnu, hns⟩
  exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial, StandingTree.standing_top⟩

/-- Proposition 3.9 at the pair (`G3.ExtendsHere`) is the total-extension hypothesis with its
`∃`-guard removed. -/
theorem slotTotalExt_of_extendsHere (h : G3.ExtendsHere M N) :
    SlotTotalExt (M := M) (N := N) :=
  fun S f _hS _hpoint => h S f

/-- **The non-unit slot from Proposition 3.9 at the pair** — no case analysis, no Lemma 3.5. -/
theorem nonUnitSlot_of_extendsHere [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : G3.ExtendsHere M N) : RouteLedger.NonUnitSlot (M := M) (N := N) :=
  nonUnitSlot_of_slotTotalExt (slotTotalExt_of_extendsHere h)

/-- **The cost of the `⊤`-witness**: a total extension at a substructure carrying a slot point
forces `#M ≤ #N`, i.e. the gate's `M7Paper.SizeHyp` (supplied by `relGate`).  The paper-shaped
route of §5 does not consume it. -/
theorem slotTotalExt_forces_size (hext : SlotTotalExt (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S)
    (hpoint : ∃ m : M, iVF m ∧ iRv m ∈ S ∧ ¬ iUnits (iRv m) ∧ ¬ M5L.Separated S m) :
    Cardinal.mk M ≤ Cardinal.mk N := by
  obtain ⟨g, _⟩ := hext S f hS hpoint
  exact Cardinal.mk_le_of_injective (Embedding.injective g)

end Exact

/-! ## 4. The gate-level deliverable: `RelNonUnit` from `QFFinSat` at `relGate`

`M5Shoenfield.relGate M N` is `M1Fix.SatRel M N ∧ M7Paper.SizeHyp M N`: the saturation half that
`QFSat` needs is part of the gate, and `QFFinSat` supplies finite satisfiability. -/

/-- **`RelNonUnit` from `QFFinSat` at `relGate`.**  The non-unit half of the not-separated slot needs
no case analysis once finite satisfiability of the pushed types is granted at the honest gate. -/
theorem relNonUnit_of_qffinsat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    RouteLedger.RelNonUnit :=
  fun M N _ _ _ _ hR =>
    nonUnitSlot_of_qfsat (G3.qfsat_of_satRel_of_qffinsat hR.1 (hfin M N hR))

/-- `RelNonUnit` from total extension at the honest gate. -/
theorem relNonUnit_of_relExtendsHere
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M5Shoenfield.relGate M N → G3.ExtendsHere M N) :
    RouteLedger.RelNonUnit :=
  fun M N _ _ _ _ hR => nonUnitSlot_of_extendsHere (h M N hR)

/-- `RelNonUnit` from the localised realisation row at the honest gate. -/
theorem relNonUnit_of_relSlotTotalExt
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M5Shoenfield.relGate M N → SlotTotalExt (M := M) (N := N)) :
    RouteLedger.RelNonUnit :=
  fun M N _ _ _ _ hR => nonUnitSlot_of_slotTotalExt (h M N hR)

/-- **The endgame list with `RelNonUnit` removed**: the remaining four parts plus `QFFinSat` at
`relGate` give the frozen target.  (Weaker than `G3.paper_theorem_rel_of_qffinsat`, whose hypothesis
is `QFFinSat` alone; recorded because it is the exact sense in which this row of the six-part list is
*implied* by the input that the alternative route consumes.) -/
theorem paper_theorem_2_3_of_rel_parts_no_nonunit (hQ : M5Shoenfield.ShoenfieldTestRel)
    (hHull : RouteLedger.RelHull) (hsep : RouteLedger.RelSeparated)
    (hu : RouteLedger.RelUnit) (hnew : RouteLedger.RelNewRV)
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ hHull hsep hu (relNonUnit_of_qffinsat hfin) hnew

/-! ## 5. The paper-shaped route: the generated substructure

Lemma 3.5 does not use `⊤`: it extends `f` to the substructure generated by `S ∪ {m}`.  That route
needs only *per-element* atomic realisation, but it must prove `Standing` of the generated
substructure. -/

section Closure
variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- **The generated-substructure route.**  Rows: `hreal` — atomic realisation of the pushed type of a
slot point (a single element, not a total extension); `hstand` — `Standing` of the generated
substructure `closure (S ∪ {m})`.  (`M3Slot.exists_oneStep_closure` supplies the embedding of the
generated substructure and `m ∈ T`; the `m ∈ S` case is trivial.) -/
theorem nonUnitSlot_of_closureRealisation_and_standing [hM : M ⊨ Axioms.ACVF]
    [hN : N ⊨ Axioms.ACVF]
    (hreal : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M,
      iVF m → iRv m ∈ S → ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
        ∃ b : N, Realize.RealizesAtomic S f m b)
    (hstand : ∀ (S : LRV.Substructure M), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
      ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
        Assembly.Standing (Substructure.closure LRV ((S : Set M) ∪ {m}))) :
    RouteLedger.NonUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnu hns
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩
  · obtain ⟨b, hb⟩ := hreal S f hS m hmVF hmrv hnu hns
    obtain ⟨g, hST, hmT, hagree⟩ := M3Slot.exists_oneStep_closure (M := M) (N := N) hb hm
    exact ⟨_, g, hST, hagree, hmT, hstand S hS m hmVF hmrv hnu hns⟩

/-- **Per-element atomic realisation at the slot points** — the `N`-side content in the weakest
model-theoretic form (a single element of `N` per slot point, no total map, no cardinality). -/
def SlotAtomic (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M,
    iVF m → iRv m ∈ S → ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
      ∃ b : N, Realize.RealizesAtomic S f m b

/-- **The slot implies per-element atomic realisation** — the `N`-side of `NonUnitSlot`, with the
`T`-row discarded (`M2Saturation.realizesAtomic_of_extends` applied to the slot's own witness).
Together with `nonUnitSlot_of_closureRealisation_and_standing` this sandwiches the slot: atomic
realisation is *necessary*, and it is *sufficient* once the generated substructure is `Standing`.  In
particular the slot does **not** need `SaturationRealization`'s total extension (hence does not need
`#M ≤ #N`) on its `N` side. -/
theorem slotAtomic_of_nonUnitSlot [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : RouteLedger.NonUnitSlot (M := M) (N := N)) : SlotAtomic (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnu hns
  obtain ⟨T, g, hST, hagree, hmT, _hT⟩ := h S f hS m hmVF hmrv hnu hns
  exact ⟨g ⟨m, hmT⟩, M2Saturation.realizesAtomic_of_extends hST hagree hmT⟩

/-- `QFSat` (atomic realisation at *every* element) gives `SlotAtomic` (atomic realisation at the
slot points), so `SlotAtomic` is the restricted form of the realisation row. -/
theorem slotAtomic_of_qfsat (h : M2Saturation.QFSat M N) : SlotAtomic (M := M) (N := N) :=
  fun S f _hS m _hmVF _hmrv _hnu _hns => h S f m

/-- The generated-substructure route with `SlotAtomic` in place of the realisation row: atomic
realisation + `Standing` of the closure give the slot. -/
theorem nonUnitSlot_of_slotAtomic_and_closureStanding [hM : M ⊨ Axioms.ACVF]
    [hN : N ⊨ Axioms.ACVF]
    (hreal : SlotAtomic (M := M) (N := N))
    (hstand : ∀ (S : LRV.Substructure M), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
      ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
        Assembly.Standing (Substructure.closure LRV ((S : Set M) ∪ {m}))) :
    RouteLedger.NonUnitSlot (M := M) (N := N) :=
  nonUnitSlot_of_closureRealisation_and_standing (M := M) (N := N) hreal hstand

/-- **The class-control route to the generated substructure's `Standing` fails at perturbation
points.**  If `m` differs from an old `VF`-element `y ∈ S` by an element `ε` whose value class is not
an old class, then `M5L.ResidualClasses S T` fails for **every** `T ⊇ S` containing `m` — so
`M5L.standing_of_ClassControl`, the tree's only bridge from class control to `Standing`, cannot
supply `hstand` there.  (`Case35.not_residualClasses_of_perturbation`, at `T = ⊤`.) -/
theorem not_residualClasses_of_perturbation_at_slot [hM : M ⊨ Axioms.ACVF]
    {S : LRV.Substructure M} {m y : M}
    (hyS : y ∈ S) (hmVF : iVF m) (hyVF : iVF y)
    (heps0 : iVFAdd m (iVFNeg y) ≠ iVFZero)
    (hnew : ∀ s : M, s ∈ S → iRV s → ¬ Transc.Cls (iRv (iVFAdd m (iVFNeg y))) s) :
    ¬ M5L.ResidualClasses S (⊤ : LRV.Substructure M) :=
  Case35.not_residualClasses_of_perturbation (M := M) (T := ⊤)
    (fun _ _ => trivial) trivial hyS hmVF hyVF heps0 hnew

/-- **The `RV`-control interface fails there too** (it is *stronger* than class control,
`M5L.RVControl_of_ClassControl`): under the same perturbation hypotheses, `rv ε` is an `RV`-element
of `T = ⊤` that is not in `S`.  So neither of the tree's two interfaces
(`M5L.standing_of_ClassControl`, `M5.standing_of_RV_le`) can produce `Standing` of the generated
substructure at a perturbation point. -/
theorem not_rvControl_of_perturbation_at_slot [hM : M ⊨ Axioms.ACVF]
    {S : LRV.Substructure M} {m y : M}
    (hyS : y ∈ S) (hmVF : iVF m) (hyVF : iVF y)
    (heps0 : iVFAdd m (iVFNeg y) ≠ iVFZero)
    (hnew : ∀ s : M, s ∈ S → iRV s → ¬ Transc.Cls (iRv (iVFAdd m (iVFNeg y))) s) :
    ¬ (∀ z : M, z ∈ (⊤ : LRV.Substructure M) → iRV z → z ∈ S) := by
  intro hRV
  have hepsVF : iVF (iVFAdd m (iVFNeg y)) :=
    Transfer.vf_add_mem hM hmVF (Transfer.vf_neg_mem hM hyVF)
  have hmem : iRv (iVFAdd m (iVFNeg y)) ∈ S :=
    hRV _ trivial (rv_mem hM hepsVF)
  exact hnew _ hmem (rv_mem hM hepsVF) (Transc.cls_refl hM (rv_mem hM hepsVF))

/-- **The perturbation points are slot points.**  If `y ∈ S` strictly dominates `ε`, then
`rv (y + ε)` is class-equal to `rv y`, hence in `S` under `KEqTop S` — so the configuration in which
class control fails is an instance of the slot's own hypothesis `iRv m ∈ S`
(`Case35.perturbation_rv_mem`).  Hence the class-control row is not merely unproved here: it is
*false* on a sub-regime of the slot. -/
theorem perturbation_rv_mem_at_slot [hM : M ⊨ Axioms.ACVF] {S : LRV.Substructure M} {y ε : M}
    (hK : Assembly.KEqTop S) (hyS : y ∈ S) (hyVF : iVF y) (heVF : iVF ε)
    (hle : Transc.VLe y ε) (hnle : ¬ Transc.VLe ε y) :
    iRv (iVFAdd y ε) ∈ S :=
  Case35.perturbation_rv_mem (M := M) hK hyS hyVF heVF hle hnle

end Closure

/-! ## 6. Stress tests -/

section Stress
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **A non-unit exists in every model of `ACVF`**: the axiom `Axioms.axNontrivialRV` ("some nonzero
`VF`-element has value strictly below the value of `1`") is read off through
`Assembly.real_exSorted_vf`, and `RVCalc.units_iff_le_one` turns `¬ (rv a ≤ rv 1)` into
`¬ iUnits (rv a)`.  (The tree had no extraction of this axiom; it is what makes the non-unit
hypothesis `¬ iUnits (iRv m)` satisfiable, hence the slot non-vacuous.) -/
theorem exists_nonunit (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] :
    ∃ m : M, iVF m ∧ m ≠ iVFZero ∧ ¬ iUnits (iRv m) := by
  have hmem : Axioms.axNontrivialRV ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.repairRV, Axioms.ofList]
  have hreal : M ⊨ Axioms.axNontrivialRV := Theory.realize_sentence_of_mem (T := Axioms.ACVF) hmem
  obtain ⟨a, haVF, ha⟩ :=
    (Assembly.real_exSorted_vf (M := M) (xs := Fin.elim0)
      (φ := (∼(pEq (&0) tVFZero) ⊓ ∼(pLe (tRv (&0)) (tRv tVFOne))))).mp hreal
  rw [BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_not] at ha
  obtain ⟨hne, hle⟩ := ha
  have hne' : a ≠ iVFZero := by
    intro h0
    apply hne
    rw [pEq, BoundedFormula.realize_bdEqual, realize_tVFZero]
    simp only [h0]
    exact Fin.snoc_last (α := fun _ => M) iVFZero (Fin.elim0 : Fin 0 → M)
  have hle' : ¬ iLe (iRv a) iRVOne := by
    intro h
    apply hle
    rw [realize_pLe, realize_tRv, realize_tRv, realize_tVFOne, RVCalc.rv_one hM]
    exact h
  refine ⟨a, haVF, hne', ?_⟩
  intro hunit
  exact hle' ((RVCalc.units_iff_le_one hM (rv_mem hM haVF)
    (Case35.rv_mem_ne haVF hne')).mp hunit).2

/-- **The non-unit slot's hypothesis cone is inhabited in every model**: take a non-unit `m`
(`exists_nonunit`) and `S = ⊤`.  All five hypothesis rows hold simultaneously.  (Compare
`Case35.caseNotSeparated_hyp_satisfiable`, which is the same statement for the *whole* not-separated
slot, i.e. including the unit half.) -/
theorem exists_nonUnit_hyp_top (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] :
    ∃ m : M, Assembly.Standing (⊤ : LRV.Substructure M) ∧ iVF m ∧
      iRv m ∈ (⊤ : LRV.Substructure M) ∧ ¬ iUnits (iRv m) ∧
      ¬ M5L.Separated (⊤ : LRV.Substructure M) m := by
  obtain ⟨m, hmVF, hm0, hnu⟩ := exists_nonunit (M := M)
  exact ⟨m, StandingTree.standing_top, hmVF, trivial, hnu, Case35.notSeparated_top hmVF hm0⟩

/-- The unit and the non-unit halves are both inhabited, so the split into `UnitSlot` /
`NonUnitSlot` is not a vacuous one. -/
theorem unit_and_nonunit_both_occur (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] :
    iUnits (iRVOne (M := M)) ∧ ∃ m : M, iVF m ∧ m ≠ iVFZero ∧ ¬ iUnits (iRv m) :=
  ⟨StandingTree.rv_one_units (M := M), exists_nonunit M⟩

/-- **The `m ∈ S` case of the slot is trivial** — so the slot's content is only at genuinely new
elements, and the `⊤`-witness of §1 is not hiding an `m ∉ S` obligation. -/
theorem nonUnitSlot_concl_of_mem {M N : Type} [LRV.Structure M] [LRV.Structure N]
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S) {m : M} (hm : m ∈ S) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T :=
  ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩

/-- **The tree's branch hypothesis adds nothing**: under `Standing S` and `IsVFGen S`, the
exponent-one normal form `Case35.RVOldClass S m` is *equivalent* to `¬ M5L.Separated S m`
(`Case35.notSeparated_iff_RVOldClass`).  So `Case35.NotSeparatedBranch`'s only restriction over the
slot is its class-control conclusion — which §5 refutes at perturbation points. -/
theorem branch_hypothesis_is_slot_hypothesis {S : LRV.Substructure M} (hS : Assembly.Standing S)
    (hgen : Assembly.IsVFGen S) {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S) :
    Case35.RVOldClass S m ↔ ¬ M5L.Separated S m :=
  (Case35.notSeparated_iff_RVOldClass hS hgen hmVF hm0 hmrv).symm

end Stress

/-! ## 7. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_of_extAlongStanding
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitHull_of_clamped
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.gammaHullInitial_top_top
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitHull_holds
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_of_hull_and_extAlong
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_of_satReal
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_of_qfsat
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_of_slotTotalExt
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_of_extendsHere
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.slotTotalExt_forces_size
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.relNonUnit_of_qffinsat
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.relNonUnit_of_relExtendsHere
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.relNonUnit_of_relSlotTotalExt
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.paper_theorem_2_3_of_rel_parts_no_nonunit
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_of_closureRealisation_and_standing
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.slotAtomic_of_qfsat
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.slotAtomic_of_nonUnitSlot
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_of_slotAtomic_and_closureStanding
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.not_rvControl_of_perturbation_at_slot
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.not_residualClasses_of_perturbation_at_slot
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.perturbation_rv_mem_at_slot
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.exists_nonunit
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.exists_nonUnit_hyp_top
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.unit_and_nonunit_both_occur
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.nonUnitSlot_concl_of_mem
#print axioms SpecialTransformations.Milestone0.NonUnitAssembly.branch_hypothesis_is_slot_hypothesis

end SpecialTransformations.Milestone0.NonUnitAssembly
