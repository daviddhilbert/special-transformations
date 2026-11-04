/-
# m5 / d8 — can the honest-gate endgame's hypothesis list be shortened?

The question of this direction: `QE/RouteLedger.lean`'s
`paper_theorem_2_3_of_five_rel` consumes **six** hypotheses

    ShoenfieldTestRel, RelHull, RelSeparated, RelUnit, RelNonUnit, RelNewRV.

Filling a slot is u1–u4's work; this file asks the *other* question: is any of the six
**redundant**, i.e. can the list be made strictly shorter?  This file records the
machine-checked answer for the hull slot, which is the only slot whose object (Lemma 3.3,
`G3.HullExtension`) is not attached to a `Standing` domain:

* **§1  the gate's `SizeHyp` is exactly what the hull slot needs.**  `RelHull` forces
  `#Kˣ(M) ≤ #N` at every pair (`D7.hullExtension_forces_units_size_restated`); `relGate`'s
  second conjunct `M7Paper.SizeHyp M N` is `#M ≤ #N`, and `#Kˣ(M) ≤ #M`, so `relGate`
  supplies it.  Hence the size conjunct of the gate is not idle — it is the obstruction the
  hull slot would otherwise hit.
* **§2  `RelHull`'s content is confined to the `¬ Standing` domains.**  At every `Standing S`
  the hull is `S` and the slot costs nothing (`D7.hullExtensionAt_of_standing`).  So the hull
  slot is *equivalent* to its restriction to non-`Standing` domains.  Every one of the four
  case slots (`RelSeparated`, `RelUnit`, `RelNonUnit`, `RelNewRV`) has `Assembly.Standing S`
  as a hypothesis, so no case slot can ever discharge the hull slot's remaining content.
* **§3  the hull slot at the gate is exactly its two single steps** (`D7`: unit adjoinment and
  the `ω`-iteration of root adjoinments), each of which is again confined: the base step to
  `¬ KEqTop` domains, the root residual to `KEqTop ∧ ¬ Standing` domains.
* **§4  the endgame, re-run** with the hull slot replaced by each of the reduced forms, so the
  reduction is usable rather than decorative.

All `#print axioms` are `[propext, Classical.choice, Quot.sound]`.
-/
import RouteLedger
import D7Hull

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0
namespace M5Shrink

/-! ## 1. The gate's size conjunct is exactly the hull slot's cardinality need -/

/-- `#Kˣ(M) ≤ #M`: the units are a subtype of the carrier. -/
theorem units_card_le (M : Type) [LRV.Structure M] :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk M :=
  Cardinal.mk_subtype_le _

/-- **`relGate` supplies the cardinality the hull slot forces.**  `RelHull` forces
`#Kˣ(M) ≤ #N` at every pair (D7's `hullExtension_forces_units_size_restated`); the gate's
`M7Paper.SizeHyp` is `#M ≤ #N`.  So the gate is exactly strong enough for the obstruction, and
`RelHull`'s failure mode at deficient pairs is excluded by the gate, not by the slot. -/
theorem relGate_units_card {M N : Type} [LRV.Structure M] [LRV.Structure N]
    (h : M5Shoenfield.relGate M N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  le_trans (units_card_le M) h.2

/-- The same, contrapositive: at a `relGate` pair the hull slot's cardinality obstruction
(`D7.not_hullExtension_of_cardinality`) never applies. -/
theorem relGate_no_card_obstruction {M N : Type} [LRV.Structure M] [LRV.Structure N]
    (h : M5Shoenfield.relGate M N) :
    ¬ (Cardinal.mk N < Cardinal.mk {x : M // iUnits x}) :=
  not_lt.mpr (relGate_units_card h)

/-! ## 2. `RelHull`'s content is confined to the `¬ Standing` domains -/

section FixedPair

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]

/-- **Lemma 3.3's map half costs nothing at `Standing` domains**, so the hull slot is
*equivalent* to its restriction to the complement.  This is where the disjointness from the
four case slots comes from: every case slot's hypothesis list begins with `Assembly.Standing S`. -/
theorem hullExtension_iff_nonStanding :
    G3.HullExtension M N ↔
      ∀ (S : LRV.Substructure M), ¬ Assembly.Standing S → D7.HullExtensionAt (N := N) S := by
  constructor
  · intro h S _
    exact D7.hullExtension_iff_forall_hullExtensionAt.mp h S
  · intro h
    refine D7.hullExtension_iff_forall_hullExtensionAt.mpr (fun S => ?_)
    by_cases hS : Assembly.Standing S
    · exact D7.hullExtensionAt_of_standing S hS
    · exact h S hS

/-- **Lemma 3.3's map half is exactly its two single steps** (restated from `D7` at the fixed
pair so that the gate version below is a one-line lift). -/
theorem hullExtension_iff_base_root :
    G3.HullExtension M N ↔ D7.HullBaseStep M N ∧ D7.HullRootStep M N :=
  D7.hullExtension_iff_base_root

/-- `HullRootStep` gives the root residual: every monomorphism out of a `KEqTop` domain extends
along one root adjoinment.  (The converse is `D7.hullRootStep_of_rootStepResidual`, so the two
forms are equivalent; `D7.rootStepResidual_iff` then confines the residual's content to
`KEqTop ∧ ¬ Standing` domains.) -/
theorem rootStepResidual_of_hullRootStep (h : D7.HullRootStep M N) : D7.RootStepResidual M N := by
  intro T f hK
  have hb : M8Hull.hullSeq T 0 = T := D7.baseClosure_eq_of_KEqTop hK
  have h1 : M8Hull.hullSeq T 1 = M8Hull.rootClosure T := by
    show M8Hull.rootClosure (M8Hull.hullSeq T 0) = M8Hull.rootClosure T
    rw [hb]
  obtain ⟨g, hg⟩ := h T 0 (f.comp (Substructure.inclusion (le_of_eq hb)))
  refine ⟨g.comp (Substructure.inclusion (le_of_eq h1.symm)), ?_⟩
  intro y hy
  exact hg y ((le_of_eq hb.symm) hy)

end FixedPair

section FixedPair2

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]

/-! ### 2′. The two regions, in usable form

`Standing S` is `KEqTop S ∧ GammaDivisible S` (`QE/Assembly_frozen.lean`), so the two content
classes of §3 are characterized by these two elementary implications. -/

/-- A substructure missing a unit is not `KEqTop`, hence not `Standing`. -/
theorem not_standing_of_missing_unit {S : LRV.Substructure M} {x : M}
    (hx : iUnits x) (hxS : x ∉ S) : ¬ Assembly.Standing S :=
  fun h => hxS (h.1 x hx)

/-- `Standing` implies `KEqTop`: the base step's `¬ KEqTop` region is disjoint from every case
slot's domain. -/
theorem not_standing_of_not_KEqTop {S : LRV.Substructure M} (h : ¬ Assembly.KEqTop S) :
    ¬ Assembly.Standing S :=
  fun hS => h hS.1

/-- Conversely, at a `Standing` domain the hull slot is free (`D7.hullExtensionAt_of_standing`):
so the case slots' whole domain is a region where `RelHull` has no content. -/
theorem hullExtensionAt_at_caseSlot_domain (S : LRV.Substructure M) (hS : Assembly.Standing S) :
    D7.HullExtensionAt (N := N) S :=
  D7.hullExtensionAt_of_standing S hS

end FixedPair2

/-! ## 3. The gate-level forms -/

/-- **Lemma 3.3's map half at `relGate`, restricted to the `¬ Standing` domains**: the reduced
form of `RouteLedger.RelHull` that §2 shows is equivalent to it. -/
def RelHullNonStanding : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → ∀ (S : LRV.Substructure M), ¬ Assembly.Standing S →
      D7.HullExtensionAt (N := N) S

/-- **Lemma 3.3's map half at `relGate`, as its two single steps.** -/
def RelHullBaseRoot : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → D7.HullBaseStep M N ∧ D7.HullRootStep M N

/-- **Lemma 3.3's map half at `relGate`, as the unit adjoinment plus the named root residual.**
This is the sharpest form of the slot in the tree: each conjunct is content-confined
(`D7.hullBaseStep_iff_nonKEqTop`, `D7.rootStepResidual_iff`), and the two content classes are
`¬ KEqTop` and `KEqTop ∧ ¬ Standing`, i.e. both are *outside* the `Standing` region in which
all four case slots live. -/
def RelHullBaseRootResidual : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → D7.HullBaseStep M N ∧ D7.RootStepResidual M N

/-- **The hull slot at the honest gate is its restriction to the non-`Standing` domains**: no
content is lost, and the case slots cannot supply that content. -/
theorem relHull_iff_nonStanding : RouteLedger.RelHull ↔ RelHullNonStanding := by
  constructor
  · rintro h M N _ _ _ _ hG S hS
    exact (hullExtension_iff_nonStanding.mp (h M N hG)) S hS
  · intro h M N _ _ _ _ hG
    exact hullExtension_iff_nonStanding.mpr (fun S hS => h M N hG S hS)

/-- **The hull slot at the honest gate is exactly its two single steps.** -/
theorem relHull_iff_baseRoot : RouteLedger.RelHull ↔ RelHullBaseRoot := by
  constructor
  · rintro h M N _ _ _ _ hG
    exact hullExtension_iff_base_root.mp (h M N hG)
  · intro h M N _ _ _ _ hG
    exact hullExtension_iff_base_root.mpr (h M N hG)

/-- The two-step form implies the residual form. -/
theorem baseRootResidual_of_baseRoot (h : RelHullBaseRoot) : RelHullBaseRootResidual :=
  fun M N _ _ _ _ hG =>
    ⟨(h M N hG).1, rootStepResidual_of_hullRootStep (h M N hG).2⟩

/-- The residual form implies the two-step form (hence the hull slot). -/
theorem baseRoot_of_baseRootResidual (h : RelHullBaseRootResidual) : RelHullBaseRoot :=
  fun M N _ _ _ _ hG =>
    ⟨(h M N hG).1, D7.hullRootStep_of_rootStepResidual (h M N hG).2⟩

/-- **The residual form is the hull slot.** -/
theorem relHull_iff_baseRootResidual : RouteLedger.RelHull ↔ RelHullBaseRootResidual :=
  relHull_iff_baseRoot.trans
    ⟨baseRootResidual_of_baseRoot, baseRoot_of_baseRootResidual⟩

/-! ## 4. The endgame re-run with the reduced hull slot

Each of the three reduced forms replaces `RouteLedger.RelHull` in the honest-gate endgame
without changing anything else, so the reduction is usable by whoever proves the hull slot. -/

/-- The honest-gate endgame with the hull slot given on the `¬ Standing` domains only. -/
theorem paper_theorem_2_3_of_five_rel_nonStanding
    (hQ : M5Shoenfield.ShoenfieldTestRel) (hH : RelHullNonStanding)
    (hsep : RouteLedger.RelSeparated) (hu : RouteLedger.RelUnit)
    (hn : RouteLedger.RelNonUnit) (hnew : RouteLedger.RelNewRV) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ (relHull_iff_nonStanding.mpr hH) hsep hu hn hnew

/-- The honest-gate endgame with the hull slot split into its two single steps. -/
theorem paper_theorem_2_3_of_five_rel_baseRoot
    (hQ : M5Shoenfield.ShoenfieldTestRel) (hH : RelHullBaseRoot)
    (hsep : RouteLedger.RelSeparated) (hu : RouteLedger.RelUnit)
    (hn : RouteLedger.RelNonUnit) (hnew : RouteLedger.RelNewRV) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ (relHull_iff_baseRoot.mpr hH) hsep hu hn hnew

/-- The honest-gate endgame with the hull slot as the unit adjoinment plus the named root
residual. -/
theorem paper_theorem_2_3_of_five_rel_baseRootResidual
    (hQ : M5Shoenfield.ShoenfieldTestRel) (hH : RelHullBaseRootResidual)
    (hsep : RouteLedger.RelSeparated) (hu : RouteLedger.RelUnit)
    (hn : RouteLedger.RelNonUnit) (hnew : RouteLedger.RelNewRV) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ (relHull_iff_baseRootResidual.mpr hH)
    hsep hu hn hnew

/-! ## 4b. Machine check of §1a: the split carries no hypothesis strength

"Shortening" the six-part list by replacing `RelUnit ∧ RelNonUnit` with `RelCases` (or the four
parts with `RelCases`, or the whole list with `Input5R`) is a *definitional* rewrite: the
equivalences below are machine-checked, so none of those rewrites adds or removes anything.  A
strictly shorter list therefore exists only by proving a part. -/

section FixedPair3

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]

/-- `M4Cases.CaseNotSeparated` gives the unit half (the extra `iUnits` hypothesis is simply
ignored). -/
theorem unitSlot_of_caseNotSeparated (h : M4Cases.CaseNotSeparated (M := M) (N := N)) :
    RouteLedger.UnitSlot (M := M) (N := N) :=
  fun S f hS m hmVF hmrv _ hns => h S f hS m hmVF hmrv hns

/-- `M4Cases.CaseNotSeparated` gives the non-unit half. -/
theorem nonUnitSlot_of_caseNotSeparated (h : M4Cases.CaseNotSeparated (M := M) (N := N)) :
    RouteLedger.NonUnitSlot (M := M) (N := N) :=
  fun S f hS m hmVF hmrv _ hns => h S f hS m hmVF hmrv hns

/-- **The two halves are the whole, at a fixed pair**: the unit/non-unit split of the
not-separated slot is an equivalence, not a strengthening. -/
theorem caseNotSeparated_iff_halves :
    M4Cases.CaseNotSeparated (M := M) (N := N) ↔
      RouteLedger.UnitSlot (M := M) (N := N) ∧
        RouteLedger.NonUnitSlot (M := M) (N := N) :=
  ⟨fun h => ⟨unitSlot_of_caseNotSeparated h, nonUnitSlot_of_caseNotSeparated h⟩,
   fun h => RouteLedger.caseNotSeparated_of_halves h.1 h.2⟩

/-- **The four paper lemmas are `Cases`**, at a fixed pair. -/
theorem cases_iff_parts :
    M4Cases.Cases (M := M) (N := N) ↔
      M4Cases.CaseSeparated (M := M) (N := N) ∧
        RouteLedger.UnitSlot (M := M) (N := N) ∧
          RouteLedger.NonUnitSlot (M := M) (N := N) ∧
            M4Cases.CaseNewRV (M := M) (N := N) := by
  constructor
  · intro h
    exact ⟨h.separated, unitSlot_of_caseNotSeparated h.notSeparated,
      nonUnitSlot_of_caseNotSeparated h.notSeparated, h.newRV⟩
  · rintro ⟨hsep, hu, hn, hnew⟩
    exact RouteLedger.cases_of_parts hsep hu hn hnew

end FixedPair3

/-- **The six-part honest-gate list is exactly the four-part-plus-hull list**: the unit split is
an equivalence at the gate. -/
theorem relCases_iff_parts :
    RouteLedger.RelCases ↔
      RouteLedger.RelSeparated ∧ RouteLedger.RelUnit ∧ RouteLedger.RelNonUnit ∧
        RouteLedger.RelNewRV := by
  constructor
  · intro h
    exact ⟨fun M N _ _ _ _ hG => (cases_iff_parts.mp (h M N hG)).1,
      fun M N _ _ _ _ hG => (cases_iff_parts.mp (h M N hG)).2.1,
      fun M N _ _ _ _ hG => (cases_iff_parts.mp (h M N hG)).2.2.1,
      fun M N _ _ _ _ hG => (cases_iff_parts.mp (h M N hG)).2.2.2⟩
  · rintro ⟨hsep, hu, hn, hnew⟩
    exact RouteLedger.relCases_of_parts hsep hu hn hnew

/-- **THE MACHINE-CHECKED ANSWER TO THE DIRECTION'S QUESTION**: the six-part list is *equivalent*
to Marker's saturated realisation `Input5R` (i.e. to the two-hypothesis endgame
`Prop39Decomp.paper_theorem_rel_two`).  Hence no restructuring shortens it; only a proof does. -/
theorem input5R_iff_relHull_and_fourParts :
    M5Shoenfield.Input5R ↔
      RouteLedger.RelHull ∧ RouteLedger.RelSeparated ∧ RouteLedger.RelUnit ∧
        RouteLedger.RelNonUnit ∧ RouteLedger.RelNewRV := by
  rw [← RouteLedger.relHull_and_cases_iff_input5R, relCases_iff_parts]

/-! ## 5. A finer frontier: the unit slot split at the gate

`RouteLedger` splits `L3x` into four parts; its own §4.1 shows the unit half further splits into
Lemma 3.4's algebraic case and Lemma 3.6's transcendental case, but only at a fixed pair
(`RouteLedger.unitSlot_of_algebraic_transcendental`).  Here is the gate-level version, so the two
halves can be attacked as separate frontier parts: the endgame below consumes *seven* named
statements, and its unit slot is `RelAlgebraicUnit ∧ RelTranscendentalUnit`. -/

/-- Lemma 3.4 at the honest gate. -/
def RelAlgebraicUnit : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → RouteLedger.AlgebraicUnitSlot (M := M) (N := N)

/-- Lemma 3.6 at the honest gate. -/
def RelTranscendentalUnit : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → RouteLedger.TranscendentalUnitSlot (M := M) (N := N)

/-- The two unit halves give `RouteLedger.RelUnit` at the gate. -/
theorem relUnit_of_algebraic_transcendental (ha : RelAlgebraicUnit)
    (ht : RelTranscendentalUnit) : RouteLedger.RelUnit :=
  fun M N _ _ _ _ hG =>
    RouteLedger.unitSlot_of_algebraic_transcendental (ha M N hG) (ht M N hG)

/-- **The honest-gate endgame with the unit slot split into Lemmas 3.4 and 3.6.** -/
theorem paper_theorem_2_3_of_six_rel
    (hQ : M5Shoenfield.ShoenfieldTestRel) (hH : RouteLedger.RelHull)
    (hsep : RouteLedger.RelSeparated) (ha : RelAlgebraicUnit) (ht : RelTranscendentalUnit)
    (hn : RouteLedger.RelNonUnit) (hnew : RouteLedger.RelNewRV) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ hH hsep
    (relUnit_of_algebraic_transcendental ha ht) hn hnew

end M5Shrink
end SpecialTransformations.Milestone0

#print axioms SpecialTransformations.Milestone0.M5Shrink.relGate_units_card
#print axioms SpecialTransformations.Milestone0.M5Shrink.relGate_no_card_obstruction
#print axioms SpecialTransformations.Milestone0.M5Shrink.hullExtension_iff_nonStanding
#print axioms SpecialTransformations.Milestone0.M5Shrink.rootStepResidual_of_hullRootStep
#print axioms SpecialTransformations.Milestone0.M5Shrink.not_standing_of_missing_unit
#print axioms SpecialTransformations.Milestone0.M5Shrink.not_standing_of_not_KEqTop
#print axioms SpecialTransformations.Milestone0.M5Shrink.hullExtensionAt_at_caseSlot_domain
#print axioms SpecialTransformations.Milestone0.M5Shrink.relHull_iff_nonStanding
#print axioms SpecialTransformations.Milestone0.M5Shrink.relHull_iff_baseRoot
#print axioms SpecialTransformations.Milestone0.M5Shrink.relHull_iff_baseRootResidual
#print axioms SpecialTransformations.Milestone0.M5Shrink.paper_theorem_2_3_of_five_rel_nonStanding
#print axioms SpecialTransformations.Milestone0.M5Shrink.paper_theorem_2_3_of_five_rel_baseRootResidual
#print axioms SpecialTransformations.Milestone0.M5Shrink.caseNotSeparated_iff_halves
#print axioms SpecialTransformations.Milestone0.M5Shrink.cases_iff_parts
#print axioms SpecialTransformations.Milestone0.M5Shrink.relCases_iff_parts
#print axioms SpecialTransformations.Milestone0.M5Shrink.input5R_iff_relHull_and_fourParts
#print axioms SpecialTransformations.Milestone0.M5Shrink.relUnit_of_algebraic_transcendental
#print axioms SpecialTransformations.Milestone0.M5Shrink.paper_theorem_2_3_of_six_rel
