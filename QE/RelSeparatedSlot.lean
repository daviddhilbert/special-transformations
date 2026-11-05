/-
# u3 — `RelSeparated`: the frozen 3.7 slot, its exact residual, and what it actually costs

Member `m3`, swarm `smw2qpqe7`, direction `u3`.  Target of the slot: `QE/RouteLedger.lean`'s

    RelSeparated := ∀ (M N) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF],
      M5Shoenfield.relGate M N → M4Cases.CaseSeparated (M := M) (N := N)

where `M4Cases.CaseSeparated` (`QE/OneStepCases.lean`) is the paper's `e:transc` case: at
`S Standing`, `m ∈ VF(M)`, `iRv m ∈ S`, `M5L.Separated S m`, produce `T ≥ S` with `m ∈ T`,
`T Standing`, and a monomorphism `T ↪[LRV] N` agreeing with `f` on `S`.

## Results, in decreasing sharpness

**§4b — THE HEADLINE: at `relGate`, `RelSeparated` follows from finite satisfiability alone.**

    relSeparated_of_qffinsat :  (∀ M N, relGate M N → QFFinSat M N)  →  RelSeparated

(`M2Saturation.QFFinSat`, `QE/SatReal.lean`.)  The gate supplies `SatRel`; `QFFinSat` supplies the
finite satisfiability that `SatRel` consumes, so the pushed atomic types are realised
(`qfsat_of_satRel_qffinsat`, using the tree's `Assembly.realizesAtomic_of_clause`), so input 5 holds
(`M2Saturation.satReal_of_qfsat`), so a *total* extension exists at the pair
(`G3.extendsHere_of_satReal`), and the slot is discharged with `T = ⊤`
(`M4Cases.cases_of_global_extension`).  **3.7 therefore has no `Γ`-theoretic content of its own at the
gate**: it is not an independent obligation of the frontier, and it consumes none of
`VFInvClosedOn`, `IsVFGen`, `PolyExpansions`, the Engler–Prestel material, or the Mathlib-level
Lemmas 3.7/3.8 (`QE/Lemma37.lean`, `QE/Case38Value.lean`, `QE/Lemma38RV.lean`, `QE/Lemma38EP.lean`
are all at the Mathlib `Valuation` level and none of them mentions `LRV`, so none of them can feed
this slot directly).

**§2b — the slot in canonical form**: the existential `T` is always the least `Standing` extension

    canonicalHull S m := standingHull (closure (S ∪ {m})),

so `CaseSeparated` is *equivalent* to the extension of `f` to that fixed domain
(`caseSeparated_iff_canonicalHullExtension`), i.e. `RelSeparated ⟺ RelHullOneStep`.  The map
statement is the second half of the paper's Claim (⋆); the `RV`-control half is *not* needed, and
neither is `M5L.VFInvClosedOn`: those are the price of taking `T = closure (S ∪ {m})`, which is what
`Realize.exists_oneStep` hands over, and the hull removes that price.

**§4b (structural form)**: `RelHull` (the frontier's 3.3 part) plus the realisation of one atomic
type per separated instance already give the slot (`relSeparated_of_relHull_slotFinSat`), because
`G3.HullExtension` is quantified over *every* substructure and hence applies at the generated
closure.

**§0–§4 — the field-theoretic route, calibrated.**  `VFClassControl S T` (`Γ`-class control of the
`VF`-part of the extension, the weakest form of Claim (⋆) that `M5L.standing_of_ClassControl`
consumes) gives the slot from `IsVFGen T` alone (`caseSeparated_of_realization_vfClassControl`);
`VFInvClosedOn + QuotExpansions` and `PolyExpansions` both imply `VFClassControl`
(`vfClassControl_of_quotInv`, `vfClassControl_of_poly`), so the merged interfaces are recovered.  The
residual is stated `M`-only (`SlotClassData`, §4) and the model-theoretic row is reduced to finite
satisfiability of the pushed type (§3, `SlotTypeReal ↔ SlotFinSatAt` at a `SatRel` pair).

**§5 — audit.**  The slot's conclusion is non-vacuous (`caseSeparated_of_global_extension`,
`caseSeparated_of_extendsHere`); its hypotheses force `m ∉ S` and `rv(m) ∉ Kˣ`; they are empty at
`S = ⊤` unless `m = 0`, and at every `VF`-generated `S` (`QE/Lemma36Audit.lean`, restated).  The
satisfiability of the *separated* hypothesis bundle in an actual model of `ACVF` is **not**
established here or anywhere in the tree — see `SeparatedHypSatisfiable` at the end.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import RouteLedger
import InterfaceClosure
import Lemma36Audit
import M1Fix
import ShoenfieldQuote
import SatReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.Transc

namespace SpecialTransformations.Milestone0.M3Sep

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ## 0. The residual: `Γ`-class control of the `VF`-part of the extension

`M5L.ResidualClasses S T` asks for a class-equal element of `S` for *every* `RV`-element of `T`.
`Assembly.IsVFGen T` (Remark 3.1: `RV(T) = rv(VF(T)) ∪ {0}`) reduces that to the `VF`-elements of
`T`, and that is what the paper's Claim (⋆) actually proves (`RV(⟨Ŝ,e⟩) ⊆ RV(Ŝ)`).  So this is the
honest residual, and it is the weakest statement `M5L.standing_of_ClassControl` consumes. -/

/-- **Claim (⋆), `VF`-part, `Γ`-class form**: every `VF`-element of `T` has the `Γ`-class of an
element of `S`.  No membership of `iRv x` in `S` is demanded (only its class), and no representation
of `x` as a polynomial or quotient. -/
def VFClassControl (S T : LRV.Substructure M) : Prop :=
  ∀ x : M, x ∈ T → iVF x → ∃ s : M, s ∈ S ∧ iRV s ∧ Transc.Cls (iRv x) s

/-- The residual is satisfied trivially when the extension adds no `VF`-classes (in particular at
`T = S`): the witness is `iRv x` itself, which lies in `S` because `S` is closed under the `rv`
symbol.  So `VFClassControl` is not contradictory. -/
theorem vfClassControl_of_le {S T : LRV.Substructure M} (h : T ≤ S) : VFClassControl S T := by
  intro x hxT hxVF
  have hxS : x ∈ S := h hxT
  exact ⟨iRv x, S.fun_mem Fn.rvMap ![x] (fun i => by fin_cases i; exact hxS),
    rv_mem hM hxVF, Transc.cls_refl hM (rv_mem hM hxVF)⟩

/-- **`PolyExpansions` implies the new residual.**  `QE/InterfaceClosure.lean`'s polynomial route
gives `iRv x ∈ S` for every `VF`-element of `T` (`M3Slot.rv_mem_of_polyExpansions`), which is more
than the class.  So this file's residual is implied by the merged one: no weakening in disguise. -/
theorem vfClassControl_of_poly {S T : LRV.Substructure M} (hK : Assembly.KEqTop S) {e : M}
    (he : iVF e) (he0 : e ≠ iVFZero) (heS : iRv e ∈ S) (hsep : M5L.Separated S e)
    (hpoly : M3Slot.PolyExpansions (M := M) S T e) : VFClassControl S T := by
  intro x hxT hxVF
  exact ⟨iRv x, M3Slot.rv_mem_of_polyExpansions hM hK he he0 heS hsep hpoly x hxT hxVF,
    rv_mem hM hxVF, Transc.cls_refl hM (rv_mem hM hxVF)⟩

/-- **`QuotExpansions + VFInvClosedOn` implies the new residual** — i.e. the merged interface
(`QE/M5L34_36.lean`'s `ResidualClasses_of_VFGen`), with its extra hypothesis on `S`, is a special
case.  So `VFClassControl` is implied by *both* merged residuals and is the weakest of the three. -/
theorem vfClassControl_of_quotInv {S T : LRV.Substructure M} (hK : Assembly.KEqTop S)
    (hfinv : M5L.VFInvClosedOn S) {e : M} (he : iVF e) (he0 : e ≠ iVFZero) (heS : iRv e ∈ S)
    (hsep : M5L.Separated S e) (hquot : M5L.QuotExpansions S T e) : VFClassControl S T := by
  intro x hxT hxVF
  by_cases hx0 : x = iVFZero
  · refine ⟨iRVZero, M5L.rvZero_mem_sub S, MulNormalForm.rv_zero_mem hM, ?_⟩
    rw [hx0, RVCalc.rv_zero_eq hM]
    exact Transc.cls_refl hM (MulNormalForm.rv_zero_mem hM)
  · obtain ⟨b, c, mM, mN, hb, hbS, hb0, hc, hcS, hc0, hq0, hxq⟩ := hquot x hxT hxVF hx0
    exact ⟨iRv x,
      M5L.rvQuotExpansion_mem hM hK hfinv he he0 heS hb hbS hb0 hc hcS hc0 hsep hxVF hq0 hxq,
      rv_mem hM hxVF, Transc.cls_refl hM (rv_mem hM hxVF)⟩

/-! ## 1. Claim (⋆) in the form `Standing` consumes -/

/-- **Claim (⋆) in `Γ`-class form, from the weakest residual**: `IsVFGen T` (Remark 3.1) plus
`VFClassControl S T` give `M5L.ResidualClasses S T`.  Compare `M5L.ResidualClasses_of_VFGen`
(`QuotExpansions` and `VFInvClosedOn`) and `M3Slot.ResidualClasses_of_poly` (`PolyExpansions`). -/
theorem residualClasses_of_vfClassControl {S T : LRV.Substructure M}
    (hVFGen : Assembly.IsVFGen T) (hcc : VFClassControl S T) : M5L.ResidualClasses S T := by
  intro y hyT hyRV
  rcases hVFGen y hyT hyRV with ⟨x, hxT, hxVF, hxr⟩ | hz
  · obtain ⟨s, hsS, hsRV, hcls⟩ := hcc x hxT hxVF
    exact ⟨s, hsS, hsRV, by rw [← hxr]; exact hcls⟩
  · refine ⟨iRVZero, M5L.rvZero_mem_sub S, MulNormalForm.rv_zero_mem hM, ?_⟩
    rw [hz]
    exact Transc.cls_refl hM (MulNormalForm.rv_zero_mem hM)

/-- **`Standing T` from the residual**, through the tree's `M5L.standing_of_ClassControl`. -/
theorem standing_of_vfClassControl {S T : LRV.Substructure M} (hST : S ≤ T)
    (hS : Assembly.Standing S) (hVFGen : Assembly.IsVFGen T) (hcc : VFClassControl S T) :
    Assembly.Standing T :=
  M5L.standing_of_ClassControl hST hS (residualClasses_of_vfClassControl hVFGen hcc)

/-! ## 2. The slot at a fixed pair -/

/-- **The slot from its two residuals, with `VFInvClosedOn` gone.**  Same shape as
`M3Slot.caseSeparated_of_slotRealization_and_fieldData`, but the field row is
`VFClassControl` at the canonical extension `closure (S ∪ {m})` instead of `PolyExpansions`, so the
row is strictly weaker (and mentions neither `f` nor `N`). -/
theorem caseSeparated_of_realization_vfClassControl
    (hreal : M3Slot.SlotRealization (M := M) (N := N))
    (hfield : ∀ (S : LRV.Substructure M) (_f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M,
      iVF m → iRv m ∈ S → M5L.Separated S m →
        Assembly.IsVFGen (Substructure.closure LRV ((S : Set M) ∪ {m})) ∧
          VFClassControl (M := M) S (Substructure.closure LRV ((S : Set M) ∪ {m}))) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩
  · have hm0 : m ≠ iVFZero := fun h => hm (h ▸ M3Slot.vfZero_mem_sub (M := M) S)
    obtain ⟨b, hb⟩ := hreal S f hS m hmVF hm
    obtain ⟨g, hST, hmT, hagree⟩ := M3Slot.exists_oneStep_closure (M := M) (N := N) hb hm
    obtain ⟨hgen, hcc⟩ := hfield S f hS m hmVF hmrv hsep
    exact ⟨Substructure.closure LRV ((S : Set M) ∪ {m}), g, hST, hagree, hmT,
      standing_of_vfClassControl hST hS hgen hcc⟩

/-! ## 2b. THE SHARP FORM: the slot is a hull-extension statement at a canonical domain

`CaseSeparated`'s witness `T` is existentially quantified.  `QE/StandingHull.lean` supplies the
*least* `Standing` superstructure `M8Hull.standingHull`, and `M8Hull.standingHull_le` its minimality
principle, so the slot has a canonical witness:

    T := standingHull (closure (S ∪ {m})),

which is `Standing` by construction and contains `S` and `m`.  Two consequences, both proved below:

* **the slot is *equivalent* to the extension of `f` to that one fixed domain** — so nothing about the
  choice of `T` is left in the obligation;
* **the `RV`/`Γ`-control half of the paper's Claim (⋆) is not needed for the frozen slot.**  It is
  the price of using `closure (S ∪ {m})` as the witness `T` (which is what `Realize.exists_oneStep`
  hands over); with the hull as `T` the `Standing` obligation is discharged by
  `M8Hull.standing_standingHull` and the only remaining content is the *map* `f* : ⟨Ŝ,e⟩ → N` — the
  second half of Claim (⋆).  So `VFInvClosedOn`, `IsVFGen`, `PolyExpansions` and `VFClassControl`
  are all *sufficient* ways of proving the map extends, not necessary ones (§2's chain remains as
  the field-theoretic route). -/

/-- **The canonical extension**: the least `Standing` substructure containing `S ∪ {m}` — the frozen
form of the paper's `⟨Ŝ, e⟩`. -/
def canonicalHull (S : LRV.Substructure M) (m : M) : LRV.Substructure M :=
  M8Hull.standingHull (Substructure.closure LRV ((S : Set M) ∪ {m}))

/-- `S` lies in the canonical extension. -/
theorem le_canonicalHull (S : LRV.Substructure M) (m : M) : S ≤ canonicalHull S m := by
  intro x hx
  exact M8Hull.le_standingHull _ (Substructure.subset_closure (Set.mem_union_left {m} hx))

/-- The new element lies in the canonical extension. -/
theorem mem_canonicalHull_self (S : LRV.Substructure M) (m : M) : m ∈ canonicalHull S m :=
  M8Hull.le_standingHull _
    (Substructure.subset_closure (Set.mem_union_right _ (Set.mem_singleton m)))

/-- The canonical extension is `Standing` — this is the whole `Standing T` obligation of the slot,
discharged for free by the hull construction. -/
theorem standing_canonicalHull (S : LRV.Substructure M) (m : M) :
    Assembly.Standing (canonicalHull S m) :=
  M8Hull.standing_standingHull _

/-- The canonical extension is contained in **every** `Standing` superstructure of `S` containing
`m` — the minimality that makes it the canonical witness. -/
theorem canonicalHull_le {S T : LRV.Substructure M} {m : M} (hST : S ≤ T) (hmT : m ∈ T)
    (hStand : Assembly.Standing T) : canonicalHull S m ≤ T := by
  refine M8Hull.standingHull_le ?_ hStand
  refine (Substructure.closure_le).mpr ?_
  intro x hx
  rcases hx with hxS | hxm
  · exact hST hxS
  · rw [Set.mem_singleton_iff] at hxm
    rw [hxm]
    exact hmT

/-- **The map-extension half of the slot's conclusion, at the canonical domain.** -/
def HullExtAt (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : Prop :=
  ∃ g : canonicalHull S m ↪[LRV] N,
    ∀ x : S, g ⟨(x : M), le_canonicalHull S m x.2⟩ = f x

/-- **The accepted conclusion and the canonical-hull extension are the same statement.**  So the
slot's `∃ T` adds nothing: the minimal `Standing` witness is always available, and the obligation is
the extension of `f` to it. -/
theorem exists_standing_extension_iff_hullExtAt (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) :
    (∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) ↔
      HullExtAt (M := M) (N := N) S f m := by
  constructor
  · rintro ⟨T, g, hST, hagree, hmT, hStand⟩
    have hle : canonicalHull S m ≤ T := canonicalHull_le hST hmT hStand
    refine ⟨g.comp (Substructure.inclusion hle), ?_⟩
    intro x
    have h1 : (Substructure.inclusion hle) ⟨(x : M), le_canonicalHull S m x.2⟩
        = ⟨(x : M), hST x.2⟩ := rfl
    show g ((Substructure.inclusion hle) ⟨(x : M), le_canonicalHull S m x.2⟩) = f x
    rw [h1]
    exact hagree x
  · rintro ⟨g, hg⟩
    exact ⟨canonicalHull S m, g, le_canonicalHull S m, hg, mem_canonicalHull_self S m,
      standing_canonicalHull S m⟩

/-- **THE SLOT, IN CANONICAL FORM**: `CaseSeparated` is exactly "every monomorphism out of a
`Standing S` extends to `f*` on the least `Standing` extension by a separated element".  No `∃ T`, no
`VF`-class control, no `VFInvClosedOn`. -/
theorem caseSeparated_iff_canonicalHullExtension :
    M4Cases.CaseSeparated (M := M) (N := N) ↔
      ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
        iRv m ∈ S → M5L.Separated S m → HullExtAt (M := M) (N := N) S f m :=
  ⟨fun h S f hS m hmVF hmrv hsep =>
      (exists_standing_extension_iff_hullExtAt S f m).mp (h S f hS m hmVF hmrv hsep),
    fun h S f hS m hmVF hmrv hsep =>
      (exists_standing_extension_iff_hullExtAt S f m).mpr (h S f hS m hmVF hmrv hsep)⟩

/-- `CaseSeparated` from the canonical-hull extension (the direction the assembler uses). -/
theorem caseSeparated_of_canonicalHullExtension
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → M5L.Separated S m → HullExtAt (M := M) (N := N) S f m) :
    M4Cases.CaseSeparated (M := M) (N := N) :=
  caseSeparated_iff_canonicalHullExtension.mpr h

/-- The canonical-hull extension at the pair, when `m` is **already** in `S`: nothing has to be
added, and `f` itself is the witness (the hull collapses to `S`).  So the slot's content sits at new
elements only — the `⊤`-witness of `QE/Lemma36Audit.lean` in the hull vocabulary. -/
theorem hullExtAt_of_mem {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M} (hm : m ∈ S)
    (hS : Assembly.Standing S) : HullExtAt (M := M) (N := N) S f m := by
  have hle : canonicalHull S m ≤ S := canonicalHull_le (le_refl S) hm hS
  refine ⟨f.comp (Substructure.inclusion hle), ?_⟩
  intro x
  have h1 : (Substructure.inclusion hle) ⟨(x : M), le_canonicalHull S m x.2⟩
      = ⟨(x : M), (le_refl S) x.2⟩ := rfl
  show f ((Substructure.inclusion hle) ⟨(x : M), le_canonicalHull S m x.2⟩) = f x
  rw [h1]

/-- **The hull-extension principle plus one atomic-type realisation gives the canonical-hull
extension at a new element.**  `M3Slot.exists_oneStep_closure` realises the type on the generated
closure, and `G3.HullExtension` — quantified over *every* substructure — then extends to its hull. -/
theorem hullExtAt_of_hullExtension (hHull : G3.HullExtension (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M)
    (hreal : ∃ b : N, Realize.RealizesAtomic S f m b) (hm : m ∉ S) :
    HullExtAt (M := M) (N := N) S f m := by
  obtain ⟨b, hb⟩ := hreal
  obtain ⟨f₁, hST₁, _hmT₁, hagree₁⟩ := M3Slot.exists_oneStep_closure (M := M) (N := N) hb hm
  obtain ⟨g, hg⟩ := hHull (Substructure.closure LRV ((S : Set M) ∪ {m})) f₁
  refine ⟨g, ?_⟩
  intro x
  have hx₁ : (x : M) ∈ Substructure.closure LRV ((S : Set M) ∪ {m}) := hST₁ x.2
  have h1 : (⟨(x : M), le_canonicalHull S m x.2⟩ : canonicalHull S m)
      = ⟨(x : M), M8Hull.le_standingHull _ hx₁⟩ := Subtype.ext rfl
  rw [h1]
  exact (hg ⟨(x : M), hx₁⟩).trans (hagree₁ x)

/-- **The gate-level form**: a single named proposition, the `e:transc` one-element hull step. -/
def RelHullOneStep : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S →
      ∀ m : M, iVF m → iRv m ∈ S → M5L.Separated S m →
        HullExtAt (M := M) (N := N) S f m

/-- **`RelSeparated` *is* the one-element hull step** — the tightest form of the fifth frontier part:
`HasQE`'s `RelSeparated` slot neither asks for a `Standing` witness nor for `Γ`-control, only for the
extension of `f` to the canonical hull of `S ∪ {m}`. -/
theorem relSeparated_iff_relHullOneStep : RouteLedger.RelSeparated ↔ RelHullOneStep := by
  constructor
  · intro h M N _ _ _ _ hR
    exact caseSeparated_iff_canonicalHullExtension.mp (h M N hR)
  · intro h M N _ _ _ _ hR
    exact caseSeparated_iff_canonicalHullExtension.mpr (h M N hR)

/-! ## 2c. THE EXACT RESIDUAL, as an equivalence

§2b says the slot's `T` is canonical.  What is left is a *map*; the theorem below identifies it as
one atomic-type realisation per separated instance, and nothing else, **given the 3.3 part**:

    RelHull  →  (RelSeparated  ↔  RelSepRealization)

where `RelSepRealization` is `SlotRealization` restricted to the slot's own hypotheses.  The `←`
direction is §4b's hull argument; the `→` direction reads the realised type off the slot's own
embedding (`M2Saturation.realizesAtomic_of_extends`).  So no field theory, no `Γ`-control and no
`VFInvClosedOn` survives in the residual. -/

/-- **The realisation residual at the slot's own hypotheses**: one atomic type per separated
instance.  This is `M3Slot.SlotRealization` cut down to `iVF m`, `iRv m ∈ S`, `m ∉ S` and
`M5L.Separated S m`. -/
def RelSepRealization : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S →
      ∀ m : M, iVF m → iRv m ∈ S → m ∉ S → M5L.Separated S m →
        ∃ b : N, Realize.RealizesAtomic S f m b

/-- The realisation row of `QE/InterfaceClosure.lean` implies the restricted one. -/
theorem relSepRealization_of_slotRealization
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M3Slot.SlotRealization (M := M) (N := N)) : RelSepRealization :=
  fun M N _ _ _ _ _ S f hS m hmVF _hmrv hm _hsep => h M N S f hS m hmVF hm

/-- **THE EXACT RESIDUAL.**  Given the frontier's 3.3 part (`RelHull`), the separated slot is
*equivalent* to the realisation of one atomic type per separated instance.  Nothing about `Standing`
preservation, `Γ`-control or inverse-closure appears on the right-hand side. -/
theorem relSeparated_iff_relSepRealization (hHull : RouteLedger.RelHull) :
    RouteLedger.RelSeparated ↔ RelSepRealization := by
  constructor
  · intro h M N _ _ _ _ hR S f hS m hmVF hmrv _hm hsep
    obtain ⟨T, g, hST, hagree, hmT, _hStand⟩ := h M N hR S f hS m hmVF hmrv hsep
    exact ⟨g ⟨m, hmT⟩, M2Saturation.realizesAtomic_of_extends hST hagree hmT⟩
  · intro hreal M N _ _ _ _ hR
    refine caseSeparated_of_canonicalHullExtension (M := M) (N := N) ?_
    intro S f hS m hmVF hmrv hsep
    by_cases hm : m ∈ S
    · exact hullExtAt_of_mem hm hS
    · exact hullExtAt_of_hullExtension (hHull M N hR) S f m
        (hreal M N hR S f hS m hmVF hmrv hm hsep) hm

/-! ## 3. The realisation row is exactly the gate's saturation plus finite satisfiability

`M3Slot.SlotRealization` asks that the *atomic* type of a new element, pushed by `f`, be realised in
`N`; that is what `Realize.exists_oneStep` consumes.  `M1Fix.SatRel M N` — the saturation conjunct of
the gate `relGate`, hence a *hypothesis* of `RelSeparated` — realises *complete* types from finite
satisfiability.  The two views agree at the gate:

    SlotTypeReal  (∃ b, every formula true of m over S holds of b)   ⟺  SlotFinSatAt  (per formula)
    SlotTypeReal  ⟹  SlotRealization                                (`realizesAtomic_of_clause`)

so the model-theoretic content of the slot is *finite satisfiability of the pushed type* — the
paper's Remark 3.1 / qf-type consistency — and nothing about saturation: the gate already supplies
the saturation. -/

/-- The pushed complete type of `m` over `S` is realised: the conclusion of `M1Fix.SatRel`'s clause
at the slot's hypotheses. -/
def SlotTypeReal (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : Prop :=
  ∃ b : N, ∀ φ : LRV.Formula (S ⊕ Unit), φ.Realize (Realize.mv S m) → φ.Realize (Realize.wv f b)

/-- Finite satisfiability of the pushed type at one point: every single formula true of `m` over `S`
has a witness under `f`.  (`M1Fix.SatRel`'s hypothesis, in the slot's vocabulary.) -/
def SlotFinSatAt (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : Prop :=
  ∀ φ : LRV.Formula (S ⊕ Unit), φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b)

/-- **Finite satisfiability of the pushed type at every point of the slot** — the model-theoretic
residual of `RelSeparated`, once the gate has been used. -/
def SlotFinSat : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → m ∉ S →
    SlotFinSatAt (M := M) (N := N) S f m

/-- **The equivalence that makes the residual finite**: at a `SatRel` pair, realising the complete
type and satisfying every finite part of it are the same thing.  The `→` direction is immediate (the
realising element serves every formula); the `←` direction is `SatRel` itself. -/
theorem slotTypeReal_iff_finSatAt (hSat : M1Fix.SatRel M N) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) (m : M) :
    SlotTypeReal (M := M) (N := N) S f m ↔ SlotFinSatAt (M := M) (N := N) S f m :=
  ⟨fun ⟨b, hb⟩ φ hφ => ⟨b, hb φ hφ⟩, fun h => hSat S f m h⟩

/-- Realisation of the complete pushed type gives the atomic realisation the tree consumes. -/
theorem realizesAtomic_of_typeReal {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (h : SlotTypeReal (M := M) (N := N) S f m) :
    ∃ b : N, Realize.RealizesAtomic S f m b :=
  Assembly.realizesAtomic_of_clause S f m h

/-- **The model-theoretic row of the slot, from the gate plus finite satisfiability.** -/
theorem slotRealization_of_satRel_finSat (hSat : M1Fix.SatRel M N)
    (hfin : SlotFinSat (M := M) (N := N)) : M3Slot.SlotRealization (M := M) (N := N) :=
  fun S f hS m hmVF hm =>
    realizesAtomic_of_typeReal ((slotTypeReal_iff_finSatAt hSat S f m).mpr (hfin S f hS m hmVF hm))

/-- **The slot at a fixed pair, from `SatRel` + the two residuals.** -/
theorem caseSeparated_of_satRel_finSat_vfClassControl (hSat : M1Fix.SatRel M N)
    (hfin : SlotFinSat (M := M) (N := N))
    (hfield : ∀ (S : LRV.Substructure M) (_f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M,
      iVF m → iRv m ∈ S → M5L.Separated S m →
        Assembly.IsVFGen (Substructure.closure LRV ((S : Set M) ∪ {m})) ∧
          VFClassControl (M := M) S (Substructure.closure LRV ((S : Set M) ∪ {m}))) :
    M4Cases.CaseSeparated (M := M) (N := N) :=
  caseSeparated_of_realization_vfClassControl (slotRealization_of_satRel_finSat hSat hfin) hfield

/-! ## 4. The residual is `M`-only: `RelSeparated` from class data plus finite satisfiability -/

/-- **The `M`-side residual of 3.7.**  It mentions neither `N` nor the monomorphism `f`: at every
`Standing S` and every separated `m` with `iRv m ∈ S`, the *canonical* extension
`closure (S ∪ {m})` is `VF`-generated and its `VF`-part is class-controlled by `S`.  This is where
the paper's field theory (Claim (⋆) for 3.7) sits in the frozen encoding. -/
def SlotClassData (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    M5L.Separated S m →
      Assembly.IsVFGen (Substructure.closure LRV ((S : Set M) ∪ {m})) ∧
        VFClassControl (M := M) S (Substructure.closure LRV ((S : Set M) ∪ {m}))

/-- **`RelSeparated` from an `M`-only field residual and a pair-level finite-satisfiability
residual.**  The gate `relGate` enters only through its saturation conjunct `M1Fix.SatRel`; the size
conjunct is not used (and is not needed by the slot). -/
theorem relSeparated_of_slotClassData_finSat
    (hdata : ∀ (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF], SlotClassData M)
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      SlotFinSat (M := M) (N := N)) :
    RouteLedger.RelSeparated := by
  intro M N _ _ _ _ hR
  exact caseSeparated_of_satRel_finSat_vfClassControl hR.1 (hfin M N)
    (fun S f hS m hmVF hmrv hsep => hdata M S hS m hmVF hmrv hsep)

/-- **The merged route, at the gate.**  `M5L.OneStepSeparatedP` plus the bridge
`∀ S, Standing S → VFInvClosedOn S` give `RelSeparated`.  Recorded so that the matrix of the
endgame (`QE/RouteLedger.lean` §7) has this row machine-checked, and so that the new residual above
can be compared with it: `VFClassControl` needs neither `VFInvClosedOn` nor the size conjunct. -/
theorem relSeparated_of_oneStepSeparatedP
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M5L.OneStepSeparatedP (M := M) (N := N))
    (hfinv : ∀ (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
      (S : LRV.Substructure M), Assembly.Standing S → M5L.VFInvClosedOn S) :
    RouteLedger.RelSeparated := by
  intro M N _ _ _ _ hR
  exact RouteLedger.caseSeparated_of_oneStepSeparatedP (h M N hR) (hfinv M)

/-! ## 4b. Calibration of the slot: what it really costs

The frontier records 3.7 as the field-theoretic case (`VFInvClosedOn`, Claim (⋆)).  The theorems
below locate it precisely, in three calibrated forms.

* **Hull form (§2b) + one element**: `G3.HullExtension` at the pair, together with the realisation of
  the *single* atomic type of `m` over `S`, already gives the slot — because `HullExtension` is
  quantified over *all* substructures, so it applies to the generated `closure (S ∪ {m})` and then
  extends to the canonical hull, which is `Standing` by construction.  So the separated slot costs
  **one instance of the hull-extension principle plus one atomic-type realisation**, and no
  `Γ`-control.
* **Finite satisfiability alone, at the gate**: with the gate's `SatRel`, the tree's
  `M2Saturation.QFFinSat` (finite satisfiability of the pushed types — `QE/SatReal.lean`) gives
  `QFSat`, hence input 5, hence a *total* extension at the pair, hence the slot with `T = ⊤`.  So at
  `relGate`, **`QFFinSat ⇒ RelSeparated`**, with no case analysis at all.
* Consequently the field-theoretic routes of §0–§2 (`VFInvClosedOn`, `PolyExpansions`,
  `VFClassControl`) are *sufficient* conditions, and none of them is needed: the slot has no
  `Γ`-content beyond what the hull and the saturation supply. -/

/-- **`QFFinSat` plus the gate's `SatRel` give qf-type realisation** (`QFSat`): the finite
satisfiability hypothesis is exactly what `SatRel` consumes. -/
theorem qfsat_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M2Saturation.QFSat M N :=
  fun S f m => Assembly.realizesAtomic_of_clause S f m (hSat S f m (hfin S f m))

/-- This file's residual is *weaker* than the tree's `QFFinSat` (which carries no `Standing`, no `iVF`
and no `m ∉ S` restriction), so the `M`-only route of §4 is implied by the calibration below. -/
theorem slotFinSat_of_qffinsat (h : M2Saturation.QFFinSat M N) :
    SlotFinSat (M := M) (N := N) :=
  fun S f _hS m _hmVF _hm => h S f m

/-- **Proposition 3.9 at the pair gives the slot** (with `T = ⊤`): `Assembly.Standing ⊤` holds, so a
total extension of `f` is a witness.  This is the `⊤`-witness stress test in its positive form. -/
theorem caseSeparated_of_extendsHere (h : G3.ExtendsHere M N) :
    M4Cases.CaseSeparated (M := M) (N := N) :=
  (M4Cases.cases_of_global_extension (M := M) (N := N) h).separated

/-- **The whole case ledger from finite satisfiability at a `SatRel` pair.**  `QFFinSat` gives
`QFSat` (above), `QFSat` gives input 5 (`M2Saturation.satReal_of_qfsat`), input 5 gives the total
extension (`G3.extendsHere_of_satReal`), and a total extension discharges every slot with `T = ⊤`
(`M4Cases.cases_of_global_extension`).  So *no* case analysis of the paper's `lift:*` type survives
once finite satisfiability at the pair is granted. -/
theorem cases_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.Cases (M := M) (N := N) :=
  M4Cases.cases_of_global_extension (M := M) (N := N)
    (G3.extendsHere_of_satReal (M := M) (N := N)
      (M2Saturation.satReal_of_qfsat (M := M) (N := N)
        (qfsat_of_satRel_qffinsat hSat hfin)))

/-- **THE SLOT FROM FINITE SATISFIABILITY AT THE GATE.**  No separation-specific field theory enters:
`QFFinSat` at a `SatRel` pair already yields input 5, hence the total extension, hence the slot. -/
theorem caseSeparated_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.CaseSeparated (M := M) (N := N) :=
  (cases_of_satRel_qffinsat hSat hfin).separated

/-- **`RelSeparated` from finite satisfiability at the gate.**  So the fifth frontier part is implied
by

    ∀ M N, relGate M N → QFFinSat M N,

which is the hypothesis `QE/SatReal.lean` isolates as the *only* content of input 5 once saturation
is granted.  In particular 3.7 does not need Lemmas 3.5/3.8, `IsVFGen`, `PolyExpansions` or the
Engler–Prestel material. -/
theorem relSeparated_of_qffinsat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    RouteLedger.RelSeparated := by
  intro M N _ _ _ _ hR
  exact caseSeparated_of_satRel_qffinsat hR.1 (hfin M N hR)

/-! ### 4c. Byproduct for the master reduction (u6): the other frontier parts at the same hypothesis

The same three steps discharge the *other* parts of `QE/RouteLedger.lean`'s endgame list.  These are
corollaries of `cases_of_satRel_qffinsat` and of `G3.hullExtension_of_satReal`, recorded here because
they come for free and locate the whole five-part list at one hypothesis; the consolidated
single-hypothesis statement is direction u6's, this is only its `QFFinSat` row. -/

/-- **The 3.3 part (`RelHull`) from finite satisfiability at the gate.** -/
theorem relHull_of_qffinsat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    RouteLedger.RelHull :=
  fun M N _ _ _ _ hR =>
    G3.hullExtension_of_satReal (M := M) (N := N)
      (M2Saturation.satReal_of_qfsat (M := M) (N := N)
        (qfsat_of_satRel_qffinsat hR.1 (hfin M N hR)))

/-- **The case ledger (`RelCases`, hence `RelUnit`, `RelNonUnit`, `RelNewRV`) from finite
satisfiability at the gate.** -/
theorem relCases_of_qffinsat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    RouteLedger.RelCases :=
  fun M N _ _ _ _ hR => cases_of_satRel_qffinsat hR.1 (hfin M N hR)

/-- **The frozen target from Marker's quotation and finite satisfiability at the gate.**  This is
`RouteLedger.paper_theorem_2_3_of_relHull_relCases` with both non-quoted parts supplied by
`QFFinSat`; it is *not* this file's submission (direction u3 is the separated slot), it is the
machine-checked statement that the five-part list collapses to one hypothesis on the `QFFinSat`
row. -/
theorem paper_theorem_2_3_of_qffinsat (hQ : M5Shoenfield.ShoenfieldTestRel)
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_relHull_relCases hQ
    (relHull_of_qffinsat hfin) (relCases_of_qffinsat hfin)

/-- **The case ledger from qf-type realisation alone** (no gate, no saturation). -/
theorem cases_of_qfsat (h : M2Saturation.QFSat M N) : M4Cases.Cases (M := M) (N := N) :=
  M4Cases.cases_of_global_extension (M := M) (N := N)
    (G3.extendsHere_of_satReal (M2Saturation.satReal_of_qfsat h))

/-! ### 4d. Caveat: the finite-satisfiability row is *not* available at every honest-gate pair

`relSeparated_of_qffinsat` is a **per-pair** conditional, and its gated antecedent is known to be
**false**: at an Archimedean target carrying the tree's infinitesimal configuration, `QFFinSat` fails
(`G3.not_finSat_of_satRel_of_archimedean`, and the `∀`-form `G3.not_forall_qffinsat_at_relGate`,
restated below).  So no blanket finite-satisfiability hypothesis can discharge `RelSeparated`, and §4b
must be read as a *containment*: **the slot's content is contained in the finite-satisfiability
content at a pair**, not as a proof of the slot.  What survives without any caveat is §2b's and §2c's
*equivalences*: they say what `RelSeparated` *is* — the extension of `f` to the canonical hull
(`RelHullOneStep`), equivalently (given `RelHull`) one atomic-type realisation per separated instance
(`RelSepRealization`) — and both are open exactly as `RelSeparated` is.

Whether the *restricted* row `SlotFinSat` (`VF`-sorted witness, `Standing S`, `m ∉ S`, `Separated`)
is also refutable at `relGate` pairs is **open**: the tree's refutations are stated for `RV`-sorted
witnesses (`iRV m`), and the upgrade to a `VF`-sorted witness (via `Axioms.rvSurj`) is not carried out
in the tree or here.  This matters: `SlotFinSat` at every `relGate` pair, together with `RelHull`,
would give `RelSeparated` (`relSeparated_of_relHull_slotFinSat`), so its status must be recorded
rather than assumed. -/

/-- **The gated finite-satisfiability antecedent of §4b is refutable** — `G3.not_forall_qffinsat_at_relGate`
restated so that this file's audit is self-contained. -/
theorem not_forall_qffinsat_at_relGate (hSat : M1Fix.SatRel M N) (hsize : M7Paper.SizeHyp M N)
    (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ (∀ (M' N' : Type) [LRV.Structure M'] [LRV.Structure N']
        [M' ⊨ Axioms.ACVF] [N' ⊨ Axioms.ACVF],
        M5Shoenfield.relGate M' N' → M2Saturation.QFFinSat M' N') :=
  G3.not_forall_qffinsat_at_relGate (S := S) (f := f) hSat hsize hArch hsS hsRV hsne hsgt
    hmRV hmne hmgt hinf

/-- **At such a pair `QFFinSat` itself fails** (not merely its `∀`-form), so the containment of §4b
cannot be turned into a hypothesis at every pair. -/
theorem not_qffinsat_of_config (hSat : M1Fix.SatRel M N) (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ M2Saturation.QFFinSat M N :=
  G3.not_finSat_of_satRel_of_archimedean (S := S) (f := f) hSat hArch hsS hsRV hsne hsgt
    hmRV hmne hmgt hinf

/-- **At a hull-extension pair the whole case ledger is *equivalent* to qf-type realisation.**  The
`←` direction is `QFSat → input 5 → total extension → every slot with T = ⊤`; the `→` direction is
the tree's `RouteLedger.hull_and_cases_iff_satReal` followed by `satReal_iff_qfsat`.  So on the
`RelHull` row of the frontier, `RelCases` and `QFSat` are the same obligation — the case lemmas of the
paper are exactly the qf-type realisation statement. -/
theorem cases_iff_qfsat_of_hullExtension (hHull : G3.HullExtension (M := M) (N := N)) :
    M4Cases.Cases (M := M) (N := N) ↔ M2Saturation.QFSat M N :=
  ⟨fun hC =>
    M2Saturation.qfsat_of_satReal
      ((RouteLedger.hull_and_cases_iff_satReal (M := M) (N := N)).mp ⟨hHull, hC⟩),
   cases_of_qfsat⟩

/-- **The slot from the hull-extension principle plus the realisation row** — the form that uses no
`Γ`-control at all. -/
theorem caseSeparated_of_hullExtension_slotRealization
    (hHull : G3.HullExtension (M := M) (N := N))
    (hreal : M3Slot.SlotRealization (M := M) (N := N)) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  refine caseSeparated_of_canonicalHullExtension (M := M) (N := N) ?_
  intro S f hS m hmVF hmrv _hsep
  by_cases hm : m ∈ S
  · exact hullExtAt_of_mem hm hS
  · exact hullExtAt_of_hullExtension hHull S f m (hreal S f hS m hmVF hm) hm

/-- **`RelSeparated` from `RelHull` (the frontier's 3.3 part) plus finite satisfiability at the
gate.**  Note what is *absent*: no `Standing T` obligation, no `VFInvClosedOn`, no `IsVFGen`, no
`VFClassControl`, no `PolyExpansions`.  The separated slot is one instance of the same hull-extension
principle the 3.3 part already asks for, at the generated domain, plus the model-theoretic
realisation. -/
theorem relSeparated_of_relHull_slotFinSat (hHull : RouteLedger.RelHull)
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → SlotFinSat (M := M) (N := N)) :
    RouteLedger.RelSeparated := by
  intro M N _ _ _ _ hR
  exact caseSeparated_of_hullExtension_slotRealization (hHull M N hR)
    (slotRealization_of_satRel_finSat hR.1 (hfin M N hR))

/-- **The slot from qf-type realisation alone** (no gate, no saturation, no model hypotheses):
`QFSat` gives input 5, hence the total extension, hence the slot. -/
theorem caseSeparated_of_qfsat (h : M2Saturation.QFSat M N) :
    M4Cases.CaseSeparated (M := M) (N := N) :=
  caseSeparated_of_extendsHere (M := M) (N := N)
    (G3.extendsHere_of_satReal (M2Saturation.satReal_of_qfsat h))

/-- **The `rv`-old one-step needs no case split once the hull principle is granted.**  `Separated`
does not appear in this statement at all: with `G3.HullExtension` at the pair and the realisation of
one atomic type, *every* new `VF`-element whose `rv` is already in `S` can be adjoined — the hull
supplies `Standing T` and the `Γ`-control that `M5L34_36.lean` needed `VFInvClosedOn` for.  This is
the precise sense in which the separated slot is not a case of its own at this hypothesis; the paper
splits it because its `T` is `⟨Ŝ,e⟩` rather than the hull. -/
theorem oneStepRVOld_of_hullExtension_slotRealization
    (hHull : G3.HullExtension (M := M) (N := N))
    (hreal : M3Slot.SlotRealization (M := M) (N := N)) : M5.OneStepRVOld (M := M) (N := N) := by
  intro S f hS m hmVF _hmrv
  by_cases hm : m ∈ S
  · exact (exists_standing_extension_iff_hullExtAt S f m).mpr (hullExtAt_of_mem hm hS)
  · exact (exists_standing_extension_iff_hullExtAt S f m).mpr
      (hullExtAt_of_hullExtension hHull S f m (hreal S f hS m hmVF hm) hm)

/-- Consequently `OneStepVFP` at the pair costs only the `rv`-new half. -/
theorem oneStepVFP_of_hullExtension_slotRealization
    (hHull : G3.HullExtension (M := M) (N := N))
    (hreal : M3Slot.SlotRealization (M := M) (N := N))
    (hnew : M5.OneStepRVNew (M := M) (N := N)) : Assembly.OneStepVFP (M := M) (N := N) :=
  M5.oneStepVFP_of_two_steps (oneStepRVOld_of_hullExtension_slotRealization hHull hreal) hnew

/-! ## 5. Audit of the slot

The slot's conclusion is non-vacuous, its hypotheses are consistent with the conclusion, and they are
*empty* in the two configurations the frozen tree keeps hitting: the top substructure, and every
`VF`-generated substructure. -/

section Audit

/-- The slot's hypothesis bundle, named (same content as `Lemma36AuditACVF.CaseSeparatedHyp`). -/
def SepHyp (S : LRV.Substructure M) (m : M) : Prop :=
  Assembly.Standing S ∧ iVF m ∧ iRv m ∈ S ∧ M5L.Separated S m

/-- **Non-vacuity of the conclusion**: if every monomorphism out of a substructure of `M` extends to
a total embedding, the separated slot holds (with `T = ⊤`).  So the slot is not contradictory. -/
theorem caseSeparated_of_global_extension
    (hglob : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) :
    M4Cases.CaseSeparated (M := M) (N := N) :=
  (M4Cases.cases_of_global_extension (M := M) (N := N) hglob).separated

/-- **Every instance of the slot is a new, non-unit element.**  So the slot never asks for anything
at a unit (that is the `RelUnit` slot) and never at an element already present. -/
theorem sepHyp_properties {S : LRV.Substructure M} {m : M} (h : SepHyp (M := M) S m)
    (hm0 : m ≠ iVFZero) : m ∉ S ∧ ¬ iUnits (iRv m) :=
  ⟨fun hmS => Lemma36AuditACVF.not_separated_of_mem hmS h.2.1 hm0 h.2.2.2,
    Lemma36AuditACVF.separated_not_units h.2.2.2⟩

/-- **The slot is empty at `VF`-generated `S`** (`QE/Lemma36Audit.lean`, restated in the slot's
vocabulary): `IsVFGen S` turns `iRv m ∈ S` into the class of a `VF`-element of `S`, which separation
forbids.  Consequence for the field residual: `SlotClassData` is asserted at `closure (S ∪ {m})`
only — asserting `IsVFGen S` at the *base* would make the slot vacuous. -/
theorem sepHyp_empty_of_vfgen {S : LRV.Substructure M} {m : M} (h : SepHyp (M := M) S m)
    (hm0 : m ≠ iVFZero) (hgen : Assembly.IsVFGen S) : False :=
  Lemma36AuditACVF.not_separated_of_vfgen h.2.1 hm0 h.2.2.1 hgen h.2.2.2

/-- **The `⊤`-witness**: at `S = ⊤` the slot's hypotheses force `m = 0`, where the conclusion is
trivial (`T = ⊤`, `g` any witness of the conclusion's own cardinality-free form).  So the slot has
no content at the top substructure. -/
theorem sepHyp_at_top_forces_zero {m : M} (hmVF : iVF m)
    (hsep : M5L.Separated (⊤ : LRV.Substructure M) m) : m = iVFZero :=
  Lemma36AuditACVF.separated_top_forces_zero hmVF hsep

/-- The residual holds at the trivial extension, for every separated instance: so `SlotClassData`'s
second conjunct is consistent with its hypotheses, and the residual measures exactly the growth of
`Γ` in the new `VF`-elements. -/
theorem vfClassControl_of_sepHyp_at_self {S : LRV.Substructure M} {m : M}
    (_h : SepHyp (M := M) S m) : VFClassControl S S :=
  vfClassControl_of_le (le_refl S)

/-- **OPEN, and named so that it stays open**: the separated hypothesis bundle is realised by *some*
model of `ACVF`, substructure and element.  Nothing in this tree establishes it, and it cannot be
established from `Axioms.ACVF` by pure syntax: `iRv m ∈ S` with `Separated S m` is a statement about
*which* substructures a model has, and `QE/Lemma36Audit.lean` shows it fails at `⊤` and at every
`VF`-generated `S`.  If it were false in every model, `RelSeparated` would hold vacuously; §4b shows
the sharper fact that it holds from `QFFinSat` at the gate either way.  A consistency witness would
need the Hahn-series model of `QE/HahnModel.lean` (`[IsAlgClosed VFT]` is still a hypothesis there,
and the per-axiom ledger is incomplete), so it is recorded rather than attempted. -/
def SeparatedHypSatisfiable : Prop :=
  ∃ (M : Type) (_ : LRV.Structure M), M ⊨ Axioms.ACVF ∧
    ∃ (S : LRV.Substructure M) (m : M), SepHyp (M := M) S m ∧ m ≠ iVFZero

end Audit

/-! ## 6. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M3Sep.vfClassControl_of_le
#print axioms SpecialTransformations.Milestone0.M3Sep.vfClassControl_of_poly
#print axioms SpecialTransformations.Milestone0.M3Sep.vfClassControl_of_quotInv
#print axioms SpecialTransformations.Milestone0.M3Sep.residualClasses_of_vfClassControl
#print axioms SpecialTransformations.Milestone0.M3Sep.standing_of_vfClassControl
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_of_realization_vfClassControl
#print axioms SpecialTransformations.Milestone0.M3Sep.slotTypeReal_iff_finSatAt
#print axioms SpecialTransformations.Milestone0.M3Sep.realizesAtomic_of_typeReal
#print axioms SpecialTransformations.Milestone0.M3Sep.slotRealization_of_satRel_finSat
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_of_satRel_finSat_vfClassControl
#print axioms SpecialTransformations.Milestone0.M3Sep.relSeparated_of_slotClassData_finSat
#print axioms SpecialTransformations.Milestone0.M3Sep.relSeparated_of_oneStepSeparatedP
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_of_global_extension
#print axioms SpecialTransformations.Milestone0.M3Sep.sepHyp_properties
#print axioms SpecialTransformations.Milestone0.M3Sep.sepHyp_empty_of_vfgen
#print axioms SpecialTransformations.Milestone0.M3Sep.le_canonicalHull
#print axioms SpecialTransformations.Milestone0.M3Sep.canonicalHull_le
#print axioms SpecialTransformations.Milestone0.M3Sep.exists_standing_extension_iff_hullExtAt
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_iff_canonicalHullExtension
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_of_canonicalHullExtension
#print axioms SpecialTransformations.Milestone0.M3Sep.relSeparated_iff_relHullOneStep
#print axioms SpecialTransformations.Milestone0.M3Sep.relSepRealization_of_slotRealization
#print axioms SpecialTransformations.Milestone0.M3Sep.relSeparated_iff_relSepRealization
#print axioms SpecialTransformations.Milestone0.M3Sep.qfsat_of_satRel_qffinsat
#print axioms SpecialTransformations.Milestone0.M3Sep.slotFinSat_of_qffinsat
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_of_extendsHere
#print axioms SpecialTransformations.Milestone0.M3Sep.cases_of_satRel_qffinsat
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_of_satRel_qffinsat
#print axioms SpecialTransformations.Milestone0.M3Sep.relSeparated_of_qffinsat
#print axioms SpecialTransformations.Milestone0.M3Sep.relHull_of_qffinsat
#print axioms SpecialTransformations.Milestone0.M3Sep.relCases_of_qffinsat
#print axioms SpecialTransformations.Milestone0.M3Sep.paper_theorem_2_3_of_qffinsat
#print axioms SpecialTransformations.Milestone0.M3Sep.cases_of_qfsat
#print axioms SpecialTransformations.Milestone0.M3Sep.cases_iff_qfsat_of_hullExtension
#print axioms SpecialTransformations.Milestone0.M3Sep.hullExtAt_of_mem
#print axioms SpecialTransformations.Milestone0.M3Sep.hullExtAt_of_hullExtension
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_of_hullExtension_slotRealization
#print axioms SpecialTransformations.Milestone0.M3Sep.relSeparated_of_relHull_slotFinSat
#print axioms SpecialTransformations.Milestone0.M3Sep.caseSeparated_of_qfsat
#print axioms SpecialTransformations.Milestone0.M3Sep.oneStepRVOld_of_hullExtension_slotRealization
#print axioms SpecialTransformations.Milestone0.M3Sep.oneStepVFP_of_hullExtension_slotRealization
#print axioms SpecialTransformations.Milestone0.M3Sep.vfClassControl_of_sepHyp_at_self
#print axioms SpecialTransformations.Milestone0.M3Sep.sepHyp_at_top_forces_zero

end SpecialTransformations.Milestone0.M3Sep
