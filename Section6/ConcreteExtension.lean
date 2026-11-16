module

public import Section6.ConcreteValued
public import Section6.AngularComponent
public import Mathlib.RingTheory.Valuation.Extension

@[expose] public section

/-! A field embedding compatible with the valuations induces an embedding
of the tagged leading-term structures. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open Valuation.HasExtension

namespace SpecialTransformations.Section6.ConcreteValued

open ConcreteRV ResidueTranscendentalTransport

variable {K L Γ Δ : Type} [Field K] [Field L] [Algebra K L]
variable [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
variable (v : Valuation K Γ) (w : Valuation L Δ) [v.HasExtension w]
local notation "ι" => algebraMap K L

theorem rv_surjective : Function.Surjective (RVCalc.rv v) := by
  intro q
  cases q with
  | none => exact ⟨0, RVCalc.rv_zero⟩
  | some q =>
    obtain ⟨x, _, hx⟩ := RVCalc.rv_surjective v q
    exact ⟨x, hx⟩

private theorem rv_map_eq_iff (x y : K) :
    RVCalc.rv w (ι x) = RVCalc.rv w (ι y) ↔ RVCalc.rv v x = RVCalc.rv v y := by
  by_cases hx : x = 0
  · subst x
    rw [map_zero, RVCalc.rv_zero, RVCalc.rv_zero]
    exact eq_comm.trans ((RVCalc.rv_eq_none_iff.trans (map_eq_zero ι)).trans
      (RVCalc.rv_eq_none_iff.symm.trans eq_comm))
  by_cases hy : y = 0
  · subst y
    rw [map_zero, RVCalc.rv_zero, RVCalc.rv_zero, RVCalc.rv_eq_none_iff,
      RVCalc.rv_eq_none_iff, map_eq_zero]
  rw [RVCalc.rv_eq_iff ((map_ne_zero ι).mpr hx) ((map_ne_zero ι).mpr hy), RVCalc.rv_eq_iff hx hy,
    ← map_sub, val_map_lt_iff v w]

def extensionRV (q : RVCalc.RV v) : RVCalc.RV w := RVCalc.rv w (ι ((rv_surjective v q).choose))

@[simp] theorem extensionRV_rv (x : K) :
    extensionRV v w (RVCalc.rv v x) = RVCalc.rv w (ι x) :=
  (rv_map_eq_iff v w _ _).mpr (rv_surjective v _).choose_spec

theorem extensionRV_injective : Function.Injective (extensionRV v w) := by
  intro q r h
  obtain ⟨x, rfl⟩ := rv_surjective v q
  obtain ⟨y, rfl⟩ := rv_surjective v r
  rw [extensionRV_rv, extensionRV_rv] at h
  exact (rv_map_eq_iff v w x y).mp h

@[simp] theorem extensionRV_zero : extensionRV v w none = none := by
  simpa only [map_zero, RVCalc.rv_zero] using extensionRV_rv v w (0 : K)

@[simp] theorem extensionRV_one : extensionRV v w (some 1) = some 1 := by
  have h {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ) :
      RVCalc.rv u 1 = some 1 := by simp [RVCalc.rv, Units.mk0_one]
  simpa only [map_one, h] using extensionRV_rv v w (1 : K)

theorem extensionRV_mul (q r : RVCalc.RV v) :
    extensionRV v w (RVCalc.rvMul v q r) =
      RVCalc.rvMul w (extensionRV v w q) (extensionRV v w r) := by
  obtain ⟨x, rfl⟩ := rv_surjective v q
  obtain ⟨y, rfl⟩ := rv_surjective v r
  rw [← rv_mul_all, extensionRV_rv, map_mul, rv_mul_all, extensionRV_rv, extensionRV_rv]

theorem extensionRV_inv (q : RVCalc.RV v) :
    extensionRV v w (q.map Inv.inv) = (extensionRV v w q).map Inv.inv := by
  obtain ⟨x, rfl⟩ := rv_surjective v q
  have h {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ]
      (u : Valuation F Γ) (p : RVCalc.RV u) : p.map Inv.inv = rvInv u p := by
    cases p <;> rfl
  rw [extensionRV_rv, h, h, ← rv_inv, ← rv_inv, extensionRV_rv, map_inv₀]

theorem extensionRV_le (q r : RVCalc.RV v) :
    RVCalc.vrv w (extensionRV v w q) ≤ RVCalc.vrv w (extensionRV v w r) ↔
      RVCalc.vrv v q ≤ RVCalc.vrv v r := by
  obtain ⟨x, rfl⟩ := rv_surjective v q
  obtain ⟨y, rfl⟩ := rv_surjective v r
  simpa only [extensionRV_rv, RVCalc.vrv_rv] using val_map_le_iff v w x y

theorem extensionRV_value_one (q : RVCalc.RV v) :
    RVCalc.vrv w (extensionRV v w q) = 1 ↔ RVCalc.vrv v q = 1 := by
  obtain ⟨x, rfl⟩ := rv_surjective v q
  simpa only [extensionRV_rv, RVCalc.vrv_rv] using val_map_eq_one_iff v w x

theorem extensionRV_code (r : ConcreteRV.Residue v) :
    extensionRV v w (residueCode v r) =
      residueCode w (algebraMap (ConcreteRV.Residue v) (ConcreteRV.Residue w) r) := by
  by_cases hr : r = 0
  · simp [hr]
  obtain ⟨x, hx, hres⟩ := AngularComponent.residue_lift_value_one v (Units.mk0 r hr)
  change IsLocalRing.residue v.valuationSubring x = r at hres
  have hy := (val_map_eq_one_iff v w (x : K)).mpr hx
  rw [← hres, algebraMap_residue_eq_residue_algebraMap v w x, residueCode_reduction,
    if_pos hx, extensionRV_rv, residueCode_reduction,
    coe_algebraMap_valuationSubring_eq, if_pos hy]

private theorem extensionRV_domain (q : RVCalc.RV v) :
    extensionRV v w q ∈ Set.range (residueCode w) ↔ q ∈ Set.range (residueCode v) := by
  rw [residueCode_range, residueCode_range, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    ← extensionRV_zero v w, (extensionRV_injective v w).eq_iff, extensionRV_value_one]

theorem extensionRV_add (q r : RVCalc.RV v) :
    extensionRV v w (addResidue v q r) = addResidue w (extensionRV v w q) (extensionRV v w r) := by
  by_cases h : q ∈ Set.range (residueCode v) ∧ r ∈ Set.range (residueCode v)
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    simp only [addResidue_code, extensionRV_code, map_add]
  · rw [addResidue, if_neg h, extensionRV_zero, addResidue, if_neg]
    simpa only [extensionRV_domain] using h

theorem extensionRV_neg (q : RVCalc.RV v) :
    extensionRV v w (negResidue v q) = negResidue w (extensionRV v w q) := by
  by_cases h : q ∈ Set.range (residueCode v)
  · obtain ⟨x, rfl⟩ := h
    simp only [negResidue_code, extensionRV_code, map_neg]
  · rw [negResidue, if_neg h, extensionRV_zero, negResidue, if_neg]
    simpa only [extensionRV_domain] using h

local instance extensionSourceStructure : LRV.Structure (Carrier v) := nativeStructure v
local instance extensionTargetStructure : LRV.Structure (Carrier w) := nativeStructure w

def extension : Carrier v ↪[LRV] Carrier w where
  toFun := Sum.map ι (extensionRV v w)
  inj' := Sum.map_injective.mpr ⟨RingHom.injective ι, extensionRV_injective v w⟩
  map_fun' := by
    intro n f z
    have hs (s : SortTag) (x : Carrier v) :
        hasSort w s (Sum.map ι (extensionRV v w) x) ↔ hasSort v s x := by
      cases s <;> cases x <;> rfl
    have hf (x : Carrier v) : vfValue w (Sum.map ι (extensionRV v w) x) = ι (vfValue v x) := by
      cases x <;> simp [vfValue]
    have hr (x : Carrier v) :
        rvValue w (Sum.map ι (extensionRV v w) x) = extensionRV v w (rvValue v x) := by
      cases x <;> simp [rvValue]
    change Sum.map ι (extensionRV v w)
        (if ∀ i, hasSort v (Fn.argSort f i) (z i) then functionValue v f z else zeroOf v (Fn.resSort f)) =
      if ∀ i, hasSort w (Fn.argSort f i) (Sum.map ι (extensionRV v w) (z i)) then
        functionValue w f (Sum.map ι (extensionRV v w) ∘ z) else zeroOf w (Fn.resSort f)
    simp only [hs]
    split
    · cases f <;>
        simp [functionValue, Function.comp_apply, hf, hr, extensionRV_mul,
          extensionRV_inv, extensionRV_add, extensionRV_neg]
    · cases Fn.resSort f <;> simp [zeroOf]
  map_rel' := by
    intro n r z
    have hs (s : SortTag) (x : Carrier v) :
        hasSort w s (Sum.map ι (extensionRV v w) x) ↔ hasSort v s x := by
      cases s <;> cases x <;> rfl
    have hr (x : Carrier v) :
        rvValue w (Sum.map ι (extensionRV v w) x) = extensionRV v w (rvValue v x) := by
      cases x <;> simp [rvValue]
    cases r with
    | memVF => exact hs .vf (z 0)
    | memRV => exact hs .rv (z 0)
    | memUnits =>
      change (hasSort w .rv (Sum.map ι (extensionRV v w) (z 0)) ∧
          RVCalc.vrv w (rvValue w (Sum.map ι (extensionRV v w) (z 0))) = 1) ↔
        (hasSort v .rv (z 0) ∧ RVCalc.vrv v (rvValue v (z 0)) = 1)
      simp only [hs, hr, extensionRV_value_one]
    | rvLe =>
      change ((∀ i, hasSort w .rv (Sum.map ι (extensionRV v w) (z i))) ∧
          RVCalc.vrv w (rvValue w (Sum.map ι (extensionRV v w) (z 1))) ≤
            RVCalc.vrv w (rvValue w (Sum.map ι (extensionRV v w) (z 0)))) ↔
        ((∀ i, hasSort v .rv (z i)) ∧ RVCalc.vrv v (rvValue v (z 1)) ≤ RVCalc.vrv v (rvValue v (z 0)))
      simp only [hs, hr, extensionRV_le]

end SpecialTransformations.Section6.ConcreteValued
