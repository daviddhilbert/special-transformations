import ValuedModelMap
import CanonicalRVOrder

/-!
Identify the actual residue field of the valuation extracted from a frozen
model with its definable encoded residue sort. Integral field elements reduce
to their RV class when they have value one and to the encoded zero otherwise.
The fibers are exactly those of the ordinary residue map.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport

namespace CanonicalResidue

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev KSort (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] :=
  {a : RVSort M // ValuedModelMap.inK a}

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation (VFType (M := M)) Γ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

include hv

theorem units_encodedRv_iff (a : VFType (M := M)) :
    iUnits (encodedRv a).1 ↔ v a = 1 := by
  by_cases ha : a = 0
  · subst a
    rw [ValuedModelMap.encodedRv_zero, map_zero]
    exact iff_of_false (fun h => ValuedModelMap.units_ne_zero h rfl) zero_ne_one
  · have hr : _root_.RVCalc.rv v a ≠ none := by
      intro h
      exact ha ((_root_.RVCalc.rv_eq_none_iff (v := v)).mp h)
    simpa only [CanonicalRV.equiv_rv, _root_.RVCalc.vrv_rv] using
      CanonicalRV.units_equiv_iff v hv (_root_.RVCalc.rv v a) hr

omit hv in
theorem residue_nonzero_iff (a : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring a ≠ 0 ↔ v (a : VFType (M := M)) = 1 := by
  have ha : v (a : VFType (M := M)) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff v _).mp a.property
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, not_lt]
  exact ⟨fun h => le_antisymm ha h, fun h => h.ge⟩

omit hv in
theorem residue_eq_iff (a b : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring a = IsLocalRing.residue v.valuationSubring b ↔
      v ((a : VFType (M := M)) - (b : VFType (M := M))) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  rfl

noncomputable def reduction (a : v.valuationSubring) : RVSort M :=
  if v (a : VFType (M := M)) = 1 then encodedRv (a : VFType (M := M)) else zeroRV

theorem reduction_zero_iff (a : v.valuationSubring) :
    reduction v a = zeroRV ↔ IsLocalRing.residue v.valuationSubring a = 0 := by
  by_cases ha : v (a : VFType (M := M)) = 1
  · have hr : IsLocalRing.residue v.valuationSubring a ≠ 0 := (residue_nonzero_iff v a).mpr ha
    have hu : iUnits (encodedRv (a : VFType (M := M))).1 :=
      (units_encodedRv_iff v hv _).mpr ha
    have hn : encodedRv (a : VFType (M := M)) ≠ zeroRV :=
      fun h => ValuedModelMap.units_ne_zero hu (congrArg Subtype.val h)
    rw [reduction, if_pos ha]
    exact iff_of_false hn hr
  · rw [reduction, if_neg ha]
    have hr : IsLocalRing.residue v.valuationSubring a = 0 := by
      by_contra h
      exact ha ((residue_nonzero_iff v a).mp h)
    exact iff_of_true rfl hr

theorem same_fibers (a b : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring a = IsLocalRing.residue v.valuationSubring b ↔
      reduction v a = reduction v b := by
  by_cases ha : IsLocalRing.residue v.valuationSubring a = 0
  · rw [ha, (reduction_zero_iff v hv a).mpr ha]
    simpa only [eq_comm] using (reduction_zero_iff v hv b).symm
  by_cases hb : IsLocalRing.residue v.valuationSubring b = 0
  · rw [hb, (reduction_zero_iff v hv b).mpr hb]
    exact (reduction_zero_iff v hv a).symm
  have hva := (residue_nonzero_iff v a).mp ha
  have hvb := (residue_nonzero_iff v b).mp hb
  have ha0 : (a : VFType (M := M)) ≠ 0 := by intro h; simpa [h] using hva
  have hb0 : (b : VFType (M := M)) ≠ 0 := by intro h; simpa [h] using hvb
  rw [reduction, reduction, if_pos hva, if_pos hvb,
    ← CanonicalRV.same_fibers v hv, _root_.RVCalc.rv_eq_iff ha0 hb0, hva]
  exact residue_eq_iff v a b

theorem reduction_inK (a : v.valuationSubring) : ValuedModelMap.inK (reduction v a) := by
  by_cases ha : v (a : VFType (M := M)) = 1
  · rw [reduction, if_pos ha]
    exact Or.inl ((units_encodedRv_iff v hv _).mpr ha)
  · rw [reduction, if_neg ha]
    exact Or.inr rfl

noncomputable def reductionK (a : v.valuationSubring) : KSort M :=
  ⟨reduction v a, reduction_inK v hv a⟩

theorem reductionK_surjective : Function.Surjective (reductionK v hv) := by
  rintro ⟨a, ha⟩
  rcases ha with ha | rfl
  · obtain ⟨x, rfl⟩ := CanonicalRV.encodedRv_surjective a
    have hx : v x = 1 := (units_encodedRv_iff v hv x).mp ha
    refine ⟨⟨x, (Valuation.mem_valuationSubring_iff v _).mpr hx.le⟩, ?_⟩
    apply Subtype.ext
    exact if_pos hx
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    change reduction v 0 = zeroRV
    apply (reduction_zero_iff v hv 0).mpr
    exact map_zero _

noncomputable def equiv : Residue v ≃ KSort M :=
  CanonicalRV.equivOfSameFibers (IsLocalRing.residue v.valuationSubring) (reductionK v hv)
    IsLocalRing.residue_surjective (reductionK_surjective v hv)
    (fun a b => ⟨fun h => Subtype.ext ((same_fibers v hv a b).mp h),
      fun h => (same_fibers v hv a b).mpr (congrArg Subtype.val h)⟩)

theorem equiv_residue (a : v.valuationSubring) :
    equiv v hv (IsLocalRing.residue v.valuationSubring a) = reductionK v hv a :=
  CanonicalRV.equivOfSameFibers_apply _ _ _ _ _ a

noncomputable def toRV (z : Residue v) : RVSort M := (equiv v hv z).val

theorem toRV_residue (a : v.valuationSubring) :
    toRV v hv (IsLocalRing.residue v.valuationSubring a) = reduction v a :=
  congrArg Subtype.val (equiv_residue v hv a)

theorem toRV_injective : Function.Injective (toRV v hv) := by
  intro a b h
  exact (equiv v hv).injective (Subtype.ext h)

noncomputable def encodeResidue (z : Residue v) : M := (toRV v hv z).val

theorem encodeResidue_injective : Function.Injective (encodeResidue v hv) := by
  intro a b h
  exact toRV_injective v hv (Subtype.ext h)

theorem encodeResidue_inK (z : Residue v) :
    iUnits (encodeResidue v hv z) ∨ encodeResidue v hv z = iRVZero :=
  (equiv v hv z).property.imp id (congrArg Subtype.val)

theorem encodeResidue_surjective_inK (a : M) (ha : iUnits a ∨ a = iRVZero) :
    ∃ z : Residue v, encodeResidue v hv z = a := by
  let b : RVSort M := ⟨a, iRV_of_inK hM ha⟩
  have hb : ValuedModelMap.inK b := ha.imp id Subtype.ext
  obtain ⟨z, hz⟩ := (equiv v hv).surjective ⟨b, hb⟩
  exact ⟨z, congrArg (fun k : KSort M => k.val.val) hz⟩

end CanonicalResidue

#print axioms CanonicalResidue.units_encodedRv_iff
#print axioms CanonicalResidue.same_fibers
#print axioms CanonicalResidue.equiv
#print axioms CanonicalResidue.toRV_residue
#print axioms CanonicalResidue.toRV_injective
#print axioms CanonicalResidue.encodeResidue_injective
#print axioms CanonicalResidue.encodeResidue_surjective_inK
