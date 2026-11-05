import CanonicalResidue

/-! Arithmetic compatibility of the actual residue field with the definable
encoded residue sort. These identities support guarded formula translation. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport

namespace CanonicalResidue

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation (VFType (M := M)) Γ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

include hv

theorem reduction_zero : reduction v 0 = (zeroRV : RVSort M) :=
  (reduction_zero_iff v hv 0).mpr (map_zero _)

theorem reduction_one : reduction v 1 = (oneRV : RVSort M) := by
  change (if v (1 : VFType (M := M)) = 1 then encodedRv 1 else zeroRV) = oneRV
  rw [if_pos (map_one v)]
  exact ValuedModelMap.encodedRv_one

theorem toRV_zero : toRV v hv 0 = (zeroRV : RVSort M) := by
  have h := toRV_residue v hv (0 : v.valuationSubring)
  simpa only [map_zero, reduction_zero v hv] using h

theorem toRV_one : toRV v hv 1 = (oneRV : RVSort M) := by
  have h := toRV_residue v hv (1 : v.valuationSubring)
  simpa only [map_one, reduction_one v hv] using h

theorem toRV_vres_of_unit (x : VFType (M := M)) (hx : v x = 1) :
    toRV v hv (M7.vres v x hx.le) = encodedRv x := by
  have h := toRV_residue v hv ⟨x, (Valuation.mem_valuationSubring_iff v x).mpr hx.le⟩
  exact h.trans (if_pos hx)

omit hv in
theorem zero_mulRV (a : RVSort M) : mulRV zeroRV a = zeroRV :=
  Subtype.ext (rv_mul_zero_left_of_model hM a.2)

omit hv in
theorem mulRV_zero (a : RVSort M) : mulRV a zeroRV = zeroRV :=
  Subtype.ext (rv_mul_zero_right_of_model hM a.2)

theorem reduction_mul (a b : v.valuationSubring) :
    reduction v (a * b) = mulRV (reduction v a) (reduction v b) := by
  have ha : v (a : VFType (M := M)) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff v _).mp a.property
  have hb : v (b : VFType (M := M)) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff v _).mp b.property
  by_cases ha1 : v (a : VFType (M := M)) = 1
  · by_cases hb1 : v (b : VFType (M := M)) = 1
    · have hp : v ((a * b : v.valuationSubring) : VFType (M := M)) = 1 := by
        change v ((a : VFType (M := M)) * (b : VFType (M := M))) = 1
        rw [map_mul, ha1, hb1, one_mul]
      rw [reduction, reduction, reduction, if_pos hp, if_pos ha1, if_pos hb1]
      exact ValuedModelMap.encodedRv_mul _ _
    · have hp : v ((a * b : v.valuationSubring) : VFType (M := M)) < 1 := by
        change v ((a : VFType (M := M)) * (b : VFType (M := M))) < 1
        rw [map_mul, ha1, one_mul]
        exact lt_of_le_of_ne hb hb1
      rw [reduction, reduction, reduction, if_neg hp.ne, if_pos ha1, if_neg hb1,
        mulRV_zero]
  · have hp : v ((a * b : v.valuationSubring) : VFType (M := M)) < 1 := by
      change v ((a : VFType (M := M)) * (b : VFType (M := M))) < 1
      rw [map_mul]
      calc
        v (a : VFType (M := M)) * v (b : VFType (M := M)) ≤
            v (a : VFType (M := M)) * 1 := mul_le_mul_of_nonneg_left hb zero_le
        _ = v (a : VFType (M := M)) := mul_one _
        _ < 1 := lt_of_le_of_ne ha ha1
    rw [reduction, reduction, if_neg hp.ne, if_neg ha1, zero_mulRV]

theorem reduction_add (a b : v.valuationSubring) :
    reduction v (a + b) = addK (reduction v a) (reduction v b) := by
  by_cases ha : IsLocalRing.residue v.valuationSubring a = 0
  · rw [(reduction_zero_iff v hv a).mpr ha,
      ValuedModelMap.zero_addK _ (reduction_inK v hv b)]
    apply (same_fibers v hv (a + b) b).mp
    rw [map_add, ha, zero_add]
  by_cases hb : IsLocalRing.residue v.valuationSubring b = 0
  · rw [(reduction_zero_iff v hv b).mpr hb,
      ValuedModelMap.addK_zero _ (reduction_inK v hv a)]
    apply (same_fibers v hv (a + b) a).mp
    rw [map_add, hb, add_zero]
  have ha1 := (residue_nonzero_iff v a).mp ha
  have hb1 := (residue_nonzero_iff v b).mp hb
  have hua := (units_encodedRv_iff v hv (a : VFType (M := M))).mpr ha1
  have hub := (units_encodedRv_iff v hv (b : VFType (M := M))).mpr hb1
  have hs : iUnits (iRv (((a : VFType (M := M)) + (b : VFType (M := M))).1)) ↔
      v ((a : VFType (M := M)) + (b : VFType (M := M))) = 1 :=
    units_encodedRv_iff v hv _
  rw [reduction, reduction, reduction, if_pos ha1, if_pos hb1,
    ValuedModelMap.addK_units _ _ hua hub]
  change (if v ((a : VFType (M := M)) + (b : VFType (M := M))) = 1 then
      encodedRv ((a : VFType (M := M)) + (b : VFType (M := M))) else zeroRV) =
    if iUnits (iRv (((a : VFType (M := M)) + (b : VFType (M := M))).1)) then
      encodedRv ((a : VFType (M := M)) + (b : VFType (M := M))) else zeroRV
  by_cases hab : v ((a : VFType (M := M)) + (b : VFType (M := M))) = 1
  · rw [if_pos hab, if_pos (hs.mpr hab)]
  · rw [if_neg hab, if_neg (fun h => hab (hs.mp h))]

theorem reduction_neg (a : v.valuationSubring) :
    reduction v (-a) = negK (reduction v a) := by
  by_cases ha : IsLocalRing.residue v.valuationSubring a = 0
  · have hneg : IsLocalRing.residue v.valuationSubring (-a) = 0 := by
      rw [map_neg, ha, neg_zero]
    rw [(reduction_zero_iff v hv a).mpr ha, (reduction_zero_iff v hv (-a)).mpr hneg,
      ValuedModelMap.negK_zero]
  · have ha1 := (residue_nonzero_iff v a).mp ha
    have hneg : v ((-a : v.valuationSubring) : VFType (M := M)) = 1 := by
      change v (-(a : VFType (M := M))) = 1
      rw [Valuation.map_neg, ha1]
    rw [reduction, reduction, if_pos hneg, if_pos ha1,
      ValuedModelMap.negK_units _ ((units_encodedRv_iff v hv _).mpr ha1)]
    rfl

theorem toRV_mul (x y : Residue v) :
    toRV v hv (x * y) = mulRV (toRV v hv x) (toRV v hv y) := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  rw [← map_mul, toRV_residue, toRV_residue, toRV_residue, reduction_mul v hv]

theorem toRV_add (x y : Residue v) :
    toRV v hv (x + y) = addK (toRV v hv x) (toRV v hv y) := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  rw [← map_add, toRV_residue, toRV_residue, toRV_residue, reduction_add v hv]

theorem toRV_neg (x : Residue v) : toRV v hv (-x) = negK (toRV v hv x) := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rw [← map_neg, toRV_residue, toRV_residue, reduction_neg v hv]

theorem toRV_units_iff (x : Residue v) : iUnits (toRV v hv x).1 ↔ x ≠ 0 := by
  constructor
  · intro h hx
    rw [hx, toRV_zero] at h
    exact ValuedModelMap.units_ne_zero h rfl
  · intro hx
    rcases (equiv v hv x).property with hu | hz
    · exact hu
    · exact False.elim (hx ((toRV_injective v hv) (hz.trans (toRV_zero v hv).symm)))

theorem encodeResidue_zero : encodeResidue v hv 0 = (iRVZero : M) :=
  congrArg Subtype.val (toRV_zero v hv)

theorem encodeResidue_one : encodeResidue v hv 1 = (iRVOne : M) :=
  congrArg Subtype.val (toRV_one v hv)

theorem encodeResidue_add (x y : Residue v) :
    encodeResidue v hv (x + y) = iKAdd (encodeResidue v hv x) (encodeResidue v hv y) :=
  congrArg Subtype.val (toRV_add v hv x y)

theorem encodeResidue_mul (x y : Residue v) :
    encodeResidue v hv (x * y) = iRVMul (encodeResidue v hv x) (encodeResidue v hv y) :=
  congrArg Subtype.val (toRV_mul v hv x y)

theorem encodeResidue_neg (x : Residue v) :
    encodeResidue v hv (-x) = TrivCase.iKNeg (encodeResidue v hv x) :=
  congrArg Subtype.val (toRV_neg v hv x)

theorem encodeResidue_units_iff (x : Residue v) : iUnits (encodeResidue v hv x) ↔ x ≠ 0 :=
  toRV_units_iff v hv x

end CanonicalResidue

#print axioms CanonicalResidue.toRV_zero
#print axioms CanonicalResidue.toRV_one
#print axioms CanonicalResidue.toRV_vres_of_unit
#print axioms CanonicalResidue.toRV_mul
#print axioms CanonicalResidue.toRV_add
#print axioms CanonicalResidue.toRV_neg
#print axioms CanonicalResidue.toRV_units_iff
#print axioms CanonicalResidue.encodeResidue_add
#print axioms CanonicalResidue.encodeResidue_mul
