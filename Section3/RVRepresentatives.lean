module

public import CanonicalResidueOperations
public import CanonicalStructure

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap
namespace SpecialTransformations.Section3.RVRepresentatives
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

def InResidue (a : VFType (M := M)) : Prop := v a = 1 ∨ a = 0

include hv in
theorem inResidue_iff (a : VFType (M := M)) :
    InResidue v a ↔ inK (encodedRv a) := by
  unfold InResidue inK
  rw [CanonicalResidue.units_encodedRv_iff v hv]
  apply or_congr Iff.rfl
  constructor
  · intro ha; subst a; exact encodedRv_zero
  · intro ha; exact (encodedRv_zero_iff a).mp (congrArg Subtype.val ha)

noncomputable def add (a b : VFType (M := M)) : VFType (M := M) :=
  if InResidue v a ∧ InResidue v b then
    if a = 0 then b else if b = 0 then a else if v (a + b) = 1 then a + b else 0
  else 0

noncomputable def neg (a : VFType (M := M)) : VFType (M := M) :=
  if v a = 1 then -a else 0

include hv in
theorem add_correct (a b : VFType (M := M)) :
    encodedRv (add v a b) = addK (encodedRv a) (encodedRv b) := by
  classical
  by_cases ha : InResidue v a
  · by_cases hb : InResidue v b
    · rw [add, if_pos ⟨ha, hb⟩]
      by_cases ha0 : a = 0
      · rw [if_pos ha0, ha0, encodedRv_zero,
          zero_addK _ ((inResidue_iff v hv b).mp hb)]
      rw [if_neg ha0]
      by_cases hb0 : b = 0
      · rw [if_pos hb0, hb0, encodedRv_zero,
          addK_zero _ ((inResidue_iff v hv a).mp ha)]
      rw [if_neg hb0]
      have hua := (CanonicalResidue.units_encodedRv_iff v hv a).mpr (ha.resolve_right ha0)
      have hub := (CanonicalResidue.units_encodedRv_iff v hv b).mpr (hb.resolve_right hb0)
      rw [addK_units a b hua hub]
      have he : iUnits (iRv (a + b).val) ↔ v (a + b) = 1 :=
        CanonicalResidue.units_encodedRv_iff v hv (a + b)
      by_cases hs : v (a + b) = 1
      · rw [if_pos hs, if_pos (he.mpr hs)]
      · rw [if_neg hs, if_neg (fun h => hs (he.mp h)), encodedRv_zero]
    · rw [add, if_neg (fun h => hb h.2), encodedRv_zero,
        addK_junk _ _ (Or.inr (fun h => hb ((inResidue_iff v hv b).mpr h)))]
  · rw [add, if_neg (fun h => ha h.1), encodedRv_zero,
      addK_junk _ _ (Or.inl (fun h => ha ((inResidue_iff v hv a).mpr h)))]

include hv in
theorem neg_correct (a : VFType (M := M)) :
    encodedRv (neg v a) = negK (encodedRv a) := by
  classical
  by_cases ha : v a = 1
  · rw [neg, if_pos ha, negK_units a
      ((CanonicalResidue.units_encodedRv_iff v hv a).mpr ha)]
  · rw [neg, if_neg ha, encodedRv_zero]
    by_cases ha0 : a = 0
    · rw [ha0, encodedRv_zero, negK_zero]
    · rw [negK_junk _ (fun h =>
        ((inResidue_iff v hv a).mpr h).elim ha ha0)]

theorem inv_correct (a : VFType (M := M)) :
    (encodedRv a⁻¹).val = iRVInvFn (encodedRv a).val := by
  by_cases ha : a = 0
  · subst a
    rw [inv_zero, encodedRv_zero]
    exact (CanonicalStructure.rvInv_zero hM).symm
  · have harv : (encodedRv a).val ≠ iRVZero := by
      intro h
      exact ha ((encodedRv_zero_iff a).mp h)
    apply Transfer.rv_mul_left_cancel_of_model hM
      (encodedRv a⁻¹).property (encodedRv a).property harv
      (CanonicalStructure.rvInv_mem hM (encodedRv a).property)
    have hl : iRVMul (encodedRv a⁻¹).val (encodedRv a).val = iRVOne := by
      change (mulRV (encodedRv a⁻¹) (encodedRv a)).val = _
      rw [← encodedRv_mul, inv_mul_cancel₀ ha, encodedRv_one]
      rfl
    exact hl.trans (CanonicalStructure.rvInv_mul hM (encodedRv a).property harv).symm

end SpecialTransformations.Section3.RVRepresentatives