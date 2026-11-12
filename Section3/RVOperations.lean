module

public import Section3.GammaPresentation
public import Section3.GammaValueLaws
public import SubstructureRVGroup
public import CanonicalResidueOperations

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVOperations
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The actual frozen RV carrier, including its single absorbing element,
is equivalent to the canonical quotient group with zero. -/
noncomputable def presentation : CanonicalRV.RVSort M ≃
    WithZero (_root_.RVCalc.RVUnit (Values.presentationValuation (M := M))) :=
  (CanonicalRV.equiv Values.presentationValuation Values.presentation_compatible).symm

/-- Transfer pattern: Mathlib Algebra/GroupWithZero/TransferInstance.lean,
Apache-2.0, Johannes Hoelzl. No order on RV is introduced. -/
noncomputable instance rvGroup : CommGroupWithZero (CanonicalRV.RVSort M) := by
  let e := presentation (M := M)
  letI := e.zero
  letI := e.one
  letI := e.mul
  letI := e.Inv
  letI := e.div
  letI := e.pow ℕ
  letI := e.pow ℤ
  apply e.injective.commGroupWithZero e <;> intros <;> exact e.apply_symm_apply _

theorem zero_val : (0 : CanonicalRV.RVSort M).val = iRVZero :=
  CanonicalRV.equiv_zero Values.presentationValuation Values.presentation_compatible

theorem one_val : (1 : CanonicalRV.RVSort M).val = iRVOne := by
  have he : _root_.RVCalc.rv Values.presentationValuation (1 : VFType (M := M)) =
      (1 : WithZero (_root_.RVCalc.RVUnit (Values.presentationValuation (M := M)))) := by
    simp [_root_.RVCalc.rv,Units.mk0_one]
    rfl
  change (CanonicalRV.equiv Values.presentationValuation Values.presentation_compatible
    (1 : WithZero (_root_.RVCalc.RVUnit (Values.presentationValuation (M := M))))).val = _
  rw [← he]
  exact CanonicalRV.equiv_one Values.presentationValuation Values.presentation_compatible

theorem mul_val (x y : CanonicalRV.RVSort M) : (x*y).val = iRVMul x.val y.val := by
  let v := Values.presentationValuation (M := M)
  let hv := Values.presentation_compatible (M := M)
  let e := CanonicalRV.equiv v hv
  change (e ((presentation x)*(presentation y))).val = _
  have he : (presentation x)*(presentation y) =
      _root_.RVCalc.rvMul v (presentation x) (presentation y) := by
    cases presentation x <;> cases presentation y <;> rfl
  rw [he,CanonicalRV.equiv_mul]
  change iRVMul ((presentation (M := M)).symm (presentation x)).val
    ((presentation (M := M)).symm (presentation y)).val = _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

theorem inv_val (x : CanonicalRV.RVSort M) : (x⁻¹).val = iRVInvFn x.val := by
  let v := Values.presentationValuation (M := M)
  let hv := Values.presentation_compatible (M := M)
  change (CanonicalRV.equiv v hv
    ((presentation x)⁻¹ : WithZero (_root_.RVCalc.RVUnit v))).val = _
  have he : ((presentation x)⁻¹ : WithZero (_root_.RVCalc.RVUnit v)) =
      ResidueTranscendentalTransport.rvInv v (presentation x) := by
    cases presentation x <;> rfl
  rw [he,CanonicalRV.equiv_inv]
  change iRVInvFn ((presentation (M := M)).symm (presentation x)).val = _
  rw [Equiv.symm_apply_apply]

theorem rv_zero : CanonicalRV.encodedRv (0 : VFType (M := M)) = 0 := by
  apply Subtype.ext
  exact (RVCalc.rv_zero_eq hM).trans zero_val.symm

theorem rv_one : CanonicalRV.encodedRv (1 : VFType (M := M)) = 1 := by
  apply Subtype.ext
  exact (RVCalc.rv_one hM).trans one_val.symm

theorem rv_mul (x y : VFType (M := M)) :
    CanonicalRV.encodedRv (x*y) = CanonicalRV.encodedRv x * CanonicalRV.encodedRv y := by
  apply Subtype.ext
  rw [mul_val]
  exact rv_mul_hom_of_model hM x.property y.property

noncomputable def rvHom : VFType (M := M) →*₀ CanonicalRV.RVSort M where
  toFun := CanonicalRV.encodedRv
  map_zero' := rv_zero
  map_one' := rv_one
  map_mul' := rv_mul

theorem vrv_zero : Values.vrv (0 : CanonicalRV.RVSort M) = 0 := by
  rw [← rv_zero]
  exact Values.vf_value_zero

theorem vrv_one : Values.vrv (1 : CanonicalRV.RVSort M) = 1 := by
  rw [← rv_one]
  exact Values.vf_value_one

theorem vrv_mul (x y : CanonicalRV.RVSort M) :
    Values.vrv (x*y) = Values.vrv x * Values.vrv y := by
  have he : x*y = (⟨iRVMul x.val y.val,rv_mul_mem hM x.property y.property⟩ : CanonicalRV.RVSort M) :=
    Subtype.ext (mul_val x y)
  rw [he]
  exact Values.vrv_mul x y

noncomputable def vrvHom : CanonicalRV.RVSort M →*₀ Values.GammaTop (M := M) where
  toFun := Values.vrv
  map_zero' := vrv_zero
  map_one' := vrv_one
  map_mul' := vrv_mul

theorem rv_ne_zero (x : VFType (M := M)) : CanonicalRV.encodedRv x ≠ 0 ↔ x ≠ 0 := by
  have he : CanonicalRV.encodedRv x = 0 ↔ x = 0 := by
    rw [Subtype.ext_iff,zero_val]
    exact CanonicalRV.encodedRv_zero_iff x
  exact not_congr he

/-- Absolute values for internal estimates use the restricted value group,
so every unit radius has a VF representative. The paper Gamma order is the
reverse order; the RV carrier itself is given no linear order. -/
noncomputable def absoluteHom : CanonicalRV.RVSort M →*₀
    MonoidWithZeroHom.ValueGroup₀ (.ofClass (Values.presentationValuation (M := M))) where
  toFun t := Values.valueEquiv Values.presentationValuation Values.presentation_compatible (Values.vrv t)
  map_zero' := by rw [vrv_zero]; exact Values.paperValue_zero
  map_one' := by rw [vrv_one]; exact Values.paperValue_one
  map_mul' x y := by rw [vrv_mul]; exact Values.paperValue_mul _ _

theorem absolute_rv (x : VFType (M := M)) : absoluteHom (CanonicalRV.encodedRv x) =
    (Values.presentationValuation (M := M)).restrict x :=
  Values.valueEquiv_apply_vf Values.presentationValuation Values.presentation_compatible x

theorem absolute_eq_zero (t : CanonicalRV.RVSort M) : absoluteHom t = 0 ↔ t = 0 := by
  change Values.valueEquiv Values.presentationValuation Values.presentation_compatible (Values.vrv t) = 0 ↔ t = 0
  rw [Values.valueEquiv_eq_zero,Values.vrv_eq_infinity_iff]
  simp only [Subtype.ext_iff,zero_val]

theorem units_iff_absolute_one (t : CanonicalRV.RVSort M) (ht : t ≠ 0) :
    iUnits t.val ↔ absoluteHom t = 1 := by
  have ht0 : t.val ≠ iRVZero := fun he => ht (Subtype.ext (he.trans zero_val.symm))
  rw [RVCalc.units_iff_le_one hM t.property ht0]
  have hl := Values.valueEquiv_rv_le Values.presentationValuation Values.presentation_compatible
    t (1 : CanonicalRV.RVSort M)
  have hr := Values.valueEquiv_rv_le Values.presentationValuation Values.presentation_compatible
    (1 : CanonicalRV.RVSort M) t
  change iLe t.val (1 : CanonicalRV.RVSort M).val ↔ absoluteHom 1 ≤ absoluteHom t at hl
  change iLe (1 : CanonicalRV.RVSort M).val t.val ↔ absoluteHom t ≤ absoluteHom 1 at hr
  rw [one_val,map_one] at hl hr
  rw [hl,hr]
  exact ⟨fun h => le_antisymm h.1 h.2,fun h => by rw [h]; exact ⟨le_rfl,le_rfl⟩⟩

theorem zeroRV_eq : (ValuedModelMap.zeroRV : CanonicalRV.RVSort M) = 0 :=
  Subtype.ext zero_val.symm

theorem oneRV_eq : (ValuedModelMap.oneRV : CanonicalRV.RVSort M) = 1 :=
  Subtype.ext one_val.symm

theorem mulRV_eq (x y : CanonicalRV.RVSort M) : ValuedModelMap.mulRV x y = x*y :=
  Subtype.ext (mul_val x y).symm

theorem inK_iff (t : CanonicalRV.RVSort M) :
    ValuedModelMap.inK t ↔ t = 0 ∨ absoluteHom t = 1 := by
  rw [ValuedModelMap.inK,zeroRV_eq]
  by_cases ht : t = 0
  · exact ⟨fun _ => Or.inl ht,fun _ => Or.inr ht⟩
  · simp only [ht,or_false,false_or]
    exact units_iff_absolute_one t ht

theorem not_inK_of_absolute_ne_one (t : CanonicalRV.RVSort M)
    (ht : t ≠ 0) (hv : absoluteHom t ≠ 1) : ¬ ValuedModelMap.inK t := by
  intro h
  exact ((inK_iff t).mp h).elim ht hv

/-- Both residue operations always land in the residue subset, including
their junk-zero branches. The field law is reused from the released bridge. -/
theorem addK_inK (x y : CanonicalRV.RVSort M) : ValuedModelMap.inK (ValuedModelMap.addK x y) := by
  by_cases hx : ValuedModelMap.inK x
  · by_cases hy : ValuedModelMap.inK y
    · let v := Values.presentationValuation (M := M)
      let hv := Values.presentation_compatible (M := M)
      let e := CanonicalResidue.equiv v hv
      let a := e.symm ⟨x,hx⟩
      let b := e.symm ⟨y,hy⟩
      have ha : CanonicalResidue.toRV v hv a = x :=
        congrArg (fun z : CanonicalResidue.KSort M => z.val) (e.apply_symm_apply ⟨x,hx⟩)
      have hb : CanonicalResidue.toRV v hv b = y :=
        congrArg (fun z : CanonicalResidue.KSort M => z.val) (e.apply_symm_apply ⟨y,hy⟩)
      rw [← ha,← hb,← CanonicalResidue.toRV_add]
      exact (e (a+b)).property
    · rw [ValuedModelMap.addK_junk x y (Or.inr hy)]
      exact Or.inr rfl
  · rw [ValuedModelMap.addK_junk x y (Or.inl hx)]
    exact Or.inr rfl

theorem negK_inK (x : CanonicalRV.RVSort M) : ValuedModelMap.inK (ValuedModelMap.negK x) := by
  by_cases hx : ValuedModelMap.inK x
  · exact ValuedModelMap.negK_inK x hx
  · rw [ValuedModelMap.negK_junk x hx]
    exact Or.inr rfl

end SpecialTransformations.Section3.RVOperations
