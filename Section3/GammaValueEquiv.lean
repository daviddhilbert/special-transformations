import Section3.ValueQuotient
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open MonoidWithZeroHom
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

noncomputable def valueEquiv : GammaTop (M := M) ≃ ValueGroup₀ (.ofClass v) :=
  CanonicalRV.equivOfSameFibers (fun x : VFType (M := M) => vrv (CanonicalRV.encodedRv x))
    v.restrict
    (vrv_surjective.comp CanonicalRV.encodedRv_surjective)
    (ValueGroup₀.restrict₀_surjective (.ofClass v))
    (fun x y => (vf_value_eq_iff v hv x y).trans v.restrict_inj.symm)

theorem valueEquiv_apply_vf (x : VFType (M := M)) :
    valueEquiv v hv (vrv (CanonicalRV.encodedRv x)) = v.restrict x :=
  CanonicalRV.equivOfSameFibers_apply _ _ _ _ _ x

theorem valueEquiv_infinity : valueEquiv v hv (infinity (M := M)) = 0 := by
  have he : infinity (M := M) = vrv (CanonicalRV.encodedRv (0 : VFType (M := M))) := by
    apply congrArg vrv
    apply Subtype.ext
    exact (CanonicalRV.encodedRv_zero_iff _).mpr rfl |>.symm
  rw [he, valueEquiv_apply_vf, map_zero]

theorem valueEquiv_eq_zero (γ : GammaTop (M := M)) :
    valueEquiv v hv γ = 0 ↔ γ = infinity := by
  rw [← valueEquiv_infinity v hv]
  exact (valueEquiv v hv).injective.eq_iff

theorem valueEquiv_rv_le (t u : CanonicalRV.RVSort M) :
    iLe t.val u.val ↔ valueEquiv v hv (vrv u) ≤ valueEquiv v hv (vrv t) := by
  obtain ⟨x, rfl⟩ := CanonicalRV.encodedRv_surjective t
  obtain ⟨y, rfl⟩ := CanonicalRV.encodedRv_surjective u
  rw [valueEquiv_apply_vf, valueEquiv_apply_vf, Valuation.restrict_le_iff]
  exact hv y x

theorem valueEquiv_rv_mul (t u : CanonicalRV.RVSort M) :
    valueEquiv v hv (vrv ⟨iRVMul t.val u.val, rv_mul_mem hM t.property u.property⟩) =
      valueEquiv v hv (vrv t) * valueEquiv v hv (vrv u) := by
  obtain ⟨x, rfl⟩ := CanonicalRV.encodedRv_surjective t
  obtain ⟨y, rfl⟩ := CanonicalRV.encodedRv_surjective u
  have he : (⟨iRVMul (CanonicalRV.encodedRv x).val (CanonicalRV.encodedRv y).val,
      rv_mul_mem hM (CanonicalRV.encodedRv x).property (CanonicalRV.encodedRv y).property⟩ : CanonicalRV.RVSort M) =
      CanonicalRV.encodedRv (x * y) := by
    apply Subtype.ext
    exact (rv_mul_hom_of_model hM x.property y.property).symm
  rw [he, valueEquiv_apply_vf, valueEquiv_apply_vf, valueEquiv_apply_vf, map_mul]

/-- This equivalence is on the actual imaginary quotient. It does not
name representatives or a section as parameters. -/
noncomputable def gammaUnitsEquiv : Gamma (M := M) ≃ (ValueGroup₀ (.ofClass v))ˣ where
  toFun γ := Units.mk0 (valueEquiv v hv γ.val)
    (fun h => γ.property ((valueEquiv_eq_zero v hv γ.val).mp h))
  invFun u := ⟨(valueEquiv v hv).symm u.val, by
    intro he
    have hh := congrArg (valueEquiv v hv) he
    simp only [Equiv.apply_symm_apply, valueEquiv_infinity] at hh
    exact Units.ne_zero u hh⟩
  left_inv γ := by apply Subtype.ext; exact (valueEquiv v hv).symm_apply_apply γ.val
  right_inv u := by apply Units.ext; exact (valueEquiv v hv).apply_symm_apply u.val

end SpecialTransformations.Section3.Values
