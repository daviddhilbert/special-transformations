import Section3.GammaOperations
import Section3.GammaDefinability
import ValuedFieldExtension
import VFAlgClosed
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem le_infinity (γ : GammaTop (M := M)) : γ ≤ infinity := by
  change valueEquiv presentationValuation presentation_compatible infinity ≤
    valueEquiv presentationValuation presentation_compatible γ
  rw [valueEquiv_infinity]
  exact zero_le

theorem vf_value_zero : vrv (CanonicalRV.encodedRv (0 : VFType (M := M))) = (0 : GammaTop (M := M)) := by
  have he : CanonicalRV.encodedRv (0 : VFType (M := M)) =
      (⟨iRVZero,rv_zero_mem hM⟩ : CanonicalRV.RVSort M) :=
    Subtype.ext ((CanonicalRV.encodedRv_zero_iff _).mpr rfl)
  rw [he]
  exact infinity_eq_zero

theorem vf_value_one : vrv (CanonicalRV.encodedRv (1 : VFType (M := M))) = (1 : GammaTop (M := M)) := by
  apply (paperValueEquiv (M := M)).injective
  rw [paperValue_one]
  change valueEquiv presentationValuation presentation_compatible (vrv (CanonicalRV.encodedRv (1 : VFType (M := M)))) = 1
  rw [valueEquiv_apply_vf,map_one]

theorem vf_value_mul (x y : VFType (M := M)) :
    vrv (CanonicalRV.encodedRv (x*y)) = vrv (CanonicalRV.encodedRv x) * vrv (CanonicalRV.encodedRv y) := by
  have he : CanonicalRV.encodedRv (x*y) =
      (⟨iRVMul (CanonicalRV.encodedRv x).val (CanonicalRV.encodedRv y).val,
        rv_mul_mem hM (CanonicalRV.encodedRv x).property (CanonicalRV.encodedRv y).property⟩ : CanonicalRV.RVSort M) :=
    Subtype.ext (rv_mul_hom_of_model hM x.property y.property)
  rw [he,vrv_mul]

noncomputable def vfValueHom : VFType (M := M) →*₀ GammaTop (M := M) where
  toFun x := vrv (CanonicalRV.encodedRv x)
  map_zero' := vf_value_zero
  map_one' := vf_value_one
  map_mul' := vf_value_mul

noncomputable def gammaValHom : Gamma (M := M) →* GammaTop (M := M) where
  toFun := Subtype.val
  map_one' := gamma_val_one
  map_mul' := gamma_val_mul

theorem vf_pred_iff_gamma_le (x y : VFType (M := M)) :
    VFValued.predV x y ↔ vfValueHom y ≤ vfValueHom x :=
  (vrv_le_iff (CanonicalRV.encodedRv y) (CanonicalRV.encodedRv x)).symm

/-- Divisibility of the actual Gamma carrier comes from roots in the VF
field, without choosing RV or Gamma representatives as parameters. -/
theorem gamma_pow_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun γ : Gamma (M := M) => γ ^ n) := by
  intro γ
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨t,ht0,htγ⟩ := gamma_has_nonzero_representative γ
  obtain ⟨b,hb⟩ := CanonicalRV.encodedRv_surjective t
  have hb0 : b ≠ 0 := by
    intro hz
    exact ht0 ((congrArg Subtype.val hb).symm.trans ((CanonicalRV.encodedRv_zero_iff _).mpr hz))
  obtain ⟨a,hpow⟩ := IsAlgClosed.exists_pow_nat_eq b (Nat.pos_of_ne_zero hn)
  have ha0 : a ≠ 0 := by
    intro hz
    apply hb0
    rw [← hpow,hz,zero_pow hn]
  have htA : (CanonicalRV.encodedRv a).val ≠ iRVZero :=
    fun hz => ha0 ((CanonicalRV.encodedRv_zero_iff a).mp hz)
  let δ := gammaOf (CanonicalRV.encodedRv a) htA
  refine ⟨δ,?_⟩
  apply Subtype.ext
  calc
    (δ ^ n).val = δ.val ^ n := map_pow gammaValHom δ n
    _ = (vfValueHom a) ^ n := rfl
    _ = vfValueHom (a ^ n) := (map_pow vfValueHom a n).symm
    _ = vfValueHom b := congrArg vfValueHom hpow
    _ = γ.val := (congrArg vrv hb).trans htγ

noncomputable instance gammaRootable : RootableBy (Gamma (M := M)) ℕ :=
  rootableByOfPowLeftSurj (Gamma (M := M)) ℕ (fun {n} hn => gamma_pow_surjective n hn)

instance gammaNontrivial : Nontrivial (Gamma (M := M)) := by
  obtain ⟨ε,hε0,hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  have htε : (CanonicalRV.encodedRv ε).val ≠ iRVZero :=
    fun hz => hε0 ((CanonicalRV.encodedRv_zero_iff ε).mp hz)
  let γ := gammaOf (CanonicalRV.encodedRv ε) htε
  refine ⟨γ,1,?_⟩
  intro he
  have hvTop : vfValueHom ε = (1 : GammaTop (M := M)) :=
    (congrArg Subtype.val he).trans gamma_val_one
  have hv := congrArg (paperValueEquiv (M := M)) hvTop
  rw [paperValue_one] at hv
  change valueEquiv presentationValuation presentation_compatible (vrv (CanonicalRV.encodedRv ε)) = 1 at hv
  rw [valueEquiv_apply_vf] at hv
  have hvε : presentationValuation ε = 1 := (Valuation.restrict_eq_one_iff (v := presentationValuation (M := M))).mp hv
  exact hε ((presentation_compatible 1 ε).mpr (by rw [map_one,hvε]))

end SpecialTransformations.Section3.Values
