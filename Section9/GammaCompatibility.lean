import Section9.GammaJacobian
import Section9.Differentiation
import Section4.CanonicalLift
import Section3.RVOperations

/-! The pointwise Gamma compatibility in the paper is the determinant
value condition used by the affine construction. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {n : ℕ}
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M

theorem rvGammaJacobian_value_of_representatives
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    (t s : Fin n → RV) (ht : ∀ i, (t i).val ≠ iRVZero) (hs : ∀ i, (s i).val ≠ iRVZero)
    (ω : RV) (hω : Values.vrv ω = (rvGammaJacobian t s ht hs).val)
    (x y : Fin n → VF) (c : VF) (hx : tupleRV x = t) (hy : tupleRV y = s)
    (hc : CanonicalRV.encodedRv c = ω) : v c = (∏ i, v (y i)) / ∏ i, v (x i) := by
  subst t
  subst s
  let u := (∏ i, y i) / ∏ i, x i
  have hweight (a : Fin n → VF) (ha : ∀ i, (tupleRV a i).val ≠ iRVZero) :
      (rvVolumeGamma (tupleRV a) ha).val = ∏ i, Values.vfValueHom (a i) :=
    map_prod Values.gammaValHom (fun i => Values.gammaOf (tupleRV a i) (ha i)) Finset.univ
  have hdiv (a b : Values.Gamma (M := M)) : (a / b).val = a.val / b.val := by
    rw [div_eq_mul_inv, Values.gamma_val_mul, Values.gamma_val_inv, div_eq_mul_inv]
  have he : Values.vfValueHom c = Values.vfValueHom u := by
    change Values.vrv (CanonicalRV.encodedRv c) = Values.vfValueHom u
    rw [hc, hω, rvGammaJacobian, hdiv, hweight, hweight]
    change _ = Values.vfValueHom ((∏ i, y i) / ∏ i, x i)
    rw [map_div₀, map_prod, map_prod]
  have hval : v c = v u := le_antisymm
    ((hv c u).mp ((Values.vf_pred_iff_gamma_le c u).mpr he.ge))
    ((hv u c).mp ((Values.vf_pred_iff_gamma_le u c).mpr he.le))
  rw [hval, show u = _ from rfl, map_div₀, map_prod, map_prod]

theorem rv_nonzero_of_gammaJacobian_value
    (t s : Fin n → RV) (ht : ∀ i, (t i).val ≠ iRVZero) (hs : ∀ i, (s i).val ≠ iRVZero)
    (ω : RV) (hω : Values.vrv ω = (rvGammaJacobian t s ht hs).val) : ω.val ≠ iRVZero := by
  intro hz
  have he : ω = (0 : RV) := Subtype.ext (hz.trans RVOperations.zero_val.symm)
  have hz' : Values.vrv ω = 0 := he ▸ RVOperations.vrv_zero
  exact finiteValue_ne_zero (rvGammaJacobian t s ht hs) (hω.symm.trans hz')

end SpecialTransformations.Section9
