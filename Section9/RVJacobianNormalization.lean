import Section9.ResidueTangentScaling

/-! The point normalization of Definition 9.14 agrees with a
normalization using any nonzero representatives of the value fibre. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M

theorem isRVJacobianAt_of_normalized_residue_jacobian
    (C : Set (Fin (n + n) → RV)) (a b : Fin n → RV) (x y : Fin n → k)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hxy : productTuple x y ∈ normalizedCorrespondence C a b)
    (D : Matrix (Fin n) (Fin n) k)
    (hD : IsResidueJacobianMap (M := M) (normalizedCorrespondence C a b) (productTuple x y) (Matrix.toLin' D))
    (hd : D.det ≠ 0) :
    IsRVJacobianAt C (residueScale a x) (residueScale b y)
      (((∏ i, b i) / ∏ i, a i) * residueRV D.det) := by
  classical
  let t := residueScale a x
  let s := residueScale b y
  let u := productTuple x y
  let E := Matrix.diagonal (fun i => (y i)⁻¹) * D * Matrix.diagonal x
  have hxy₀ (i) : u i ≠ 0 := by
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      change productTuple x y (productLeft n n j) ≠ 0
      rw [productTuple_left]
      exact hx j
    | inr j =>
      change productTuple x y (productRight n n j) ≠ 0
      rw [productTuple_right]
      exact hy j
  have hres (c : k) (hc : c ≠ 0) : residueRV c ≠ (0 : RV) := (residueRV_ne_zero c).mpr hc
  have ht (i) : t i ≠ 0 := mul_ne_zero (ha i) (hres _ (hx i))
  have hs (i) : s i ≠ 0 := mul_ne_zero (hb i) (hres _ (hy i))
  have hprod : productTuple t s = residueScale (productTuple a b) u := by
    apply productTuple_ext
    · intro i
      simp only [t, u, residueScale, productTuple_left]
    · intro i
      simp only [s, u, residueScale, productTuple_right]
  have hset : normalizedCorrespondence C t s = coordinateScale u ⁻¹' normalizedCorrespondence C a b := by
    ext z
    have hscale : residueScale (productTuple t s) z = residueScale (productTuple a b) (coordinateScale u z) := by
      rw [hprod]
      funext i
      change (_ * residueRVHom (u i)) * residueRVHom (z i) = _ * residueRVHom (u i * z i)
      rw [map_mul, mul_assoc]
    change (_ ∈ C ∧ ∀ i, z i ≠ 0) ↔ (_ ∈ C ∧ ∀ i, u i * z i ≠ 0)
    rw [hscale]
    exact and_congr_right fun _ => ⟨fun hz i => mul_ne_zero (hxy₀ i) (hz i),
      fun hz i h => hz i (by rw [h, mul_zero])⟩
  have hscale (v w : Fin n → k) : coordinateScale u (productTuple v w) =
      productTuple (coordinateScale x v) (coordinateScale y w) := by
    apply productTuple_ext
    · intro i
      simp only [coordinateScale, u, productTuple_left]
    · intro i
      simp only [coordinateScale, u, productTuple_right]
  have hdiag (q w : Fin n → k) : (Matrix.diagonal q).mulVec w = coordinateScale q w := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, coordinateScale]
  have hE : IsResidueJacobianMap (M := M) (normalizedCorrespondence C t s) (fun _ => 1) (Matrix.toLin' E) := by
    intro v w
    rw [hset, polynomialTangent_scale_iff u hxy₀, hscale]
    have hone : coordinateScale u (fun _ => 1) = productTuple x y := by
      funext i
      exact mul_one _
    rw [hone, hD, Matrix.toLin'_apply, Matrix.toLin'_apply]
    simp only [E, ← Matrix.mulVec_mulVec, hdiag]
    constructor
    · intro h
      funext i
      rw [← h]
      change w i = (y i)⁻¹ * (y i * w i)
      rw [← mul_assoc, inv_mul_cancel₀ (hy i), one_mul]
    · intro h
      rw [h]
      funext i
      change y i * ((y i)⁻¹ * _) = _
      rw [← mul_assoc, mul_inv_cancel₀ (hy i), one_mul]
  have hdet : E.det = ((∏ i, y i)⁻¹ * D.det) * ∏ i, x i := by
    rw [show E = _ from rfl, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Matrix.det_diagonal, Finset.prod_inv_distrib]
  refine ⟨hprod.symm ▸ hxy.1, ht, hs, Matrix.toLin' E, hE, ?_, ?_⟩
  · rw [LinearMap.toMatrix'_toLin', hdet]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hy i))) hd)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hx i))
  · let X := ∏ i, residueRVHom (x i)
    let Y := ∏ i, residueRVHom (y i)
    have hX : X ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hres _ (hx i))
    have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hres _ (hy i))
    have hvalue (q : Fin n → RV) (z : Fin n → k) :
        (∏ i, residueScale q z i) = (∏ i, q i) * ∏ i, residueRVHom (z i) := Finset.prod_mul_distrib
    rw [LinearMap.toMatrix'_toLin', hdet, hvalue, hvalue]
    change _ = ((∏ i, b i) * Y / ((∏ i, a i) * X)) * residueRVHom (((∏ i, y i)⁻¹ * D.det) * ∏ i, x i)
    simp only [map_mul, map_inv₀, map_prod]
    change _ = ((∏ i, b i) * Y / ((∏ i, a i) * X)) * ((Y⁻¹ * residueRVHom D.det) * X)
    rw [← div_mul_div_comm, div_eq_mul_inv Y X, mul_assoc]
    rw [show Y * X⁻¹ * (Y⁻¹ * residueRVHom D.det * X) =
      (Y * Y⁻¹) * (X * X⁻¹) * residueRVHom D.det by ac_rfl]
    rw [mul_inv_cancel₀ hY, mul_inv_cancel₀ hX, one_mul, one_mul]
    rfl

end SpecialTransformations.Section9
