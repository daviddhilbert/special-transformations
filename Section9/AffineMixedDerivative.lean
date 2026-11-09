import Section9.AffineMixedMaps
import Section9.MixedGenericDifferentiation

/-! The fixed-label derivative of the named diagonal affine coordinate
change, in either direction. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF
local notation "Mixed" => (V × (Fin r → CanonicalRV.RVSort M))

theorem affineMixedMap_injective (A : DefSet (rawMixedSpace (M := M) n r) S)
    (a b : V) (ha : ∀ i, (a i).val ∈ S) (hb : ∀ i, (b i).val ∈ S)
    (ha₀ : ∀ i, a i ≠ 0) : Function.Injective (affineMixedMap A a b ha hb) := by
  intro p q h
  have he := congrArg (fun p => ((p.val : Mixed))) h
  rw [affineMixedMap_apply, affineMixedMap_apply] at he
  have hs := congrArg (fun p : Mixed => p.2) he
  have hf := congrArg (fun p : Mixed => p.1) he
  apply Subtype.ext
  refine Prod.ext (funext fun i => ?_) hs
  exact mul_left_cancel₀ (ha₀ i) (add_right_cancel (congrFun hf i))

noncomputable def affineMixedImage (A : DefSet (rawMixedSpace (M := M) n r) S)
    (a b : V) (ha : ∀ i, (a i).val ∈ S) (hb : ∀ i, (b i).val ∈ S) :=
  (affineMixedMap A a b ha hb).toImage

theorem affineMixedImage_bijective (A : DefSet (rawMixedSpace (M := M) n r) S)
    (a b : V) (ha : ∀ i, (a i).val ∈ S) (hb : ∀ i, (b i).val ∈ S)
    (ha₀ : ∀ i, a i ≠ 0) : Function.Bijective (affineMixedImage A a b ha hb) := by
  constructor
  · intro p q h
    apply affineMixedMap_injective A a b ha hb ha₀
    exact Subtype.ext (congrArg (fun p => (p.val : Mixed)) h)
  · rintro ⟨p, x, rfl⟩
    exact ⟨x, rfl⟩

@[simp] theorem affineMixedImage_inverse_apply (A : DefSet (rawMixedSpace (M := M) n r) S)
    (a b : V) (ha : ∀ i, (a i).val ∈ S) (hb : ∀ i, (b i).val ∈ S)
    (ha₀ : ∀ i, a i ≠ 0) (p : (affineMixedMap A a b ha hb).image) :
    ((affineMixedImage A a b ha hb).inverse (affineMixedImage_bijective A a b ha hb ha₀) p).val =
      (fun i => (a i)⁻¹ * p.val.1 i + (-(a i)⁻¹ * b i), p.val.2) := by
  let f := affineMixedImage A a b ha hb
  let g := f.inverse (affineMixedImage_bijective A a b ha hb ha₀)
  have he := congrArg Subtype.val (Map.apply_inverse f (affineMixedImage_bijective A a b ha hb ha₀) p)
  change (affineMixedMap A a b ha hb (g p)).val = p.val at he
  rw [affineMixedMap_apply] at he
  have hs := congrArg (fun p : Mixed => p.2) he
  have hf := congrArg (fun p : Mixed => p.1) he
  refine Prod.ext (funext fun i => ?_) hs
  change (g p).val.1 i = (a i)⁻¹ * p.val.1 i + -(a i)⁻¹ * b i
  have hei : a i * (g p).val.1 i + b i = p.val.1 i :=
    congrFun hf i
  rw [← hei, mul_add, ← mul_assoc, inv_mul_cancel₀ (ha₀ i), one_mul, neg_mul, add_neg_cancel_right]

noncomputable def vfDiagonalLinear (a : V) : V →ₗ[VF] V :=
  Matrix.toLin' (Matrix.diagonal a)

theorem det_vfDiagonalLinear (a : V) :
    (LinearMap.toMatrix' (vfDiagonalLinear a)).det = ∏ i, a i := by
  rw [vfDiagonalLinear, LinearMap.toMatrix'_toLin', Matrix.det_diagonal]

theorem hasMixedVFDerivativeAt_of_affine_formula [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued VF Γ]
    (hv : ∀ a b : VF, VFValued.predV a b ↔ Valued.v a ≤ Valued.v b)
    {A B : DefSet (rawMixedSpace (M := M) n r) S} (f : Map A B) (p : A)
    (hp : AlgebraicIndependent (vfParameterField S) p.val.1)
    (a b : V) (hf : ∀ q : A, (f q).val.1 = fun i => a i * q.val.1 i + b i) :
    HasMixedVFDerivativeAt f p (vfDiagonalLinear a) := by
  obtain ⟨_, _, ⟨ρ, hρ⟩, _⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f p hp
  have hlinear (x : V) : vfDiagonalLinear a x = fun i => a i * x i := by
    funext i
    change (Matrix.diagonal a).mulVec x i = _
    rw [Matrix.mulVec_diagonal]
  refine ⟨fun x => vfDiagonalLinear a x + b, ⟨ρ, fun x hx => ?_⟩,
    hasVFDerivativeAt_affine (vfDiagonalLinear a) b p.val.1⟩
  obtain ⟨h, hval⟩ := hρ x hx
  have hlabel := congrArg (fun p : Mixed => p.2) hval
  refine ⟨h, Prod.ext ?_ hlabel⟩
  change (f ⟨(x, p.val.2), h⟩).val.1 = vfDiagonalLinear a x + b
  rw [hf, hlinear]
  rfl

end SpecialTransformations.Section9
