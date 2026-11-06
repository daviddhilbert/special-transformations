import Section4.ZariskiDensity
import Section4.PolynomialSubringDimension

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def coordinateQuotient {S : Set M} {n r k : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (v : Fin k → Fin n) :
    MvPolynomial (Fin k) (VFType (M := M)) →ₐ[VFType (M := M)]
      (MvPolynomial (Fin n) (VFType (M := M)) ⧸ vfVanishingIdeal A) :=
  (Ideal.Quotient.mkₐ (VFType (M := M)) (vfVanishingIdeal A)).comp (MvPolynomial.rename v)

theorem coordinateQuotient_injective_of_full_image
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r k : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (v : Fin k → Fin n)
    (hne : (vfSelect v A).image.carrier.Nonempty)
    (hdim : vfDim Δ (vfSelect v A).image = k) :
    Function.Injective (coordinateQuotient A v) := by
  intro p q he
  apply sub_eq_zero.mp
  apply polynomial_eq_zero_of_full_dimension hcan hκ hs hsmall Δ hΔ
    (vfSelect v A).image hne hdim
  have hzero : coordinateQuotient A v (p - q) = 0 := by rw [map_sub, he, sub_self]
  have hmem : MvPolynomial.rename v (p - q) ∈ vfVanishingIdeal A :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  intro b
  obtain ⟨a, ha⟩ := b.property
  rw [← congrArg Prod.fst ha]
  change (p - q).eval (a.val.1 ∘ v) = 0
  simpa only [MvPolynomial.eval_rename] using (mem_vfVanishingIdeal_iff A _).mp hmem a

theorem vfDim_le_vfZariski_dimension
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (hne : A.carrier.Nonempty) :
    (vfDim Δ A : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) (VFType (M := M)) ⧸ vfVanishingIdeal A) := by
  obtain ⟨a, ha⟩ := exists_point_of_maximum_vf_rank hcan hs hsmall Δ hΔ A hne
  obtain ⟨v, hvind⟩ := exists_independent_coordinates_of_rank (vfParameterField S) a.val.1 ha
  let f := vfSelect v A
  let B := f.image
  let b : B := f.toImage a
  have hrank : vfTupleTrdeg S b.val.1 = (vfDim Δ A : Cardinal) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) b.val.1).mpr hvind
  have hBdim : vfDim Δ B = vfDim Δ A := by
    apply (vfDim_le_arity Δ B).antisymm
    have h := vfTupleTrdeg_le_vfDim hcan Δ hΔ B b
    rw [hrank] at h
    exact_mod_cast h
  have hBne : B.carrier.Nonempty := ⟨b.val, b.property⟩
  exact polynomial_subring_le_ringKrullDim (coordinateQuotient A v)
    (coordinateQuotient_injective_of_full_image hcan hκ hs hsmall Δ hΔ A v hBne hBdim)

end SpecialTransformations.Section4

end
