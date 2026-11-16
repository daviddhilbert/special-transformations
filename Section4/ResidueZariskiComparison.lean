module

public import Section4.ResidueZariskiPrimeBound
public import Section4.ResidueZariskiDensity
public import Section4.CoordinateRank
public import Section4.ZariskiDimensionUpper
public import Section4.PolynomialSubringDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem residueZariski_dimension_le
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    {n : ℕ} (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def (residueParameterField B) D) :
    ringKrullDim (MvPolynomial (Fin n) (ModelResidue M) ⧸ residueVanishingIdeal D) ≤
      rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
        (residueParameterField_le_definableField B) D hD) := by
  apply ringKrullDim_quotient_le_of_prime_quotient_le
  intro P hP hIP
  letI := hP
  rw [AffineKrullDimension.ringKrullDim_eq_trdeg_toNat (ModelResidue M) _]
  exact_mod_cast residue_prime_quotient_trdeg_le_dimension hcan hex hs B hB D hD P hIP

def residueCoordinateQuotient {n k : ℕ} (D : Set (Fin n → ModelResidue M)) (v : Fin k → Fin n) :
    MvPolynomial (Fin k) (ModelResidue M) →ₐ[ModelResidue M]
      (MvPolynomial (Fin n) (ModelResidue M) ⧸ residueVanishingIdeal D) :=
  (Ideal.Quotient.mkₐ (ModelResidue M) (residueVanishingIdeal D)).comp (MvPolynomial.rename v)

theorem residueCoordinateQuotient_injective_of_full_projection
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    {n k : ℕ} (D : Set (Fin n → ModelResidue M))
    (v : Fin k → Fin n)
    (hD' : Relative.Def (residueParameterField B) ((fun a => a ∘ v) '' D))
    (hne : ((fun a => a ∘ v) '' D).Nonempty)
    (hdim : rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
      (residueParameterField_le_definableField B) _ hD') = k) :
    Function.Injective (residueCoordinateQuotient D v) := by
  intro p q he
  apply sub_eq_zero.mp
  apply residue_polynomial_eq_zero_of_full_dimension hcan hex hκ hs hh B hB
    _ hD' hne hdim
  have hz : residueCoordinateQuotient D v (p - q) = 0 := by rw [map_sub, he, sub_self]
  have hmem : MvPolynomial.rename v (p - q) ∈ residueVanishingIdeal D :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  rintro b ⟨a, ha, rfl⟩
  simpa only [MvPolynomial.eval_rename] using (mem_residueVanishingIdeal_iff D _).mp hmem a ha

theorem residue_dimension_le_Zariski
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    {n : ℕ} (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def (residueParameterField B) D)
    (hne : D.Nonempty) :
    (rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
      (residueParameterField_le_definableField B) D hD) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) (ModelResidue M) ⧸ residueVanishingIdeal D) := by
  let E := residueParameterField B
  let A := residueRVSet hcan E (B : Set M) (residueParameterField_le_definableField B) D hD
  obtain ⟨a, ha, hrank⟩ := exists_residue_point_of_maximum_rank hcan hex hs B hB D hD hne
  obtain ⟨v, hvind⟩ := exists_independent_coordinates_of_rank E a hrank
  let D' := (fun a => a ∘ v) '' D
  have hD' : Relative.Def E D' := hD.image_comp v
  let A' := residueRVSet hcan E (B : Set M) (residueParameterField_le_definableField B) D' hD'
  have hdim : rvDim A' = rvDim A := by
    apply (rvDim_le_arity A').antisymm
    have h := residueTupleRank_le_dimension hcan hex B D' hD' ⟨a ∘ v, a, ha, rfl⟩
    rw [(tupleField_trdeg_eq_arity_iff E (a ∘ v)).mpr hvind] at h
    exact_mod_cast h
  exact polynomial_subring_le_ringKrullDim (residueCoordinateQuotient D v)
    (residueCoordinateQuotient_injective_of_full_projection hcan hex hκ hs hh B hB
      D v hD' ⟨a ∘ v, a, ha, rfl⟩ hdim)

/-- Actual coordinate-ring Krull dimension of a nonempty definable
residue set equals the RV dimension of its field interpretation. -/
theorem residue_dimension_eq_Zariski
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    {n : ℕ} (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def (residueParameterField B) D)
    (hne : D.Nonempty) :
    ringKrullDim (MvPolynomial (Fin n) (ModelResidue M) ⧸ residueVanishingIdeal D) =
      rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
        (residueParameterField_le_definableField B) D hD) :=
  (residueZariski_dimension_le hcan hex hs B hB D hD).antisymm
    (residue_dimension_le_Zariski hcan hex hκ hs hh B hB D hD hne)

def residueZariskiClosure {n : ℕ} (D : Set (Fin n → ModelResidue M)) :
    Set (Fin n → ModelResidue M) :=
  MvPolynomial.zeroLocus (ModelResidue M) (residueVanishingIdeal D)

theorem residue_subset_zariskiClosure {n : ℕ} (D : Set (Fin n → ModelResidue M)) :
    D ⊆ residueZariskiClosure D := MvPolynomial.zeroLocus_vanishingIdeal_le D

theorem residueZariskiClosure_minimal {n : ℕ} (D : Set (Fin n → ModelResidue M))
    (I : Ideal (MvPolynomial (Fin n) (ModelResidue M)))
    (h : D ⊆ MvPolynomial.zeroLocus (ModelResidue M) I) :
    residueZariskiClosure D ⊆ MvPolynomial.zeroLocus (ModelResidue M) I :=
  MvPolynomial.zeroLocus_anti_mono (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal.mp h)

theorem residueZariskiClosure_vanishingIdeal {n : ℕ} (D : Set (Fin n → ModelResidue M)) :
    MvPolynomial.vanishingIdeal (ModelResidue M) (residueZariskiClosure D) =
      residueVanishingIdeal D := by
  apply le_antisymm
  · exact MvPolynomial.vanishingIdeal_anti_mono (residue_subset_zariskiClosure D)
  · exact MvPolynomial.le_vanishingIdeal_zeroLocus (residueVanishingIdeal D)

end SpecialTransformations.Section4.ResiduePurity

end
