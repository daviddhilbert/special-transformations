module

public import Section4.ZariskiDimensionUpper
public import Section4.ZariskiDimensionLower

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The algebraic Zariski closure: the smallest polynomial zero locus
containing the VF projection. Its dimension below is actual Krull dimension
of the coordinate ring, rather than a definition by transcendence degree. -/
def vfZariskiClosure {S : Set M} {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) : Set (Fin n → VFType (M := M)) :=
  MvPolynomial.zeroLocus (VFType (M := M)) (vfVanishingIdeal A)

theorem vf_projection_subset_zariskiClosure {S : Set M} {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Prod.fst '' A.carrier ⊆ vfZariskiClosure A :=
  MvPolynomial.zeroLocus_vanishingIdeal_le _

theorem vfZariskiClosure_minimal {S : Set M} {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (I : Ideal (MvPolynomial (Fin n) (VFType (M := M))))
    (h : Prod.fst '' A.carrier ⊆ MvPolynomial.zeroLocus (VFType (M := M)) I) :
    vfZariskiClosure A ⊆ MvPolynomial.zeroLocus (VFType (M := M)) I :=
  MvPolynomial.zeroLocus_anti_mono (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal.mp h)

theorem vfZariskiClosure_vanishingIdeal {S : Set M} {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    MvPolynomial.vanishingIdeal (VFType (M := M)) (vfZariskiClosure A) =
      vfVanishingIdeal A := by
  apply le_antisymm
  · exact MvPolynomial.vanishingIdeal_anti_mono (vf_projection_subset_zariskiClosure A)
  · exact MvPolynomial.le_vanishingIdeal_zeroLocus (vfVanishingIdeal A)

/-- Proposition 4.8, also allowing retained RV coordinates. Nonemptiness
is explicit: VF dimension uses zero on the empty set, whereas the Krull
dimension of its zero coordinate ring is bottom. -/
theorem proposition_4_8 (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (hne : A.carrier.Nonempty) :
    ringKrullDim (MvPolynomial (Fin n) (VFType (M := M)) ⧸ vfVanishingIdeal A) = vfDim Δ A :=
  (vfZariski_dimension_le hcan hs hsmall Δ hΔ A).antisymm
    (vfDim_le_vfZariski_dimension hcan hκ hs hsmall Δ hΔ A hne)

theorem proposition_4_8_closure (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (hne : A.carrier.Nonempty) :
    ringKrullDim (MvPolynomial (Fin n) (VFType (M := M)) ⧸
      MvPolynomial.vanishingIdeal (VFType (M := M)) (vfZariskiClosure A)) = vfDim Δ A := by
  rw [vfZariskiClosure_vanishingIdeal]
  exact proposition_4_8 hcan hκ hs hsmall Δ hΔ A hne

end SpecialTransformations.Section4

end
