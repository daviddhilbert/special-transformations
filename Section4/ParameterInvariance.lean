module

public import Section4.CoordinateRank
public import Section4.CoordinateMaps
public import Section4.FullDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfDim_extend_le (Δ : DefinableGeometry.Space LRV M)
    {S T : Set M} (hST : S ⊆ T) {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    vfDim Δ (A.extend hST) ≤ vfDim Δ A := by
  obtain ⟨i, f, hf⟩ := vfDim_attained Δ A
  exact (vfDim_le_iff Δ (A.extend hST) _).mpr
    ⟨vfDim Δ A, le_rfl, i, f.extend hST, hf.extend hST⟩

theorem exists_point_of_maximum_vf_rank
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded) {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hne : A.carrier.Nonempty) :
    ∃ a : A, vfTupleTrdeg S a.val.1 = (vfDim Δ A : Cardinal) := by
  obtain ⟨a₀, ha₀⟩ := hne
  have hrange : (Set.range (fun a : A => (vfTupleTrdeg S a.val.1).toNat)).Nonempty :=
    ⟨_, ⟨a₀, ha₀⟩, rfl⟩
  obtain ⟨a, ha⟩ := Nat.sSup_mem hrange (vfTrdeg_bounded A)
  change (vfTupleTrdeg S a.val.1).toNat = vfTrdeg A at ha
  rw [← lemma_4_4 hcan hs hsmall Δ hΔ A] at ha
  have hfin := (vfTupleTrdeg_le_arity S a.val.1).trans_lt Cardinal.natCast_lt_aleph0
  refine ⟨a, ?_⟩
  rw [← Cardinal.cast_toNat_of_lt_aleph0 hfin, ha]

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

/-- The unnumbered parameter-invariance assertion in Section 4.1. Both
parameter sets remain small. The proof uses a coordinate image containing
an open polydisc, rather than assuming genericity over the larger base. -/
theorem vfDim_parameter_invariant
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S T : Set M}
    (hS : Cardinal.mk S < κ) (hT : Cardinal.mk T < κ) (hST : S ⊆ T)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) :
    vfDim Δ (A.extend hST) = vfDim Δ A := by
  apply (vfDim_extend_le Δ hST A).antisymm
  by_cases hne : A.carrier.Nonempty
  · obtain ⟨a, ha⟩ := exists_point_of_maximum_vf_rank hcan hs hS Δ hΔ A hne
    obtain ⟨v, hvind⟩ := exists_independent_coordinates_of_rank
      (vfParameterField S) a.val.1 ha
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
    obtain ⟨t, D, hD⟩ := (lemma_4_6 hcan hs hS Δ hΔ hv B hBne).mp hBdim
    have hBT : vfDim Δ (B.extend hST) = vfDim Δ A :=
      vfDim_eq_arity_of_contains_polydisc hcan hs hT Δ hΔ hv (B.extend hST) t D hD
    have he : (f.extend hST).image = B.extend hST := by
      apply DefSet.eq_of_carrier_eq
      rfl
    have h := vfDim_image_le hcan hs hT Δ hΔ (f.extend hST)
    rw [he, hBT] at h
    exact h
  · have hz : vfDim Δ A = 0 := by
      have he : A = DefSet.empty (rawMixedSpace (M := M) n r) S := by
        apply DefSet.eq_of_carrier_eq
        exact Set.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      exact Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space Δ) (.rv 0)
    rw [hz]
    exact Nat.zero_le _

end SpecialTransformations.Section4

end
