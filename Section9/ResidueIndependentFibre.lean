module

public import Section4.ResidueComparison
public import Section4.RVMaximumValueFibre

@[expose] public section

/-! Full-dimensional RV loci contain an independent residue tuple on
a fixed value fibre. The auxiliary names for its normalization do
not change the dimension of the fibre. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem exists_independent_normalized_residue
    (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hh : StronglyHomogeneous M κ)
    {S : Set M} (hS : Cardinal.mk S < κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (hSB : S ⊆ (B : Set M)) (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) (hsB : ∀ i, (s i).val ∈ B)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i))
    (hne : A.carrier.Nonempty) (hdim : rvDim A = n) :
    ∃ x ∈ normalizedResidueSet (A.extend hSB) s, AlgebraicIndependent (residueParameterField B) x := by
  let A' := A.extend hSB
  let E := residueParameterField B
  let D := normalizedResidueSet A' s
  have hval' : ∀ t ∈ A'.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i) := hval
  have hD := normalizedResidueSet_definable_base hc B A' s hsB
  obtain ⟨t, ht⟩ := hne
  have hDne : D.Nonempty := ⟨residueNormalize s t, residueNormalize_mem A' s hval' ⟨t, ht⟩⟩
  have he : residueRVSet hc E (B : Set M) (residueParameterField_le_definableField B) D hD =
      (rvNamedDivision A' s hsB).image :=
    DefSet.eq_of_carrier_eq (rvNamedDivision_image_eq A' s hsB hval').symm
  obtain ⟨x, hx, hr⟩ := exists_residue_point_of_maximum_rank hc hex hs B hB D hD hDne
  refine ⟨x, hx, (tupleField_trdeg_eq_arity_iff E x).mp ?_⟩
  rw [hr, he, rvNamedDivision_dimension A' s hsB hval',
    rvDim_parameter_invariant hc hex hκ hs hh hSB hS hB A, hdim]

end SpecialTransformations.Section9
