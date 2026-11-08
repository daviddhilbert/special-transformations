import Section4.VFTranscendence
import Section4.TupleBasis
import Section4.CoordinateDimension
import Section3.VFDefinableClosure

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_mixed_map_of_point_trdeg {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ)
    (hdeg : ∀ a : A, vfTupleTrdeg S a.val.1 ≤ (k : Cardinal)) :
    ∃ f : Map A (DefSet.univ (rawMixedSpace (M := M) k r) S), f.FiniteFibres := by
  apply finite_mixed_map_of_coordinate_algebraicity hs hsmall A k
  intro a
  obtain ⟨d, hd, v, hv⟩ := exists_algebraic_coordinate_basis
    (vfParameterField S) a.val.1 (hdeg a)
  refine ⟨d, hd, v, ?_⟩
  intro j
  apply AlgebraicAt.raw_finite_witness
  apply (algebraicAt_vf_iff_parameterField _ (a.val.1 j)).mpr
  rw [vfParameterField_union_tuple]
  exact hv j

theorem vfDim_le_of_point_trdeg {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ)
    (hdeg : ∀ a : A, vfTupleTrdeg S a.val.1 ≤ (k : Cardinal)) :
    vfDim Γ A ≤ k := by
  obtain ⟨f, hf⟩ := finite_mixed_map_of_point_trdeg hs hsmall A k hdeg
  exact (vfDim_le_iff Γ A k).mpr ⟨k, le_rfl, .rv r, f, hf⟩

/-- The pointwise rank criterion, including empty sets and zero arities. -/
theorem vfDim_le_iff_point_trdeg
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded) {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) :
    vfDim Γ A ≤ k ↔ ∀ a : A, vfTupleTrdeg S a.val.1 ≤ (k : Cardinal) := by
  constructor
  · intro h a
    exact (vfTupleTrdeg_le_vfDim hcan Γ hΓ A a).trans (by exact_mod_cast h)
  · exact vfDim_le_of_point_trdeg hs hsmall Γ A k

/-- Maximum VF field transcendence degree, with value zero on the empty set.
The arity bound makes this natural-number supremum a finite maximum whenever
the set is nonempty. -/
def vfTrdeg {S : Set M} {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) : ℕ :=
  ⨆ a : A, (vfTupleTrdeg S a.val.1).toNat

theorem vfTrdeg_bounded {S : Set M} {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    BddAbove (Set.range (fun a : A => (vfTupleTrdeg S a.val.1).toNat)) := by
  refine ⟨n, ?_⟩
  rintro _ ⟨a, rfl⟩
  simpa using Cardinal.toNat_le_toNat (vfTupleTrdeg_le_arity S a.val.1)
    Cardinal.natCast_lt_aleph0

/-- Lemma 4.4, for actual definable mixed tuples and genuine saturation.
The auxiliary Gamma presentation must be RV-coded; the actual quotient has
this property by gammaSpace_rvCoded. -/
theorem lemma_4_4 (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded) {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) : vfDim Γ A = vfTrdeg A := by
  apply Nat.le_antisymm
  · apply vfDim_le_of_point_trdeg hs hsmall Γ A (vfTrdeg A)
    intro a
    have hfin := (vfTupleTrdeg_le_arity S a.val.1).trans_lt Cardinal.natCast_lt_aleph0
    rw [← Cardinal.cast_toNat_of_lt_aleph0 hfin]
    exact_mod_cast (le_ciSup (vfTrdeg_bounded A) a)
  · apply ciSup_le'
    intro a
    simpa using Cardinal.toNat_le_toNat (vfTupleTrdeg_le_vfDim hcan Γ hΓ A a)
      Cardinal.natCast_lt_aleph0

end SpecialTransformations.Section4

end
