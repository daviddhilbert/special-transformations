module

public import Section4.RVDimensionRank
public import Section4.RVSequenceMovement
public import Section4.MapParameters

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rvDim_extend_le {S T : Set M} (hST : S ⊆ T) {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) : rvDim (A.extend hST) ≤ rvDim A := by
  obtain ⟨f, hf⟩ := rvDim_attained A
  exact (rvDim_le_iff (A.extend hST) (rvDim A)).mpr
    ⟨rvDim A, le_rfl, f.extend hST, hf.extend hST⟩

/-- The parameter-invariance assertion after Definition 4.9. The larger
base may contain parameters of either real sort. The proof moves a genuine
independent RV basis using saturation and strong homogeneity. -/
theorem rvDim_parameter_invariant
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) {S T : Set M} (hST : S ⊆ T)
    (hS : Cardinal.mk S < κ) (hT : Cardinal.mk T < κ)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :
    rvDim (A.extend hST) = rvDim A := by
  apply (rvDim_extend_le hST A).antisymm
  by_cases hne : A.carrier.Nonempty
  · obtain ⟨a, ha⟩ := exists_point_of_maximum_rv_rank hcan hex hs hS A hne
    obtain ⟨v, _, hvinj, hI, _⟩ := exists_rv_coordinate_basis_independent hcan hex S a.val
    have hseq := (rvSequenceIndependent_iff hcan hex S (a.val ∘ v)).mpr ⟨hvinj, hI⟩
    obtain ⟨e, hefix, hmov⟩ := exists_automorphism_rv_sequence_independent hcan
      hκ hs hh hST hS hT (a.val ∘ v) hseq
    let t := rvAutomorphism e ∘ a.val
    have htmem : t ∈ A.carrier := by
      let P := rawRVSpace (M := M) n
      have hcode : rvValues a.val ∈ P.preimage A.carrier :=
        ⟨⟨a.val, rfl⟩, by simpa only [P, decode_rvValues] using a.property⟩
      have hecode : e ∘ rvValues a.val = rvValues t := rfl
      have hnew := (definable_mem_automorphism_iff e hefix A.definable
        (rvValues a.val)).mpr hcode
      rw [hecode] at hnew
      obtain ⟨hz, hdec⟩ := hnew
      simpa only [P, decode_rvValues] using hdec
    let b : A.extend hST := ⟨t, htmem⟩
    have hseqT : RVSequenceIndependent T (t ∘ v) := hmov
    obtain ⟨htvinj, hTI⟩ := (rvSequenceIndependent_iff hcan hex T (t ∘ v)).mp hseqT
    have hsub : Set.range (t ∘ v) ⊆ Set.range t := by
      rintro _ ⟨i, rfl⟩
      exact ⟨v i, rfl⟩
    have hrank := hTI.encard_le_eRk_of_subset hsub
    have hcard : (rvTupleRank hcan hex S a.val : ℕ∞) ≤ (Set.range (t ∘ v)).encard := by
      simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] using htvinj.encard_range.ge
    have hrank' := hcard.trans hrank
    have hnat : rvTupleRank hcan hex S a.val ≤ rvTupleRank hcan hex T t := by
      have hfinite : rvTupleERank hcan hex T t ≠ ⊤ :=
        ne_top_of_le_ne_top (ENat.natCast_ne_top n) (rvTupleERank_le_arity hcan hex T t)
      simpa only [rvTupleRank, rvTupleERank, ENat.toNat_natCast] using
        ENat.toNat_le_toNat hrank' hfinite
    exact ha.symm.trans_le (hnat.trans (rvTupleRank_le_rvDim hcan hex (A.extend hST) b))
  · have hfin : A.carrier.Finite := by
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
    rw [(rvDim_eq_zero_iff_finite A).mpr hfin]
    exact Nat.zero_le _

end SpecialTransformations.Section4

end
