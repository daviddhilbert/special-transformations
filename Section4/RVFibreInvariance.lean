import Section4.RVFibreDimension
import Section4.RVDimensionRank
import Section4.MixedRVAlgebraicity
import Section3.SmallFiniteParameters

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r m s : ℕ}

theorem rvFibreDim_le_of_bijective
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B)
    (hf : Function.Bijective f) : rvFibreDim A ≤ rvFibreDim B := by
  apply ciSup_le'
  intro a
  apply rvDim_le_of_point_rank hcan hex hs
    (small_union_range hκ S hsmall (vfValues a.val.1)) (fixedVFFibre A a.val.1)
  intro t
  let p : A := ⟨(a.val.1, t.val), t.property⟩
  let q := f p
  have he := mixed_bijection_point_rv_rank hcan hex f hf p
  change rvTupleRank hcan hex (S ∪ Set.range (vfValues a.val.1)) t.val ≤ rvFibreDim B
  rw [← he]
  let u : fixedVFFibre B q.val.1 := ⟨q.val.2, q.property⟩
  exact (rvTupleRank_le_rvDim hcan hex (fixedVFFibre B q.val.1) u).trans
    (le_ciSup (rvFibreDim_bounded B) q)

/-- Lemma 4.13. VF outputs are algebraic over the input VF base by the
given Section 3 result. Inverse maps make those two bases mutually
algebraic, so their genuine RV ranks agree. No parameter-invariance or
uniform-map conclusion from Section 4 is assumed. -/
theorem lemma_4_13
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B)
    (hf : Function.Bijective f) : rvFibreDim A = rvFibreDim B := by
  apply (rvFibreDim_le_of_bijective hcan hex hκ hs hsmall f hf).antisymm
  exact rvFibreDim_le_of_bijective hcan hex hκ hs hsmall (f.inverse hf)
    (Equiv.ofBijective f hf).symm.bijective

end SpecialTransformations.Section4

end
