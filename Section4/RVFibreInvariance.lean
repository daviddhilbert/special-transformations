import Section4.RVFibreDimension
import Section4.RVDimensionRank
import Section4.MixedRVAlgebraicity
import Section4.EarlierRVInputs
import Section3.SmallFiniteParameters
import Section3.CanonicalContext
import Section3.NormalizationSaturation

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
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

namespace Paper

/-- Lemma 4.13 in the canonical presentation of the released model.
The RV exchange premise is supplied by Section 3. -/
theorem lemma_4_13 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ)
    {A : @DefSet LRV M (CanonicalStructure.normalize (M := M))
      (@rawMixedSpace M (CanonicalStructure.normalize (M := M)) n r) S}
    {B : @DefSet LRV M (CanonicalStructure.normalize (M := M))
      (@rawMixedSpace M (CanonicalStructure.normalize (M := M)) m s) S}
    (f : @Map LRV M (CanonicalStructure.normalize (M := M)) _ _ S A B)
    (hf : Function.Bijective f) :
    @rvFibreDim M (CanonicalStructure.normalize (M := M)) S n r A =
      @rvFibreDim M (CanonicalStructure.normalize (M := M)) S m s B := by
  have hn := normalized_model00 h00
  have hc := CanonicalStructure.normalize_isCanonical (M := M)
  let hs' := hs.normalize
  let N := @CanonicalStructure.normalize M sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
  exact @Section4.lemma_4_13 M N hN S n r m s hc
    (@rvExchangeInput_of_earlier M N hN κ hκ hs' hn) κ hκ hs' hsmall A B f hf

end Paper

end SpecialTransformations.Section4

end
