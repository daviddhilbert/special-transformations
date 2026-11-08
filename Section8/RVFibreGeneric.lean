import Section8.MixedLocalFormula

/-! Lemma 8.9 in the canonical presentation. The full local-constancy
locus is definable and open, and its complement has smaller VF dimension. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

noncomputable def rvFibreBadObject {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) :=
  vfObjectOfRaw ((vfRawUniverse_definable S n).inter (rvConstantRaw_definable hG).compl)

theorem rvFibreBad_dim_lt (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded)
    {G : Set (Fin n ⊕ Fin m → M)} (hG : S.Definable LRV G) :
    vfDim Δ (rvFibreBadObject hG) < n := by
  apply vfDim_lt_of_no_independent hc hs hsmall Δ hΔ hn
  intro a ha hind
  exact ha.2 ((mem_rvConstantRaw_iff hv G a).mpr
    (rvFibre_locallyConstant_of_independent hc hv hG a hind))

theorem lemma_8_9_canonical (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {G : Set (Fin n ⊕ Fin m → M)} (hG : S.Definable LRV G) :
    ∃ U : Set (Fin n → M), ∃ hU : S.Definable LRV U,
      U ⊆ vfRawUniverse n ∧
      vfDim (rawRVSpace (M := M) 1)
        (vfObjectOfRaw ((vfRawUniverse_definable S n).inter hU.compl)) < n ∧
      rvLocallyConstantOn (rvFibre G) {a | vfValues a ∈ U} := by
  let U := rvConstantRaw G
  have hU : S.Definable LRV U := rvConstantRaw_definable hG
  refine ⟨U, hU, fun a ha => ha.1, ?_, ?_⟩
  · exact rvFibreBad_dim_lt hc hs hsmall hn hv _ (rawRVSpace_rvCoded 1) hG
  · have he : {a | vfValues a ∈ U} = {a | rvLocallyConstantAt (rvFibre G) a} :=
      Set.ext (fun a => mem_rvConstantRaw_iff hv G a)
    rw [he]
    exact ⟨isOpen_rvLocallyConstantAt (rvFibre G), fun _ h => h⟩

end SpecialTransformations.Section8
