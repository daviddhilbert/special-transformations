import Section3.GammaSpecialization
import Section3.RVFibreConstancy
import Section3.AdditiveCosets
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem additive_subgroup_isBall_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (P : Base (M := M)) (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAtBase P .vf (Subtype.val '' (H : Set (VFType (M := M))))) :
    IsBall (Subtype.val '' (H : Set (VFType (M := M)))) := by
  obtain ⟨k,t,hH⟩ := hH.specialize
  exact definable_additive_subgroup_isBall h00 (P.real ∪ Set.range (rawTuple t)) H hH

theorem corollary_3_12_gamma_base (P : Base (M := M)) {m : ℕ}
    (B : Set M) (f : RVFibreConstancy.domain B → Fin m → M)
    (hf : ∀ a i, iRV (f a i))
    (hgraph : DefinableOverBase P MixedPolynomialSyntax.contextSort (RVFibreConstancy.graph B f)) :
    {t : M | t ∈ B ∧ ∃ a b : RVFibreConstancy.domain B,
      iRv a.val.val = t ∧ iRv b.val.val = t ∧ f a ≠ f b}.Finite := by
  obtain ⟨k,t,hG⟩ := hgraph.specialize
  exact SpecialTransformations.Section3.corollary_3_12 (P.real ∪ Set.range (rawTuple t)) B f hf hG

theorem lemma_3_18_1_gamma_base (h00 : M ⊨ Axioms.ACVF00) (P : Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAtBase P .vf (Subtype.val '' (H : Set (VFType (M := M)))))
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : DefinableOverBase P MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    {d : VFType (M := M) ⧸ H | ∃ x y, QuotientAddGroup.mk' H x = d ∧
      QuotientAddGroup.mk' H y = d ∧ f x ≠ f y}.Finite := by
  obtain ⟨k,t,hHd⟩ := hH.specialize
  obtain ⟨l,u,hGd⟩ := hgraph.specialize
  let S := (P.real ∪ Set.range (rawTuple t)) ∪ Set.range (rawTuple u)
  have hH' : SpecialTransformations.Section3.DefinableAt S .vf (Subtype.val '' (H : Set (VFType (M := M)))) :=
    hHd.mono Set.subset_union_left
  have hsub : P.real ∪ Set.range (rawTuple u) ⊆ S := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  exact SpecialTransformations.Section3.lemma_3_18_1 h00 S H hH' f hf (hGd.mono hsub)

end SpecialTransformations.Section3.GammaParameters
namespace SpecialTransformations.Section3
export GammaParameters (corollary_3_12_gamma_base lemma_3_18_1_gamma_base)
end SpecialTransformations.Section3
