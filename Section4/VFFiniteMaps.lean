import Section4.VFFibreFiniteness
import Section4.MapAlgebraicity
import Section4.VFCategories
import Section4.RVDimension
import Section3.SmallFiniteParameters

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r k : ℕ}

theorem finite_map_to_vf_of_dimension_and_finite_rv_fibres
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hdim : vfDim Δ A ≤ k)
    (hRV : ∀ a, {t | (a, t) ∈ A.carrier}.Finite) :
    ∃ f : Map A (DefSet.univ (rawVFSpace (M := M) k) S), f.FiniteFibres := by
  obtain ⟨d, hd, i, f, hf⟩ := (vfDim_le_iff Δ A k).mp hdim
  let g := (vfPadding hd (i.space Δ) S).comp f
  have hg : g.FiniteFibres :=
    (Map.finiteFibres_of_injective (vfPadding_injective hd (i.space Δ) S)).comp hf
  let h := (Map.fst (rawVFSpace (M := M) k) (i.space Δ) S
    (DefSet.univ ((rawVFSpace k).prod (i.space Δ)) S)).comp g
  refine ⟨h, (Map.finiteFibres_iff_fibreCarrier_finite h).mpr ?_⟩
  intro b
  let c : (rawVFSpace (M := M) k).domain := ⟨vfValues b.val, ⟨b.val, rfl⟩⟩
  let C := h.fibre b c (decode_vfValues b.val)
  have halg : ∀ p : C, ∀ j, AlgebraicAt (S ∪ Set.range (vfValues b.val)) .vf
      (p.val.1 j).val := by
    rintro ⟨p, a, hap, hab⟩ j
    have hb : (g a).val.1 = b.val := congrArg Subtype.val hab
    have ha := finite_map_vf_coordinate_isAlgebraic hcan Δ hΔ i g hg a j
    rw [hb] at ha
    apply (algebraicAt_vf_iff_parameterField _ _).mpr
    simpa only [← hap] using ha
  have hVF : (Prod.fst '' C.carrier).Finite := finite_vf_projection_of_algebraic hs
    (small_union_range hκ S hsmall (vfValues b.val)) C halg
  apply finite_mixed_of_finite_projection C.carrier hVF
  intro a
  apply (hRV a).subset
  rintro t ⟨p, hp, _⟩
  change (a, t) ∈ A.carrier
  rw [← hp]
  exact p.property

theorem dimension_and_finite_rv_fibres_of_finite_map_to_vf
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (Δ : DefinableGeometry.Space LRV M)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) k) S)) (hf : f.FiniteFibres) :
    vfDim Δ A ≤ k ∧ ∀ a, {t | (a, t) ∈ A.carrier}.Finite := by
  let z : Map A (DefSet.univ (rawRVSpace (M := M) 0) S) :=
    Map.toSubsingleton A (rawRVSpace 0)
  let g := (f.pair z).toUniv
  have hg : g.FiniteFibres := by
    intro b
    apply (hf ⟨b.val.1, Set.mem_univ _⟩).subset
    intro a ha
    exact Subtype.ext (congrArg (fun q => q.val.1) ha)
  refine ⟨(vfDim_le_iff Δ A k).mpr ⟨k, le_rfl, .rv 0, g, hg⟩, ?_⟩
  intro a
  let p := Map.fst (rawVFSpace (M := M) n) (rawRVSpace r) S A
  let b : DefSet.univ (rawVFSpace (M := M) n) S := ⟨a, Set.mem_univ _⟩
  let c : (rawVFSpace (M := M) n).domain := ⟨vfValues a, ⟨a, rfl⟩⟩
  let C := p.fibre b c (decode_vfValues a)
  let T := S ∪ Set.range (vfValues a)
  have hsub : C.carrier ⊆ (A.extend (T := T) Set.subset_union_left).carrier := by
    rintro x ⟨u, rfl, _⟩
    exact u.property
  let gC := (g.extend (T := T) Set.subset_union_left).restrict hsub
  have hgC : gC.FiniteFibres := (hg.extend Set.subset_union_left).restrict hsub
  have himVF : (Prod.fst '' gC.image.carrier).Finite := by
    apply finite_vf_projection_of_algebraic hs (small_union_range hκ S hsmall (vfValues a))
    rintro ⟨y, x, hxy⟩ j
    obtain ⟨u, hux, hub⟩ := x.property
    have hua : u.val.1 = a := congrArg Subtype.val hub
    have hxg : (gC x).val = (g u).val := by
      change (g ⟨x.val, hsub x.property⟩).val = (g u).val
      have hxu : (⟨x.val, hsub x.property⟩ : A) = u := Subtype.ext hux.symm
      rw [hxu]
    apply (algebraicAt_vf_iff_parameterField _ _).mpr
    rw [vfParameterField_union_tuple]
    have halg := map_output_vf_coordinate_isAlgebraic hcan g u j
    rw [hua] at halg
    have hy : y.1 j = (g u).val.1 j := congrArg (fun q => q.1 j) (hxy.symm.trans hxg)
    rwa [hy]
  have him : gC.image.carrier.Finite := finite_mixed_of_finite_projection
    gC.image.carrier himVF (fun _ => Set.toFinite _)
  have hCfin : C.carrier.Finite := gC.finite_source_of_finite_image hgC him
  apply (hCfin.image Prod.snd).subset
  intro t ht
  refine ⟨(a, t), ?_, rfl⟩
  exact ⟨⟨(a, t), ht⟩, rfl, rfl⟩

/-- The alternative finite-map characterization in Definition 4.14. -/
theorem vf_bounded_finite_iff_finite_map
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    (vfDim Δ A ≤ k ∧ ∀ a, {t | (a, t) ∈ A.carrier}.Finite) ↔
      ∃ f : Map A (DefSet.univ (rawVFSpace (M := M) k) S), f.FiniteFibres := by
  exact ⟨fun h => finite_map_to_vf_of_dimension_and_finite_rv_fibres
    hcan hκ hs hsmall Δ hΔ A h.1 h.2,
    fun ⟨f, hf⟩ => dimension_and_finite_rv_fibres_of_finite_map_to_vf hcan hκ hs hsmall Δ f hf⟩

end SpecialTransformations.Section4

end
