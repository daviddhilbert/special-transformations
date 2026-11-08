import Section5.CategoryLift
import Section4.VFDimensionRank
import Section3.NormalizationSaturation

/-! Real mixed presentations in the paper's VF categories. Pointwise VF
rank is unchanged by allowing auxiliary Gamma coordinates in the dimension
definition. Its finite-map proof already keeps only real RV coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

private def flattenPresentation (S : Set M) (k r j : ℕ) :
    Map (PresentedSet.univ (spaceProd (rawPointSpace (M := M) k r)
      (rawRVSpace (M := M) j)) S) (PresentedSet.univ (pointSpace k (r + j)) S) :=
  Map.ofCodes _ (fun p => (p.1.1, Fin.append p.1.2 p.2))
    (fun z => Sum.elim (fun i => z (.inl (.inl i)))
      (Fin.append (fun i => z (.inl (.inr i))) (fun i => z (.inr i))))
    (by
      intro i
      cases i with
      | inl i => exact rawProj S _
      | inr i =>
        cases i using Fin.addCases with
        | left i =>
          change RawFun S ((Fin k ⊕ Fin r) ⊕ Fin j)
            (fun z => Fin.append (fun a => z (.inl (.inr a))) (fun b => z (.inr b))
              (Fin.castAdd j i))
          simp_rw [Fin.append_left]
          exact rawProj S _
        | right i =>
          change RawFun S ((Fin k ⊕ Fin r) ⊕ Fin j)
            (fun z => Fin.append (fun a => z (.inl (.inr a))) (fun b => z (.inr b))
              (Fin.natAdd r i))
          simp_rw [Fin.append_right]
          exact rawProj S _)
    (by
      intro c
      obtain ⟨v, hv⟩ := c.property.1.1
      obtain ⟨t, ht⟩ := c.property.1.2
      obtain ⟨u, hu⟩ := c.property.2
      refine ⟨fun i => ?_, fun i => ?_⟩
      · exact congrFun hv i ▸ (v i).property
      · cases i using Fin.addCases with
        | left i =>
          simp only [Function.comp_apply, Sum.elim_inr, Fin.append_left]
          change iRV (c.val (.inl (.inr i)))
          have he : (t i).val = c.val (.inl (.inr i)) := congrFun ht i
          exact he ▸ (t i).property
        | right i =>
          simp only [Function.comp_apply, Sum.elim_inr, Fin.append_right]
          change iRV (c.val (.inr i))
          have he : (u i).val = c.val (.inr i) := congrFun hu i
          exact he ▸ (u i).property)
    (by
      intro c
      have h := @mixedValues_decode M N k r ⟨c.val ∘ Sum.inl, c.property.1⟩
      have h' := rawRV_decode_values (⟨c.val ∘ Sum.inr, c.property.2⟩ : pDomain (rawRVSpace j))
      refine Prod.ext (funext fun i => Subtype.ext (congrFun h (.inl i)).symm) ?_
      funext i
      apply Subtype.ext
      cases i using Fin.addCases with
      | left i =>
        simp only [Function.comp_apply, Sum.elim_inr, Fin.append_left]
        exact (congrFun h (.inr i)).symm
      | right i =>
        simp only [Function.comp_apply, Sum.elim_inr, Fin.append_right]
        exact (congrFun h' i).symm)

private theorem flattenPresentation_injective (S : Set M) (k r j : ℕ) :
    Function.Injective (flattenPresentation S k r j (M := M)) := by
  intro a b he
  have hv := congrArg (fun p => p.val.1) he
  have ht := congrArg (fun p => p.val.2) he
  change a.val.1.1 = b.val.1.1 at hv
  change Fin.append a.val.1.2 a.val.2 = Fin.append b.val.1.2 b.val.2 at ht
  apply Subtype.ext
  refine Prod.ext (Prod.ext hv ?_) ?_
  · funext i
    simpa only [Fin.append_left] using congrFun ht (Fin.castAdd j i)
  · funext i
    simpa only [Fin.append_right] using congrFun ht (Fin.natAdd r i)

theorem dimensional_presentation {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : PresentedSpace (M := M)) (hΔ : @Space.RVCoded M N Δ) (k : ℕ)
    (A : normalizedVFObject Δ S k) :
    ∃ m : ℕ, ∃ D : DefSet (M := M) S k m,
      ∃ f : Map (normalizedVFData Δ S k A).2 D, Function.Bijective f := by
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  let hsN : @Saturated M N κ := hs.normalize
  let hcan := @CanonicalStructure.normalize_isCanonical M sM
  let flatten (r j : ℕ) := flattenPresentation (M := M) S k r j
  have flatten_injective (r j : ℕ) := flattenPresentation_injective (M := M) S k r j
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  let A' : VFObject Δ (M := M) S k := A
  have hrank := (vfDim_le_iff_point_trdeg hcan hsN hsmall Δ hΔ A'.obj.set k).mp A'.property
  obtain ⟨p, hp⟩ := finite_mixed_map_of_point_trdeg hsN hsmall A'.obj.set k hrank
  obtain ⟨j, h, hh⟩ := injection_refinement h00N hsN hsmall p hp
  let g := DefinableGeometry.Map.comp (flatten A'.obj.index.2 j) (p.pair h).toUniv
  have hg : Function.Injective g :=
    (flatten_injective _ _).comp (DefinableGeometry.Map.toUniv_injective hh)
  refine ⟨_, DefinableGeometry.Map.image g, DefinableGeometry.Map.toImage g, ?_⟩
  constructor
  · intro a b he
    exact hg (Subtype.ext (congrArg (fun z : DefinableGeometry.Map.image g => z.val) he))
  · rintro ⟨b, ⟨a, rfl⟩⟩
    exact ⟨a, rfl⟩

end SpecialTransformations.Section5
