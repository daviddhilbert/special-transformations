import Section9.MixedDerivativeFormula
import Section9.MixedGenericDifferentiation
import Section4.Products

/-! The almost-everywhere form of the mixed chain rule. Full
differentiability on the two fixed-label charts is a same-base
definable condition. Finite fibres preserve generic VF points. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s t : ℕ}
local notation "VF" => VFType (M := M)

theorem mixed_vfDim_lt_of_no_independent
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded) (hn : 0 < n)
    (E : DefSet (rawMixedSpace (M := M) n r) S)
    (hno : ∀ p : E, ¬ AlgebraicIndependent (vfParameterField S) p.val.1) :
    vfDim Δ E < n := by
  by_cases hne : E.carrier.Nonempty
  · apply lt_of_le_of_ne (vfDim_le_arity Δ E)
    intro he
    obtain ⟨p, hp⟩ := exists_independent_of_full_dimension hc hs hsmall Δ hΔ E hne he
    exact hno p hp
  · have he : E = DefSet.empty (rawMixedSpace (M := M) n r) S := by
      have he : E.carrier = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      cases E
      cases he
      rfl
    have hz : vfDim Δ (DefSet.empty (rawMixedSpace (M := M) n r) S) = 0 :=
      Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space Δ) (.rv r)
    rwa [he, hz]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VFType (M := M)) G]

theorem exists_mixedJacobianOne_exception
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B)
    (hgeneric : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ L : (Fin n → VF) →ₗ[VF] (Fin n → VF),
        HasMixedVFDerivativeAt f p L ∧ (LinearMap.toMatrix' L).det = 1) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → HasMixedVFJacobianAt f p 1 := by
  let P := rawMixedSpace (M := M) n r
  let D := mixedDerivativeLocus f (fun A => A.det = 1)
  let E : DefSet P S := ⟨A.carrier \ D, A.definable.sdiff P (mixedJacobianOneLocus_definable hn f)⟩
  refine ⟨E, Set.diff_subset, ?_, ?_⟩
  · apply mixed_vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn
    intro p hp
    let q : A := ⟨p.val, p.property.1⟩
    obtain ⟨L, hL, hdet⟩ := hgeneric q hp
    exact p.property.2 ⟨q, rfl, LinearMap.toMatrix' L, hdet,
      by simpa only [Matrix.toLin'_toMatrix'] using hL⟩
  · intro p hp
    have h : p.val ∈ D := by
      by_contra h
      exact hp ⟨p.property, h⟩
    obtain ⟨q, hq, B, hdet, F, hF, hd⟩ := h
    have he : q = p := Subtype.ext hq
    subst q
    refine ⟨F, hF, ?_⟩
    have ht := hd.hasJacobianAt
    rw [LinearMap.toMatrix'_toLin', hdet] at ht
    exact ht

/-- Lemma 9.12 with the approved finite-fibre hypothesis for its
almost-everywhere form. The exceptional set is defined over the base
of the two original maps. -/
theorem lemma_9_12_ae_of_compatible_valuation [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    {C : DefSet (rawMixedSpace (M := M) n t) S}
    (f : Map A B) (g : Map B C) (hf : f.FiniteFibres) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → ∃ J K : VF,
        HasMixedVFJacobianAt f p J ∧ HasMixedVFJacobianAt g (f p) K ∧
        HasMixedVFJacobianAt (g ∘ f) p (K * J) := by
  let F := {x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt f p L}
  let H := {x | ∃ q : B, q.val = x ∧ ∃ L, HasMixedVFDerivativeAt g q L}
  let P := rawMixedSpace (M := M) n r
  let Y := {x | ∃ p : A, p.val = x ∧ (f p).val ∈ H}
  let E : DefSet P S := ⟨A.carrier \ (F ∩ Y), A.definable.sdiff P
    ((mixedDifferentiabilityLocus_definable hn f).inter P
      (f.definable_preimage (mixedDifferentiabilityLocus_definable hn g)))⟩
  refine ⟨E, Set.diff_subset, ?_, ?_⟩
  · apply mixed_vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn
    intro p hp
    have hA : p.val ∈ A.carrier := p.property.1
    let q : A := ⟨p.val, hA⟩
    exact p.property.2 ⟨⟨q, rfl, mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f q hp⟩,
      ⟨q, rfl, f q, rfl, mixedDifferentiableAt_of_independent hc hκ hs hsmall hv g (f q)
        (independent_map_of_finiteFibres hc f hf q hp)⟩⟩
  · intro p hp
    have h : p.val ∈ F ∩ Y := by
      by_contra h
      exact hp ⟨p.property, h⟩
    obtain ⟨p', hp', L, hL⟩ := h.1
    obtain ⟨p'', hp'', q, hq, D, hD⟩ := h.2
    have he' : p' = p := Subtype.ext hp'
    have he'' : p'' = p := Subtype.ext hp''
    subst p'
    subst p''
    have he : q = f p := Subtype.ext hq
    subst q
    exact ⟨_, _, mixedVFJacobian_comp_of_full_derivative hL hD⟩

theorem lemma_9_12_ae [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    {C : DefSet (rawMixedSpace (M := M) n t) S}
    (f : Map A B) (g : Map B C) (hf : f.FiniteFibres) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → ∃ J K : VF,
        HasMixedVFJacobianAt f p J ∧ HasMixedVFJacobianAt g (f p) K ∧
        HasMixedVFJacobianAt (g ∘ f) p (K * J) := by
  letI : Valued VF (Values.presentationType (M := M)) := Valued.mk' Values.presentationValuation
  exact lemma_9_12_ae_of_compatible_valuation hc hκ hs hsmall Values.presentation_compatible hn f g hf

theorem lemma_9_12_zero_arity
    {S : Set M} {A : DefSet (rawMixedSpace (M := M) 0 r) S}
    {B : DefSet (rawMixedSpace (M := M) 0 s) S}
    {C : DefSet (rawMixedSpace (M := M) 0 t) S}
    (f : Map A B) (g : Map B C) (p : A) :
    HasMixedVFJacobianAt f p 1 ∧ HasMixedVFJacobianAt g (f p) 1 ∧
      HasMixedVFJacobianAt (g ∘ f) p (1 * 1) := by
  refine ⟨hasMixedVFJacobianAt_zero_arity f p, hasMixedVFJacobianAt_zero_arity g (f p), ?_⟩
  rw [one_mul]
  exact hasMixedVFJacobianAt_zero_arity (g ∘ f) p

end SpecialTransformations.Section9
