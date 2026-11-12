module

public import Section4.RelationFibres
public import Section4.VFDimensionRank

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

/-- Algebraicity of the output tuple over the input field implies the
corresponding transcendence-degree inequality. -/
theorem tupleField_trdeg_mono_of_isAlgebraic {K : Type} [Field K]
    (E : Subfield K) {n m : ℕ} (a : Fin n → K) (b : Fin m → K)
    (hb : ∀ j, IsAlgebraic (tupleField E a) (b j)) :
    relativeTrdeg E (tupleField E b) (le_tupleField E b) ≤
      relativeTrdeg E (tupleField E a) (le_tupleField E a) := by
  let G := tupleField E a
  let H := (algebraicClosure G K).toSubfield
  have hGH : G ≤ H := by
    intro x hx
    exact mem_algebraicClosure_iff.mpr
      (show IsAlgebraic G x from isAlgebraic_algebraMap (⟨x, hx⟩ : G))
  have hBH : tupleField E b ≤ H := by
    apply sup_le ((le_tupleField E a).trans hGH)
    exact Subfield.closure_le.mpr
      (by rintro x ⟨j, rfl⟩; exact mem_algebraicClosure_iff.mpr (hb j))
  have heq := relativeTrdeg_eq_of_algebraic E G H (le_tupleField E a) hGH
    (fun _ hx => mem_algebraicClosure_iff.mp hx)
  exact (relativeTrdeg_mono E _ H (le_tupleField E b) hBH).trans_eq heq.symm

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r m s : ℕ}

def finiteRelationImage (A : DefSet (rawMixedSpace (M := M) n r) S)
    {R : (rawMixedSpace (M := M) n r).Carrier → (rawMixedSpace m s).Carrier → Prop}
    (hR : (rawMixedSpace n r).RelationDefinable (rawMixedSpace m s) S R) :
    DefSet (rawMixedSpace (M := M) m s) S where
  carrier := {b | ∃ a : A, R a.val b}
  definable := by
    let P := rawMixedSpace (M := M) n r
    let Q := rawMixedSpace (M := M) m s
    have h : Q.Definable S {y | ∃ x, x ∈ A.carrier ∧ R x y} :=
      ((A.definable.left_relation P Q).inter P Q hR).swap P Q |>.exists_right Q P
    have he : {y | ∃ x, x ∈ A.carrier ∧ R x y} = {y | ∃ a : A, R a.val y} := by
      ext y
      constructor
      · rintro ⟨x, hx, hr⟩
        exact ⟨⟨x, hx⟩, hr⟩
      · rintro ⟨a, hr⟩
        exact ⟨a.val, a.property, hr⟩
    rwa [he] at h

/-- Corollary 4.5 for an actual definable finite-valued relation. Its image
is the union of the finite output sets, rather than the image of a selected
single-valued branch. -/
theorem corollary_4_5 (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    {R : (rawMixedSpace (M := M) n r).Carrier → (rawMixedSpace m s).Carrier → Prop}
    (hR : (rawMixedSpace n r).RelationDefinable (rawMixedSpace m s) S R)
    (hf : ∀ a : A, {b | R a.val b}.Finite) :
    vfDim Γ (finiteRelationImage A hR) ≤ vfDim Γ A := by
  apply vfDim_le_of_point_trdeg hs hsmall Γ _ (vfDim Γ A)
  rintro ⟨b, a, hab⟩
  have halg (j : Fin m) :=
    finite_relation_vf_coordinate_isAlgebraic hcan hR a.val b hab (hf a) j
  exact (tupleField_trdeg_mono_of_isAlgebraic (vfParameterField S) a.val.1 b.1 halg).trans
    (vfTupleTrdeg_le_vfDim hcan Γ hΓ A a)

end SpecialTransformations.Section4

end
