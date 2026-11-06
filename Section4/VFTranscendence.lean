import Section4.VFAlgebraicCoordinates
import Section4.TupleTranscendence

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfParameterField_union_tuple (S : Set M) {n : ℕ} (a : Fin n → VFType (M := M)) :
    vfParameterField (S ∪ Set.range (vfValues a)) = tupleField (vfParameterField S) a := by
  have hset : {x : VFType (M := M) | x.val ∈ S ∪ Set.range (vfValues a)} =
      {x : VFType (M := M) | x.val ∈ S} ∪ Set.range a := by
    ext x
    constructor
    · rintro (hx | ⟨j, hj⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨j, Subtype.ext hj⟩
    · rintro (hx | ⟨j, rfl⟩)
      · exact Or.inl hx
      · exact Or.inr (Set.mem_range_self j)
  change Subfield.closure _ = _
  rw [hset, Subfield.closure_union]
  rfl

/-- Relative field transcendence degree of the VF coordinates of a point.
RV coordinates do not contribute generators. -/
def vfTupleTrdeg (S : Set M) {n : ℕ} (a : Fin n → VFType (M := M)) : Cardinal :=
  relativeTrdeg (vfParameterField S) (tupleField (vfParameterField S) a)
    (le_tupleField (vfParameterField S) a)

theorem vfTupleTrdeg_le_arity (S : Set M) {n : ℕ} (a : Fin n → VFType (M := M)) :
    vfTupleTrdeg S a ≤ (n : Cardinal) := tupleField_trdeg_le _ a

/-- The lower-bound half of Lemma 4.4: every point has VF transcendence
degree at most the dimension defined by genuine finite-to-one maps. -/
theorem vfTupleTrdeg_le_vfDim
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    {S : Set M} {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (a : A) :
    vfTupleTrdeg S a.val.1 ≤ (vfDim Γ A : Cardinal) := by
  obtain ⟨i, f, hf⟩ := vfDim_attained Γ A
  have halg (j : Fin n) := finite_map_vf_coordinate_isAlgebraic hcan Γ hΓ i f hf a j
  rw [vfParameterField_union_tuple] at halg
  exact tupleField_trdeg_le_of_isAlgebraic (vfParameterField S) a.val.1 (f a).val.1 halg

end SpecialTransformations.Section4

end
