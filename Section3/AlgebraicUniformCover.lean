import Section3.TupleRelations
import Section3.TupleCompactness
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

/-- Finite-cover part of TupleDescent, with a possibly larger domain base B.
The covering relation is still definable over the original S. This permits
temporary representative parameters in compactness without retaining them
in the resulting relation. The proof adapts algebraicity_descent_raw. -/
theorem uniform_good_relation_cover {κ : Cardinal} (hs : Saturated M κ)
    (S B : Set M) (hSB : S ⊆ B) (A : Set (Fin n → M)) (b : M)
    (hsmall : Cardinal.mk ↥(insert b B) < κ) (hA : B.Definable LRV A)
    (hb : ∀ a ∈ A, AlgebraicOver (S ∪ Set.range a) b) :
    ∃ R : GoodRelation (n := n) S, ∀ a ∈ A, (a,b) ∈ R.val := by
  let slice (R : GoodRelation (n := n) S) : Set (Fin n → M) := {a | (a,b) ∈ R.val}
  let C := Set.range slice
  have hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨R,hR⟩ := good_relation_of_algebraic S a b (hb a ha)
    exact ⟨slice R,Set.mem_range_self _,hR⟩
  have hInsert : insert b S ⊆ insert b B := by
    intro x hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (hSB hx)
  obtain ⟨C₀,hC₀,hsub,hcover⟩ := hs.definable_finite_subcover_tuple
    (insert b B) hsmall A (hA.mono (Set.subset_insert b B)) C
    (by rintro _ ⟨R,rfl⟩; exact (slice_definable S b R).mono hInsert) hcov
  haveI : Finite C₀ := hC₀.to_subtype
  have hchoice (c : C₀) : ∃ R : GoodRelation (n := n) S, slice R = c.val := hsub c.property
  let rel (c : C₀) := Classical.choose (hchoice c)
  have hrel (c : C₀) : slice (rel c) = c.val := Classical.choose_spec (hchoice c)
  let R : Set ((Fin n → M) × M) := {p | ∃ c : C₀, p ∈ (rel c).val}
  have hR : RelationDefinable S R := by
    have hu := Set.definable_iUnion_of_finite (fun c : C₀ => (rel c).property.1)
    simpa only [RelationDefinable,R,Set.mem_ofPred_eq,Set.iUnion_ofPred] using hu
  have hf (a : Fin n → M) : {x | (a,x) ∈ R}.Finite := by
    have h := Set.finite_iUnion (fun c : C₀ => (rel c).property.2 a)
    simpa only [R,Set.iUnion_ofPred,Set.mem_ofPred_eq] using h
  refine ⟨⟨R,hR,hf⟩,?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hcover a ha
  refine ⟨⟨c,hc⟩,?_⟩
  change a ∈ slice (rel ⟨c,hc⟩)
  rw [hrel]
  exact hac

end SpecialTransformations.Section3.RawClosure.Tuple
