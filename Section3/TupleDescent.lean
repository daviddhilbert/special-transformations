module

public import Section3.TupleRelations
public import Section3.TupleCompactness

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

theorem uniform_intersection_definable (S : Set M) (A : Set (Fin n → M))
    (hA : S.Definable LRV A) (R : Set ((Fin n → M) × M))
    (hR : RelationDefinable S R) : S.Definable₁ LRV {x | ∀ a ∈ A, (a, x) ∈ R} := by
  have hr := hR.preimage_comp
    (Sum.elim (fun i : Fin n => Sum.inr i) (fun i : Fin 1 => Sum.inl i) :
      Fin n ⊕ Fin 1 → Fin 1 ⊕ Fin n)
  have ha := hA.preimage_comp (Sum.inr : Fin n → Fin 1 ⊕ Fin n)
  have h := (ha.compl.union hr).forall_of_finite
  change S.Definable LRV {x : Fin 1 → M | ∀ a ∈ A, (a, x 0) ∈ R}
  convert h using 1
  ext x
  simp only [Set.preimage_ofPred_eq, Set.mem_ofPred_eq, Set.mem_union,
    Set.mem_compl_iff, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Sum.elim_comp_inr, Sum.elim_comp_inl]
  constructor
  · intro hx a
    by_cases ha : a ∈ A
    · exact Or.inr (hx a ha)
    · exact Or.inl ha
  · intro hx a ha
    exact (hx a).resolve_left (not_not.mpr ha)

theorem algebraicity_descent_raw {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (A : Set (Fin n → M)) (b : M)
    (hsmall : Cardinal.mk ↥(insert b S) < κ)
    (hA : S.Definable LRV A) (hne : A.Nonempty)
    (hb : ∀ a ∈ A, AlgebraicOver (S ∪ Set.range a) b) : AlgebraicOver S b := by
  classical
  let slice (R : GoodRelation (n := n) S) : Set (Fin n → M) := {a | (a, b) ∈ R.val}
  let C := Set.range slice
  have hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨R, hR⟩ := good_relation_of_algebraic S a b (hb a ha)
    exact ⟨slice R, Set.mem_range_self _, hR⟩
  obtain ⟨C₀, hC₀, hsub, hcover⟩ := hs.definable_finite_subcover_tuple
    (insert b S) hsmall A (hA.mono (Set.subset_insert b S)) C
    (by rintro _ ⟨R, rfl⟩; exact slice_definable S b R) hcov
  haveI : Finite C₀ := hC₀.to_subtype
  have hchoice (c : C₀) : ∃ R : GoodRelation (n := n) S, slice R = c.val := hsub c.property
  let rel (c : C₀) := Classical.choose (hchoice c)
  have hrel (c : C₀) : slice (rel c) = c.val := Classical.choose_spec (hchoice c)
  let R : Set ((Fin n → M) × M) := {p | ∃ c : C₀, p ∈ (rel c).val}
  have hR : RelationDefinable S R := by
    have hu := Set.definable_iUnion_of_finite (fun c : C₀ => (rel c).property.1)
    simpa only [RelationDefinable, R, Set.mem_ofPred_eq, Set.iUnion_ofPred] using hu
  let T : Set M := {x | ∀ a ∈ A, (a, x) ∈ R}
  refine ⟨T, uniform_intersection_definable S A hA R hR, ?_, ?_⟩
  · obtain ⟨a₀, ha₀⟩ := hne
    have hf : {x | (a₀, x) ∈ R}.Finite := by
      have hf := Set.finite_iUnion (fun c : C₀ => (rel c).property.2 a₀)
      simpa only [R, Set.iUnion_ofPred, Set.mem_ofPred_eq] using hf
    exact hf.subset (fun x hx => hx a₀ ha₀)
  · intro a ha
    obtain ⟨c, hc, hac⟩ := hcover a ha
    refine ⟨⟨c, hc⟩, ?_⟩
    change a ∈ slice (rel ⟨c, hc⟩)
    rw [hrel]; exact hac

end SpecialTransformations.Section3.RawClosure.Tuple