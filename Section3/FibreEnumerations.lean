module

public import Section3.TuplePromotion
public import Section3.Counting

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

/-- Complete injective enumeration of one fibre of a definable relation. -/
def Enumerates (R : Set ((Fin n → M) × M)) (k : ℕ)
    (t : Fin n → M) (c : Fin k → M) : Prop :=
  Function.Injective c ∧ (∀ i, (t, c i) ∈ R) ∧
    ∀ b, (t, b) ∈ R → ∃ i, c i = b

theorem enumeration_definable (S : Set M) (R : Set ((Fin n → M) × M))
    (hR : RelationDefinable S R) (k : ℕ) :
    S.Definable LRV {z : Fin n ⊕ Fin k → M |
      Enumerates R k (z ∘ Sum.inl) (z ∘ Sum.inr)} := by
  let ι := Fin n ⊕ Fin k
  have hmem (i : Fin k) : S.Definable LRV
      {z : ι → M | (z ∘ Sum.inl, z (.inr i)) ∈ R} :=
    hR.preimage_comp (Sum.map id (fun _ : Fin 1 => i))
  have hne (p : Fin k × Fin k) : S.Definable LRV
      {z : ι → M | p.1 = p.2 ∨ z (.inr p.1) ≠ z (.inr p.2)} := by
    by_cases hp : p.1 = p.2
    · simpa [hp] using Set.definable_univ S LRV (α := ι)
    · simpa only [hp, false_or, Set.compl_ofPred] using
        (definable_equal_coordinates S (.inr p.1 : ι) (.inr p.2)).compl
  have hrel : S.Definable LRV {z : ι ⊕ Fin 1 → M |
      (z ∘ Sum.inl ∘ Sum.inl, z (.inr 0)) ∈ R} :=
    hR.preimage_comp (Sum.elim (fun i : Fin n => (Sum.inl (Sum.inl i) : ι ⊕ Fin 1))
      (Sum.inr : Fin 1 → ι ⊕ Fin 1))
  have heq (i : Fin k) : S.Definable LRV {z : ι ⊕ Fin 1 → M |
      z (.inl (.inr i)) = z (.inr 0)} :=
    definable_equal_coordinates S (.inl (.inr i) : ι ⊕ Fin 1) (.inr 0)
  have hcov := (hrel.compl.union (Set.definable_iUnion_of_finite heq)).forall_of_finite
  have hfull := ((Set.definable_iInter_of_finite hne).inter
    (Set.definable_iInter_of_finite hmem)).inter hcov
  convert hfull using 1
  ext z
  simp only [Enumerates, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_iUnion, Set.mem_compl_iff, Set.mem_union, Function.comp_apply,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hinj, hmem, hsurj⟩
    refine ⟨⟨fun p => or_iff_not_imp_left.mpr (fun hp => hinj.ne hp), hmem⟩, ?_⟩
    intro b
    by_cases hb : (z ∘ Sum.inl, b 0) ∈ R
    · exact Or.inr (hsurj (b 0) hb)
    · exact Or.inl hb
  · rintro ⟨⟨hinj, hmem⟩, hsurj⟩
    refine ⟨?_, hmem, ?_⟩
    · intro i j hij
      exact (hinj (i, j)).resolve_right (not_not.mpr hij)
    · intro b hb
      exact (hsurj ![b]).resolve_left (not_not.mpr hb)

end SpecialTransformations.Section3.RawClosure.Tuple
