module

public import Section3.TuplePromotion

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

def HasMore (R : Set ((Fin n → M) × M)) (k : ℕ) : Set (Fin n → M) :=
  {a | ∃ x : Fin (k + 1) → M, Function.Injective x ∧ ∀ i, (a, x i) ∈ R}

theorem hasMore_definable (S : Set M) (R : Set ((Fin n → M) × M))
    (hR : RelationDefinable S R) (k : ℕ) : S.Definable LRV (HasMore R k) := by
  classical
  let ι := Fin n ⊕ Fin (k + 1)
  have hrel (i : Fin (k + 1)) : S.Definable LRV
      {x : ι → M | (x ∘ Sum.inl, x (.inr i)) ∈ R} := by
    exact hR.preimage_comp (Sum.map id (fun _ : Fin 1 => i))
  have hne (p : Fin (k + 1) × Fin (k + 1)) : S.Definable LRV
      {x : ι → M | p.1 = p.2 ∨ x (.inr p.1) ≠ x (.inr p.2)} := by
    by_cases h : p.1 = p.2
    · simpa [h] using (Set.definable_univ S LRV (α := ι))
    · simpa [h, Set.compl_ofPred] using
        (definable_equal_coordinates S (.inr p.1 : ι) (.inr p.2)).compl
  have hfull := ((Set.definable_iInter_of_finite hne).inter
    (Set.definable_iInter_of_finite hrel)).exists_of_finite
  convert hfull using 1
  ext x
  simp only [HasMore, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff,
    Sum.elim_inl, Sum.elim_inr, Sum.elim_comp_inl]
  constructor
  · rintro ⟨u, hu, hRu⟩
    exact ⟨u, fun p => or_iff_not_imp_left.mpr (fun hp => hu.ne hp), hRu⟩
  · rintro ⟨u, hu, hRu⟩
    refine ⟨u, ?_, hRu⟩
    intro i j hij
    exact (hu (i, j)).resolve_right (by simpa using hij)

def GoodRelation (S : Set M) := {R : Set ((Fin n → M) × M) //
  RelationDefinable S R ∧ ∀ a : Fin n → M, {x | (a, x) ∈ R}.Finite}

theorem good_relation_of_algebraic (S : Set M) (a : Fin n → M) (b : M)
    (hb : AlgebraicOver (S ∪ Set.range a) b) :
    ∃ R : GoodRelation (n := n) S, (a, b) ∈ R.val := by
  classical
  obtain ⟨R, hR, hab, hf⟩ := promote_tuple S a b hb
  let k := ({x | (a, x) ∈ R} : Set M).ncard
  let Q : Set ((Fin n → M) × M) := {p | p ∈ R ∧ p.1 ∉ HasMore R k}
  have hnot := (hasMore_definable S R hR k).compl
  have hQ : RelationDefinable S Q := by
    have hp := hnot.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin 1)
    exact hR.inter hp
  have ha : a ∉ HasMore R k := (no_inj_iff_finite_ncard_le).mpr ⟨hf, le_rfl⟩
  refine ⟨⟨Q, hQ, ?_⟩, hab, ha⟩
  intro c
  by_cases hc : c ∈ HasMore R k
  · have he : {x | (c, x) ∈ Q} = ∅ := by ext x; simp [Q, hc]
    rw [he]; exact Set.finite_empty
  · have hcf := (no_inj_iff_finite_ncard_le (s := {x | (c, x) ∈ R}) (k := k)).mp hc
    exact hcf.1.subset (fun x hx => hx.1)

theorem slice_definable (S : Set M) (b : M) (R : GoodRelation (n := n) S) :
    (insert b S).Definable LRV {a | (a, b) ∈ R.val} := by
  have hR : RelationDefinable (insert b S) R.val :=
    R.property.1.mono (Set.subset_insert b S)
  let F (x : Fin n → M) : Fin n ⊕ Fin 1 → M := Sum.elim x (fun _ => b)
  have hF : (insert b S).DefinableMap LRV F := by
    intro i
    cases i with
    | inl j => exact Set.DefinableFun.proj LRV
    | inr j => exact LRV.definableFun_const (Fin n) (Set.mem_insert b S)
  exact hR.preimage_map hF

end SpecialTransformations.Section3.RawClosure.Tuple