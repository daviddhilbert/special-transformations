import Section3.RawAlgebraicity
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

def RelationDefinable (S : Set M) (R : Set ((Fin n → M) × M)) : Prop :=
  S.Definable LRV {x : Fin n ⊕ Fin 1 → M | (x ∘ Sum.inl, x (Sum.inr 0)) ∈ R}

theorem promote_tuple (S : Set M) (a : Fin n → M) (b : M)
    (hb : AlgebraicOver (S ∪ Set.range a) b) :
    ∃ R : Set ((Fin n → M) × M), RelationDefinable S R ∧ (a, b) ∈ R ∧
      {x | (a, x) ∈ R}.Finite := by
  classical
  obtain ⟨t, ht, hf, hb⟩ := hb
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp ht
  let index (u : ↥(S ∪ Set.range a)) (hu : u.val ∉ S) : Fin n :=
    Classical.choose ((u.property : u.val ∈ S ∨ u.val ∈ Set.range a).resolve_left hu)
  have hindex (u : ↥(S ∪ Set.range a)) (hu : u.val ∉ S) : a (index u hu) = u.val :=
    Classical.choose_spec ((u.property : u.val ∈ S ∨ u.val ∈ Set.range a).resolve_left hu)
  let g : (↥(S ∪ Set.range a) ⊕ Fin 1) → S ⊕ (Fin n ⊕ Fin 1) :=
    Sum.elim (fun u => if hu : u.val ∈ S then Sum.inl ⟨u.val, hu⟩
      else Sum.inr (Sum.inl (index u hu))) (fun i => Sum.inr (Sum.inr i))
  let ψ : LRV.Formula (S ⊕ (Fin n ⊕ Fin 1)) := φ.relabel g
  let R : Set ((Fin n → M) × M) :=
    {p | ψ.Realize (Sum.elim Subtype.val (Sum.elim p.1 ![p.2]))}
  have hreal (x : M) : (a, x) ∈ R ↔ x ∈ t := by
    change (φ.relabel g).Realize (Sum.elim Subtype.val (Sum.elim a ![x])) ↔ x ∈ t
    rw [Formula.realize_relabel]
    have he : Sum.elim (Subtype.val : S → M) (Sum.elim a ![x]) ∘ g =
        Sum.elim (Subtype.val : ↥(S ∪ Set.range a) → M) ![x] := by
      funext u
      cases u with
      | inl u =>
        by_cases hu : u.val ∈ S
        · simp [g, hu]
        · simp only [Function.comp_apply, g, Sum.elim_inl, dif_neg hu, Sum.elim_inr]
          exact hindex u hu
      | inr i => rfl
    rw [he]
    have hm := congrArg (fun U : Set (Fin 1 → M) => ![x] ∈ U) hφ
    exact (Iff.of_eq hm).symm
  refine ⟨R, ?_, (hreal b).mpr hb, ?_⟩
  · rw [RelationDefinable, Set.definable_iff_exists_formula_sum]
    refine ⟨ψ, ?_⟩
    ext x
    have hx : Sum.elim (x ∘ Sum.inl) ![x (Sum.inr 0)] = x := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => fin_cases i; rfl
    simp only [R, Set.mem_ofPred_eq, hx]
  · have he : {x | (a, x) ∈ R} = t := by ext x; exact hreal x
    rwa [he]

end SpecialTransformations.Section3.RawClosure.Tuple