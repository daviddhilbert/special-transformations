module

public import Section3.Counting

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure
variable {M : Type} [LRV.Structure M]

def AlgebraicOver (S : Set M) (b : M) : Prop :=
  ∃ t : Set M, S.Definable₁ LRV t ∧ t.Finite ∧ b ∈ t

theorem promote_parameter (S : Set M) (a b : M) (hb : AlgebraicOver (insert a S) b) :
    ∃ R : Set (M × M), S.Definable₂ LRV R ∧ (a, b) ∈ R ∧ {x | (a, x) ∈ R}.Finite := by
  classical
  obtain ⟨t, ht, hfin, hb⟩ := hb
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp ht
  let g : (↥(insert a S) ⊕ Fin 1) → (S ⊕ Fin 2) :=
    Sum.elim (fun u => if hu : u.val ∈ S then Sum.inl ⟨u.val, hu⟩ else Sum.inr 0)
      (fun _ => Sum.inr 1)
  let ψ : LRV.Formula (S ⊕ Fin 2) := φ.relabel g
  let R : Set (M × M) := {p | ψ.Realize (Sum.elim Subtype.val ![p.1, p.2])}
  have hreal (x : M) : (a, x) ∈ R ↔ x ∈ t := by
    change (φ.relabel g).Realize (Sum.elim Subtype.val ![a, x]) ↔ x ∈ t
    rw [Formula.realize_relabel]
    have he : Sum.elim (fun u : S => (u : M)) ![a, x] ∘ g =
        Sum.elim (fun u : ↥(insert a S) => (u : M)) (fun _ : Fin 1 => x) := by
      funext u
      cases u with
      | inl u =>
        by_cases hu : u.val ∈ S
        · simp [g, hu]
        · have hua : u.val = a := (Set.mem_insert_iff.mp u.property).resolve_right hu
          simp only [Function.comp_apply, g, Sum.elim_inl, dif_neg hu,
            Sum.elim_inr, Matrix.cons_val_zero]
          exact hua.symm
      | inr i => rfl
    rw [he]
    have hm := congrArg (fun U : Set (Fin 1 → M) => (fun _ => x) ∈ U) hφ
    exact (Iff.of_eq hm).symm
  refine ⟨R, ?_, (hreal b).mpr hb, ?_⟩
  · rw [Set.Definable₂, Set.definable_iff_exists_formula_sum]
    refine ⟨ψ, ?_⟩
    ext x
    have hx : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
    simp only [R, Set.mem_ofPred_eq, hx]
  · have he : {x | (a, x) ∈ R} = t := by ext x; exact hreal x
    rwa [he]

end SpecialTransformations.Section3.RawClosure