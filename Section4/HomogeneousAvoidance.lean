import Section4.NonalgebraicTypes
import Section3.SmallFiniteParameters

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

def singletonAssignment (S : Set M) (a : M) : S ⊕ Unit → M :=
  Sum.elim Subtype.val (fun _ => a)

theorem singletonAssignment_formula_definable (S : Set M) {n : ℕ}
    (φ : LRV.BoundedFormula (S ⊕ Unit) n) (p : Fin n → S ⊕ Unit) :
    S.Definable₁ LRV {x | φ.Realize (singletonAssignment S x)
      (singletonAssignment S x ∘ p)} := by
  let f : S ⊕ Unit → S ⊕ Fin 1 := Sum.elim Sum.inl (fun _ => Sum.inr 0)
  let g : (S ⊕ Unit) ⊕ Fin n → S ⊕ Fin 1 := Sum.elim f (fun i => f (p i))
  rw [Set.Definable₁, Set.definable_iff_exists_formula_sum]
  refine ⟨φ.toFormula.relabel g, ?_⟩
  ext z
  simp only [Set.mem_setOf_eq, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  have hf (i : S ⊕ Unit) :
      Sum.elim (Subtype.val : S → M) z (f i) = singletonAssignment S (z 0) i := by
    cases i <;> rfl
  have hleft : (Sum.elim (Subtype.val : S → M) z ∘ g) ∘ Sum.inl =
      singletonAssignment S (z 0) := funext hf
  have hright : (Sum.elim (Subtype.val : S → M) z ∘ g) ∘ Sum.inr =
      singletonAssignment S (z 0) ∘ p := funext (fun i => hf (p i))
  rw [hleft, hright]

theorem SameUnaryType.partialElementary {S : Set M} {a b : M}
    (h : SameUnaryType S a b) :
    PartialElementary (singletonAssignment S a) (singletonAssignment S b) := by
  intro n φ p
  exact h _ (singletonAssignment_formula_definable S φ p)

/-- Genuine saturation and genuine strong homogeneity move a nonalgebraic
element outside the algebraic closure of a larger small base, while fixing
the original base pointwise. -/
theorem exists_automorphism_avoiding_algebraic_closure
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) {S T : Set M} (hST : S ⊆ T)
    (hS : Cardinal.mk S < κ) (hT : Cardinal.mk T < κ) (a : M)
    (ha : ¬ RawClosure.AlgebraicOver S a) :
    ∃ e : M ≃[LRV] M, (∀ x ∈ S, e x = x) ∧ ¬ RawClosure.AlgebraicOver T (e a) := by
  obtain ⟨b, hb, hbn⟩ := nonalgebraic_type_extension hs hST hT a ha
  have hsize : Cardinal.mk (S ⊕ Unit) < κ := by
    simpa only [Cardinal.mk_sum, Cardinal.mk_unit, Cardinal.lift_id] using
      Cardinal.add_lt_of_lt hκ hS (Cardinal.one_lt_aleph0.trans_le hκ)
  obtain ⟨e, he⟩ := hh (S ⊕ Unit) (singletonAssignment S a)
    (singletonAssignment S b) hsize hb.partialElementary
  refine ⟨e, ?_, ?_⟩
  · intro x hx
    exact he (.inl ⟨x, hx⟩)
  · have hab : e a = b := he (.inr Unit.unit)
    rwa [hab]

end SpecialTransformations.Section4

end
