import Section6.FunctionalClosure

/-! Definable closure can be checked in an elementary algebraic envelope.
This is the passage from the accepted Corollary 3.14 model to the ambient
model in the proof of Lemma 6.2. -/

open Classical FirstOrder FirstOrder.Language
set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section6

variable {L : Language} {N M : Type} [L.Structure N] [L.Structure M]

/-- Elementary embeddings introduce no new points definable over an image
base whose definable closure was already closed in the source. -/
theorem DclClosed.image {X : Set N} (hX : DclClosed (L := L) X)
    (j : N ↪ₑ[L] M) : DclClosed (L := L) (j '' X) := by
  intro b hb
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hb
  let p (s : j '' X) : X :=
    ⟨Classical.choose s.property, (Classical.choose_spec s.property).1⟩
  have hp (s : j '' X) : j (p s).val = s.val :=
    (Classical.choose_spec s.property).2
  let θ : L.BoundedFormula X 1 :=
    BoundedFormula.relabel (Sum.map p id) φ
  have hθ (y : Fin 1 → M) : θ.Realize (j ∘ Subtype.val) y ↔ y 0 = b := by
    rw [show θ = BoundedFormula.relabel (Sum.map p id) φ from rfl,
      BoundedFormula.realize_relabel]
    have he : Sum.elim (j ∘ (Subtype.val : X → N)) (y ∘ Fin.castAdd 0) ∘
        Sum.map p id = Sum.elim (Subtype.val : (j '' X) → M) y := by
      funext i
      cases i with
      | inl s => exact hp s
      | inr i => rfl
    rw [he]
    have hempty : y ∘ (Fin.natAdd 1 : Fin 0 → Fin (1 + 0)) =
        (default : Fin 0 → M) := Subsingleton.elim _ _
    rw [hempty]
    change φ.Realize (Sum.elim Subtype.val y) ↔ y 0 = b
    exact (Set.ext_iff.mp hφ y).symm
  have hexM : θ.exs.Realize (j ∘ (Subtype.val : X → N)) :=
    BoundedFormula.realize_exs.mpr ⟨fun _ => b, (hθ _).mpr rfl⟩
  have hexN := (j.map_formula θ.exs (Subtype.val : X → N)).mp hexM
  obtain ⟨a, ha⟩ := BoundedFormula.realize_exs.mp hexN
  have hab : j (a 0) = b := (hθ (j ∘ a)).mp
    ((j.map_boundedFormula θ (Subtype.val : X → N) a).mpr ha)
  have hsingle : X.Definable₁ L {a 0} := by
    rw [Set.Definable₁, Set.definable_iff_exists_formula_sum]
    refine ⟨θ.toFormula, ?_⟩
    ext x
    change x 0 = a 0 ↔ θ.toFormula.Realize (Sum.elim Subtype.val x)
    rw [BoundedFormula.realize_toFormula]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    change x 0 = a 0 ↔ θ.Realize Subtype.val x
    rw [← j.map_boundedFormula θ (Subtype.val : X → N) x, hθ, ← hab]
    exact j.injective.eq_iff.symm
  exact ⟨a 0, hX _ hsingle, hab⟩

theorem FunctionallyClosed.image {X : Set N}
    (hX : FunctionallyClosed (L := L) X) (j : N ↪ₑ[L] M) :
    FunctionallyClosed (L := L) (j '' X) :=
  functionallyClosed_of_dclClosed ((dclClosed_of_functionallyClosed hX).image j)

end SpecialTransformations.Section6
