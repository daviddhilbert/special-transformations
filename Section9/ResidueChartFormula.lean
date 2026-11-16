module

public import Section7.FieldConstructibility

@[expose] public section

/-! Use the published ACF elimination theorem to obtain a single
quantifier-free ring formula for a residue correspondence. -/

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section9

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem exists_ringQF_defining_set {K : Type} [Field K] [IsAlgClosed K]
    (E : Subfield K) {n : ℕ} (D : Set (Fin n → K)) (hD : (E : Set K).Definable Language.ring D) :
    ∃ ψ : Language.ring.BoundedFormula E n, ψ.IsQF ∧
      ∀ x, x ∈ D ↔ ψ.Realize E.subtype x := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hD
  obtain ⟨ψ, hq, heq⟩ := ProvedACFExtension.fullQE E n (BoundedFormula.relabel id φ)
  refine ⟨ψ, hq, fun x => ?_⟩
  apply Iff.trans ?_ (heq K inferInstance E.subtype x)
  rw [BoundedFormula.realize_relabel]
  have hv : Sum.elim (E.subtype : E → K) (x ∘ Fin.castAdd 0) ∘ id =
      Sum.elim (E.subtype : E → K) x := by
    funext u
    cases u <;> rfl
  have hx : (x ∘ Fin.natAdd n : Fin 0 → K) = default := Subsingleton.elim _ _
  rw [hv, hx]
  change x ∈ D ↔ φ.Realize (Sum.elim Subtype.val x)
  exact Iff.of_eq (congrArg (fun U => x ∈ U) hφ)

end SpecialTransformations.Section9
