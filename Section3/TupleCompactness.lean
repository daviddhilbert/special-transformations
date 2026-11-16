module

public import Section3.DefinableCompactness

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M]

theorem raw_definable_formula_tuple {S : Set M} {n : ℕ} {A : Set (Fin n → M)}
    (hA : S.Definable LRV A) :
    ∃ θ : LRV.BoundedFormula S n, ∀ x, θ.Realize Subtype.val x ↔ x ∈ A := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hA
  refine ⟨BoundedFormula.relabel id φ, ?_⟩
  intro x
  rw [BoundedFormula.realize_relabel]
  have hv : Sum.elim (Subtype.val : S → M) (x ∘ Fin.castAdd 0) ∘ id =
      Sum.elim (Subtype.val : S → M) x := by
    funext u
    cases u with
    | inl a => rfl
    | inr i => rfl
  have hx : (x ∘ Fin.natAdd n : Fin 0 → M) = default := Subsingleton.elim _ _
  rw [hv, hx]
  change φ.Realize (Sum.elim (Subtype.val : S → M) x) ↔ x ∈ A
  have he := congrArg (fun U => x ∈ U) hφ
  exact (Iff.of_eq he).symm

theorem Saturated.definable_finite_subcover_tuple {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {n : ℕ}
    (A : Set (Fin n → M)) (hA : S.Definable LRV A)
    (C : Set (Set (Fin n → M))) (hC : ∀ c ∈ C, S.Definable LRV c)
    (hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c) :
    ∃ C₀ : Set (Set (Fin n → M)), C₀.Finite ∧ C₀ ⊆ C ∧
      ∀ a ∈ A, ∃ c ∈ C₀, a ∈ c := by
  classical
  obtain ⟨θ, hθ⟩ := raw_definable_formula_tuple hA
  have hcformula (c : C) := raw_definable_formula_tuple (hC c.val c.property)
  let φ : C → LRV.BoundedFormula S n := fun c => Classical.choose (hcformula c)
  have hφ (c : C) (x : Fin n → M) : (φ c).Realize Subtype.val x ↔ x ∈ c.val :=
    Classical.choose_spec (hcformula c) x
  have hcover (x : Fin n → M) (hx : θ.Realize Subtype.val x) :
      ∃ ψ ∈ Set.range φ, ψ.Realize Subtype.val x := by
    obtain ⟨c, hc, hxc⟩ := hcov x ((hθ _).mp hx)
    exact ⟨φ ⟨c, hc⟩, Set.mem_range_self _, (hφ ⟨c, hc⟩ _).mpr hxc⟩
  obtain ⟨s, hsC, hscov⟩ := hs.finite_subcover (Subtype.val : S → M) hsmall θ (Set.range φ) hcover
  let realizeSet (ψ : LRV.BoundedFormula S n) : Set (Fin n → M) := {x | ψ.Realize Subtype.val x}
  let C₀ : Set (Set (Fin n → M)) := realizeSet '' (s : Set (LRV.BoundedFormula S n))
  refine ⟨C₀, s.finite_toSet.image realizeSet, ?_, ?_⟩
  · rintro c ⟨ψ, hψs, rfl⟩
    obtain ⟨d, rfl⟩ := hsC ψ hψs
    have he : realizeSet (φ d) = d.val := by ext x; exact hφ d x
    rw [he]; exact d.property
  · intro a ha
    obtain ⟨ψ, hψs, hψa⟩ := hscov a ((hθ a).mpr ha)
    exact ⟨realizeSet ψ, ⟨ψ, hψs, rfl⟩, hψa⟩

end SpecialTransformations.Section3