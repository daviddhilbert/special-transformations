module

public import Section3.Compactness

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M]

theorem raw_definable_formula {S : Set M} {A : Set M} (hA : S.Definable₁ LRV A) :
    ∃ θ : LRV.BoundedFormula S 1, ∀ x, θ.Realize Subtype.val ![x] ↔ x ∈ A := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hA
  refine ⟨BoundedFormula.relabel id φ, ?_⟩
  intro x
  rw [BoundedFormula.realize_relabel]
  have hv : Sum.elim (Subtype.val : S → M) (![x] ∘ Fin.castAdd 0) ∘ id =
      Sum.elim (Subtype.val : S → M) ![x] := by
    funext u
    cases u with
    | inl a => rfl
    | inr i => fin_cases i; rfl
  have hx : (![x] ∘ Fin.natAdd 1 : Fin 0 → M) = default := Subsingleton.elim _ _
  rw [hv, hx]
  change φ.Realize (Sum.elim (fun a : S => (a : M)) ![x]) ↔ x ∈ A
  have he := congrArg (fun U : Set (Fin 1 → M) => ![x] ∈ U) hφ
  exact (Iff.of_eq he).symm

theorem Saturated.definable_finite_subcover {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (A : Set M) (hA : S.Definable₁ LRV A)
    (C : Set (Set M)) (hC : ∀ c ∈ C, S.Definable₁ LRV c)
    (hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c) :
    ∃ C₀ : Set (Set M), C₀.Finite ∧ C₀ ⊆ C ∧ ∀ a ∈ A, ∃ c ∈ C₀, a ∈ c := by
  classical
  obtain ⟨θ, hθ⟩ := raw_definable_formula hA
  have hcformula (c : C) := raw_definable_formula (hC c.val c.property)
  let φ : C → LRV.BoundedFormula S 1 := fun c => Classical.choose (hcformula c)
  have hφ (c : C) (x : M) : (φ c).Realize Subtype.val ![x] ↔ x ∈ c.val :=
    Classical.choose_spec (hcformula c) x
  have hcover (x : Fin 1 → M) (hx : θ.Realize Subtype.val x) :
      ∃ ψ ∈ Set.range φ, ψ.Realize Subtype.val x := by
    have he : ![x 0] = x := by funext i; fin_cases i; rfl
    obtain ⟨c, hc, hxc⟩ := hcov (x 0) ((hθ _).mp (he ▸ hx))
    exact ⟨φ ⟨c, hc⟩, Set.mem_range_self _, he ▸ (hφ ⟨c, hc⟩ _).mpr hxc⟩
  obtain ⟨s, hsC, hscov⟩ := hs.finite_subcover (Subtype.val : S → M) hsmall θ (Set.range φ) hcover
  let realizeSet (ψ : LRV.BoundedFormula S 1) : Set M := {x | ψ.Realize Subtype.val ![x]}
  let C₀ : Set (Set M) := realizeSet '' (s : Set (LRV.BoundedFormula S 1))
  refine ⟨C₀, s.finite_toSet.image realizeSet, ?_, ?_⟩
  · rintro c ⟨ψ, hψs, rfl⟩
    obtain ⟨d, rfl⟩ := hsC ψ hψs
    have he : realizeSet (φ d) = d.val := by ext x; exact hφ d x
    rw [he]
    exact d.property
  · intro a ha
    obtain ⟨ψ, hψs, hψa⟩ := hscov ![a] ((hθ a).mpr ha)
    exact ⟨realizeSet ψ, ⟨ψ, hψs, rfl⟩, hψa⟩

end SpecialTransformations.Section3