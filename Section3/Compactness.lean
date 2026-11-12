module

public import Section3.ModelContext

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M]

theorem Saturated.finite_subcover {κ : Cardinal} (hs : Saturated M κ)
    {α : Type} (v : α → M) (hsmall : Cardinal.mk α < κ) {n : ℕ}
    (θ : LRV.BoundedFormula α n) (C : Set (LRV.BoundedFormula α n))
    (hcover : ∀ x, θ.Realize v x → ∃ φ ∈ C, φ.Realize v x) :
    ∃ s : Finset (LRV.BoundedFormula α n), (∀ φ ∈ s, φ ∈ C) ∧
      ∀ x, θ.Realize v x → ∃ φ ∈ s, φ.Realize v x := by
  classical
  let p : Set (LRV.BoundedFormula α n) := insert θ (BoundedFormula.not '' C)
  have hp : ¬ ∃ x : Fin n → M, ∀ φ ∈ p, φ.Realize v x := by
    rintro ⟨x, hx⟩
    obtain ⟨φ, hφC, hφx⟩ := hcover x (hx θ (Set.mem_insert θ _))
    exact (BoundedFormula.realize_not.mp
      (hx φ.not (Set.mem_insert_of_mem _ ⟨φ, hφC, rfl⟩))) hφx
  obtain ⟨l, hl, hbad⟩ := hs.finite_inconsistent v hsmall p hp
  let good (φ : LRV.BoundedFormula α n) : Prop := ∃ ψ ∈ C, ψ.not = φ
  let pick (φ : LRV.BoundedFormula α n) : LRV.BoundedFormula α n :=
    if h : good φ then Classical.choose h else ⊥
  let s := (l.toFinset.filter good).image pick
  have hsC : ∀ ψ ∈ s, ψ ∈ C := by
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hψ
    have hg := (Finset.mem_filter.mp hφ).2
    exact (show pick φ ∈ C from by
      simp only [pick, dif_pos hg]; exact (Classical.choose_spec hg).1)
  refine ⟨s, hsC, ?_⟩
  intro x hθ
  by_contra hn
  apply hbad
  refine ⟨x, ?_⟩
  intro φ hφl
  rcases hl φ hφl with hφθ | hφnot
  · simpa [hφθ] using hθ
  · have hg : good φ := hφnot
    have hpick : pick φ ∈ s :=
      Finset.mem_image.mpr ⟨φ, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hφl, hg⟩, rfl⟩
    have heq : (pick φ).not = φ := by
      simp only [pick, dif_pos hg]; exact (Classical.choose_spec hg).2
    rw [← heq, BoundedFormula.realize_not]
    exact fun hreal => hn ⟨pick φ, hpick, hreal⟩

end SpecialTransformations.Section3