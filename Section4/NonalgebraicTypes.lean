module

public import Section3.DefinableCompactness
public import Section3.RawAlgebraicity
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

/-- Equality of unary types over the actual parameter set, expressed using
all definable unary sets. -/
def SameUnaryType (S : Set M) (a b : M) : Prop :=
  ∀ D : Set M, S.Definable₁ LRV D → (a ∈ D ↔ b ∈ D)

/-- Realize an arbitrary family of unary definable sets with the finite
intersection property. This is derived from genuine saturation. -/
theorem realize_unary_definable_fip {κ : Cardinal} (hs : Saturated M κ)
    (T : Set M) (hsmall : Cardinal.mk T < κ) (C : Set (Set M))
    (hC : ∀ D ∈ C, T.Definable₁ LRV D)
    (hFIP : ∀ (ι : Type) [Finite ι] (D : ι → C), ∃ x : M, ∀ i, x ∈ (D i).val) :
    ∃ x : M, ∀ D ∈ C, x ∈ D := by
  have hformula (D : C) := raw_definable_formula (hC D.val D.property)
  let φ : C → LRV.BoundedFormula T 1 := fun D => Classical.choose (hformula D)
  have hφ (D : C) (x : M) : (φ D).Realize Subtype.val ![x] ↔ x ∈ D.val :=
    Classical.choose_spec (hformula D) x
  have hp : FinitelySatisfiable (Subtype.val : T → M) (Set.range φ) := by
    intro l hl
    have hchoice (i : Fin l.length) : ∃ D : C, φ D = l.get i :=
      hl (l.get i) (List.get_mem l i)
    choose D hD using hchoice
    obtain ⟨x, hx⟩ := hFIP (Fin l.length) D
    refine ⟨![x], ?_⟩
    intro ψ hψ
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hψ
    rw [← hD i]
    exact (hφ (D i) x).mpr (hx i)
  obtain ⟨z, hz⟩ := hs T Subtype.val hsmall (Set.range φ) hp
  refine ⟨z 0, ?_⟩
  intro D hD
  have he : ![z 0] = z := by funext i; fin_cases i; rfl
  apply (hφ ⟨D, hD⟩ (z 0)).mp
  rw [he]
  exact hz (φ ⟨D, hD⟩) ⟨⟨D, hD⟩, rfl⟩

/-- A nonalgebraic unary type extends nonalgebraically over a larger small
parameter set. Finite satisfiability uses an infinite original-base type
neighbourhood minus a finite union of finite sets over the larger base. -/
theorem nonalgebraic_type_extension {κ : Cardinal} (hs : Saturated M κ)
    {S T : Set M} (hST : S ⊆ T) (hsmall : Cardinal.mk T < κ) (a : M)
    (ha : ¬ RawClosure.AlgebraicOver S a) :
    ∃ b : M, SameUnaryType S a b ∧ ¬ RawClosure.AlgebraicOver T b := by
  let C : Set (Set M) := {D | ∃ U V : Set M,
    S.Definable₁ LRV U ∧ a ∈ U ∧ T.Definable₁ LRV V ∧ V.Finite ∧ D = U \ V}
  have hC : ∀ D ∈ C, T.Definable₁ LRV D := by
    rintro D ⟨U, V, hU, _, hV, _, rfl⟩
    exact (hU.mono hST).sdiff hV
  have hFIP : ∀ (ι : Type) [Finite ι] (D : ι → C), ∃ x : M, ∀ i, x ∈ (D i).val := by
    intro ι _ D
    have hdata (i : ι) := (D i).property
    choose U V hU haU hV hVfin he using hdata
    let W : Set M := {x | ∀ i, x ∈ U i}
    have hW : S.Definable₁ LRV W := by
      change S.Definable LRV {z : Fin 1 → M | ∀ i, z 0 ∈ U i}
      convert Set.definable_iInter_of_finite hU using 1
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    have hWinf : W.Infinite := by
      intro hfinite
      exact ha ⟨W, hW, hfinite, haU⟩
    have hVunion : (⋃ i, V i).Finite := Set.finite_iUnion hVfin
    obtain ⟨x, hxW, hxV⟩ := (hWinf.diff hVunion).nonempty
    refine ⟨x, ?_⟩
    intro i
    rw [he i]
    exact ⟨hxW i, fun hi => hxV (Set.mem_iUnion.mpr ⟨i, hi⟩)⟩
  obtain ⟨b, hb⟩ := realize_unary_definable_fip hs T hsmall C hC hFIP
  have hneighbourhood (U : Set M) (hU : S.Definable₁ LRV U) (haU : a ∈ U) : b ∈ U := by
    have h := hb (U \ ∅) ⟨U, ∅, hU, haU, Set.definable_empty,
      Set.finite_empty, rfl⟩
    exact h.1
  refine ⟨b, ?_, ?_⟩
  · intro U hU
    constructor
    · exact hneighbourhood U hU
    · intro hbU
      by_contra haU
      exact (hneighbourhood Uᶜ hU.compl haU) hbU
  · rintro ⟨V, hV, hVfin, hbV⟩
    have h := hb (Set.univ \ V) ⟨Set.univ, V,
      Set.definable_univ (A := S) (L := LRV) (α := Fin 1),
      Set.mem_univ a, hV, hVfin, rfl⟩
    exact h.2 hbV

end SpecialTransformations.Section4

end
