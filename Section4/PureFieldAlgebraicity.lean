module

public import ProvedACFExtension
public import Mathlib.FieldTheory.AlgebraicClosure
public import Section4.ResidueFieldFunctions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

private theorem bounded_formula_of_definable {L : Language} {K : Type} [L.Structure K]
    {S : Set K} {n : ℕ} {A : Set (Fin n → K)} (hA : S.Definable L A) :
    ∃ φ : L.BoundedFormula S n, ∀ x, φ.Realize Subtype.val x ↔ x ∈ A := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hA
  refine ⟨BoundedFormula.relabel id φ, ?_⟩
  intro x
  rw [BoundedFormula.realize_relabel]
  have hv : Sum.elim (Subtype.val : S → K) (x ∘ Fin.castAdd 0) ∘ id =
      Sum.elim (Subtype.val : S → K) x := by
    funext u
    cases u <;> rfl
  have hx : (x ∘ Fin.natAdd n : Fin 0 → K) = default := Subsingleton.elim _ _
  rw [hv, hx]
  change φ.Realize (Sum.elim (Subtype.val : S → K) x) ↔ x ∈ A
  exact (Iff.of_eq (congrArg (fun U => x ∈ U) hφ)).symm

variable {K : Type} [Field K] [IsAlgClosed K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- A finite set definable over a subfield in pure ACF contains only
field-algebraic elements. Reuse the released ACF QE and its actual
finite/cofinite root-set theorem, rather than assume this standard fact. -/
theorem finite_field_definable_isAlgebraic (E : Subfield K) (D : Set K)
    (hD : (E : Set K).Definable₁ Language.ring D) (hfin : D.Finite) :
    ∀ x ∈ D, IsAlgebraic E x := by
  let F := algebraicClosure E K
  letI : IsAlgClosed F := IsAlgClosure.isAlgClosed E
  have hEF : (E : Set K) ⊆ (F : Set K) := by
    intro x hx
    exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨x, hx⟩ : E))
  have hDF : (F : Set K).Definable₁ Language.ring D := hD.mono hEF
  let ρ : F →+* K :=
    { toFun := fun a => a.val
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨φ, hφ⟩ := bounded_formula_of_definable hDF
  obtain ⟨ψ, hq, heq⟩ := ProvedACFExtension.fullQE F 1 φ
  have hset : {x : K | ψ.Realize (fun a : F => a.val) (fun _ => x)} = D := by
    ext x
    have h := heq K inferInstance (fun a : F => a.val) (fun _ => x)
    have h' := hφ (fun _ => x)
    change φ.Realize (fun a : F => a.val) (fun _ => x) ↔ x ∈ D at h'
    exact h.symm.trans h'
  have hgood := ACFValidation.good_solSet (f := ρ) ψ hq
  change ACFValidation.Good ρ {x : K | ψ.Realize (fun a : F => a.val) (fun _ => x)} at hgood
  rw [hset] at hgood
  rcases hgood with ⟨_, hsub⟩ | ⟨hcompl, _⟩
  · intro x hx
    obtain ⟨a, ha⟩ := hsub hx
    rw [← ha]
    exact mem_algebraicClosure_iff.mp a.property
  · have hall : (Set.univ : Set K).Finite := by
      rw [← Set.union_compl_self D]
      exact hfin.union hcompl
    exact (Set.infinite_univ hall).elim

end SpecialTransformations.Section4.ResiduePurity

end
