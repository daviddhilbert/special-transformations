import Section9.CoordinateDerivations
import Mathlib.FieldTheory.Perfect

/-! Independent input coordinates and algebraic output coordinates
give a separable graph field with coordinate derivations. -/

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section9

universe u
variable {K : Type u} [Field K] {n m : ℕ}

theorem exists_graph_coordinate_derivations [CharZero K]
    (E : Subfield K) (x : Fin n → K) (y : Fin m → K)
    (hx : AlgebraicIndependent E x)
    (hy : ∀ i, IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (y i)) :
    ∃ (L : Type u) (fL : Field L), letI := fL
      ∃ aL : Algebra E L, letI := aL
        ∃ (f : L →ₐ[E] K) (X : Fin n → L) (Y : Fin m → L) (D : Fin n → Derivation E L L),
          (∀ i, f (X i) = x i) ∧ (∀ i, f (Y i) = y i) ∧
          ∀ j i, D j (X i) = if i = j then 1 else 0 := by
  let F := IntermediateField.adjoin E (Set.range x)
  let L := IntermediateField.adjoin F (Set.range y)
  letI : Algebra E L := ((algebraMap F L).comp (algebraMap E F)).toAlgebra
  letI : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsAlgebraic F L := by
    apply IntermediateField.isAlgebraic_adjoin
    rintro z ⟨i, rfl⟩
    exact (hy i).isIntegral
  letI : Algebra.IsSeparable F L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let x₀ (i : Fin n) : F := ⟨x i, IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩
  let X (i : Fin n) : L := algebraMap F L (x₀ i)
  let Y (i : Fin m) : L := ⟨y i, IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩
  let f : L →ₐ[E] K :=
    { toRingHom := L.val.toRingHom
      commutes' := fun _ => rfl }
  choose d hd using fun j => exists_coordinate_derivation x hx j
  let d₀ (j : Fin n) : Derivation E F L := (Algebra.linearMap F L).compDer (d j)
  choose D hD using fun j => exists_derivation_extension (d₀ j)
  refine ⟨L, inferInstance, inferInstance, f, X, Y, D, fun _ => rfl, fun _ => rfl, fun j i => ?_⟩
  have he : D j (X i) = algebraMap F L (d j (x₀ i)) := hD j (x₀ i)
  have h := hd j i
  change d j (x₀ i) = if j = i then 1 else 0 at h
  rw [he, h]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

end SpecialTransformations.Section9
