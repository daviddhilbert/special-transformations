module

public import Section9.CoordinateDerivations
public import Mathlib.FieldTheory.Perfect

@[expose] public section

/-! Coordinate derivations extend to an algebraic graph field in
characteristic zero and preserve its rational function subfield. -/

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section9

variable {E K : Type*} [Field E] [Field K] [Algebra E K] {n : ℕ}

theorem exists_algebraic_coordinate_derivation [CharZero K]
    (x : Fin n → K) (hx : AlgebraicIndependent E x) (j : Fin n)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin E (Set.range x)) K) :
    ∃ D : Derivation E K K, (∀ i, D (x i) = if j = i then 1 else 0) ∧
      ∀ z ∈ IntermediateField.adjoin E (Set.range x), D z ∈ IntermediateField.adjoin E (Set.range x) := by
  let F := IntermediateField.adjoin E (Set.range x)
  letI : Algebra.IsAlgebraic F K := halg
  letI : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨d, hd⟩ := exists_coordinate_derivation x hx j
  let d₀ : Derivation E F K := (Algebra.linearMap F K).compDer d
  obtain ⟨D, hD⟩ := exists_derivation_extension d₀
  refine ⟨D, fun i => ?_, fun z hz => ?_⟩
  · let a : F := ⟨x i, IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩
    change D (algebraMap F K a) = _
    rw [hD a]
    change algebraMap F K (d a) = _
    rw [show d a = if j = i then 1 else 0 from hd i]
    split <;> simp
  · let a : F := ⟨z, hz⟩
    change D (algebraMap F K a) ∈ F
    rw [hD a]
    exact (d a).property

end SpecialTransformations.Section9
