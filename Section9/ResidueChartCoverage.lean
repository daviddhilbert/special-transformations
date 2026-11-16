module

public import Section4.ResiduePolynomialCover
public import Section7.TupleCoordinates

@[expose] public section

/-! A generic selector for a square residue system extends to a
chart above the complement of one proper input polynomial locus. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "k" => ModelResidue M
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem exists_residueChart_bad_input_polynomial
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def (residueParameterField B) C)
    (P : Fin n → MvPolynomial (Fin (n + n)) (residueParameterField B))
    (Q : MvPolynomial (Fin (n + n)) (residueParameterField B))
    (hgeneric : ∀ z, AlgebraicIndependent (residueParameterField B) (z ∘ productLeft n n) →
      (z ∈ C ↔ (∀ i, aeval z (P i) = 0) ∧ aeval z Q ≠ 0)) :
    ∃ D : MvPolynomial (Fin n) (residueParameterField B), D ≠ 0 ∧
      ∀ z, aeval (z ∘ productLeft n n) D ≠ 0 →
        (z ∈ C ↔ (∀ i, aeval z (P i) = 0) ∧ aeval z Q ≠ 0) := by
  let E := residueParameterField B
  let Z := {z : Fin (n + n) → k | (∀ i, aeval z (P i) = 0) ∧ aeval z Q ≠ 0}
  have hZ : Relative.Def E Z := by
    have hP (i : Fin n) : Relative.Def E {z : Fin (n + n) → k | aeval z (P i) = 0} :=
      mvPolynomial_zeroSet_definable E (P i)
    have h₁ : Relative.Def E {z : Fin (n + n) → k | ∀ i, aeval z (P i) = 0} := by
      rw [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite hP
    exact h₁.inter (mvPolynomial_zeroSet_definable E Q).compl
  let A := (C \ Z) ∪ (Z \ C)
  have hA : Relative.Def E A := (hC.inter hZ.compl).union (hZ.inter hC.compl)
  have hdep (z : Fin (n + n) → k) (hz : z ∈ A) :
      ¬ AlgebraicIndependent E (z ∘ productLeft n n) := by
    intro hInd
    have he : z ∈ C ↔ z ∈ Z := hgeneric z hInd
    rcases hz with h | h
    · exact h.2 (he.mp h.1)
    · exact h.2 (he.mpr h.1)
  obtain ⟨D, hD, hzero⟩ := exists_residue_polynomial_vanishing_on_selection
    hs B hB A hA (productLeft n n) hdep
  refine ⟨D, hD, fun z hz => ?_⟩
  have hnot : z ∉ A := fun h => hz (hzero z h)
  change z ∈ C ↔ z ∈ Z
  constructor
  · intro h
    by_contra hn
    exact hnot (Or.inl ⟨h,hn⟩)
  · intro h
    by_contra hn
    exact hnot (Or.inr ⟨h,hn⟩)

end SpecialTransformations.Section9
