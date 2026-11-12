module

public import Section9.ResidueJacobianChain
public import Section9.GraphCoordinateDerivations

@[expose] public section

/-! A single graph field gives compatible derivatives for the three
pairs at a residue-generic point. The middle point is kept fixed
throughout this comparison. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "k" => ModelResidue M
local notation "V" => Fin n → k

theorem residueJacobianMap_comp_of_independent [IsAlgClosed k] [CharZero k]
    (E : Subfield k) [IsAlgClosed E] (x y z : V)
    (hx : AlgebraicIndependent E x)
    (hy : ∀ i, IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (y i))
    (hz : ∀ i, IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (z i))
    (A B C : Set (Fin (n + n) → k))
    (hA : Relative.Def E A) (hB : Relative.Def E B) (hC : Relative.Def E C)
    (hxy : productTuple x y ∈ A) (hyz : productTuple y z ∈ B) (hxz : productTuple x z ∈ C)
    (L₁ L₂ L₃ : V →ₗ[k] V)
    (hL₁ : IsResidueJacobianMap (M := M) A (productTuple x y) L₁)
    (hL₂ : IsResidueJacobianMap (M := M) B (productTuple y z) L₂)
    (hL₃ : IsResidueJacobianMap (M := M) C (productTuple x z) L₃) :
    L₃ = L₂.comp L₁ := by
  have hAlg (i : Fin (n + n)) :
      IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (productTuple y z i) := by
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      change IsAlgebraic _ (productTuple y z (productLeft n n j))
      rw [productTuple_left]
      exact hy j
    | inr j =>
      change IsAlgebraic _ (productTuple y z (productRight n n j))
      rw [productTuple_right]
      exact hz j
  obtain ⟨K, fK, aK, f, X, YZ, D, hX, hYZ, hD⟩ :=
    exists_graph_coordinate_derivations E x (productTuple y z) hx hAlg
  letI := fK
  letI := aK
  let Y := YZ ∘ productLeft n n
  let Z := YZ ∘ productRight n n
  have h₁ : f ∘ X = x := funext hX
  have h₂ : f ∘ Y = y := funext fun i => (hYZ (productLeft n n i)).trans (productTuple_left y z i)
  have h₃ : f ∘ Z = z := funext fun i => (hYZ (productRight n n i)).trans (productTuple_right y z i)
  exact residueJacobianMap_comp_of_coordinate_derivations E f X Y Z A B C hA hB hC
    (by rwa [h₁,h₂]) (by rwa [h₂,h₃]) (by rwa [h₁,h₃]) D hD L₁ L₂ L₃
    (by rwa [h₁,h₂]) (by rwa [h₂,h₃]) (by rwa [h₁,h₃])

end SpecialTransformations.Section9
