import Section9.ResidueTangentDescent
import Section9.RVJacobian

/-! The chain rule for a residue correspondence at a graph point
with coordinate derivations. All three maps are on the same
normalization of the middle coordinates. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "k" => ModelResidue M
local notation "V" => Fin n → k

theorem residueJacobianMap_comp_of_coordinate_derivations [IsAlgClosed k]
    (E : Subfield k) [IsAlgClosed E] {K : Type} [Field K] [Algebra E K]
    (f : K →ₐ[E] k) (x y z : Fin n → K)
    (A B C : Set (Fin (n + n) → k))
    (hA : Relative.Def E A) (hB : Relative.Def E B) (hC : Relative.Def E C)
    (hx : productTuple (f ∘ x) (f ∘ y) ∈ A)
    (hy : productTuple (f ∘ y) (f ∘ z) ∈ B)
    (hz : productTuple (f ∘ x) (f ∘ z) ∈ C)
    (D : Fin n → Derivation E K K) (hD : ∀ j i, D j (x i) = if i = j then 1 else 0)
    (L₁ L₂ L₃ : V →ₗ[k] V)
    (hL₁ : IsResidueJacobianMap (M := M) A (productTuple (f ∘ x) (f ∘ y)) L₁)
    (hL₂ : IsResidueJacobianMap (M := M) B (productTuple (f ∘ y) (f ∘ z)) L₂)
    (hL₃ : IsResidueJacobianMap (M := M) C (productTuple (f ∘ x) (f ∘ z)) L₃) :
    L₃ = L₂.comp L₁ := by
  classical
  have tangent (R : Set (Fin (n + n) → k)) (hR : Relative.Def E R)
      (u w : Fin n → K) (huw : productTuple (f ∘ u) (f ∘ w) ∈ R) (j : Fin n) :
      IsPolynomialTangent R (productTuple (f ∘ u) (f ∘ w))
        (productTuple (f ∘ D j ∘ u) (f ∘ D j ∘ w)) := by
    have he (g : K → k) : g ∘ productTuple u w = productTuple (g ∘ u) (g ∘ w) := by
      apply productTuple_ext
      · simp only [Function.comp_apply, productTuple_left, implies_true]
      · simp only [Function.comp_apply, productTuple_right, implies_true]
    have h₀ := isPolynomialTangent_of_residue_derivation E f R hR (productTuple u w) ((he f).symm ▸ huw) (D j)
    rw [he f, show f ∘ D j ∘ productTuple u w = (f ∘ D j) ∘ productTuple u w from rfl,
      he (f ∘ D j)] at h₀
    exact h₀
  have hcol (j : Fin n) : f ∘ D j ∘ x = Pi.single j 1 := by
    funext i
    simp only [Function.comp_apply, hD, Pi.single_apply, apply_ite f, map_one, map_zero]
  have hA' (j : Fin n) : (f ∘ D j ∘ y) = L₁ (Pi.single j 1) := by
    have h := tangent A hA x y hx j
    rw [hcol j] at h
    exact (hL₁ _ _).mp h
  have hB' (j : Fin n) : (f ∘ D j ∘ z) = L₂ (L₁ (Pi.single j 1)) := by
    have h := tangent B hB y z hy j
    rw [hA' j] at h
    exact (hL₂ _ _).mp h
  have hC' (j : Fin n) : (f ∘ D j ∘ z) = L₃ (Pi.single j 1) := by
    have h := tangent C hC x z hz j
    rw [hcol j] at h
    exact (hL₃ _ _).mp h
  apply LinearMap.toMatrix'.injective
  ext i j
  simp only [LinearMap.toMatrix'_apply, LinearMap.comp_apply]
  exact congrFun ((hC' j).symm.trans (hB' j)) i

end SpecialTransformations.Section9
