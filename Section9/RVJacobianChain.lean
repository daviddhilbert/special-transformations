module

public import Section9.GenericResidueChain
public import Section9.RVJacobianNormalization

@[expose] public section

/-! The residue chain rule over one graph field gives the RV chain
rule after cancelling the intermediate volume scale. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M
local notation "V" => Fin n → k

theorem rvJacobian_comp_of_independent_residue [IsAlgClosed k] [CharZero k]
    (E : Subfield k) [IsAlgClosed E] (x y z : V)
    (hx : AlgebraicIndependent E x)
    (hy : ∀ i, IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (y i))
    (hz : ∀ i, IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (z i))
    (A B C : Set (Fin (n + n) → RV)) (a b c : Fin n → RV)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hx₀ : ∀ i, x i ≠ 0) (hy₀ : ∀ i, y i ≠ 0) (hz₀ : ∀ i, z i ≠ 0)
    (hA : Relative.Def E (normalizedCorrespondence A a b))
    (hB : Relative.Def E (normalizedCorrespondence B b c))
    (hC : Relative.Def E (normalizedCorrespondence C a c))
    (hxy : productTuple x y ∈ normalizedCorrespondence A a b)
    (hyz : productTuple y z ∈ normalizedCorrespondence B b c)
    (hxz : productTuple x z ∈ normalizedCorrespondence C a c)
    (D₁ D₂ D₃ : Matrix (Fin n) (Fin n) k)
    (hD₁ : IsResidueJacobianMap (M := M) (normalizedCorrespondence A a b)
      (productTuple x y) (Matrix.toLin' D₁))
    (hD₂ : IsResidueJacobianMap (M := M) (normalizedCorrespondence B b c)
      (productTuple y z) (Matrix.toLin' D₂))
    (hD₃ : IsResidueJacobianMap (M := M) (normalizedCorrespondence C a c)
      (productTuple x z) (Matrix.toLin' D₃))
    (h₁ : D₁.det ≠ 0) (h₂ : D₂.det ≠ 0) :
    ∃ ω η : RV, IsRVJacobianAt A (residueScale a x) (residueScale b y) ω ∧
      IsRVJacobianAt B (residueScale b y) (residueScale c z) η ∧
      IsRVJacobianAt C (residueScale a x) (residueScale c z) (η * ω) := by
  have hD := residueJacobianMap_comp_of_independent E x y z hx hy hz _ _ _ hA hB hC hxy hyz hxz
    _ _ _ hD₁ hD₂ hD₃
  have he : D₃ = D₂ * D₁ := by
    have h := congrArg LinearMap.toMatrix' hD
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using h
  have h₃ : D₃.det ≠ 0 := by rw [he, Matrix.det_mul]; exact mul_ne_zero h₂ h₁
  have hA' := isRVJacobianAt_of_normalized_residue_jacobian A a b x y ha hb hx₀ hy₀ hxy D₁ hD₁ h₁
  have hB' := isRVJacobianAt_of_normalized_residue_jacobian B b c y z hb hc hy₀ hz₀ hyz D₂ hD₂ h₂
  have hC' := isRVJacobianAt_of_normalized_residue_jacobian C a c x z ha hc hx₀ hz₀ hxz D₃ hD₃ h₃
  refine ⟨_, _, hA', hB', ?_⟩
  have hb₀ : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  have hval : (((∏ i, c i) / ∏ i, b i) * residueRV D₂.det) *
      (((∏ i, b i) / ∏ i, a i) * residueRV D₁.det) =
      ((∏ i, c i) / ∏ i, a i) * residueRV D₃.det := by
    rw [he, Matrix.det_mul, residueRV_mul]
    simp only [div_eq_mul_inv]
    calc
      _ = ((∏ i, c i) * (∏ i, a i)⁻¹) *
          (((∏ i, b i)⁻¹ * ∏ i, b i) * (residueRV D₂.det * residueRV D₁.det)) := by ac_rfl
      _ = _ := by rw [inv_mul_cancel₀ hb₀, one_mul]
  exact hval.symm ▸ hC'

end SpecialTransformations.Section9
