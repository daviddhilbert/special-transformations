import Section9.RVJacobianChain
import Section9.ResidueFiniteProjection
import Section9.ResidueJacobianExistence

/-! At one residue-generic point, all three finite volume
correspondences admit compatible Jacobians over common scales. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M
local notation "V" => Fin n → k
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private def FiniteProjections (R : Set (Fin (n + n) → k)) : Prop :=
  (∀ x : V, {y | productTuple x y ∈ R}.Finite) ∧
  (∀ y : V, {x | productTuple x y ∈ R}.Finite)

theorem exists_rvJacobian_chain_at_generic_residue [IsAlgClosed k] [CharZero k]
    {κ : Cardinal} (hs : Saturated M κ) (B₀ : LRV.Substructure M) (hB₀ : Cardinal.mk B₀ < κ)
    (E : Subfield k) [IsAlgClosed E] (hE : residueParameterField B₀ ≤ E)
    (A B C : Set (Fin (n + n) → RV)) (a b c : Fin n → RV)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (x y z : V) (hx : AlgebraicIndependent E x)
    (hx₀ : ∀ i, x i ≠ 0) (hy₀ : ∀ i, y i ≠ 0) (hz₀ : ∀ i, z i ≠ 0)
    (hA : Relative.Def (residueParameterField B₀) (normalizedCorrespondence A a b))
    (hB : Relative.Def (residueParameterField B₀) (normalizedCorrespondence B b c))
    (hC : Relative.Def (residueParameterField B₀) (normalizedCorrespondence C a c))
    (hAf : FiniteProjections (normalizedCorrespondence A a b))
    (hBf : FiniteProjections (normalizedCorrespondence B b c))
    (hCf : FiniteProjections (normalizedCorrespondence C a c))
    (hxy : productTuple x y ∈ normalizedCorrespondence A a b)
    (hyz : productTuple y z ∈ normalizedCorrespondence B b c)
    (hxz : productTuple x z ∈ normalizedCorrespondence C a c) :
    ∃ ω η : RV, IsRVJacobianAt A (residueScale a x) (residueScale b y) ω ∧
      IsRVJacobianAt B (residueScale b y) (residueScale c z) η ∧
      IsRVJacobianAt C (residueScale a x) (residueScale c z) (η * ω) := by
  let A' := normalizedCorrespondence A a b
  let B' := normalizedCorrespondence B b c
  let C' := normalizedCorrespondence C a c
  have hA' : Relative.Def E A' := hA.mono hE
  have hB' : Relative.Def E B' := hB.mono hE
  have hC' : Relative.Def E C' := hC.mono hE
  have hy := residue_independent_target_of_finite_reverse E A' hA' x y hxy (hAf.2 y) hx
  have hz := residue_independent_target_of_finite_reverse E C' hC' x z hxz (hCf.2 z) hx
  have hAlgY (i : Fin n) : IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (y i) := by
    have h := finite_residue_row_coordinate_isAlgebraic E A' hA' x y hxy (hAf.1 x) i
    rwa [tupleField_eq_adjoin] at h
  have hAlgZ (i : Fin n) : IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (z i) := by
    have h := finite_residue_row_coordinate_isAlgebraic E C' hC' x z hxz (hCf.1 x) i
    rwa [tupleField_eq_adjoin] at h
  obtain ⟨D₁, hD₁, hd₁⟩ := exists_residueJacobianMap_over_coefficients hs B₀ hB₀ E hE A' hA
    hAf.1 hAf.2 x y hxy hx hy
  obtain ⟨D₂, hD₂, hd₂⟩ := exists_residueJacobianMap_over_coefficients hs B₀ hB₀ E hE B' hB
    hBf.1 hBf.2 y z hyz hy hz
  obtain ⟨D₃, hD₃, _⟩ := exists_residueJacobianMap_over_coefficients hs B₀ hB₀ E hE C' hC
    hCf.1 hCf.2 x z hxz hx hz
  apply rvJacobian_comp_of_independent_residue E x y z hx hAlgY hAlgZ A B C a b c ha hb hc
    hx₀ hy₀ hz₀ hA' hB' hC' hxy hyz hxz (LinearMap.toMatrix' D₁) (LinearMap.toMatrix' D₂)
    (LinearMap.toMatrix' D₃) _ _ _ hd₁ hd₂
  · simpa only [Matrix.toLin'_toMatrix'] using hD₁
  · simpa only [Matrix.toLin'_toMatrix'] using hD₂
  · simpa only [Matrix.toLin'_toMatrix'] using hD₃

end SpecialTransformations.Section9
