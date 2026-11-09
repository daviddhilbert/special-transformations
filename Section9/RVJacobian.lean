import Section4.ResidueNormalization
import Section4.ResidueScaledPredicates
import Section9.GammaJacobian
import Section7.TupleCoordinates
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option backward.isDefEq.respectTransparency false

/-! Definition 9.14 on a nondegenerate volume correspondence. A tangent
vector annihilates the differentials of the polynomials vanishing on
the residue correspondence. Its tangent space is a graph where the
first projection is an isomorphism. The second projection is an
isomorphism precisely when the resulting linear map is invertible. -/

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open scoped BigOperators

namespace SpecialTransformations.Section9

def IsPolynomialTangent {K : Type*} [Field K] {d : ℕ}
    (C : Set (Fin d → K)) (p h : Fin d → K) : Prop :=
  ∀ P : MvPolynomial (Fin d) K, (∀ q ∈ C, P.eval q = 0) →
    ∑ i, (pderiv i P).eval p * h i = 0

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M

/-- Normalize the fixed value fibre by the point's own RV coordinates. -/
def normalizedCorrespondence (C : Set (Fin (n + n) → RV)) (t s : Fin n → RV) :
    Set (Fin (n + n) → k) :=
  {z | residueScale (productTuple t s) z ∈ C ∧ ∀ i, z i ≠ 0}

def IsResidueJacobianMap (C : Set (Fin (n + n) → k)) (p : Fin (n + n) → k)
    (L : (Fin n → k) →ₗ[k] (Fin n → k)) : Prop :=
  ∀ x y : Fin n → k, IsPolynomialTangent C p (productTuple x y) ↔ y = L x

theorem IsResidueJacobianMap.unique {C : Set (Fin (n + n) → k)} {p : Fin (n + n) → k}
    {L D : (Fin n → k) →ₗ[k] (Fin n → k)}
    (hL : IsResidueJacobianMap (M := M) C p L) (hD : IsResidueJacobianMap (M := M) C p D) : L = D := by
  apply LinearMap.ext
  intro x
  exact (hD x (L x)).mp ((hL x (L x)).mpr rfl)

/-- The residue determinant, multiplied by the ratio of the original
target and source RV coordinates. The relation is partial. -/
def IsRVJacobianAt (C : Set (Fin (n + n) → RV)) (t s : Fin n → RV) (ω : RV) : Prop :=
  productTuple t s ∈ C ∧ (∀ i, t i ≠ 0) ∧ (∀ i, s i ≠ 0) ∧
    ∃ L : (Fin n → k) →ₗ[k] (Fin n → k),
      IsResidueJacobianMap (M := M) (normalizedCorrespondence C t s) (fun _ => 1) L ∧
      (LinearMap.toMatrix' L).det ≠ 0 ∧
      ω = ((∏ i, s i) / ∏ i, t i) * residueRV (LinearMap.toMatrix' L).det

theorem IsRVJacobianAt.unique {C : Set (Fin (n + n) → RV)} {t s : Fin n → RV} {ω η : RV}
    (hω : IsRVJacobianAt C t s ω) (hη : IsRVJacobianAt C t s η) : ω = η := by
  obtain ⟨_, _, _, L, hL, _, rfl⟩ := hω
  obtain ⟨_, _, _, D, hD, _, rfl⟩ := hη
  rw [hL.unique hD]

/-- The residue determinant contributes unit value. The value of the
scaled RV Jacobian is the ratio of the two volume weights in the
multiplicative presentation of Gamma. -/
theorem IsRVJacobianAt.absolute_eq_weight_ratio
    {C : Set (Fin (n + n) → RV)} {t s : Fin n → RV} {ω : RV} (hω : IsRVJacobianAt C t s ω) :
    RVOperations.absoluteHom ω =
      (∏ i, RVOperations.absoluteHom (s i)) / ∏ i, RVOperations.absoluteHom (t i) := by
  obtain ⟨_, _, _, L, _, hdet, rfl⟩ := hω
  simp only [map_mul, map_div₀, map_prod, absolute_residue, if_neg hdet, mul_one]

/-- The RV determinant projects to the paper's actual Gamma Jacobian. -/
theorem IsRVJacobianAt.gamma_eq
    {C : Set (Fin (n + n) → RV)} {t s : Fin n → RV} {ω : RV} (hω : IsRVJacobianAt C t s ω)
    (ht : ∀ i, (t i).val ≠ iRVZero) (hs : ∀ i, (s i).val ≠ iRVZero) :
    Values.vrv ω = (rvGammaJacobian t s ht hs).val := by
  obtain ⟨_, _, _, L, _, hdet, rfl⟩ := hω
  have hunit : RVOperations.vrvHom (residueRV (LinearMap.toMatrix' L).det) = 1 := by
    apply (Values.paperValueEquiv (M := M)).injective
    change RVOperations.absoluteHom (residueRV (LinearMap.toMatrix' L).det) =
      Values.paperValueEquiv 1
    rw [absolute_residue, if_neg hdet, Values.paperValue_one]
  have hweight (x : Fin n → RV) (hx : ∀ i, (x i).val ≠ iRVZero) :
      (rvVolumeGamma x hx).val = ∏ i, RVOperations.vrvHom (x i) :=
    map_prod Values.gammaValHom (fun i => Values.gammaOf (x i) (hx i)) Finset.univ
  change RVOperations.vrvHom _ = (rvGammaJacobian t s ht hs).val
  rw [map_mul, hunit, mul_one, map_div₀, map_prod, map_prod]
  have hdiv (a b : Values.Gamma (M := M)) : (a / b).val = a.val / b.val := by
    rw [div_eq_mul_inv, Values.gamma_val_mul, Values.gamma_val_inv, div_eq_mul_inv]
  rw [rvGammaJacobian, hdiv, hweight, hweight]

end SpecialTransformations.Section9
