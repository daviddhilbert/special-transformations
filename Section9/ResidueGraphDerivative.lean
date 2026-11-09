import Section9.ResidueDerivation
import Section9.ResidueJacobianGeneric

/-! Reduce the actual bounded graph derivations and compare their
matrix to the residue tangent graph. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M K Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [Field K] [LinearOrderedCommGroupWithZero Γ] {n : ℕ}
local notation "k" => ModelResidue M

theorem isResidueJacobianMap_of_bounded_graph_derivations [IsAlgClosed k]
    (v : Valuation K Γ) (E : Subfield K)
    (A : Subfield k) [IsAlgClosed A]
    (g : ResidueField v.valuationSubring →+* k)
    (j : A →+* ResidueField (v.comap E.subtype).valuationSubring)
    (hj : ∀ a, g (residueFieldInclusion v E (j a)) = (a : k))
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def A C)
    (x y : Fin n → v.valuationSubring)
    (D : Fin n → Derivation E K K)
    (hD : ∀ l i, D l (x i : K) = if i = l then 1 else 0)
    (hbound : ∀ l z, v (D l z) ≤ v z)
    (hp : let r := g ∘ residue v.valuationSubring
      productTuple (r ∘ x) (r ∘ y) ∈ C)
    (hvertical : let r := g ∘ residue v.valuationSubring
      ∀ z, IsPolynomialTangent C (productTuple (r ∘ x) (r ∘ y)) (productTuple 0 z) → z = 0)
    (hhorizontal : let r := g ∘ residue v.valuationSubring
      ∀ z, IsPolynomialTangent C (productTuple (r ∘ x) (r ∘ y)) (productTuple z 0) → z = 0) :
    let r := g ∘ residue v.valuationSubring
    let J : Matrix (Fin n) (Fin n) k := Matrix.of fun i l =>
      r ⟨D l (y i : K), (hbound l (y i)).trans (y i).property⟩
    IsResidueJacobianMap (M := M) C (productTuple (r ∘ x) (r ∘ y)) (Matrix.toLin' J) ∧ J.det ≠ 0 := by
  classical
  let B := v.valuationSubring
  let Q := ResidueField (v.comap E.subtype).valuationSubring
  let R := ResidueField B
  let ι := residueFieldInclusion v E
  letI : Algebra Q R := ι.toAlgebra
  letI : Algebra A Q := j.toAlgebra
  letI : Algebra A R := (ι.comp j).toAlgebra
  letI : IsScalarTower A Q R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : R →ₐ[A] k := { toRingHom := g, commutes' := hj }
  choose d hd using fun l => exists_residue_derivation v E (D l) (hbound l)
  let p := productTuple (residue B ∘ x) (residue B ∘ y)
  let r := g ∘ residue B
  have he : f ∘ p = productTuple (r ∘ x) (r ∘ y) := by
    apply productTuple_ext
    · intro i
      change g (productTuple (residue B ∘ x) (residue B ∘ y) (productLeft n n i)) = _
      rw [productTuple_left, productTuple_left]
      rfl
    · intro i
      change g (productTuple (residue B ∘ x) (residue B ∘ y) (productRight n n i)) = _
      rw [productTuple_right, productTuple_right]
      rfl
  have hcol (l i : Fin n) : (d l).restrictScalars A (p (productLeft n n i)) = if i = l then 1 else 0 := by
    change d l (productTuple _ _ (productLeft n n i)) = _
    rw [productTuple_left]
    change d l (residue B (x i)) = _
    rw [hd]
    by_cases hi : i = l
    · rw [if_pos hi]
      exact (congrArg (residue B) (Subtype.ext (by
        change D l (x i : K) = (1 : K)
        rw [hD l i, if_pos hi]))).trans (map_one _)
    · rw [if_neg hi]
      exact (congrArg (residue B) (Subtype.ext (by
        change D l (x i : K) = (0 : K)
        rw [hD l i, if_neg hi]))).trans (map_zero _)
  have h := isResidueJacobianMap_of_coordinate_derivations A f C hC p (he.symm ▸ hp)
    (fun l => (d l).restrictScalars A) hcol (he.symm ▸ hvertical) (he.symm ▸ hhorizontal)
  have hJ : (Matrix.of fun i l => f ((d l).restrictScalars A (p (productRight n n i)))) =
      (Matrix.of fun i l => r ⟨D l (y i : K), (hbound l (y i)).trans (y i).property⟩) := by
    ext i l
    change g (d l (productTuple _ _ (productRight n n i))) = _
    rw [productTuple_right]
    exact congrArg g (hd l (y i))
  dsimp only at h
  rw [he, hJ] at h
  exact h

end SpecialTransformations.Section9
