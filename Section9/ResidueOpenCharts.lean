import Section9.OpenResidueSelector
import Section9.ResidueChartCoverage
import Section9.ResidueJacobianExistence
import Section9.ResidueFiniteProjection
import Section9.ResidueChartJacobian

/-! A finite residue correspondence admits a square open chart at
every independent source tuple. The chart equations vanish on the
whole correspondence. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "k" => ModelResidue M
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private theorem residueOutputJacobian_nonzero_of_diagonal {E : Type} [Field E] [Algebra E k]
    (P : Fin n → MvPolynomial (Fin (n + n)) E) (z : Fin (n + n) → k)
    (hoff : ∀ i j : Fin n, j ≠ i → pderiv (productRight n n j) (P i) = 0)
    (hdiag : ∀ i, aeval z (pderiv (productRight n n i) (P i)) ≠ 0) :
    aeval z (residueOutputJacobian P) ≠ 0 := by
  classical
  let A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => aeval z (pderiv (productRight n n j) (P i))
  have hA : A = Matrix.diagonal (fun i => aeval z (pderiv (productRight n n i) (P i))) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [A]
    · change aeval z (pderiv (productRight n n j) (P i)) = _
      rw [hoff i j (Ne.symm h), map_zero, Matrix.diagonal_apply_ne _ h]
  change (aeval z).toRingHom (residueOutputJacobian P) ≠ 0
  rw [residueOutputJacobian, RingHom.map_det]
  change A.det ≠ 0
  rw [hA, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)

theorem exists_open_residue_chart [CharZero k] [IsAlgClosed k]
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def (residueParameterField B) C)
    (hfin : ∀ x : Fin n → k, {y | productTuple x y ∈ C}.Finite) :
    ∃ P : Fin n → MvPolynomial (Fin (n + n)) (residueParameterField B),
      ∃ T : MvPolynomial (Fin (n + n)) (residueParameterField B),
        let Q := residueOutputJacobian P * T
        (∀ z ∈ C, ∀ i, aeval z (P i) = 0) ∧
        (∀ z, (∀ i, aeval z (P i) = 0) → aeval z Q ≠ 0 → z ∈ C) ∧
        (∀ z ∈ C, AlgebraicIndependent (residueParameterField B) (z ∘ productLeft n n) →
          aeval z Q ≠ 0) := by
  let E := residueParameterField B
  obtain ⟨P, hP, hoff, hdiag⟩ := exists_residue_simple_equations hs B hB C hC hfin
  obtain ⟨T, hT⟩ := exists_generic_open_residueSelector E C hC P
  let Q := residueOutputJacobian P * T
  have hQ (z) (hz : z ∈ C) (hind : AlgebraicIndependent E (z ∘ productLeft n n)) :
      aeval z Q ≠ 0 := by
    have hdet := residueOutputJacobian_nonzero_of_diagonal P z hoff (hdiag z hz hind)
    have hT' := (hT z hind (hP z hz) hdet).mp hz
    change aeval z (residueOutputJacobian P * T) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hdet hT'
  have he (z) (hz : AlgebraicIndependent E (z ∘ productLeft n n)) :
      z ∈ C ↔ (∀ i, aeval z (P i) = 0) ∧ aeval z Q ≠ 0 := by
    constructor
    · intro hz'
      exact ⟨hP z hz', hQ z hz' hz⟩
    · rintro ⟨hP', hQ'⟩
      change aeval z (residueOutputJacobian P * T) ≠ 0 at hQ'
      rw [map_mul, mul_ne_zero_iff] at hQ'
      exact (hT z hz hP' hQ'.1).mpr hQ'.2
  obtain ⟨D, hD, hcover⟩ := exists_residueChart_bad_input_polynomial hs B hB C hC P Q he
  let T' := T * rename (productLeft n n) D
  have heval (z : Fin (n + n) → k) :
      aeval z (residueOutputJacobian P * T') = aeval z Q * aeval (z ∘ productLeft n n) D := by
    simp only [T', Q, map_mul, aeval_rename, mul_assoc]
  refine ⟨P, T', hP, ?_, ?_⟩
  · intro z hP' hQ'
    rw [heval, mul_ne_zero_iff] at hQ'
    exact (hcover z hQ'.2).mpr ⟨hP', hQ'.1⟩
  · intro z hz hind
    rw [heval, mul_ne_zero_iff]
    refine ⟨hQ z hz hind, fun h => hD ?_⟩
    exact hind.eq_zero_of_aeval_eq_zero D h

theorem exists_residue_chart_with_input_cut [CharZero k] [IsAlgClosed k]
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def (residueParameterField B) C)
    (hfinR : ∀ x : Fin n → k, {y | productTuple x y ∈ C}.Finite)
    (hfinL : ∀ y : Fin n → k, {x | productTuple x y ∈ C}.Finite) :
    let E := residueParameterField B
    ∃ (P : Fin n → MvPolynomial (Fin (n + n)) E) (T : MvPolynomial (Fin (n + n)) E)
      (D : MvPolynomial (Fin n) E), D ≠ 0 ∧
      let Q := residueOutputJacobian P * T
      let R := (Matrix.of fun i j => pderiv (productLeft n n j) (P i)).det
      (∀ z ∈ C, ∀ i, aeval z (P i) = 0) ∧
      (∀ z, (∀ i, aeval z (P i) = 0) → aeval z Q ≠ 0 → z ∈ C) ∧
      (∀ z ∈ C, aeval (z ∘ productLeft n n) D ≠ 0 → aeval z Q ≠ 0 ∧ aeval z R ≠ 0) := by
  let E := residueParameterField B
  obtain ⟨P, T, hP, hchart, hQ⟩ := exists_open_residue_chart hs B hB C hC hfinR
  let Q := residueOutputJacobian P * T
  let R := (Matrix.of fun i j => pderiv (productLeft n n j) (P i)).det
  have hR (z) (hz : z ∈ C) (hind : AlgebraicIndependent E (z ∘ productLeft n n)) : aeval z R ≠ 0 := by
    let x := z ∘ productLeft n n
    let y := z ∘ productRight n n
    have hxy : productTuple x y = z := by
      apply productTuple_ext
      · intro i
        simp only [productTuple_left, x, Function.comp_apply]
      · intro i
        simp only [productTuple_right, y, Function.comp_apply]
    have hy := residue_independent_target_of_finite_reverse E C hC x y (hxy.symm ▸ hz) (hfinL y) hind
    obtain ⟨_, hhor⟩ := residue_tangent_kernels_eq_zero_of_independent_projections
      hs B hB C hC hfinR hfinL x y (hxy.symm ▸ hz) hind hy
    rw [hxy] at hhor
    let P' (i : Fin n) := (P i).map E.subtype
    let Q' := Q.map E.subtype
    let T' := T.map E.subtype
    have hQ' : Q' = residueOutputJacobian P' * T' := by
      change MvPolynomial.map E.subtype (residueOutputJacobian P * T) = _
      rw [map_mul, residueOutputJacobian, residueOutputJacobian, RingHom.map_det]
      congr 1
      apply congrArg Matrix.det
      apply Matrix.ext
      intro i j
      change ((pderiv (productRight n n j) (P i)).map E.subtype) =
        pderiv (productRight n n j) ((P i).map E.subtype)
      rw [pderiv_map]
    have hRP := residueChart_inputBlock_det_ne_zero C z hz P' Q' T' hQ'
      (fun i w hw => by rw [eval_map]; exact hP w hw i)
      (by rw [eval_map]; exact hQ z hz hind)
      (fun w h₁ h₂ => hchart w (fun i => by
        have hi := h₁ i
        change ((P i).map E.subtype).eval w = 0 at hi
        rw [eval_map] at hi
        exact hi) (by
        change (Q.map E.subtype).eval w ≠ 0 at h₂
        rw [eval_map] at h₂
        exact h₂)) hhor
    change (aeval z).toRingHom ((Matrix.of fun i j => pderiv (productLeft n n j) (P i)).det) ≠ 0
    rw [RingHom.map_det]
    have hM : (aeval z).toRingHom.mapMatrix (Matrix.of fun i j => pderiv (productLeft n n j) (P i)) =
        Matrix.of (fun i j => (pderiv (productLeft n n j) (P' i)).eval z) := by
      apply Matrix.ext
      intro i j
      change aeval z (pderiv (productLeft n n j) (P i)) =
        (pderiv (productLeft n n j) ((P i).map E.subtype)).eval z
      rw [pderiv_map, eval_map] <;> rfl
    rw [hM]
    exact hRP
  let Y := {z | z ∈ C ∧ (aeval z Q = 0 ∨ aeval z R = 0)}
  have hY : Relative.Def E Y :=
    hC.inter ((mvPolynomial_zeroSet_definable E Q).union (mvPolynomial_zeroSet_definable E R))
  obtain ⟨D, hD, hvan⟩ := exists_residue_polynomial_vanishing_on_selection hs B hB Y hY
    (productLeft n n) (fun z hz hi => hz.2.elim (hQ z hz.1 hi) (hR z hz.1 hi))
  exact ⟨P, T, D, hD, hP, hchart, fun z hz hd =>
    ⟨fun h => hd (hvan z ⟨hz, Or.inl h⟩), fun h => hd (hvan z ⟨hz, Or.inr h⟩)⟩⟩

end SpecialTransformations.Section9
