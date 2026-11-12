module

public import Section9.PolynomialDifferentiation
public import Section9.WeightedJacobian

@[expose] public section

/-! Identification of the VF derivative of a local branch with the
implicit matrix of its equations. The branch is differentiable on the
generic locus by the independent-point theorem. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8 SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

local notation "VF" => VFType (M := M)

private noncomputable def graphLinearMap (L : (Fin n → VF) →ₗ[VF] (Fin m → VF)) :
    (Fin n → VF) →ₗ[VF] (Fin (n + m) → VF) where
  toFun h := productTuple h (L h)
  map_add' h k := by
    apply productTuple_ext
    · intro i
      simp [productTuple_left]
    · intro i
      simp [productTuple_right]
  map_smul' t h := by
    apply productTuple_ext
    · intro i
      simp only [RingHom.id_apply, productTuple_left, Pi.smul_apply]
    · intro i
      rw [RingHom.id_apply, Pi.smul_apply, productTuple_right, productTuple_right]
      exact congrFun (L.map_smul t h) i

private theorem HasVFDerivativeAt.graph
    {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {L : (Fin n → VF) →ₗ[VF] (Fin m → VF)} (hL : HasVFDerivativeAt f a L) :
    HasVFDerivativeAt (fun x => productTuple x (f x)) a (graphLinearMap L) := by
  apply hasVFDerivativeAt_of_components
  intro i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j =>
    intro ε
    refine ⟨1, fun h hn _ => ?_⟩
    change ε.val * vfTupleValue h < Values.vfValueHom
      (productTuple (a + h) (f (a + h)) (productLeft n m j) -
        productTuple a (f a) (productLeft n m j) - productTuple h (L h) (productLeft n m j))
    rw [productTuple_left, productTuple_left, productTuple_left, Pi.add_apply,
      add_sub_cancel_left, sub_self, map_zero]
    exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε) (vfTupleValue_ne_zero hn))
  | inr j =>
    change ∀ ε : Values.Gamma (M := M), ∃ δ : Values.Gamma (M := M),
      ∀ h : Fin n → VF, h ≠ 0 → δ.val < vfTupleValue h →
        ε.val * vfTupleValue h < Values.vfValueHom
          (productTuple (a + h) (f (a + h)) (productRight n m j) -
            productTuple a (f a) (productRight n m j) - productTuple h (L h) (productRight n m j))
    simpa only [productTuple_right]
      using hL.component j

private theorem graphDerivative_matrix
    (D : Matrix (Fin m) (Fin (n + m)) VF) (L : (Fin n → VF) →ₗ[VF] (Fin m → VF)) :
    LinearMap.toMatrix' ((Matrix.toLin' D).comp (graphLinearMap L)) =
      (Matrix.of fun i k => D i (productRight n m k)) * LinearMap.toMatrix' L +
        (Matrix.of fun i j => D i (productLeft n m j)) := by
  classical
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix'_apply]
  change (Matrix.toLin' D (productTuple (Pi.single j 1) (L (Pi.single j 1)))) i = _
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [← (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).sum_comp]
  rw [Fintype.sum_sum_type]
  change (∑ k : Fin n, D i (productLeft n m k) *
      productTuple (Pi.single j 1) (L (Pi.single j 1)) (productLeft n m k)) +
    (∑ k : Fin m, D i (productRight n m k) *
      productTuple (Pi.single j 1) (L (Pi.single j 1)) (productRight n m k)) = _
  simp only [productTuple_left, productTuple_right]
  have hinput :
      (∑ k : Fin n, D i (productLeft n m k) * (Pi.single j 1 : Fin n → VF) k) =
        D i (productLeft n m j) := by
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, mul_zero]
    · simp
  rw [hinput]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, LinearMap.toMatrix'_apply, add_comm]

private theorem derivative_eq_zero_of_eqOn_zero
    (f : (Fin n → VF) → Fin m → VF) (a : Fin n → VF)
    (L : (Fin n → VF) →ₗ[VF] (Fin m → VF)) (hL : HasVFDerivativeAt f a L)
    (ρ : Values.Gamma (M := M)) (hf : Set.EqOn f (fun _ => 0) (vfBall a ρ)) : L = 0 := by
  have hzero : HasVFDerivativeAt (fun _ : Fin n → VF => (0 : Fin m → VF)) a 0 := by
    simpa only [LinearMap.zero_apply, zero_add] using
      (hasVFDerivativeAt_affine (0 : (Fin n → VF) →ₗ[VF] (Fin m → VF)) 0 a)
  exact (hL.congr_on_vfBall hf).unique hzero

set_option backward.isDefEq.respectTransparency true in
private theorem hasVFDerivativeAt_polynomialGraph
    (P : Fin m → MvPolynomial (Fin (n + m)) VF)
    (f : (Fin n → VF) → Fin m → VF) (a : Fin n → VF)
    (L : (Fin n → VF) →ₗ[VF] (Fin m → VF)) (hL : HasVFDerivativeAt f a L) :
    let z := productTuple a (f a)
    let D : Matrix (Fin m) (Fin (n + m)) VF := Matrix.of fun i j => aeval z (pderiv j (P i))
    HasVFDerivativeAt (fun x i => aeval (productTuple x (f x)) (P i)) a
      ((Matrix.toLin' D).comp (graphLinearMap L)) := by
  let g : (Fin (n + m) → VF) → Fin m → VF := fun z i => aeval z (P i)
  let f' : (Fin n → VF) → Fin (n + m) → VF := fun x => productTuple x (f x)
  let D : Matrix (Fin m) (Fin (n + m)) VF :=
    Matrix.of fun i j => aeval (f' a) (pderiv j (P i))
  have hg : HasVFDerivativeAt g (f' a) (Matrix.toLin' D) :=
    hasVFDerivativeAt_aeval (R := VF) P (f' a)
  have hf : HasVFDerivativeAt f' a (graphLinearMap L) := HasVFDerivativeAt.graph hL
  change HasVFDerivativeAt (g ∘ f') a ((Matrix.toLin' D).comp (graphLinearMap L))
  exact HasVFDerivativeAt.comp (f := f') (g := g) (a := a)
    (L := graphLinearMap L) (D := Matrix.toLin' D) hg hf

/-- Any differentiable branch of a polynomial system satisfies its
linearized equations. -/
theorem jacobian_satisfies_polynomialSystem
    (P : Fin m → MvPolynomial (Fin (n + m)) VF)
    (f : (Fin n → VF) → Fin m → VF) (a : Fin n → VF)
    (L : (Fin n → VF) →ₗ[VF] (Fin m → VF))
    (hL : HasVFDerivativeAt f a L) (ρ : Values.Gamma (M := M))
    (hP : ∀ x ∈ vfBall a ρ, ∀ i, (P i).eval (productTuple x (f x)) = 0) :
    partialJacobianMatrix (productRight n m) P (productTuple a (f a)) * LinearMap.toMatrix' L +
      partialJacobianMatrix (productLeft n m) P (productTuple a (f a)) = 0 := by
  classical
  let z := productTuple a (f a)
  let D : Matrix (Fin m) (Fin (n + m)) VF := Matrix.of fun i j => aeval z (pderiv j (P i))
  let E : (Fin n → VF) →ₗ[VF] (Fin m → VF) := (Matrix.toLin' D).comp (graphLinearMap L)
  have hgraph : HasVFDerivativeAt (fun x i => aeval (productTuple x (f x)) (P i)) a E :=
    hasVFDerivativeAt_polynomialGraph P f a L hL
  have he : Set.EqOn (fun x i => aeval (productTuple x (f x)) (P i))
      (fun _ => 0) (vfBall a ρ) := by
    intro x hx
    funext i
    change aeval (productTuple x (f x)) (P i) = 0
    rw [aeval_eq_eval]
    exact hP x hx i
  have hE : E = 0 := derivative_eq_zero_of_eqOn_zero _ a E hgraph ρ he
  have hmat : LinearMap.toMatrix' E = 0 := by rw [hE, map_zero]
  have hsplit := (graphDerivative_matrix D L).symm.trans hmat
  simpa only [D, z, aeval_eq_eval, Matrix.of_apply, partialJacobianMatrix] using hsplit

/-- The two weighted block values give the determinant ratio for the
actual differentiable branch. This form only needs the equality tested
by the definable good domains. -/
theorem vfJacobian_value_of_blocks
    {G : Type*} [LinearOrderedCommGroupWithZero G] (v : Valuation VF G)
    (P : Fin n → MvPolynomial (Fin (n + n)) VF)
    (f : (Fin n → VF) → Fin n → VF) (a : Fin n → VF)
    (L : (Fin n → VF) →ₗ[VF] (Fin n → VF)) (hL : HasVFDerivativeAt f a L)
    (ρ : Values.Gamma (M := M))
    (heq : ∀ x ∈ vfBall a ρ, ∀ i, (P i).eval (productTuple x (f x)) = 0)
    (ha : ∀ j, a j ≠ 0)
    (hblocks : let z := productTuple a (f a)
      let A := (partialJacobianPolynomial (productLeft n n) P).eval z * ∏ i, a i
      let B := (partialJacobianPolynomial (productRight n n) P).eval z * ∏ i, f a i
      B ≠ 0 ∧ v A = v B) :
    v (LinearMap.toMatrix' L).det = (∏ i, v (f a i)) / ∏ i, v (a i) := by
  let z := productTuple a (f a)
  let A := partialJacobianMatrix (productLeft n n) P z
  let B := partialJacobianMatrix (productRight n n) P z
  have hB : B.det ≠ 0 := by
    rw [det_partialJacobianMatrix]
    exact left_ne_zero_of_mul hblocks.1
  have h := jacobian_satisfies_polynomialSystem P f a L hL ρ heq
  have he : B * LinearMap.toMatrix' L = -A := eq_neg_of_add_eq_zero_left h
  have hv := congrArg (fun D : Matrix (Fin n) (Fin n) VF => v D.det) he
  simp only [Matrix.det_mul, Matrix.det_neg, map_mul, map_pow, v.map_neg, map_one,
    one_pow, one_mul] at hv
  have hw := hblocks.2
  simp only [← det_partialJacobianMatrix, map_mul, map_prod] at hw
  have ha₀ : (∏ i, v (a i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => v.ne_zero_iff.mpr (ha i)
  apply (eq_div_iff ha₀).mpr
  apply mul_left_cancel₀ (v.ne_zero_iff.mpr hB)
  rw [← mul_assoc, hv]
  exact hw

/-- The VF Jacobian of a simple weighted graph has the Gamma value of
the target-to-source RV volume ratio. -/
theorem weightedVFJacobian_value
    {G : Type*} [LinearOrderedCommGroupWithZero G] (v : Valuation VF G)
    (t s : Fin n → RVCalc.RV v) (ht : ∀ j, t j ≠ none) (hs : ∀ j, s j ≠ none)
    {α : Fin n → G}
    (P : Fin n → MvPolynomial (Fin (n + n)) VF)
    (hP : ∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (productTuple t s j)) (α i) (P i))
    (hleft : ¬ IsResidueRoot v (productTuple t s)
      (jacobianValue (fun j => RVCalc.vrv v (t j)) α) (partialJacobianPolynomial (productLeft n n) P))
    (hright : ¬ IsResidueRoot v (productTuple t s)
      (jacobianValue (fun j => RVCalc.vrv v (s j)) α) (partialJacobianPolynomial (productRight n n) P))
    (f : (Fin n → VF) → Fin n → VF) (a : Fin n → VF)
    (ha : a ∈ RVFibre v t) (hf : f a ∈ RVFibre v s)
    (L : (Fin n → VF) →ₗ[VF] (Fin n → VF)) (hL : HasVFDerivativeAt f a L)
    (ρ : Values.Gamma (M := M))
    (heq : ∀ x ∈ vfBall a ρ, ∀ i, (P i).eval (productTuple x (f x)) = 0) :
    v (LinearMap.toMatrix' L).det = (∏ j, RVCalc.vrv v (s j)) / ∏ j, RVCalc.vrv v (t j) := by
  let u := productTuple t s
  let z := productTuple a (f a)
  let R := productRight n n
  have hu (j : Fin (n + n)) : u j ≠ none := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change u (productLeft n n i) ≠ none
      simpa only [u, productTuple_left] using ht i
    | inr i =>
      change u (R i) ≠ none
      simpa only [u, R, productTuple_right] using hs i
  have hz : z ∈ RVFibre v u := productTuple_mem_RVFibre v ha hf
  have hγ (j : Fin (n + n)) : RVCalc.vrv v (u j) ≠ 0 := by
    rw [← rvFibre_value v hz j]
    exact v.ne_zero_iff.mpr (fun h => hu j ((hz j).symm.trans (h ▸ RVCalc.rv_zero)))
  have hB := (not_residueRoot_iff_eval_eq v hu
      (isGammaPolynomial_partialJacobian v hγ hP R)).mp
    (by simpa only [u, R, jacobianValue, Function.comp_apply, productTuple_right] using hright) z hz
  have hunit : IsUnit (partialJacobianMatrix R P z).det := by
    apply isUnit_iff_ne_zero.mpr
    apply v.ne_zero_iff.mp
    rw [det_partialJacobianMatrix, hB, jacobianValue]
    exact div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (hP i).2.1)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hγ (R i))
  rw [implicitMatrix_unique _ _ hunit _ (jacobian_satisfies_polynomialSystem P f a L hL ρ heq)]
  exact weightedImplicitMatrix_value v t s ht hs P hP hleft hright ha hf

end SpecialTransformations.Section9
