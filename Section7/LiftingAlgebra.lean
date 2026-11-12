module

public import Section7.TupleCoordinates
public import Section7.PolynomialCoordinateMaps
public import Section7.WeightedPolynomialTests
public import Section7.JacobianNormalization
public import Section7.SimpleRootNormalization
public import Section7.ResidueFibreEvaluation
public import Section7.IntegerAvoidance
public import Section7.GeneralizedHensel
public import Section7.LiftRelations

@[expose] public section

section WeightedDerivativeProductProof

/-!
# Aligning residue-root equations without adding coefficients

A simple coordinate derivative of a polynomial, multiplied by that
variable, has exactly the weight of the original polynomial. It can
therefore be used to align an equation of the opposite block. The
derivative of the multiplier contributes only below the prescribed
value, because the original equation vanishes in residue.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem IsGammaPolynomial.zsmul (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {P : MvPolynomial (Fin n) K}
    (hP : IsGammaPolynomial v γ α P) (z : ℤ) :
    IsGammaPolynomial v γ α (z • P) := by
  cases z with
  | ofNat n => simpa using hP.nsmul v n
  | negSucc n =>
    have hz : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
    rw [hz, neg_zsmul, natCast_zsmul]
    exact (hP.nsmul v (n + 1)).neg v

theorem gammaPolynomial_derivativeMultiplier (v : Valuation K Γ)
    {n : ℕ} {γ : Fin n → Γ} {α : Γ} {P : MvPolynomial (Fin n) K}
    (hP : IsGammaPolynomial v γ α P) (i : Fin n) :
    IsGammaPolynomial v γ α (X i * pderiv i P) := by
  have h := (isGammaPolynomial_X v hP.1 i).mul v (hP.pderiv v i)
  rwa [mul_div_cancel₀ α (hP.1 i)] at h

theorem derivativeMultiplier_eval_value (v : Valuation K Γ)
    {n : ℕ} {γ : Fin n → Γ} {α : Γ} {P : MvPolynomial (Fin n) K}
    (hP : IsGammaPolynomial v γ α P) (i : Fin n) (a : Fin n → K)
    (ha : ∀ j, v (a j) = γ j) (h : v ((pderiv i P).eval a) = α / γ i) :
    v ((X i * pderiv i P).eval a) = α := by
  rw [eval_mul, eval_X, map_mul, ha, h, mul_div_cancel₀ α (hP.1 i)]

theorem residueRoot_mul_left (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} {α β : Γ} {A P : MvPolynomial (Fin n) K}
    (hA : IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) β A)
    (hP : IsResidueRoot v t α P) :
    IsResidueRoot v t (β * α) (A * P) := by
  intro a ha
  rw [eval_mul, map_mul]
  exact (mul_le_mul_of_nonneg_right (gammaPolynomial_eval_le v hA (rvFibre_value v ha))
    (zero_le : 0 ≤ v (P.eval a))).trans_lt
    (mul_lt_mul_of_pos_left (hP a ha) (pos_iff_ne_zero.mpr hA.2.1))

theorem derivative_multiplier_error_lt (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α β : Γ} {A P : MvPolynomial (Fin n) K}
    (hA : IsGammaPolynomial v γ β A) (i : Fin n) (a : Fin n → K)
    (ha : ∀ j, v (a j) = γ j) (hP : v (P.eval a) < α) :
    v ((pderiv i A).eval a * P.eval a) < (β * α) / γ i := by
  rw [map_mul]
  calc
    _ ≤ (β / γ i) * v (P.eval a) :=
      mul_le_mul_of_nonneg_right (gammaPolynomial_eval_le v (hA.pderiv v i) ha) zero_le
    _ < (β / γ i) * α :=
      mul_lt_mul_of_pos_left hP (pos_iff_ne_zero.mpr (div_ne_zero hA.2.1 (hA.1 i)))
    _ = (β * α) / γ i := by simp only [div_eq_mul_inv]; ac_rfl

theorem derivative_weighted_mul_eval_eq (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α β : Γ} {A P : MvPolynomial (Fin n) K}
    (hA : IsGammaPolynomial v γ β A) (i : Fin n) (a : Fin n → K)
    (ha : ∀ j, v (a j) = γ j) (hP : v (P.eval a) < α)
    (hAeq : v (A.eval a) = β) (hDeq : v ((pderiv i P).eval a) = α / γ i) :
    v ((pderiv i (A * P)).eval a) = (β * α) / γ i := by
  have he := derivative_multiplier_error_lt v hA i a ha hP
  have hm : v (A.eval a * (pderiv i P).eval a) = (β * α) / γ i := by
    rw [map_mul, hAeq, hDeq, mul_div_assoc]
  rw [pderiv_mul, eval_add, eval_mul, eval_mul]
  exact (v.map_add_eq_of_lt_right (hm.symm ▸ he)).trans hm

theorem derivative_weighted_mul_eval_lt (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α β : Γ} {A P : MvPolynomial (Fin n) K}
    (hA : IsGammaPolynomial v γ β A) (i : Fin n) (a : Fin n → K)
    (ha : ∀ j, v (a j) = γ j) (hP : v (P.eval a) < α)
    (hAeq : v (A.eval a) = β) (hDlt : v ((pderiv i P).eval a) < α / γ i) :
    v ((pderiv i (A * P)).eval a) < (β * α) / γ i := by
  rw [pderiv_mul, eval_add, eval_mul, eval_mul]
  apply v.map_add_lt (derivative_multiplier_error_lt v hA i a ha hP)
  rw [map_mul, hAeq, mul_div_assoc]
  exact mul_lt_mul_of_pos_left hDlt (pos_iff_ne_zero.mpr hA.2.1)

end SpecialTransformations.Section7

end WeightedDerivativeProductProof

section PartialJacobianResiduesProof

/-!
# Partial Jacobians at a common RV anchor

Each normalized partial derivative has an actual valuation-ring entry.
Reduction of this matrix detects simplicity of the system in the chosen
block. The anchor is used only to test this property, not as a coefficient
in the original-base system.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

section Partial

variable (v : Valuation K Γ) {n m : ℕ}
    {γ : Fin m → Γ} {α : Fin n → Γ}
    (F : Fin n → MvPolynomial (Fin m) K) (a : Fin m → K) (e : Fin n → K)
    (hF : ∀ i, IsGammaPolynomial v γ (α i) (F i))
    (ha : ∀ j, v (a j) = γ j) (he : ∀ i, v (e i) * α i = 1)

include hF ha he in
theorem normalizedPartialEntry_le (i : Fin n) (j : Fin m) :
    v (e i * a j * (pderiv j (F i)).eval a) ≤ 1 := by
  rw [map_mul, map_mul, ha]
  calc
    _ ≤ v (e i) * γ j * (α i / γ j) :=
      mul_le_mul_of_nonneg_left (gammaPolynomial_eval_le v ((hF i).pderiv v j) ha) zero_le
    _ = 1 := by
      rw [mul_assoc, mul_div_cancel₀ _ ((hF i).1 j), he]

noncomputable def integralPartialJacobian (f : Fin n ↪ Fin m) :
    Matrix (Fin n) (Fin n) v.valuationSubring :=
  Matrix.of fun i j => ⟨e i * a (f j) * (pderiv (f j) (F i)).eval a,
    (Valuation.mem_valuationSubring_iff v _).mpr
      (normalizedPartialEntry_le v F a e hF ha he i (f j))⟩

noncomputable def residuePartialJacobian (f : Fin n ↪ Fin m) :
    Matrix (Fin n) (Fin n) (ResidueField v.valuationSubring) :=
  (integralPartialJacobian v F a e hF ha he f).map (residue v.valuationSubring)

theorem residuePartialJacobian_entry_eq_zero_iff (f : Fin n ↪ Fin m) (i j : Fin n) :
    residuePartialJacobian v F a e hF ha he f i j = 0 ↔
      v ((pderiv (f j) (F i)).eval a) < α i / γ (f j) := by
  have he0 : v (e i) ≠ 0 := by
    intro h
    simpa [h] using he i
  have hfactor : v (e i) * γ (f j) * (α i / γ (f j)) = 1 := by
    rw [mul_assoc, mul_div_cancel₀ _ ((hF i).1 (f j)), he]
  change residue v.valuationSubring (integralPartialJacobian v F a e hF ha he f i j) = 0 ↔ _
  rw [residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change v (e i * a (f j) * (pderiv (f j) (F i)).eval a) < 1 ↔ _
  rw [map_mul, map_mul, ha, ← hfactor]
  exact mul_lt_mul_iff_right₀
    (pos_iff_ne_zero.mpr (mul_ne_zero he0 ((hF i).1 (f j))))

theorem residuePartialJacobian_det_ne_zero_of_diagonal (f : Fin n ↪ Fin m)
    (hd : ∀ i, v ((pderiv (f i) (F i)).eval a) = α i / γ (f i))
    (hoff : ∀ i j, i ≠ j → v ((pderiv (f j) (F i)).eval a) < α i / γ (f j)) :
    (residuePartialJacobian v F a e hF ha he f).det ≠ 0 := by
  classical
  let A := residuePartialJacobian v F a e hF ha he f
  have hA : A = Matrix.diagonal (fun i => A i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact (residuePartialJacobian_entry_eq_zero_iff v F a e hF ha he f i j).mpr (hoff i j hij)
  change A.det ≠ 0
  conv_lhs => rw [hA, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  intro hz
  have h := (residuePartialJacobian_entry_eq_zero_iff v F a e hF ha he f i i).mp hz
  rw [hd] at h
  exact (lt_irrefl _) h

end Partial

theorem partialJacobian_value_of_residue_det_ne_zero (v : Valuation K Γ) {n m : ℕ}
    {γ : Fin m → Γ} {α : Fin n → Γ}
    (F : Fin n → MvPolynomial (Fin m) K) (a : Fin m → K) (e : Fin n → K)
    (hγ : ∀ j, γ j ≠ 0) (hF : ∀ i, IsGammaPolynomial v γ (α i) (F i))
    (ha : ∀ j, v (a j) = γ j) (he : ∀ i, v (e i) * α i = 1)
    (f : Fin n ↪ Fin m)
    (hn : (residuePartialJacobian v F a e hF ha he f).det ≠ 0) :
    v ((jacobianPolynomial (fun i => specializeCoordinates f a (F i))).eval (a ∘ f)) =
      jacobianValue (γ ∘ f) α := by
  classical
  let A := integralPartialJacobian v F a e hF ha he f
  let B := fun i => specializeCoordinates f a (F i)
  let c := a ∘ f
  have hs : Function.extend f c a = a := by
    funext j
    by_cases hj : ∃ k, f k = j
    · obtain ⟨k, rfl⟩ := hj
      exact f.injective.extend_apply c a k
    · exact Function.extend_apply' c a j hj
  change ((residue v.valuationSubring).mapMatrix A).det ≠ 0 at hn
  rw [← RingHom.map_det] at hn
  have hvalue := valuationRing_value_one_of_residue_ne_zero v A.det hn
  have hA : v.valuationSubring.subtype.mapMatrix A =
      Matrix.diagonal e * jacobianMatrix B c * Matrix.diagonal c := by
    change A.map v.valuationSubring.subtype = _
    ext i j
    simp only [A, integralPartialJacobian, Matrix.map_apply, Matrix.of_apply,
      jacobianMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, B,
      pderiv_specializeCoordinates, specializeCoordinates_eval, hs]
    change e i * a (f j) * (pderiv (f j) (F i)).eval a = _
    dsimp only [c, Function.comp_apply]
    ring
  change v (v.valuationSubring.subtype A.det) = 1 at hvalue
  rw [RingHom.map_det, hA, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal, ← eval_jacobianPolynomial] at hvalue
  have hprod : (∏ i, e i) * (jacobianPolynomial B).eval c * (∏ i, c i) =
      (∏ i, e i * c i) * (jacobianPolynomial B).eval c := by
    rw [Finset.prod_mul_distrib]
    ring
  rw [hprod, map_mul] at hvalue
  have hscale := jacobian_normalizingFactor_value v (c := c) (e := e)
    (fun i => hγ (f i)) (fun i => ha (f i)) he
  have hnonzero : v (∏ i, e i * c i) ≠ 0 := by
    intro hz
    simp [hz] at hscale
  exact mul_left_cancel₀ hnonzero (hvalue.trans hscale.symm)

end SpecialTransformations.Section7

end PartialJacobianResiduesProof

section IntegerPartialJacobiansProof

/-!
# Simultaneously simple equations in two blocks

The two residue Jacobians vary by the same integer row combinations.
The checked integer avoidance theorem then produces one system with
both determinants nonzero. Integer operations keep the coefficients in
the original field and preserve all residue-root bounds.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem valuation_zsmul_lt (v : Valuation K Γ) {x : K} {α : Γ}
    (h : v x < α) (z : ℤ) : v (z • x) < α := by
  have hn (k : ℕ) : v (k • x) < α := by
    induction k with
    | zero => simpa only [zero_nsmul, map_zero] using (lt_of_le_of_lt zero_le h)
    | succ k ih => simpa only [succ_nsmul] using v.map_add_lt ih h
  cases z with
  | ofNat k => simpa using hn k
  | negSucc k =>
    have hz : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := rfl
    rw [hz, neg_zsmul, natCast_zsmul, Valuation.map_neg v]
    exact hn (k + 1)

section

variable (v : Valuation K Γ) {n m : ℕ}
    {γ : Fin m → Γ} {α : Fin n → Γ}
    (F G : Fin n → MvPolynomial (Fin m) K) (a : Fin m → K) (e : Fin n → K)
    (hF : ∀ i, IsGammaPolynomial v γ (α i) (F i))
    (hG : ∀ i, IsGammaPolynomial v γ (α i) (G i))
    (ha : ∀ j, v (a j) = γ j) (he : ∀ i, v (e i) * α i = 1)

noncomputable def integerPolynomialCombination {R : Type*} [CommRing R] {ι σ : Type*}
    (F G : ι → MvPolynomial σ R) (p q : ι → ℤ) (i : ι) :
    MvPolynomial σ R := p i • F i + q i • G i

include hF hG in
theorem integerPolynomialCombination_gamma (p q : Fin n → ℤ) (i : Fin n) :
    IsGammaPolynomial v γ (α i) (integerPolynomialCombination F G p q i) :=
  ((hF i).zsmul v (p i)).add v ((hG i).zsmul v (q i))

theorem residuePartialJacobian_integerCombination (f : Fin n ↪ Fin m)
    (p q : Fin n → ℤ) :
    residuePartialJacobian v (integerPolynomialCombination F G p q) a e
        (integerPolynomialCombination_gamma v F G hF hG p q) ha he f =
      Matrix.of fun i j =>
        (p i : ResidueField v.valuationSubring) * residuePartialJacobian v F a e hF ha he f i j +
        (q i : ResidueField v.valuationSubring) * residuePartialJacobian v G a e hG ha he f i j := by
  ext i j
  let U := integralPartialJacobian v F a e hF ha he f i j
  let W := integralPartialJacobian v G a e hG ha he f i j
  let T := integralPartialJacobian v (integerPolynomialCombination F G p q) a e
    (integerPolynomialCombination_gamma v F G hF hG p q) ha he f i j
  have hT : T = p i • U + q i • W := by
    apply Subtype.ext
    change e i * a (f j) * (pderiv (f j) (integerPolynomialCombination F G p q i)).eval a =
      v.valuationSubring.subtype (p i • U + q i • W)
    simp only [integerPolynomialCombination, map_add, map_zsmul]
    change e i * a (f j) * (p i • (pderiv (f j) (F i)).eval a +
      q i • (pderiv (f j) (G i)).eval a) =
      p i • (e i * a (f j) * (pderiv (f j) (F i)).eval a) +
      q i • (e i * a (f j) * (pderiv (f j) (G i)).eval a)
    simp only [zsmul_eq_mul]
    ring
  change residue v.valuationSubring T = (p i : ResidueField v.valuationSubring) *
    residue v.valuationSubring U + (q i : ResidueField v.valuationSubring) *
    residue v.valuationSubring W
  rw [hT, map_add, map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]

theorem exists_integerCombination_partialJacobians
    [CharZero (ResidueField v.valuationSubring)]
    (f g : Fin n ↪ Fin m)
    (hf : (residuePartialJacobian v F a e hF ha he f).det ≠ 0)
    (hg : (residuePartialJacobian v G a e hG ha he g).det ≠ 0) :
    ∃ p q : Fin n → ℤ,
      let H := integerPolynomialCombination F G p q
      let hH := integerPolynomialCombination_gamma v F G hF hG p q
      (residuePartialJacobian v H a e hH ha he f).det ≠ 0 ∧
      (residuePartialJacobian v H a e hH ha he g).det ≠ 0 := by
  obtain ⟨p, q, hp, hq⟩ := exists_integer_rowCombinations _ _ _ _ hf hg
  refine ⟨p, q, ?_⟩
  dsimp only
  rw [residuePartialJacobian_integerCombination v F G a e hF hG ha he f p q,
    residuePartialJacobian_integerCombination v F G a e hF hG ha he g p q]
  exact ⟨hp, hq⟩

end

end SpecialTransformations.Section7

end IntegerPartialJacobiansProof

section BidirectionalHenselProof

/-!
# From partial Jacobians at one anchor to whole-fibre bijections

The partial determinant is itself a polynomial of the prescribed
value. Its exact value at a single representative therefore applies
throughout the actual RV fibre. Specializing one block gives the
simple-root hypotheses of Lemma 7.2 for every fixed representative
of that block.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

noncomputable def partialJacobianPolynomial {n m : ℕ}
    (f : Fin n ↪ Fin m) (F : Fin n → MvPolynomial (Fin m) K) :
    MvPolynomial (Fin m) K :=
  Matrix.det (Matrix.of fun i j => pderiv (f j) (F i))

theorem isGammaPolynomial_partialJacobian (v : Valuation K Γ) {n m : ℕ}
    {γ : Fin m → Γ} {α : Fin n → Γ} {F : Fin n → MvPolynomial (Fin m) K}
    (hγ : ∀ j, γ j ≠ 0) (hF : ∀ i, IsGammaPolynomial v γ (α i) (F i))
    (f : Fin n ↪ Fin m) :
    IsGammaPolynomial v γ (jacobianValue (γ ∘ f) α) (partialJacobianPolynomial f F) := by
  classical
  have hα : ∀ i, α i ≠ 0 := fun i => (hF i).2.1
  have hvalue : jacobianValue (γ ∘ f) α ≠ 0 :=
    div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hα i)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hγ (f i))
  rw [partialJacobianPolynomial, Matrix.det_apply]
  apply IsGammaPolynomial.sum v hγ hvalue
  intro σ
  have hp := IsGammaPolynomial.prod v hγ Finset.univ
    (fun j _ => (hF (σ j)).pderiv v (f j))
  have he : (∏ j, α (σ j) / γ (f j)) = jacobianValue (γ ∘ f) α := by
    rw [Finset.prod_div_distrib, Equiv.prod_comp σ]
    rfl
  rw [he] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp.neg v

theorem eval_jacobian_specializeCoordinates {n m : ℕ}
    (f : Fin n ↪ Fin m) (F : Fin n → MvPolynomial (Fin m) K)
    (a : Fin m → K) (b : Fin n → K) :
    (jacobianPolynomial (fun i => specializeCoordinates f a (F i))).eval b =
      (partialJacobianPolynomial f F).eval (Function.extend f b a) := by
  rw [eval_jacobianPolynomial, partialJacobianPolynomial, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp only [jacobianMatrix, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    pderiv_specializeCoordinates, specializeCoordinates_eval]

theorem extend_coordinates_self {n m : ℕ} (f : Fin n ↪ Fin m) (a : Fin m → K) :
    Function.extend f (a ∘ f) a = a := by
  funext j
  by_cases hj : ∃ k, f k = j
  · obtain ⟨k, rfl⟩ := hj
    exact f.injective.extend_apply (a ∘ f) a k
  · exact Function.extend_apply' (a ∘ f) a j hj

theorem partialJacobian_not_residueRoot_of_residue_det_ne_zero (v : Valuation K Γ)
    {n m : ℕ} {t : Fin m → RVCalc.RV v} (ht : ∀ j, t j ≠ none)
    {α : Fin n → Γ} (F : Fin n → MvPolynomial (Fin m) K)
    (hF : ∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) (α i) (F i))
    (a : Fin m → K) (ha : a ∈ RVFibre v t)
    (e : Fin n → K) (he : ∀ i, v (e i) * α i = 1)
    (f : Fin n ↪ Fin m)
    (hn : (residuePartialJacobian v F a e hF (rvFibre_value v ha) he f).det ≠ 0) :
    ¬ IsResidueRoot v t (jacobianValue (fun j => RVCalc.vrv v (t (f j))) α)
      (partialJacobianPolynomial f F) := by
  have hγ (j : Fin m) : RVCalc.vrv v (t j) ≠ 0 := by
    rw [← rvFibre_value v ha j]
    exact (Valuation.ne_zero_iff v).mpr (fun h => ht j ((ha j).symm.trans (h ▸ RVCalc.rv_zero)))
  have hval := partialJacobian_value_of_residue_det_ne_zero v F a e hγ hF
    (rvFibre_value v ha) he f hn
  rw [eval_jacobian_specializeCoordinates, extend_coordinates_self] at hval
  intro h
  have hlt := h a ha
  rw [hval] at hlt
  exact (lt_irrefl _) hlt

theorem simpleResidueRoot_specializeCoordinates (v : Valuation K Γ)
    {n m : ℕ} {t : Fin m → RVCalc.RV v} (ht : ∀ j, t j ≠ none)
    {α : Fin n → Γ} {F : Fin n → MvPolynomial (Fin m) K}
    (hF : ∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) (α i) (F i))
    (hr : ∀ i, IsResidueRoot v t (α i) (F i))
    (f : Fin n ↪ Fin m)
    (hJ : ¬ IsResidueRoot v t (jacobianValue (fun j => RVCalc.vrv v (t (f j))) α)
      (partialJacobianPolynomial f F))
    (a : Fin m → K) (ha : a ∈ RVFibre v t) :
    IsSimpleCommonResidueRoot v (t ∘ f) α (fun i => specializeCoordinates f a (F i)) := by
  have hγ (j : Fin m) : RVCalc.vrv v (t j) ≠ 0 := by
    rw [← rvFibre_value v ha j]
    exact (Valuation.ne_zero_iff v).mpr (fun h => ht j ((ha j).symm.trans (h ▸ RVCalc.rv_zero)))
  have hext (b : Fin n → K) (hb : b ∈ RVFibre v (t ∘ f)) :
      Function.extend f b a ∈ RVFibre v t := by
    intro j
    by_cases hj : ∃ k, f k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [f.injective.extend_apply]
      exact hb k
    · rw [Function.extend_apply' _ _ _ hj]
      exact ha j
  refine ⟨fun i => ht (f i), fun i =>
    IsGammaPolynomial.specializeCoordinates f v (hF i) a (rvFibre_value v ha),
    ?_, ?_⟩
  · intro i b hb
    rw [specializeCoordinates_eval]
    exact hr i _ (hext b hb)
  · intro hh
    have hb : a ∘ f ∈ RVFibre v (t ∘ f) := fun i => ha (f i)
    have hlt := hh (a ∘ f) hb
    rw [eval_jacobian_specializeCoordinates, extend_coordinates_self] at hlt
    have he := (not_residueRoot_iff_eval_eq v ht (isGammaPolynomial_partialJacobian v hγ hF f)).mp
      hJ a ha
    rw [he] at hlt
    exact (lt_irrefl _) hlt

end SpecialTransformations.Section7

end BidirectionalHenselProof

section PolynomialFibreBijectionProof

/-!
# A square system giving both directions of a local lift

The exact same polynomial equations define the two directions.
No independent choice of forward and inverse lifts is made.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem productTuple_mem_RVFibre (v : Valuation K Γ) {m n : ℕ}
    {t : Fin m → RVCalc.RV v} {s : Fin n → RVCalc.RV v}
    {a : Fin m → K} {b : Fin n → K} (ha : a ∈ RVFibre v t) (hb : b ∈ RVFibre v s) :
    productTuple a b ∈ RVFibre v (productTuple t s) := by
  have h : (fun i => RVCalc.rv v (productTuple a b i)) = productTuple t s := by
    apply productTuple_ext
    · intro i; simpa only [productTuple_left] using ha i
    · intro j; simpa only [productTuple_right] using hb j
  exact congrFun h

theorem fibreBijection_of_polynomial_partialJacobians [IsAlgClosed K]
    (v : Valuation K Γ) {n : ℕ}
    (t s : Fin n → RVCalc.RV v) (ht : ∀ j, t j ≠ none) (hs : ∀ j, s j ≠ none)
    {α : Fin n → Γ} (F : Fin n → MvPolynomial (Fin (n + n)) K)
    (hF : ∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (productTuple t s j)) (α i) (F i))
    (hr : ∀ i, IsResidueRoot v (productTuple t s) (α i) (F i))
    (hleft : ¬ IsResidueRoot v (productTuple t s)
      (jacobianValue (fun j => RVCalc.vrv v (t j)) α)
      (partialJacobianPolynomial (productLeft n n) F))
    (hright : ¬ IsResidueRoot v (productTuple t s)
      (jacobianValue (fun j => RVCalc.vrv v (s j)) α)
      (partialJacobianPolynomial (productRight n n) F)) :
    FibreBijection v {p | ∀ i, (F i).eval (productTuple p.1 p.2) = 0} t s := by
  have htprod (j : Fin (n + n)) : productTuple t s j ≠ none := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change productTuple t s (productLeft n n i) ≠ none
      simpa only [productTuple_left] using ht i
    | inr i =>
      change productTuple t s (productRight n n i) ≠ none
      simpa only [productTuple_right] using hs i
  have hlt : productTuple t s ∘ productLeft n n = t := funext (productTuple_left t s)
  have hrt : productTuple t s ∘ productRight n n = s := funext (productTuple_right t s)
  have hl := simpleResidueRoot_specializeCoordinates v htprod hF hr (productLeft n n)
  have hh := simpleResidueRoot_specializeCoordinates v htprod hF hr (productRight n n)
  constructor
  · intro a ha
    obtain ⟨b, hb⟩ := rvFibre_nonempty v s
    have hJ : ¬ IsResidueRoot v (productTuple t s)
        (jacobianValue (fun j => RVCalc.vrv v (productTuple t s (productRight n n j))) α)
        (partialJacobianPolynomial (productRight n n) F) := by
      simpa only [productTuple_right] using hright
    have h := generalized_hensel v (hh hJ (productTuple a b) (productTuple_mem_RVFibre v ha hb))
    rw [hrt] at h
    simpa only [Set.mem_ofPred_eq, specializeCoordinates_eval, extend_productRight] using h
  · intro b hb
    obtain ⟨a, ha⟩ := rvFibre_nonempty v t
    have hJ : ¬ IsResidueRoot v (productTuple t s)
        (jacobianValue (fun j => RVCalc.vrv v (productTuple t s (productLeft n n j))) α)
        (partialJacobianPolynomial (productLeft n n) F) := by
      simpa only [productTuple_left] using hleft
    have h := generalized_hensel v (hl hJ (productTuple a b) (productTuple_mem_RVFibre v ha hb))
    rw [hlt] at h
    simpa only [Set.mem_ofPred_eq, specializeCoordinates_eval, extend_productLeft] using h

end SpecialTransformations.Section7

end PolynomialFibreBijectionProof

section LocalPolynomialSystemProof

/-!
# The original-field local system in Theorem 7.6

The two coordinate families have simple diagonal derivatives in their
own blocks and are independent of the other coordinates of those blocks.
After balancing, one integer combination yields the exact same graph
in both directions. The field representatives used in the proof never
become coefficients of the output.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- The local lifting system together with its weights and both simple
Jacobian blocks. The extra witnesses are used in Section 9 to compute
the Jacobian of this particular lift. -/
theorem exists_weightedLocalPolynomialSystem [IsAlgClosed K]
    (v : Valuation K Γ) [CharZero (ResidueField v.valuationSubring)] (E : Subfield K)
    {n : ℕ} (t s : Fin n → RVCalc.RV v) (ht : ∀ i, t i ≠ none) (hs : ∀ i, s i ≠ none)
    (α β : Fin n → Γ) (F G : Fin n → MvPolynomial (Fin (n + n)) E) :
    let u := productTuple t s
    let γ := fun j => RVCalc.vrv v (u j)
    let f := fun i => (F i).map E.subtype
    let g := fun i => (G i).map E.subtype
    (∀ i, IsGammaPolynomial v γ (α i) (f i)) →
    (∀ i, IsGammaPolynomial v γ (β i) (g i)) →
    (∀ i, IsResidueRoot v u (α i) (f i)) →
    (∀ i, IsResidueRoot v u (β i) (g i)) →
    (∀ i, ¬ IsResidueRoot v u (α i / γ (productRight n n i))
      (pderiv (productRight n n i) (f i))) →
    (∀ i, ¬ IsResidueRoot v u (β i / γ (productLeft n n i))
      (pderiv (productLeft n n i) (g i))) →
    (∀ i j, i ≠ j → pderiv (productRight n n j) (f i) = 0) →
    (∀ i j, i ≠ j → pderiv (productLeft n n j) (g i) = 0) →
    ∃ (H : Fin n → MvPolynomial (Fin (n + n)) E) (w : Fin n → Γ),
      let Z := fun i => (H i).map E.subtype
      (∀ i, IsGammaPolynomial v γ (w i) (Z i)) ∧
      ¬ IsResidueRoot v u (jacobianValue (fun j => γ (productLeft n n j)) w)
        (partialJacobianPolynomial (productLeft n n) Z) ∧
      ¬ IsResidueRoot v u (jacobianValue (fun j => γ (productRight n n j)) w)
        (partialJacobianPolynomial (productRight n n) Z) ∧
      FibreBijection v {p | ∀ i, (Z i).eval (productTuple p.1 p.2) = 0} t s := by
  classical
  let u := productTuple t s
  let γ := fun j => RVCalc.vrv v (u j)
  let f := fun i => (F i).map E.subtype
  let g := fun i => (G i).map E.subtype
  let L := productLeft n n
  let R := productRight n n
  change (∀ i, IsGammaPolynomial v γ (α i) (f i)) →
    (∀ i, IsGammaPolynomial v γ (β i) (g i)) →
    (∀ i, IsResidueRoot v u (α i) (f i)) →
    (∀ i, IsResidueRoot v u (β i) (g i)) →
    (∀ i, ¬ IsResidueRoot v u (α i / γ (R i)) (pderiv (R i) (f i))) →
    (∀ i, ¬ IsResidueRoot v u (β i / γ (L i)) (pderiv (L i) (g i))) →
    (∀ i j, i ≠ j → pderiv (R j) (f i) = 0) →
    (∀ i j, i ≠ j → pderiv (L j) (g i) = 0) → _
  intro hf hg hfr hgr hdf hdg hoffF hoffG
  have hu (j : Fin (n + n)) : u j ≠ none := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change u (L i) ≠ none
      simpa [u, L] using ht i
    | inr i =>
      change u (R i) ≠ none
      simpa [u, R] using hs i
  obtain ⟨a, ha⟩ := rvFibre_nonempty v u
  have hav : ∀ j, v (a j) = γ j := rvFibre_value v ha
  have hγ (j : Fin (n + n)) : γ j ≠ 0 := by
    rw [← hav j]
    exact (Valuation.ne_zero_iff v).mpr (fun h => hu j ((ha j).symm.trans (h ▸ RVCalc.rv_zero)))
  have hvF (i : Fin n) : v ((pderiv (R i) (f i)).eval a) = α i / γ (R i) :=
    (not_residueRoot_iff_eval_eq v hu ((hf i).pderiv v (R i))).mp (hdf i) a ha
  have hvG (i : Fin n) : v ((pderiv (L i) (g i)).eval a) = β i / γ (L i) :=
    (not_residueRoot_iff_eval_eq v hu ((hg i).pderiv v (L i))).mp (hdg i) a ha
  let A := fun i => X (L i) * pderiv (L i) (g i)
  let D := fun i => X (R i) * pderiv (R i) (f i)
  have hA (i : Fin n) : IsGammaPolynomial v γ (β i) (A i) :=
    gammaPolynomial_derivativeMultiplier v (hg i) (L i)
  have hD (i : Fin n) : IsGammaPolynomial v γ (α i) (D i) :=
    gammaPolynomial_derivativeMultiplier v (hf i) (R i)
  have hAv (i : Fin n) : v ((A i).eval a) = β i :=
    derivativeMultiplier_eval_value v (hg i) (L i) a hav (hvG i)
  have hDv (i : Fin n) : v ((D i).eval a) = α i :=
    derivativeMultiplier_eval_value v (hf i) (R i) a hav (hvF i)
  let w := fun i => β i * α i
  let f' := fun i => A i * f i
  let g' := fun i => D i * g i
  have hf' (i : Fin n) : IsGammaPolynomial v γ (w i) (f' i) := (hA i).mul v (hf i)
  have hg' (i : Fin n) : IsGammaPolynomial v γ (w i) (g' i) := by
    simpa only [w, mul_comm (β i) (α i)] using (hD i).mul v (hg i)
  have hfr' (i : Fin n) : IsResidueRoot v u (w i) (f' i) :=
    residueRoot_mul_left v (hA i) (hfr i)
  have hgr' (i : Fin n) : IsResidueRoot v u (w i) (g' i) := by
    simpa only [w, mul_comm (β i) (α i)] using residueRoot_mul_left v (hD i) (hgr i)
  let e := fun i => ((A i).eval a * (D i).eval a)⁻¹
  have he (i : Fin n) : v (e i) * w i = 1 := by
    dsimp only [e, w]
    rw [map_inv₀, map_mul, hAv, hDv]
    exact inv_mul_cancel₀ (hf' i).2.1
  have hdF (i : Fin n) : v ((pderiv (R i) (f' i)).eval a) = w i / γ (R i) :=
    derivative_weighted_mul_eval_eq v (hA i) (R i) a hav (hfr i a ha) (hAv i) (hvF i)
  have hdG (i : Fin n) : v ((pderiv (L i) (g' i)).eval a) = w i / γ (L i) := by
    simpa only [w, mul_comm (β i) (α i)] using
      derivative_weighted_mul_eval_eq v (hD i) (L i) a hav (hgr i a ha) (hDv i) (hvG i)
  have hoF (i j : Fin n) (hij : i ≠ j) : v ((pderiv (R j) (f' i)).eval a) < w i / γ (R j) := by
    apply derivative_weighted_mul_eval_lt v (hA i) (R j) a hav (hfr i a ha) (hAv i)
    rw [hoffF i j hij, map_zero, map_zero]
    exact pos_iff_ne_zero.mpr (div_ne_zero (hf i).2.1 (hγ _))
  have hoG (i j : Fin n) (hij : i ≠ j) : v ((pderiv (L j) (g' i)).eval a) < w i / γ (L j) := by
    dsimp only [w]
    rw [mul_comm (β i) (α i)]
    apply derivative_weighted_mul_eval_lt v (hD i) (L j) a hav (hgr i a ha) (hDv i)
    rw [hoffG i j hij, map_zero, map_zero]
    exact pos_iff_ne_zero.mpr (div_ne_zero (hg i).2.1 (hγ _))
  have hdetF := residuePartialJacobian_det_ne_zero_of_diagonal v f' a e hf' hav he R hdF hoF
  have hdetG := residuePartialJacobian_det_ne_zero_of_diagonal v g' a e hg' hav he L hdG hoG
  obtain ⟨p, q, hR, hL⟩ :=
    exists_integerCombination_partialJacobians v f' g' a e hf' hg' hav he R L hdetF hdetG
  let Z := integerPolynomialCombination f' g' p q
  have hZ := integerPolynomialCombination_gamma v f' g' hf' hg' p q
  have hZr (i : Fin n) : IsResidueRoot v u (w i) (Z i) := by
    intro x hx
    change v ((integerPolynomialCombination f' g' p q i).eval x) < w i
    simp only [integerPolynomialCombination, map_add, map_zsmul]
    exact v.map_add_lt (valuation_zsmul_lt v (hfr' i x hx) (p i))
      (valuation_zsmul_lt v (hgr' i x hx) (q i))
  have hJR := partialJacobian_not_residueRoot_of_residue_det_ne_zero v hu Z hZ a ha e he R hR
  have hJL := partialJacobian_not_residueRoot_of_residue_det_ne_zero v hu Z hZ a ha e he L hL
  let H := integerPolynomialCombination
    (fun i => (X (L i) * pderiv (L i) (G i)) * F i)
    (fun i => (X (R i) * pderiv (R i) (F i)) * G i) p q
  have hmap : (fun i => (H i).map E.subtype) = Z := by
    funext i
    simp only [H, Z, integerPolynomialCombination, f', g', A, D, f, g, map_add, map_zsmul,
      map_mul, map_X, pderiv_map]
  refine ⟨H, w, ?_⟩
  let W := fun i => (H i).map E.subtype
  change (∀ i, IsGammaPolynomial v γ (w i) (W i)) ∧
    ¬ IsResidueRoot v u (jacobianValue (fun j => γ (L j)) w) (partialJacobianPolynomial L W) ∧
    ¬ IsResidueRoot v u (jacobianValue (fun j => γ (R j)) w) (partialJacobianPolynomial R W) ∧
    FibreBijection v {p | ∀ i, (W i).eval (productTuple p.1 p.2) = 0} t s
  rw [show W = Z from hmap]
  exact ⟨hZ, hJL, hJR, fibreBijection_of_polynomial_partialJacobians v t s ht hs Z hZ hZr
    (by simpa only [u, L, productTuple_left] using hJL)
    (by simpa only [u, R, productTuple_right] using hJR)⟩

theorem exists_localPolynomialSystem [IsAlgClosed K]
    (v : Valuation K Γ) [CharZero (ResidueField v.valuationSubring)] (E : Subfield K)
    {n : ℕ} (t s : Fin n → RVCalc.RV v) (ht : ∀ i, t i ≠ none) (hs : ∀ i, s i ≠ none)
    (α β : Fin n → Γ) (F G : Fin n → MvPolynomial (Fin (n + n)) E) :
    let u := productTuple t s
    let γ := fun j => RVCalc.vrv v (u j)
    let f := fun i => (F i).map E.subtype
    let g := fun i => (G i).map E.subtype
    (∀ i, IsGammaPolynomial v γ (α i) (f i)) →
    (∀ i, IsGammaPolynomial v γ (β i) (g i)) →
    (∀ i, IsResidueRoot v u (α i) (f i)) →
    (∀ i, IsResidueRoot v u (β i) (g i)) →
    (∀ i, ¬ IsResidueRoot v u (α i / γ (productRight n n i))
      (pderiv (productRight n n i) (f i))) →
    (∀ i, ¬ IsResidueRoot v u (β i / γ (productLeft n n i))
      (pderiv (productLeft n n i) (g i))) →
    (∀ i j, i ≠ j → pderiv (productRight n n j) (f i) = 0) →
    (∀ i j, i ≠ j → pderiv (productLeft n n j) (g i) = 0) →
    ∃ H : Fin n → MvPolynomial (Fin (n + n)) E,
      FibreBijection v {p | ∀ i, ((H i).map E.subtype).eval (productTuple p.1 p.2) = 0} t s := by
  intro u γ f g hf hg hfr hgr hdf hdg hoffF hoffG
  obtain ⟨H, w, h⟩ := exists_weightedLocalPolynomialSystem v E t s ht hs α β F G
    hf hg hfr hgr hdf hdg hoffF hoffG
  exact ⟨H, h.2.2.2⟩

end SpecialTransformations.Section7

end LocalPolynomialSystemProof
