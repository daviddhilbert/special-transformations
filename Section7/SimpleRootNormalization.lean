import Section7.JacobianNormalization

/-!
# Transport of simple common residue roots to the unit fibre

The representatives and normalizing scalars are constructed in the field.
The exact Jacobian value at all representatives follows from the proved
gamma-polynomial determinant theorem. This file does not assume a normalized
Hensel conclusion or surjectivity of the ambient value-group carrier.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- Transport a residue-root predicate along an actual scaling of RV fibres. -/
theorem residueRoot_scaled_evaluations_iff (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ i, t i ≠ none)
    {c : Fin n → K} (hc : c ∈ RVFibre v t) {e : K} {α : Γ}
    (he : v e * α = 1) {F G : MvPolynomial (Fin n) K}
    (hG : ∀ y, G.eval y = e * F.eval (fun i => c i * y i)) :
    IsResidueRoot v (fun _ => RVCalc.rv v (1 : K)) 1 G ↔ IsResidueRoot v t α F := by
  have hep : 0 < v e := by
    apply (zero_lt_iff).mpr
    intro hz
    have : (0 : Γ) = 1 := by simpa only [hz, zero_mul] using he
    exact zero_ne_one this
  have hcompare (z : K) : v (e * z) < 1 ↔ v z < α := by
    rw [map_mul, ← he, mul_lt_mul_iff_right₀ hep]
  constructor
  · intro h a ha
    have hc0 (i : Fin n) : c i ≠ 0 := by
      intro hz
      exact ht i ((hc i).symm.trans (hz ▸ RVCalc.rv_zero))
    let y : Fin n → K := fun i => a i / c i
    have hcy : (fun i => c i * y i) = a := by
      funext i
      exact mul_div_cancel₀ (a i) (hc0 i)
    have hy : y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) :=
      (rvFibre_scale_iff v ht hc y).mp (by rw [hcy]; exact ha)
    have hh := h y hy
    rw [hG, hcy] at hh
    exact (hcompare _).mp hh
  · intro h y hy
    rw [hG]
    exact (hcompare _).mpr (h _ ((rvFibre_scale_iff v ht hc y).mpr hy))

theorem jacobian_normalizingFactor_value (v : Valuation K Γ) {n : ℕ}
    {γ α : Fin n → Γ} {c e : Fin n → K}
    (hγ : ∀ i, γ i ≠ 0) (hc : ∀ i, v (c i) = γ i)
    (he : ∀ i, v (e i) * α i = 1) :
    v (∏ i, e i * c i) * jacobianValue γ α = 1 := by
  have hE : (∏ i, v (e i)) * (∏ i, α i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp only [he, Finset.prod_const_one]
  have hΓ : (∏ i, γ i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hγ i
  rw [map_prod]
  simp only [map_mul, hc]
  rw [Finset.prod_mul_distrib, jacobianValue, div_eq_mul_inv]
  calc
    _ = ((∏ i, v (e i)) * (∏ i, α i)) * ((∏ i, γ i) * (∏ i, γ i)⁻¹) := by ac_rfl
    _ = 1 := by rw [hE, mul_inv_cancel₀ hΓ, one_mul]

theorem jacobian_residueRoot_normalize_iff (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ i, t i ≠ none)
    {α : Fin n → Γ} {F : Fin n → MvPolynomial (Fin n) K}
    (hF : ∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) (α i) (F i))
    {c e : Fin n → K} (hc : c ∈ RVFibre v t) (he : ∀ i, v (e i) * α i = 1) :
    IsResidueRoot v (fun _ => RVCalc.rv v (1 : K)) 1
        (jacobianPolynomial (fun i => normalizePolynomial c (e i) (F i))) ↔
      IsResidueRoot v t (jacobianValue (fun j => RVCalc.vrv v (t j)) α)
        (jacobianPolynomial F) := by
  exact residueRoot_scaled_evaluations_iff v ht hc
    (jacobian_normalizingFactor_value v (fun i => (hF i).1 i) (rvFibre_value v hc) he)
    (jacobianPolynomial_eval_normalize F c e)

theorem IsSimpleCommonResidueRoot.normalize (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} {α : Fin n → Γ}
    {F : Fin n → MvPolynomial (Fin n) K} (h : IsSimpleCommonResidueRoot v t α F)
    {c e : Fin n → K} (hc : c ∈ RVFibre v t) (he : ∀ i, v (e i) * α i = 1) :
    IsSimpleCommonResidueRoot v (fun _ => RVCalc.rv v (1 : K)) (fun _ => 1)
      (fun i => normalizePolynomial c (e i) (F i)) := by
  refine ⟨fun _ => RVCalc.rv_ne_none one_ne_zero, ?_, ?_, ?_⟩
  · intro i
    simpa only [RVCalc.vrv_rv, map_one] using
      normalizePolynomial_isGamma v (h.2.1 i) c (e i) (rvFibre_value v hc) (he i)
  · intro i
    exact (residueRoot_scaled_evaluations_iff v h.1 hc (he i)
      (eval_normalizePolynomial c (e i) (F i))).mpr (h.2.2.1 i)
  · have hn := (not_congr (jacobian_residueRoot_normalize_iff v h.1 h.2.1 hc he)).mpr h.2.2.2
    simpa only [jacobianValue, RVCalc.vrv_rv, map_one, Finset.prod_const_one, div_self one_ne_zero]
      using hn

theorem simpleRoot_normalization_iff (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ i, t i ≠ none)
    {α : Fin n → Γ} {F : Fin n → MvPolynomial (Fin n) K}
    (hF : ∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) (α i) (F i))
    {c e : Fin n → K} (hc : c ∈ RVFibre v t) (he : ∀ i, v (e i) * α i = 1) :
    IsSimpleCommonResidueRoot v (fun _ => RVCalc.rv v (1 : K)) (fun _ => 1)
        (fun i => normalizePolynomial c (e i) (F i)) ↔
      IsSimpleCommonResidueRoot v t α F := by
  constructor
  · intro hs
    refine ⟨ht, hF, ?_, ?_⟩
    · intro i
      exact (residueRoot_scaled_evaluations_iff v ht hc (he i)
        (eval_normalizePolynomial c (e i) (F i))).mp (hs.2.2.1 i)
    · have hn : ¬ IsResidueRoot v (fun _ => RVCalc.rv v (1 : K)) 1
          (jacobianPolynomial (fun i => normalizePolynomial c (e i) (F i))) := by
        simpa only [jacobianValue, RVCalc.vrv_rv, map_one, Finset.prod_const_one,
          div_self one_ne_zero] using hs.2.2.2
      exact (not_congr (jacobian_residueRoot_normalize_iff v ht hF hc he)).mp hn
  · intro hs
    exact hs.normalize v hc he

/-- The paper's displayed conclusion: the normalized Jacobian has value one
at every representative of the unit RV tuple. -/
theorem IsSimpleCommonResidueRoot.normalized_jacobian_value (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} {α : Fin n → Γ}
    {F : Fin n → MvPolynomial (Fin n) K} (h : IsSimpleCommonResidueRoot v t α F)
    {c e : Fin n → K} (hc : c ∈ RVFibre v t) (he : ∀ i, v (e i) * α i = 1)
    {y : Fin n → K} (hy : y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K))) :
    v ((jacobianPolynomial (fun i => normalizePolynomial c (e i) (F i))).eval y) = 1 := by
  have hv := (h.normalize v hc he).jacobian_eval_value v hy
  simpa only [jacobianValue, RVCalc.vrv_rv, map_one, Finset.prod_const_one, div_self one_ne_zero]
    using hv

theorem normalization_solution_iff (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ i, t i ≠ none)
    {F : Fin n → MvPolynomial (Fin n) K} {c e : Fin n → K}
    (hc : c ∈ RVFibre v t) (he : ∀ i, e i ≠ 0) (y : Fin n → K) :
    (y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) ∧
        ∀ i, (normalizePolynomial c (e i) (F i)).eval y = 0) ↔
      ((fun i => c i * y i) ∈ RVFibre v t ∧
        ∀ i, (F i).eval (fun j => c j * y j) = 0) := by
  rw [rvFibre_scale_iff v ht hc]
  simp only [eval_normalizePolynomial, mul_eq_zero, he, false_or]

/-- Common representatives and all row scalars exist inside the valued field.
The Jacobian value and both directions of simple-root transport are proved
above. No normalized Hensel property is an input to this theorem. -/
theorem exists_simpleRoot_normalization (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} {α : Fin n → Γ}
    {F : Fin n → MvPolynomial (Fin n) K} (h : IsSimpleCommonResidueRoot v t α F) :
    ∃ c e : Fin n → K, c ∈ RVFibre v t ∧ (∀ i, v (e i) * α i = 1) ∧
      IsSimpleCommonResidueRoot v (fun _ => RVCalc.rv v (1 : K)) (fun _ => 1)
        (fun i => normalizePolynomial c (e i) (F i)) ∧
      (∀ y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)),
        v ((jacobianPolynomial (fun i => normalizePolynomial c (e i) (F i))).eval y) = 1) ∧
      (∀ y, (y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) ∧
          ∀ i, (normalizePolynomial c (e i) (F i)).eval y = 0) ↔
        ((fun i => c i * y i) ∈ RVFibre v t ∧
          ∀ i, (F i).eval (fun j => c j * y j) = 0)) := by
  classical
  obtain ⟨c, hc⟩ := rvFibre_nonempty v t
  have hs (i : Fin n) : ∃ e : K, v e * α i = 1 :=
    gammaPolynomial_normalizingScalar_exists v (h.2.1 i) (h.polynomial_ne_zero v i)
      c (rvFibre_value v hc)
  choose e he using hs
  have he0 (i : Fin n) : e i ≠ 0 := by
    intro hz
    have hh := he i
    rw [hz, map_zero, zero_mul] at hh
    exact zero_ne_one hh
  exact ⟨c, e, hc, he, h.normalize v hc he,
    fun _ hy => h.normalized_jacobian_value v hc he hy,
    normalization_solution_iff v h.1 hc he0⟩

end SpecialTransformations.Section7
