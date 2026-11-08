import Section7.IntegralNormalization
import Section7.MultivariateHensel
import Section7.ValuationHenselian

/-! Lemma 7.2 over an algebraically closed valued field, using the actual
valuation ring, proved ordinary multivariate Hensel lifting, and the proved
RV/Jacobian bridge. No normalized-Hensel, rank-one or completeness premise
is assumed. -/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem rv_eq_one_iff_sub_lt_one (v : Valuation K Γ) (x : K) :
    RVCalc.rv v x = RVCalc.rv v (1 : K) ↔ v (x - 1) < 1 := by
  by_cases hx : x = 0
  · subst x
    apply iff_of_false
    · intro h
      exact RVCalc.rv_ne_none one_ne_zero (h.symm.trans RVCalc.rv_zero)
    · simp [Valuation.map_neg]
  · rw [eq_comm, RVCalc.rv_eq_iff one_ne_zero hx, map_one,
      show (1 : K) - x = -(x - 1) by ring, Valuation.map_neg v]

theorem integer_unitFibre_iff (v : Valuation K Γ) {n : ℕ}
    (a : Fin n → v.valuationSubring) :
    (fun i => (a i : K)) ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) ↔
      ∀ i, a i - 1 ∈ maximalIdeal v.valuationSubring := by
  apply forall_congr'
  intro i
  rw [rv_eq_one_iff_sub_lt_one, Valuation.mem_maximalIdeal_iff K v]
  rfl

/-- Lemma 7.2: a simple common residue root has exactly one simultaneous
field zero in its actual RV fibre. Arbitrary finite arity includes zero. -/
theorem generalized_hensel [IsAlgClosed K] (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} {α : Fin n → Γ}
    {F : Fin n → MvPolynomial (Fin n) K} (h : IsSimpleCommonResidueRoot v t α F) :
    ∃! a : Fin n → K, a ∈ RVFibre v t ∧ ∀ i, (F i).eval a = 0 := by
  classical
  letI : HenselianLocalRing v.valuationSubring := valuationRing_henselian v
  obtain ⟨c, e, H, hc, he, hH, hsmall, hJ, hsol⟩ := exists_integral_simpleRoot_normalization v h
  obtain ⟨b, hb, huniq⟩ := multivariate_simpleRoot_lift H (fun _ => 1) hsmall hJ
  let ι : v.valuationSubring →+* K := v.valuationSubring.subtype
  have heval (a : Fin n → v.valuationSubring) (i : Fin n) :
      (normalizePolynomial c (e i) (F i)).eval (fun j => (a j : K)) =
        ι ((H i).eval a) := by
    rw [← hH i]
    exact (MvPolynomial.map_eval ι a (H i)).symm
  let y : Fin n → K := fun i => (b i : K)
  have hy : y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) :=
    (integer_unitFibre_iff v b).mpr hb.2
  have hzero (i : Fin n) : (normalizePolynomial c (e i) (F i)).eval y = 0 := by
    rw [heval, hb.1 i, map_zero]
  have hx := (hsol y).mp ⟨hy, hzero⟩
  refine ⟨fun i => c i * y i, hx, ?_⟩
  intro a ha
  have hc0 (i : Fin n) : c i ≠ 0 := by
    intro hz
    exact h.1 i ((hc i).symm.trans (hz ▸ RVCalc.rv_zero))
  let z : Fin n → K := fun i => a i / c i
  have hcz : (fun i => c i * z i) = a := by
    funext i
    exact mul_div_cancel₀ (a i) (hc0 i)
  have hz : z ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) ∧
      ∀ i, (normalizePolynomial c (e i) (F i)).eval z = 0 :=
    (hsol z).mpr (by rw [hcz]; exact ha)
  have hzval (i : Fin n) : v (z i) = 1 := by
    simpa only [RVCalc.vrv_rv, map_one] using rvFibre_value v hz.1 i
  let zO : Fin n → v.valuationSubring := fun i =>
    ⟨z i, (Valuation.mem_valuationSubring_iff v _).mpr (hzval i).le⟩
  have hzOzero (i : Fin n) : (H i).eval zO = 0 := by
    apply (show Function.Injective ι from Subtype.val_injective)
    change ι ((H i).eval zO) = 0
    rw [← heval]
    exact hz.2 i
  have hzOcongr : ∀ i, zO i - 1 ∈ maximalIdeal v.valuationSubring :=
    (integer_unitFibre_iff v zO).mp hz.1
  have hzb : zO = b := huniq zO ⟨hzOzero, hzOcongr⟩
  funext i
  calc
    a i = c i * z i := (congrFun hcz i).symm
    _ = c i * (zO i : K) := rfl
    _ = c i * (b i : K) := by rw [hzb]
    _ = c i * y i := rfl

end SpecialTransformations.Section7
