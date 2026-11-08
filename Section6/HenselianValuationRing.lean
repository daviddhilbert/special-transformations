import Section6.HenselScheme
import Section7.MultivariateHensel

/-! Identification of the simple-root scheme with the ordinary henselian
condition on the valuation ring. The arbitrary-polynomial direction uses
the one-variable case of the checked étale lifting theorem. -/

noncomputable section
open Polynomial IsLocalRing

namespace SpecialTransformations.Section6.HenselianTheory

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)

private theorem unit_iff_value_one (a : v.valuationSubring) :
    IsUnit a ↔ v a = 1 := by
  have ha := (Valuation.mem_valuationSubring_iff v (a : K)).mp a.property
  have hn : ¬ IsUnit a ↔ v a < 1 := Valuation.mem_maximalIdeal_iff K v
  rw [← not_not (a := IsUnit a), hn, not_lt]
  exact ⟨le_antisymm ha, Eq.ge⟩

theorem coefficientPolynomial_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (c : Fin (n + 1) → R) :
    (coefficientPolynomial c).map f = coefficientPolynomial (f ∘ c) := by
  simp [coefficientPolynomial, Polynomial.map_sum]

private theorem coefficientPolynomial_coeff {R : Type} [CommRing R] (p : R[X]) :
    coefficientPolynomial (fun i : Fin (p.natDegree + 1) => p.coeff i.val) = p := by
  rw [coefficientPolynomial, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
  exact p.as_sum_range_C_mul_X_pow.symm

theorem valuationRing_henselian (h : ∀ n, SimpleRootLiftAt v n) :
    HenselianLocalRing v.valuationSubring := by
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f _ a ha hunit
  let ι : v.valuationSubring →+* K := v.valuationSubring.subtype
  let c (i : Fin (f.natDegree + 1)) := f.coeff i.val
  have hc : coefficientPolynomial (ι ∘ c) = f.map ι := by
    rw [← coefficientPolynomial_map, coefficientPolynomial_coeff]
  obtain ⟨b, hb, hroot, hclose⟩ := h f.natDegree (ι ∘ c) (a : K)
    (fun i => (Valuation.mem_valuationSubring_iff v _).mp (c i).property)
    ((Valuation.mem_valuationSubring_iff v _).mp a.property)
    (by
      rw [hc]
      change v ((f.map ι).eval (ι a)) < 1
      rw [Polynomial.eval_map_apply]
      exact (Valuation.mem_maximalIdeal_iff K v).mp ha)
    (by
      rw [hc, Polynomial.derivative_map]
      change v ((f.derivative.map ι).eval (ι a)) = 1
      rw [Polynomial.eval_map_apply]
      exact (unit_iff_value_one v _).mp hunit)
  let b' : v.valuationSubring := ⟨b, (Valuation.mem_valuationSubring_iff v _).mpr hb⟩
  refine ⟨b', ?_, (Valuation.mem_maximalIdeal_iff K v).mpr hclose⟩
  change f.eval b' = 0
  apply (show Function.Injective ι from Subtype.val_injective)
  rw [map_zero, ← Polynomial.eval_map_apply]
  rwa [hc] at hroot

private theorem simpleRoot_polynomial {R : Type} [CommRing R] [HenselianLocalRing R]
    {n : ℕ} (c : Fin (n + 1) → R) (a : R)
    (ha : (coefficientPolynomial c).eval a ∈ maximalIdeal R)
    (hunit : IsUnit ((coefficientPolynomial c).derivative.eval a)) :
    ∃ b : R, (coefficientPolynomial c).eval b = 0 ∧ b - a ∈ maximalIdeal R := by
  let F : Fin 1 → MvPolynomial (Fin 1) R := fun _ =>
    ∑ i, MvPolynomial.C (c i) * (MvPolynomial.X 0) ^ i.val
  have heval (z : Fin 1 → R) (i : Fin 1) : (F i).eval z =
      (coefficientPolynomial c).eval (z 0) := by
    rw [coefficientPolynomial_eval]
    simp [F]
  have hderiv : (Section7.jacobianPolynomial F).eval (fun _ => a) =
      (coefficientPolynomial c).derivative.eval a := by
    rw [Section7.jacobianPolynomial, Matrix.det_fin_one, coefficientPolynomial_derivative_eval]
    simp only [Section7.jacobianMatrix, Matrix.of_apply, F, map_sum,
      MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self,
      mul_one, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_pow, map_natCast]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  obtain ⟨b, hroot, hclose⟩ :=
    Section7.multivariate_simpleRoot_exists F (fun _ => a)
      (fun i => (heval _ i).symm ▸ ha) (hderiv.symm ▸ hunit)
  exact ⟨b 0, (heval b 0).symm ▸ hroot 0, hclose 0⟩

theorem simpleRootLiftAt [HenselianLocalRing v.valuationSubring] (n : ℕ) :
    SimpleRootLiftAt v n := by
  intro c a hc ha hsmall hunit
  let ι : v.valuationSubring →+* K := v.valuationSubring.subtype
  let c' (i : Fin (n + 1)) : v.valuationSubring :=
    ⟨c i, (Valuation.mem_valuationSubring_iff v _).mpr (hc i)⟩
  let a' : v.valuationSubring := ⟨a, (Valuation.mem_valuationSubring_iff v _).mpr ha⟩
  have hmap : (coefficientPolynomial c').map ι = coefficientPolynomial c :=
    coefficientPolynomial_map ι c'
  obtain ⟨b, hroot, hclose⟩ := simpleRoot_polynomial c' a'
    (by
      apply (Valuation.mem_maximalIdeal_iff K v).mpr
      change v (ι ((coefficientPolynomial c').eval a')) < 1
      rwa [← Polynomial.eval_map_apply, hmap])
    (by
      apply (unit_iff_value_one v _).mpr
      change v (ι ((coefficientPolynomial c').derivative.eval a')) = 1
      rwa [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hmap])
  refine ⟨b, (Valuation.mem_valuationSubring_iff v _).mp b.property, ?_,
    (Valuation.mem_maximalIdeal_iff K v).mp hclose⟩
  rw [← hmap]
  change ((coefficientPolynomial c').map ι).eval (ι b) = 0
  rw [Polynomial.eval_map_apply, hroot, map_zero]

theorem henselian_of_compatible_equiv {L Δ : Type} [Field L]
    [LinearOrderedCommGroupWithZero Δ] (w : Valuation L Δ) (e : K ≃+* L)
    (he : ∀ x y, w (e x) ≤ w (e y) ↔ v x ≤ v y)
    [HenselianLocalRing v.valuationSubring] : HenselianLocalRing w.valuationSubring := by
  apply valuationRing_henselian w
  intro n c a hc ha hf hderiv
  let d := e.symm ∘ c
  let b := e.symm a
  have hmap : (coefficientPolynomial d).map e.toRingHom = coefficientPolynomial c := by
    rw [coefficientPolynomial_map]
    exact congrArg coefficientPolynomial (funext fun i => e.apply_symm_apply (c i))
  have hval (x : K) : w (e x) ≤ 1 ↔ v x ≤ 1 := by
    simpa only [map_one] using he x 1
  have hsmall (x : K) : w (e x) < 1 ↔ v x < 1 := by
    simpa only [map_one, not_le] using (he 1 x).not
  have hunit (x : K) : w (e x) = 1 ↔ v x = 1 := by
    simpa only [map_one, le_antisymm_iff] using and_congr (he x 1) (he 1 x)
  have hce (i) : e (d i) = c i := e.apply_symm_apply _
  have hab : e.toRingHom b = a := e.apply_symm_apply _
  obtain ⟨y, hy, hroot, hclose⟩ := simpleRootLiftAt v n d b
    (fun i => (hval _).mp (hce i ▸ hc i)) ((hval _).mp (hab ▸ ha))
    (by
      apply (hsmall _).mp
      change w (e.toRingHom _) < 1
      rw [← Polynomial.eval_map_apply, hmap, hab]
      exact hf)
    (by
      apply (hunit _).mp
      change w (e.toRingHom _) = 1
      rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hmap, hab]
      exact hderiv)
  refine ⟨e y, (hval _).mpr hy, ?_, ?_⟩
  · rw [← hmap]
    change ((coefficientPolynomial d).map e.toRingHom).eval (e.toRingHom y) = 0
    rw [Polynomial.eval_map_apply, hroot, map_zero]
  · rw [← (show e b = a from hab), ← map_sub]
    exact (hsmall _).mpr hclose

end SpecialTransformations.Section6.HenselianTheory
