module

public import Section7.GammaPolynomialAlgebra

@[expose] public section

/-!
# Clearing Laurent exponents over the original coefficient field

The guarded RV normal form uses integer exponents. A common monomial
shift makes any finite family of those exponents nonnegative, and is
nonzero on the nonzero-coordinate fibre. The resulting genuine polynomial
has coefficients in the original subfield and the prescribed shifted
weight. Neither the shift nor the construction names field representatives
of the input RV coordinates as coefficients.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

theorem exists_clearLaurentExponents {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → Fin n → ℤ) :
    ∃ (d : Fin n →₀ ℕ) (k : ι → Fin n →₀ ℕ),
      ∀ j i, (k j i : ℤ) = m j i + (d i : ℤ) := by
  classical
  let d : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => ∑ j, (-m j i).toNat)
  let k : ι → Fin n →₀ ℕ := fun j =>
    Finsupp.equivFunOnFinite.symm (fun i => (m j i + (d i : ℤ)).toNat)
  refine ⟨d, k, ?_⟩
  intro j i
  have hd : (-m j i).toNat ≤ d i := by
    simpa [d] using (Finset.single_le_sum (f := fun j => (-m j i).toNat)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ j))
  have hnonneg : 0 ≤ m j i + (d i : ℤ) := by omega
  simpa [k] using (Int.toNat_of_nonneg hnonneg)

theorem prod_shiftedLaurent_pow {G : Type*} [CommGroupWithZero G] {n : ℕ}
    (x : Fin n → G) (hx : ∀ i, x i ≠ 0) {d k : Fin n →₀ ℕ} {m : Fin n → ℤ}
    (hk : ∀ i, (k i : ℤ) = m i + (d i : ℤ)) :
    (∏ i, x i ^ k i) = (∏ i, x i ^ m i) * (∏ i, x i ^ d i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  calc
    x i ^ k i = x i ^ (k i : ℤ) := (zpow_natCast _ _).symm
    _ = x i ^ m i * x i ^ d i := by rw [hk, zpow_add₀ (hx i), zpow_natCast]

/-- A common exponent shift clears a weighted Laurent sum without changing
its coefficient field. The shift may be chosen across several such sums by
applying `exists_clearLaurentExponents` to their joint finite index. -/
theorem gammaPolynomial_of_shiftedLaurent {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (E : Subfield K)
    {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → E) (m : ι → Fin n → ℤ)
    (d : Fin n →₀ ℕ) (k : ι → Fin n →₀ ℕ)
    (hk : ∀ j i, (k j i : ℤ) = m j i + (d i : ℤ))
    {γ : Fin n → Γ} {α : Γ} (hγ : ∀ i, γ i ≠ 0) (hα : α ≠ 0)
    (hw : ∀ j, v (a j : K) * (∏ i, γ i ^ m j i) = α) :
    ∃ P : MvPolynomial (Fin n) E,
      IsGammaPolynomial v γ (α * ∏ i, γ i ^ d i) (P.map E.subtype) ∧
      ∀ x : Fin n → K, (∀ i, x i ≠ 0) →
        (P.map E.subtype).eval x =
          (∑ j, (a j : K) * ∏ i, x i ^ m j i) * (∏ i, x i ^ d i) := by
  classical
  let P := ∑ j, monomial (k j) (a j)
  have hmap : P.map E.subtype = ∑ j, monomial (k j) (a j : K) := by
    simp [P, map_sum, map_monomial]
  refine ⟨P, ?_, ?_⟩
  · rw [hmap]
    have hshift : (∏ i, γ i ^ d i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hγ i))
    apply isGammaPolynomial_ofFamily v hγ (mul_ne_zero hα hshift) (fun j => (a j : K)) k
    intro j
    rw [prod_shiftedLaurent_pow γ hγ (hk j), ← mul_assoc, hw j]
  · intro x hx
    rw [hmap, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_monomial]
    have hp : (k j).prod (fun i e => x i ^ e) = ∏ i, x i ^ k j i := by
      rw [Finsupp.prod_fintype]
      intro i
      simp
    rw [hp, prod_shiftedLaurent_pow x hx (hk j), mul_assoc]

end SpecialTransformations.Section7
