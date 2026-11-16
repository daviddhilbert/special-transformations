module

public import Section7.GammaPolynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-!
# Algebra of finite gamma-polynomial presentations

The paper's repeated summand index matters for derivatives: `m * a` is
represented by `m` copies of `a`, even when their sum has smaller valuation
or vanishes. Thus no assertion that nonzero integers have valuation one is
needed. All predicates use the released RV and the existing presentations.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

namespace PolynomialPresentation

noncomputable def ofFamily {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → K) (d : ι → Fin n →₀ ℕ) : PolynomialPresentation n K where
  length := Fintype.card ι
  coefficient j := a ((Fintype.equivFin ι).symm j)
  exponent j := d ((Fintype.equivFin ι).symm j)

theorem polynomial_ofFamily {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → K) (d : ι → Fin n →₀ ℕ) :
    (ofFamily a d).polynomial = ∑ j, monomial (d j) (a j) := by
  classical
  exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun j => monomial (d j) (a j))

end PolynomialPresentation

theorem isGammaPolynomial_ofFamily (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} (hγ : ∀ i, γ i ≠ 0) (hα : α ≠ 0)
    {ι : Type*} [Fintype ι] (a : ι → K) (d : ι → Fin n →₀ ℕ)
    (h : ∀ j, v (a j) * ∏ i, γ i ^ (d j i) = α) :
    IsGammaPolynomial v γ α (∑ j, monomial (d j) (a j)) := by
  refine ⟨hγ, hα, PolynomialPresentation.ofFamily a d,
    PolynomialPresentation.polynomial_ofFamily a d, ?_⟩
  intro j
  exact h _

theorem isGammaPolynomial_zero (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} (hγ : ∀ i, γ i ≠ 0) (hα : α ≠ 0) :
    IsGammaPolynomial v γ α (0 : MvPolynomial (Fin n) K) := by
  simpa using isGammaPolynomial_ofFamily v hγ hα (fun j : Fin 0 => j.elim0)
    (fun j : Fin 0 => j.elim0) (fun j => j.elim0)

theorem isGammaPolynomial_monomial (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} (hγ : ∀ i, γ i ≠ 0) (hα : α ≠ 0)
    (d : Fin n →₀ ℕ) (a : K) (h : v a * ∏ i, γ i ^ d i = α) :
    IsGammaPolynomial v γ α (monomial d a) := by
  simpa using isGammaPolynomial_ofFamily v hγ hα (fun _ : Fin 1 => a)
    (fun _ : Fin 1 => d) (fun _ => h)

theorem IsGammaPolynomial.sum (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} (hγ : ∀ i, γ i ≠ 0) (hα : α ≠ 0)
    {ι : Type*} [Fintype ι] {F : ι → MvPolynomial (Fin n) K}
    (hF : ∀ i, IsGammaPolynomial v γ α (F i)) :
    IsGammaPolynomial v γ α (∑ i, F i) := by
  classical
  choose P hPF hP using fun i => (hF i).2.2
  have h := isGammaPolynomial_ofFamily v hγ hα
    (fun j : Σ i, Fin (P i).length => (P j.1).coefficient j.2)
    (fun j : Σ i, Fin (P i).length => (P j.1).exponent j.2)
    (fun j => hP j.1 j.2)
  rw [Fintype.sum_sigma] at h
  change IsGammaPolynomial v γ α (∑ i, (P i).polynomial) at h
  simpa only [hPF] using h

theorem IsGammaPolynomial.add (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {F G : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (hG : IsGammaPolynomial v γ α G) :
    IsGammaPolynomial v γ α (F + G) := by
  simpa using IsGammaPolynomial.sum v hF.1 hF.2.1
    (F := fun b : Bool => cond b F G) (by intro b; cases b <;> assumption)

theorem IsGammaPolynomial.nsmul (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (k : ℕ) :
    IsGammaPolynomial v γ α (k • F) := by
  induction k with
  | zero => simpa using isGammaPolynomial_zero v hF.1 hF.2.1
  | succ k hk => rw [succ_nsmul]; exact hk.add v hF

theorem IsGammaPolynomial.neg (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) : IsGammaPolynomial v γ α (-F) := by
  obtain ⟨hγ, hα, P, rfl, hP⟩ := hF
  have h := isGammaPolynomial_ofFamily v hγ hα (fun j => -P.coefficient j) P.exponent
    (by intro j; rw [Valuation.map_neg v]; exact hP j)
  simpa only [map_neg, Finset.sum_neg_distrib, PolynomialPresentation.polynomial] using h

theorem IsGammaPolynomial.mul (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α β : Γ} {F G : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (hG : IsGammaPolynomial v γ β G) :
    IsGammaPolynomial v γ (α * β) (F * G) := by
  classical
  obtain ⟨hγ, hα, P, rfl, hP⟩ := hF
  obtain ⟨_, hβ, Q, rfl, hQ⟩ := hG
  have h := isGammaPolynomial_ofFamily v hγ (mul_ne_zero hα hβ)
    (fun j : Fin P.length × Fin Q.length => P.coefficient j.1 * Q.coefficient j.2)
    (fun j : Fin P.length × Fin Q.length => P.exponent j.1 + Q.exponent j.2) (by
      intro j
      simp only [map_mul, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
      calc
        _ = (v (P.coefficient j.1) * ∏ i, γ i ^ P.exponent j.1 i) *
            (v (Q.coefficient j.2) * ∏ i, γ i ^ Q.exponent j.2 i) := by ac_rfl
        _ = α * β := by rw [hP, hQ])
  change IsGammaPolynomial v γ (α * β)
    ((∑ j, monomial (P.exponent j) (P.coefficient j)) *
      ∑ j, monomial (Q.exponent j) (Q.coefficient j))
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simpa only [Fintype.sum_prod_type, monomial_mul] using h

theorem isGammaPolynomial_one (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} (hγ : ∀ i, γ i ≠ 0) :
    IsGammaPolynomial v γ 1 (1 : MvPolynomial (Fin n) K) := by
  simpa using isGammaPolynomial_monomial v hγ one_ne_zero 0 (1 : K) (by simp)

theorem IsGammaPolynomial.prod (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} (hγ : ∀ i, γ i ≠ 0) {ι : Type*}
    (s : Finset ι) {α : ι → Γ} {F : ι → MvPolynomial (Fin n) K}
    (hF : ∀ i ∈ s, IsGammaPolynomial v γ (α i) (F i)) :
    IsGammaPolynomial v γ (∏ i ∈ s, α i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isGammaPolynomial_one v hγ
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (hF i (by simp)).mul v (ih (fun j hj => hF j (by simp [hj])))

theorem IsGammaPolynomial.pderiv (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (i : Fin n) :
    IsGammaPolynomial v γ (α / γ i) (pderiv i F) := by
  classical
  obtain ⟨hγ, hα, P, rfl, hP⟩ := hF
  have htarget : α / γ i ≠ 0 := div_ne_zero hα (hγ i)
  rw [PolynomialPresentation.polynomial, map_sum]
  apply IsGammaPolynomial.sum v hγ htarget
  intro j
  by_cases hd : P.exponent j i = 0
  · simpa [pderiv_monomial, hd] using isGammaPolynomial_zero v hγ htarget
  · have hle : Finsupp.single i 1 ≤ P.exponent j := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr hd
    have hsingle : (∏ k, γ k ^ (Finsupp.single i 1 : Fin n →₀ ℕ) k) = γ i := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro b _ hbi
        simp [hbi]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have hweights : (∏ k, γ k ^ (P.exponent j - Finsupp.single i 1 : Fin n →₀ ℕ) k) * γ i =
        ∏ k, γ k ^ P.exponent j k := by
      conv_rhs => rw [← tsub_add_cancel_of_le hle]
      simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
      rw [hsingle]
    have hterm : v (P.coefficient j) *
        ∏ k, γ k ^ (P.exponent j - Finsupp.single i 1 : Fin n →₀ ℕ) k = α / γ i := by
      apply (eq_div_iff (hγ i)).mpr
      rw [mul_assoc, hweights, hP j]
    have hmono := isGammaPolynomial_monomial v hγ htarget
      (P.exponent j - Finsupp.single i 1) (P.coefficient j) hterm
    rw [pderiv_monomial, show P.coefficient j * (P.exponent j i : K) =
      P.exponent j i • P.coefficient j by simp [nsmul_eq_mul, mul_comm], map_nsmul]
    exact hmono.nsmul v (P.exponent j i)

end SpecialTransformations.Section7
