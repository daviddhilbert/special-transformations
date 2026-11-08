import RVClassEquality
import RVValueMap
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FinCases

/-!
# Definition 7.1: finite monomial presentations and residue roots

Yin, arXiv:1006.2467v1, Definition 7.1. A presentation retains the extra
index `j` in the paper's coefficients: several summands can have the same
exponent. Collecting them can lower their Mathlib valuation. Consequently
equal weighted values are imposed on the presented summands, not on the
collected coefficients of `MvPolynomial`.

The elementary power/product estimates are adapted from this repository's
`Section7/Sec7Gamma.lean` (Yimu Yin, MIT). RV, rv and vrv are imported from
the pinned ACVF-QE release; no replacement language or RV quotient is defined.
Paper `vv(F(a)) > alpha` means `v (F.eval a) < alpha` here.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- A finite sum before collecting equal exponents. Empty sums are allowed. -/
structure PolynomialPresentation (n : ℕ) (K : Type*) where
  length : ℕ
  coefficient : Fin length → K
  exponent : Fin length → (Fin n →₀ ℕ)

namespace PolynomialPresentation

noncomputable def polynomial {n : ℕ} (P : PolynomialPresentation n K) :
    MvPolynomial (Fin n) K :=
  ∑ j, monomial (P.exponent j) (P.coefficient j)

/-- All presented terms have the specified finite residue value. -/
def Homogeneous (v : Valuation K Γ) {n : ℕ} (γ : Fin n → Γ) (α : Γ)
    (P : PolynomialPresentation n K) : Prop :=
  ∀ j, v (P.coefficient j) * ∏ i, γ i ^ (P.exponent j i) = α

theorem eval_polynomial {n : ℕ} (P : PolynomialPresentation n K) (a : Fin n → K) :
    P.polynomial.eval a = ∑ j, P.coefficient j * ∏ i, a i ^ (P.exponent j i) := by
  classical
  simp only [polynomial, eval_sum, eval_monomial]
  congr 1
  funext j
  rw [Finsupp.prod_fintype]
  intro i
  simp

end PolynomialPresentation

/-- Definition 7.1 with the paper's finite-value requirement explicit. -/
def IsGammaPolynomial (v : Valuation K Γ) {n : ℕ} (γ : Fin n → Γ)
    (α : Γ) (F : MvPolynomial (Fin n) K) : Prop :=
  (∀ i, γ i ≠ 0) ∧ α ≠ 0 ∧
    ∃ P : PolynomialPresentation n K, P.polynomial = F ∧ P.Homogeneous v γ α

/-- The actual leading-term fibre, rather than a value-group fibre. -/
def RVFibre (v : Valuation K Γ) {n : ℕ} (t : Fin n → RVCalc.RV v) :
    Set (Fin n → K) := {a | ∀ i, RVCalc.rv v (a i) = t i}

/-- The universal formulation; `residueRoot_iff_exists` proves "some (hence all)". -/
def IsResidueRoot (v : Valuation K Γ) {n : ℕ} (t : Fin n → RVCalc.RV v)
    (α : Γ) (F : MvPolynomial (Fin n) K) : Prop :=
  ∀ a ∈ RVFibre v t, v (F.eval a) < α

theorem rvFibre_nonempty (v : Valuation K Γ) {n : ℕ} (t : Fin n → RVCalc.RV v) :
    (RVFibre v t).Nonempty := by
  classical
  have h (i : Fin n) : ∃ x : K, RVCalc.rv v x = t i := by
    cases hti : t i with
    | none => exact ⟨0, RVCalc.rv_zero⟩
    | some u =>
      obtain ⟨x, _, hx⟩ := RVCalc.rv_surjective v u
      exact ⟨x, hx⟩
  choose a ha using h
  exact ⟨a, ha⟩

theorem rvFibre_value (v : Valuation K Γ) {n : ℕ} {t : Fin n → RVCalc.RV v}
    {a : Fin n → K} (ha : a ∈ RVFibre v t) (i : Fin n) :
    v (a i) = RVCalc.vrv v (t i) := by
  rw [← ha i, RVCalc.vrv_rv]

theorem rvFibre_close (v : Valuation K Γ) {n : ℕ} {t : Fin n → RVCalc.RV v}
    (ht : ∀ i, t i ≠ none) {a b : Fin n → K}
    (ha : a ∈ RVFibre v t) (hb : b ∈ RVFibre v t) (i : Fin n) :
    v (a i - b i) < RVCalc.vrv v (t i) := by
  have ha0 : a i ≠ 0 := fun h => ht i ((ha i).symm.trans (h ▸ RVCalc.rv_zero))
  have hb0 : b i ≠ 0 := fun h => ht i ((hb i).symm.trans (h ▸ RVCalc.rv_zero))
  have h := (RVCalc.rv_eq_iff ha0 hb0).mp ((ha i).trans (hb i).symm)
  rwa [rvFibre_value v ha i] at h

/-! Elementary estimates, adapted from the legacy source cited above. -/

theorem valuation_pow_sub_pow_lt (v : Valuation K Γ) {x y : K} {γ : Γ}
    (hx : v x = γ) (hy : v y = γ) (hxy : v (x - y) < γ) (k : ℕ) :
    v (x ^ k - y ^ k) < γ ^ k := by
  have hγ : 0 < γ := lt_of_le_of_lt zero_le hxy
  induction k with
  | zero => simpa using zero_lt_one (α := Γ)
  | succ k ih =>
    have hd : x ^ (k + 1) - y ^ (k + 1) =
        (x ^ k - y ^ k) * x + y ^ k * (x - y) := by ring
    rw [hd, pow_succ]
    refine v.map_add_lt ?_ ?_
    · rw [map_mul, hx]
      exact mul_lt_mul_of_pos_right ih hγ
    · rw [map_mul, map_pow, hy]
      exact mul_lt_mul_of_pos_left hxy (pow_pos hγ k)

theorem valuation_prod_pow_sub_lt (v : Valuation K Γ) {ι : Type*} {s : Finset ι}
    {a b : ι → K} {γ : ι → Γ} (m : ι → ℕ)
    (ha : ∀ i ∈ s, v (a i) = γ i) (hb : ∀ i ∈ s, v (b i) = γ i)
    (hab : ∀ i ∈ s, v (a i - b i) < γ i) :
    v ((∏ i ∈ s, a i ^ m i) - ∏ i ∈ s, b i ^ m i) < ∏ i ∈ s, γ i ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_lt_one (α := Γ)
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx]
    have hd : a x ^ m x * ∏ i ∈ s, a i ^ m i - b x ^ m x * ∏ i ∈ s, b i ^ m i =
        a x ^ m x * ((∏ i ∈ s, a i ^ m i) - ∏ i ∈ s, b i ^ m i) +
          (a x ^ m x - b x ^ m x) * ∏ i ∈ s, b i ^ m i := by ring
    rw [hd]
    have hpos : 0 < γ x := lt_of_le_of_lt zero_le (hab x (Finset.mem_insert_self x s))
    refine v.map_add_lt ?_ ?_
    · rw [map_mul, map_pow, ha x (Finset.mem_insert_self x s)]
      exact mul_lt_mul_of_pos_left
        (ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
          (fun i hi => hb i (Finset.mem_insert_of_mem hi))
          (fun i hi => hab i (Finset.mem_insert_of_mem hi))) (pow_pos hpos _)
    · rw [map_mul, map_prod]
      have he : (∏ i ∈ s, v (b i ^ m i)) = ∏ i ∈ s, γ i ^ m i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [map_pow, hb i (Finset.mem_insert_of_mem hi)]
      rw [he]
      exact mul_lt_mul_of_pos_right
        (valuation_pow_sub_pow_lt v (ha x (Finset.mem_insert_self x s))
          (hb x (Finset.mem_insert_self x s)) (hab x (Finset.mem_insert_self x s)) _)
        (Finset.prod_pos fun i hi =>
          pow_pos (lt_of_le_of_lt zero_le (hab i (Finset.mem_insert_of_mem hi))) _)

theorem gammaPolynomial_eval_le (v : Valuation K Γ) {n : ℕ} {γ : Fin n → Γ}
    {α : Γ} {F : MvPolynomial (Fin n) K} (hF : IsGammaPolynomial v γ α F)
    {a : Fin n → K} (ha : ∀ i, v (a i) = γ i) : v (F.eval a) ≤ α := by
  obtain ⟨_, _, P, rfl, hP⟩ := hF
  rw [P.eval_polynomial]
  refine v.map_sum_le ?_
  intro j _
  rw [map_mul, map_prod]
  have he : (∏ i, v (a i ^ P.exponent j i)) = ∏ i, γ i ^ P.exponent j i := by
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow, ha i]
  rw [he, hP j]

theorem gammaPolynomial_eval_sub_lt (v : Valuation K Γ) {n : ℕ} {γ : Fin n → Γ}
    {α : Γ} {F : MvPolynomial (Fin n) K} (hF : IsGammaPolynomial v γ α F)
    {a b : Fin n → K} (ha : ∀ i, v (a i) = γ i) (hb : ∀ i, v (b i) = γ i)
    (hab : ∀ i, v (a i - b i) < γ i) : v (F.eval a - F.eval b) < α := by
  obtain ⟨_, hα, P, rfl, hP⟩ := hF
  rw [P.eval_polynomial, P.eval_polynomial, ← Finset.sum_sub_distrib]
  refine v.map_sum_lt hα ?_
  intro j _
  have hc : 0 < v (P.coefficient j) := by
    apply lt_of_le_of_ne zero_le
    intro hz
    exact hα ((hP j).symm.trans (by rw [← hz, zero_mul]))
  rw [← mul_sub, map_mul]
  exact (mul_lt_mul_of_pos_left
    (valuation_prod_pow_sub_lt v (P.exponent j) (fun i _ => ha i)
      (fun i _ => hb i) (fun i _ => hab i)) hc).trans_eq (hP j)

/-- Definition 7.1's "some (hence all)", on the released RV quotient. -/
theorem residueRoot_iff_exists (v : Valuation K Γ) {n : ℕ} {t : Fin n → RVCalc.RV v}
    (ht : ∀ i, t i ≠ none) {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v (fun i => RVCalc.vrv v (t i)) α F) :
    IsResidueRoot v t α F ↔ ∃ a ∈ RVFibre v t, v (F.eval a) < α := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := rvFibre_nonempty v t
    exact ⟨a, ha, h a ha⟩
  · rintro ⟨a, ha, hroot⟩ b hb
    have hdiff := gammaPolynomial_eval_sub_lt v hF
      (rvFibre_value v hb) (rvFibre_value v ha) (rvFibre_close v ht hb ha)
    have he : F.eval b = (F.eval b - F.eval a) + F.eval a := by ring
    rw [he]
    exact v.map_add_lt hdiff hroot

end SpecialTransformations.Section7
