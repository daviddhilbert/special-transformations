import Section7.GammaPolynomialAlgebra
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Weighted substitution of polynomial coordinates

Theorem 7.6 reindexes the original-base polynomials in a product tuple,
and specializes either block to representatives. Both operations preserve
the prescribed weight by substituting a polynomial of the matching weight
for each variable.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem isGammaPolynomial_C (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} (hγ : ∀ i, γ i ≠ 0) {b : K} (hb : v b ≠ 0) :
    IsGammaPolynomial v γ (v b) (C b) := by
  simpa only [← monomial_zero'] using
    isGammaPolynomial_monomial v hγ hb 0 b (by simp)

theorem isGammaPolynomial_X (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} (hγ : ∀ i, γ i ≠ 0) (i : Fin n) :
    IsGammaPolynomial v γ (γ i) (X i) := by
  classical
  rw [X]
  apply isGammaPolynomial_monomial v hγ (hγ i)
  rw [map_one, one_mul, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem IsGammaPolynomial.pow (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (k : ℕ) :
    IsGammaPolynomial v γ (α ^ k) (F ^ k) := by
  induction k with
  | zero => simpa using isGammaPolynomial_one v hF.1
  | succ k ih => simpa only [pow_succ] using ih.mul v hF

theorem IsGammaPolynomial.aeval (v : Valuation K Γ) {n m : ℕ}
    {γ : Fin n → Γ} {δ : Fin m → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (hδ : ∀ j, δ j ≠ 0)
    (G : Fin n → MvPolynomial (Fin m) K)
    (hG : ∀ i, IsGammaPolynomial v δ (γ i) (G i)) :
    IsGammaPolynomial v δ α (MvPolynomial.aeval G F) := by
  classical
  obtain ⟨_, hα, P, rfl, hP⟩ := hF
  rw [PolynomialPresentation.polynomial, map_sum]
  apply IsGammaPolynomial.sum v hδ hα
  intro j
  have hcoef : v (P.coefficient j) ≠ 0 := by
    intro hz
    exact hα ((hP j).symm.trans (by rw [hz, zero_mul]))
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
  have he : (∏ i ∈ (P.exponent j).support, γ i ^ (P.exponent j) i) =
      ∏ i, γ i ^ (P.exponent j) i := by
    exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  rw [← hP j, ← he]
  exact (isGammaPolynomial_C v hδ hcoef).mul v
    (IsGammaPolynomial.prod v hδ _ (fun i _ => (hG i).pow v _))

theorem IsGammaPolynomial.rename (v : Valuation K Γ) {n m : ℕ}
    {δ : Fin m → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (f : Fin n → Fin m) (hF : IsGammaPolynomial v (δ ∘ f) α F)
    (hδ : ∀ i, δ i ≠ 0) : IsGammaPolynomial v δ α (MvPolynomial.rename f F) := by
  rw [rename_eq_aeval]
  exact hF.aeval v hδ _ (fun i => isGammaPolynomial_X v hδ (f i))

theorem residueRoot_rename_iff (v : Valuation K Γ) {n m : ℕ}
    {t : Fin m → RVCalc.RV v} (ht : ∀ j, t j ≠ none)
    (f : Fin n → Fin m) {α : Γ} {P : MvPolynomial (Fin n) K}
    (hP : IsGammaPolynomial v (fun j => RVCalc.vrv v (t (f j))) α P) :
    IsResidueRoot v t α (rename f P) ↔ IsResidueRoot v (t ∘ f) α P := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := rvFibre_nonempty v t
    apply (residueRoot_iff_exists v (fun j => ht (f j)) hP).mpr
    refine ⟨a ∘ f, fun j => ha (f j), ?_⟩
    simpa only [eval_rename] using h a ha
  · intro h a ha
    rw [eval_rename]
    exact h (a ∘ f) (fun j => ha (f j))

/-- If a variable is outside the image of a coordinate renaming, its
derivative is zero. No injectivity assumption is needed for this half of
the chain rule. -/
theorem pderiv_rename_eq_zero_of_notMem_range {R : Type*} [CommRing R]
    {ι σ : Type*} [DecidableEq σ] (f : ι → σ) {i : σ} (hi : i ∉ Set.range f)
    (P : MvPolynomial ι R) : pderiv i (rename f P) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hm
  obtain ⟨j, _, hj⟩ := mem_vars_rename f P hm
  exact hi ⟨j, hj⟩

section Specialization

variable {n m : ℕ} (f : Fin n ↪ Fin m)

/-- Keep the coordinates named by an embedding and specialize the rest
to the corresponding entries of the ambient field tuple. -/
noncomputable def specializeCoordinates (a : Fin m → K) :
    MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (Function.extend f X (C ∘ a))

theorem specializeCoordinates_eval (a : Fin m → K) (b : Fin n → K)
    (P : MvPolynomial (Fin m) K) :
    (specializeCoordinates f a P).eval b = P.eval (Function.extend f b a) := by
  classical
  rw [specializeCoordinates, ← aeval_eq_eval, comp_aeval_apply, aeval_eq_eval]
  apply congrArg (fun z : Fin m → K => MvPolynomial.eval z P)
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    simp only [f.injective.extend_apply, aeval_X]
  · simp only [Function.extend_apply' _ _ _ hj, Function.comp_apply, aeval_C,
      Algebra.algebraMap_self_apply]

theorem IsGammaPolynomial.specializeCoordinates (v : Valuation K Γ)
    {γ : Fin m → Γ} {α : Γ} {P : MvPolynomial (Fin m) K}
    (hP : IsGammaPolynomial v γ α P)
    (a : Fin m → K) (ha : ∀ i, v (a i) = γ i) :
    IsGammaPolynomial v (γ ∘ f) α (specializeCoordinates f a P) := by
  apply hP.aeval v (fun i => hP.1 (f i))
  intro j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply]
    exact isGammaPolynomial_X v (fun k => hP.1 (f k)) i
  · rw [Function.extend_apply' _ _ _ hj, Function.comp_apply, ← ha j]
    exact isGammaPolynomial_C v (fun k => hP.1 (f k)) (by rw [ha j]; exact hP.1 j)

theorem pderiv_specializeCoordinates (a : Fin m → K) (i : Fin n)
    (P : MvPolynomial (Fin m) K) :
    pderiv i (specializeCoordinates f a P) =
      specializeCoordinates f a (pderiv (f i) P) := by
  classical
  have hX (j : Fin m) :
      pderiv i (specializeCoordinates f a (X j)) =
        specializeCoordinates f a (pderiv (f i) (X j)) := by
    by_cases hj : ∃ k, f k = j
    · obtain ⟨k, rfl⟩ := hj
      by_cases hk : k = i
      · subst k
        simp [specializeCoordinates, f.injective.extend_apply]
      · simp [specializeCoordinates, f.injective.extend_apply, pderiv_X_of_ne hk,
          pderiv_X_of_ne (fun h => hk (f.injective h))]
    · have hji : j ≠ f i := fun he => hj ⟨i, he.symm⟩
      simp [specializeCoordinates, Function.extend_apply' _ _ _ hj, pderiv_X_of_ne hji]
  induction P using MvPolynomial.induction_on with
  | C c => simp [specializeCoordinates]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, pderiv_mul, map_add, hp, hX]

end Specialization

end SpecialTransformations.Section7
