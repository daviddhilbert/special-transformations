import Section7.PolynomialSystemEtale
import Section7.EtaleSections

/-! Ordinary multivariate simple-root lifting over a genuine Mathlib
henselian local ring. Existence comes from the proved etale presentation
and residue-section lifting; uniqueness uses the unramified diagonal.
No nilpotence, completeness, separatedness or multivariate lifting premise
is assumed. -/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {R : Type*} [CommRing R] {n : ℕ}

theorem aeval_residue [IsLocalRing R] (a : Fin n → R) (p : MvPolynomial (Fin n) R) :
    aeval (fun i => residue R (a i)) p = residue R (p.eval a) := by
  simpa using (MvPolynomial.comp_aeval_apply (f := a)
    (Algebra.ofId R (ResidueField R)) p).symm

theorem residue_tuple_eq_of_congr [IsLocalRing R] (a b : Fin n → R)
    (h : ∀ i, b i - a i ∈ maximalIdeal R) :
    (fun i => residue R (b i)) = fun i => residue R (a i) := by
  funext i
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (residue_eq_zero_iff _).mpr (h i)

theorem residue_eval_eq_of_congr [IsLocalRing R] (a b : Fin n → R)
    (h : ∀ i, b i - a i ∈ maximalIdeal R) (p : MvPolynomial (Fin n) R) :
    residue R (p.eval b) = residue R (p.eval a) := by
  rw [← aeval_residue, ← aeval_residue, residue_tuple_eq_of_congr a b h]

theorem polynomial_eval_isUnit_of_congr [IsLocalRing R] (a b : Fin n → R)
    (h : ∀ i, b i - a i ∈ maximalIdeal R) (p : MvPolynomial (Fin n) R)
    (hp : IsUnit (p.eval a)) : IsUnit (p.eval b) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [residue_eval_eq_of_congr a b h p]
  exact (residue_ne_zero_iff_isUnit _).mpr hp

theorem multivariate_simpleRoot_unique [IsLocalRing R]
    (F : Fin n → MvPolynomial (Fin n) R) (a b c : Fin n → R)
    (hJ : IsUnit ((jacobianPolynomial F).eval a))
    (hb : ∀ i, (F i).eval b = 0) (hc : ∀ i, (F i).eval c = 0)
    (hba : ∀ i, b i - a i ∈ maximalIdeal R)
    (hca : ∀ i, c i - a i ∈ maximalIdeal R) : b = c := by
  let φb := polynomialSystemEtalePoint F b hb
    (polynomial_eval_isUnit_of_congr a b hba _ hJ)
  let φc := polynomialSystemEtalePoint F c hc
    (polynomial_eval_isUnit_of_congr a c hca _ hJ)
  have hbpoint (i : Fin n) : φb (polynomialSystemVariable F i) = b i :=
    polynomialSystemEtalePoint_variable F b hb
      (polynomial_eval_isUnit_of_congr a b hba _ hJ) i
  have hcpoint (i : Fin n) : φc (polynomialSystemVariable F i) = c i :=
    polynomialSystemEtalePoint_variable F c hc
      (polynomial_eval_isUnit_of_congr a c hca _ hJ) i
  have hred : (Algebra.ofId R (ResidueField R)).comp φb =
      (Algebra.ofId R (ResidueField R)).comp φc := by
    apply polynomialSystemHom_ext F
    intro i
    simp only [AlgHom.comp_apply, hbpoint, hcpoint, Algebra.ofId_apply, ResidueField.algebraMap_eq]
    have hbt := congrFun (residue_tuple_eq_of_congr a b hba) i
    have hct := congrFun (residue_tuple_eq_of_congr a c hca) i
    exact hbt.trans hct.symm
  have heq : φb = φc := etale_residuePoint_injective hred
  funext i
  have hv := AlgHom.congr_fun heq (polynomialSystemVariable F i)
  simpa only [hbpoint, hcpoint] using hv

theorem multivariate_simpleRoot_exists [HenselianLocalRing R]
    (F : Fin n → MvPolynomial (Fin n) R) (a : Fin n → R)
    (hF : ∀ i, (F i).eval a ∈ maximalIdeal R)
    (hJ : IsUnit ((jacobianPolynomial F).eval a)) :
    ∃ b : Fin n → R, (∀ i, (F i).eval b = 0) ∧
      ∀ i, b i - a i ∈ maximalIdeal R := by
  let aκ : Fin n → ResidueField R := fun i => residue R (a i)
  have hFκ (i : Fin n) : aeval aκ (F i) = 0 := by
    rw [aeval_residue]
    exact (residue_eq_zero_iff _).mpr (hF i)
  have hJκ : IsUnit (aeval aκ (jacobianPolynomial F)) := by
    rw [aeval_residue]
    exact hJ.map (residue R)
  let ψ : PolynomialSystemEtaleRing F →ₐ[R] ResidueField R :=
    polynomialSystemEtalePoint F aκ hFκ hJκ
  obtain ⟨φ, hφ⟩ := Imported.EtaleLifting.residuePoint_lifts ψ
  let b : Fin n → R := fun i => φ (polynomialSystemVariable F i)
  refine ⟨b, ?_, ?_⟩
  · intro i
    change aeval (fun i => φ (polynomialSystemVariable F i)) (F i) = 0
    rw [← MvPolynomial.comp_aeval_apply, polynomialSystemVariable_relation, map_zero]
  · intro i
    have hv : residue R (b i) = residue R (a i) := by
      simpa only [AlgHom.comp_apply, ψ, polynomialSystemEtalePoint_variable,
        Algebra.ofId_apply, ResidueField.algebraMap_eq, b, aκ] using
        AlgHom.congr_fun hφ (polynomialSystemVariable F i)
    apply (residue_eq_zero_iff _).mp
    rw [map_sub, hv, sub_self]

/-- Ordinary square-system Hensel lifting, including uniqueness in the
specified maximal-ideal congruence class. -/
theorem multivariate_simpleRoot_lift [HenselianLocalRing R]
    (F : Fin n → MvPolynomial (Fin n) R) (a : Fin n → R)
    (hF : ∀ i, (F i).eval a ∈ maximalIdeal R)
    (hJ : IsUnit ((jacobianPolynomial F).eval a)) :
    ∃! b : Fin n → R, (∀ i, (F i).eval b = 0) ∧
      ∀ i, b i - a i ∈ maximalIdeal R := by
  obtain ⟨b, hb, hba⟩ := multivariate_simpleRoot_exists F a hF hJ
  exact ⟨b, ⟨hb, hba⟩, fun c hc => multivariate_simpleRoot_unique F a c b hJ hc.1 hb hc.2 hba⟩

end SpecialTransformations.Section7
