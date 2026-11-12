module

public import Section3.RVOperations
public import Section3.PolynomialLocal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3

/-- Pinned Mathlib's X-power divisibility and trailing-coefficient API
give the exact factorization used in the proof of Lemma 3.17. -/
theorem factor_X_nonzero_constant {K : Type*} [Field K] (p : Polynomial K) (hp : p ≠ 0) :
    ∃ m : ℕ, ∃ q : Polynomial K, p = Polynomial.X^m*q ∧ q.eval 0 ≠ 0 := by
  have hd : Polynomial.X ^ p.natTrailingDegree ∣ p :=
    Polynomial.X_pow_dvd_iff.mpr (fun _ hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi)
  obtain ⟨q,hq⟩ := hd
  refine ⟨p.natTrailingDegree,q,hq,?_⟩
  rw [← Polynomial.coeff_zero_eq_eval_zero q]
  have hc := Polynomial.coeff_X_pow_mul q p.natTrailingDegree 0
  rw [zero_add,← hq] at hc
  intro hz
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp) (hc.trans hz)

namespace RVMonomial
open RVOperations
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem nonzero_polynomial {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    [Valued (VFType (M := M)) Γ]
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (p : Polynomial (VFType (M := M))) (hp : p ≠ 0) :
    ∃ m : ℕ, ∃ c : VFType (M := M), c ≠ 0 ∧
      ∀ᶠ x : VFType (M := M) in 𝓝 0,
        CanonicalRV.encodedRv (p.eval x) = CanonicalRV.encodedRv x ^ m * CanonicalRV.encodedRv c := by
  obtain ⟨m,q,hp,hq⟩ := factor_X_nonzero_constant p hp
  refine ⟨m,q.eval 0,hq,?_⟩
  filter_upwards [polynomial_rv_locally_constant hv q 0 hq] with x hx
  calc
    CanonicalRV.encodedRv (p.eval x) = CanonicalRV.encodedRv (x^m*q.eval x) := by
      rw [hp]
      simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
    _ = CanonicalRV.encodedRv x ^ m * CanonicalRV.encodedRv (q.eval x) := by
      change rvHom (x^m*q.eval x) = rvHom x ^ m * rvHom (q.eval x)
      rw [map_mul,map_pow]
    _ = CanonicalRV.encodedRv x ^ m * CanonicalRV.encodedRv (q.eval 0) :=
      congrArg (fun t => CanonicalRV.encodedRv x ^ m * t) (Subtype.ext hx)

theorem polynomial {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    [Valued (VFType (M := M)) Γ]
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (p : Polynomial (VFType (M := M))) :
    ∃ m : ℕ, ∃ c : VFType (M := M),
      ∀ᶠ x : VFType (M := M) in 𝓝 0,
        CanonicalRV.encodedRv (p.eval x) = CanonicalRV.encodedRv x ^ m * CanonicalRV.encodedRv c := by
  by_cases hp : p = 0
  · refine ⟨0,0,Filter.Eventually.of_forall ?_⟩
    intro x
    simp only [hp,Polynomial.eval_zero,pow_zero,rv_zero,mul_zero]
  · obtain ⟨m,c,_,hc⟩ := nonzero_polynomial hv p hp
    exact ⟨m,c,hc⟩

end RVMonomial
end SpecialTransformations.Section3
