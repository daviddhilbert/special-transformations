module

public import Section7.WeightedLeadingOperations
public import Section7.GammaPolynomialAlgebra

@[expose] public section

/-!
# A weighted equality is at most two original-field polynomial tests

At equal degrees use the difference polynomial; at unequal degrees both
leading terms must vanish. The test polynomials belong to the same field
as the two input polynomials. The theorem is stated on the actual RV
fibre, independent of the chosen field tuple.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem residueRoot_iff_eval_lt_at (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ j, t j ≠ none)
    {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) α F)
    {x : Fin n → K} (hx : x ∈ RVFibre v t) :
    IsResidueRoot v t α F ↔ v (F.eval x) < α :=
  ⟨fun h => h x hx, fun h => (residueRoot_iff_exists v ht hF).mpr ⟨x, hx, h⟩⟩

theorem weightedPolynomialEquality_iff (v : Valuation K Γ) (E : Subfield K) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ j, t j ≠ none)
    {α β : Γ} (P Q : MvPolynomial (Fin n) E)
    (hP : IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) α (P.map E.subtype))
    (hQ : IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) β (Q.map E.subtype))
    {x : Fin n → K} (hx : x ∈ RVFibre v t) :
    weightedLeadingTerm v α ((P.map E.subtype).eval x) =
        weightedLeadingTerm v β ((Q.map E.subtype).eval x) ↔
      if α = β then IsResidueRoot v t α ((P - Q).map E.subtype)
      else IsResidueRoot v t α (P.map E.subtype) ∧ IsResidueRoot v t β (Q.map E.subtype) := by
  have hPv := gammaPolynomial_eval_le v hP (rvFibre_value v hx)
  have hQv := gammaPolynomial_eval_le v hQ (rvFibre_value v hx)
  by_cases h : α = β
  · subst β
    have hPQ : IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) α ((P - Q).map E.subtype) := by
      rw [map_sub, sub_eq_add_neg]
      exact hP.add v (hQ.neg v)
    rw [if_pos rfl, weightedLeadingTerm_eq_iff_sub_lt v hP.2.1 hPv hQv,
      residueRoot_iff_eval_lt_at v ht hPQ hx, map_sub (MvPolynomial.map E.subtype),
      map_sub (MvPolynomial.eval x)]
  · rw [if_neg h]
    exact (weightedLeadingTerm_eq_iff_of_value_ne v hP.2.1 hQ.2.1 h hPv hQv).trans
      (and_congr (residueRoot_iff_eval_lt_at v ht hP hx).symm
        (residueRoot_iff_eval_lt_at v ht hQ hx).symm)

end SpecialTransformations.Section7
