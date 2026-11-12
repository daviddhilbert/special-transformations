module

public import Section7.GuardedFibreDomains
public import Section7.WeightedLeadingTerms

@[expose] public section

/-!
# The value-one leading term of a guarded residue sum

Actual VF representatives of the summands reduce via the released residue
projection. Consequently the flat RV sum is the value-one leading term
of their sum, including when cancellation makes that sum reduce to zero.
The original-base construction of the Laurent monomials is separate.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GuardedRVNormalForm
open CanonicalRV ValuedModelMap

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

theorem encoded_weightedLeadingTerm_one (x : v.valuationSubring) :
    CanonicalRV.equiv v hv (weightedLeadingTerm v 1 (x : VFType (M := M))) =
      ResidueRVAlgebra.residueRVHom v hv (IsLocalRing.residue v.valuationSubring x) := by
  change _ = CanonicalResidue.toRV v hv (IsLocalRing.residue v.valuationSubring x)
  rw [CanonicalResidue.toRV_residue]
  by_cases hx : v (x : VFType (M := M)) = 1
  · simp only [weightedLeadingTerm, CanonicalResidue.reduction, hx, if_true,
      CanonicalRV.equiv_rv]
  · simp only [weightedLeadingTerm, CanonicalResidue.reduction, hx, if_false]
    simpa only [_root_.RVCalc.rv_zero, ValuedModelMap.encodedRv_zero] using
      CanonicalRV.equiv_rv v hv (0 : VFType (M := M))

theorem residuePolynomial_rawEval_of_representatives {I R V : Type}
    (P : KPolynomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M)
    (y : V → RVSort M) (hD : P.Domain a r y) (x : Fin P.size → v.valuationSubring)
    (hx : ∀ j, (P.terms j).rawEval a r y = CanonicalRV.encodedRv (x j : VFType (M := M))) :
    P.rawEval a r y = CanonicalRV.equiv v hv
      (weightedLeadingTerm v 1 (↑(∑ j, x j) : VFType (M := M))) := by
  have hsingle (j : Fin P.size) : (P.terms j).rawEval a r y =
      ResidueRVAlgebra.residueRVHom v hv (IsLocalRing.residue v.valuationSubring (x j)) := by
    have hK := (hD j).2
    rw [hx j] at hK
    have hlead : weightedLeadingTerm v 1 (x j : VFType (M := M)) =
        _root_.RVCalc.rv v (x j : VFType (M := M)) := by
      rcases hK with hunit | hzero
      · simp only [weightedLeadingTerm,
          (CanonicalResidue.units_encodedRv_iff v hv _).mp hunit, if_true]
      · have he : (x j : VFType (M := M)) = 0 :=
          (CanonicalRV.encodedRv_zero_iff _).mp (congrArg Subtype.val hzero)
        simp [weightedLeadingTerm, he, _root_.RVCalc.rv_zero]
    rw [← encoded_weightedLeadingTerm_one v hv, hlead, CanonicalRV.equiv_rv]
    exact hx j
  rw [encoded_weightedLeadingTerm_one v hv]
  simp only [KPolynomial.rawEval, hsingle, KPolynomial.rvSum_image, map_sum]

end SpecialTransformations.Section7
