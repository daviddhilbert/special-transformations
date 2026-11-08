import Section7.GuardedBaseMonomials
import Section7.GuardedResidueSums
import Section7.WeightedLeadingOperations

/-!
# Field evaluations of the sides of a guarded RV equality

Each residue summand has value one or is zero. A flat residue sum reduces
the sum of the corresponding VF Laurent monomials. Multiplying by the
outer monomial shifts the prescribed value; the ordinary product expands
with coefficients still in the original field.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GuardedRVNormalForm
open CanonicalRV ValuedModelMap

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M I R V Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]
variable (E : Subfield (VFType (M := M))) (a : I → E) (r : R → E)
    (x : V → VFType (M := M))

noncomputable def originalLaurentValue (T : Monomial I R V) : VFType (M := M) :=
  (originalMonomialCoefficient E T a r : VFType (M := M)) * T.powers.prod (fun i m => x i ^ m)

theorem originalLaurentValue_encoded (T : Monomial I R V) :
    T.rawEval (fun i => (a i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (x i)) =
      CanonicalRV.encodedRv (originalLaurentValue E a r x T) :=
  monomial_rawEval_eq_encoded E T a r x

variable (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

theorem originalLaurentValue_value_eq (T : Monomial I R V) (y : V → VFType (M := M))
    (h : ∀ i, v (x i) = v (y i)) :
    v (originalLaurentValue E a r x T) = v (originalLaurentValue E a r y T) := by
  simp only [originalLaurentValue, map_mul, Finsupp.prod, map_prod, map_zpow₀, h]

include hv in
theorem encodedRV_absolute_eq_of_equal_values (u w : VFType (M := M)) (h : v u = v w) :
    RVOperations.absoluteHom (CanonicalRV.encodedRv u) =
      RVOperations.absoluteHom (CanonicalRV.encodedRv w) := by
  apply le_antisymm
  · apply (rvLe_iff_absolute (CanonicalRV.encodedRv w) (CanonicalRV.encodedRv u)).mp
    exact (hv u w).mpr h.le
  · apply (rvLe_iff_absolute (CanonicalRV.encodedRv u) (CanonicalRV.encodedRv w)).mp
    exact (hv w u).mpr h.ge

theorem encoded_weightedLeadingTerm_mul_of_exact {α : Γ} (hα : α ≠ 0) (β : Γ)
    {b : VFType (M := M)} (hb : v b = α) (z : VFType (M := M)) :
    CanonicalRV.equiv v hv (weightedLeadingTerm v (α * β) (b * z)) =
      CanonicalRV.encodedRv b * CanonicalRV.equiv v hv (weightedLeadingTerm v β z) := by
  rw [weightedLeadingTerm_mul_of_exact v hα β hb]
  apply Subtype.ext
  rw [CanonicalRV.equiv_mul, RVOperations.mul_val, CanonicalRV.equiv_rv]

include hv in
theorem originalLaurentValue_value_of_inK (T : Monomial I R V)
    (hK : inK (T.rawEval (fun i => (a i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (x i)))) :
    v (originalLaurentValue E a r x T) = 1 ∨ originalLaurentValue E a r x T = 0 := by
  rw [originalLaurentValue_encoded E a r x T] at hK
  rcases hK with hunit | hzero
  · exact Or.inl ((CanonicalResidue.units_encodedRv_iff v hv _).mp hunit)
  · exact Or.inr ((CanonicalRV.encodedRv_zero_iff _).mp (congrArg Subtype.val hzero))

theorem guarded_residue_sum_leadingTerm (P : KPolynomial I R V)
    (hP : P.Domain (fun i => (a i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (x i))) :
    v (∑ j, originalLaurentValue E a r x (P.terms j)) ≤ 1 ∧
      P.rawEval (fun i => (a i : VFType (M := M)))
        (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
        (fun i => CanonicalRV.encodedRv (x i)) =
        CanonicalRV.equiv v hv (weightedLeadingTerm v 1
          (∑ j, originalLaurentValue E a r x (P.terms j))) := by
  let w := fun j : Fin P.size => originalLaurentValue E a r x (P.terms j)
  have hw (j : Fin P.size) : v (w j) ≤ 1 := by
    rcases originalLaurentValue_value_of_inK E a r x v hv (P.terms j) (hP j).2 with h | h
    · change v (w j) = 1 at h
      exact h.le
    · change w j = 0 at h
      simp [h, zero_le]
  let z : Fin P.size → v.valuationSubring := fun j =>
    ⟨w j, (Valuation.mem_valuationSubring_iff v _).mpr (hw j)⟩
  have hsum : (↑(∑ j, z j) : VFType (M := M)) = ∑ j, w j := by
    change v.valuationSubring.subtype (∑ j, z j) = _
    rw [map_sum]
    rfl
  refine ⟨v.map_sum_le (fun j _ => hw j), ?_⟩
  have h := residuePolynomial_rawEval_of_representatives v hv P _ _ _ hP z
    (fun j => originalLaurentValue_encoded E a r x (P.terms j))
  simpa only [hsum, w] using h

theorem guarded_outer_times_residue_sum (T : Monomial I R V) (P : KPolynomial I R V)
    (hP : P.Domain (fun i => (a i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (x i)))
    (hT : v (originalLaurentValue E a r x T) ≠ 0) :
    let A := originalLaurentValue E a r x T
    let B := ∑ j, originalLaurentValue E a r x (P.terms j)
    v (A * B) ≤ v A ∧
      T.rawEval (fun i => (a i : VFType (M := M)))
        (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
        (fun i => CanonicalRV.encodedRv (x i)) *
      P.rawEval (fun i => (a i : VFType (M := M)))
        (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
        (fun i => CanonicalRV.encodedRv (x i)) =
      CanonicalRV.equiv v hv (weightedLeadingTerm v (v A) (A * B)) := by
  let A := originalLaurentValue E a r x T
  let B := ∑ j, originalLaurentValue E a r x (P.terms j)
  obtain ⟨hB, heB⟩ := guarded_residue_sum_leadingTerm E a r x v hv P hP
  refine ⟨?_, ?_⟩
  · change v (A * B) ≤ v A
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_left hB (zero_le : 0 ≤ v A)).trans_eq (mul_one _)
  · rw [originalLaurentValue_encoded E a r x T, heB]
    change CanonicalRV.encodedRv A * CanonicalRV.equiv v hv (weightedLeadingTerm v 1 B) =
      CanonicalRV.equiv v hv (weightedLeadingTerm v (v A) (A * B))
    have hm := weightedLeadingTerm_mul_of_exact v hT 1 (c := A) rfl B
    rw [mul_one] at hm
    rw [hm]
    apply Subtype.ext
    rw [RVOperations.mul_val, CanonicalRV.equiv_mul, CanonicalRV.equiv_rv]

theorem originalLaurentValue_mul (T U : Monomial I R V)
    (hx : ∀ i, x i ≠ 0) :
    originalLaurentValue E a r x T * originalLaurentValue E a r x U =
      (↑(originalMonomialCoefficient E T a r * originalMonomialCoefficient E U a r) :
        VFType (M := M)) * (T.powers + U.powers).prod (fun i m => x i ^ m) := by
  classical
  have hprod : (T.powers + U.powers).prod (fun i m => x i ^ m) =
      T.powers.prod (fun i m => x i ^ m) * U.powers.prod (fun i m => x i ^ m) := by
    apply Finsupp.prod_add_index'
    · intro i; exact zpow_zero _
    · intro i m k; exact zpow_add₀ (hx i) m k
  rw [hprod]
  change _ = (E.subtype (originalMonomialCoefficient E T a r *
    originalMonomialCoefficient E U a r)) * _
  simp only [originalLaurentValue, map_mul]
  ac_rfl

theorem originalLaurentValue_mul_sum (T : Monomial I R V) (P : KPolynomial I R V)
    (hx : ∀ i, x i ≠ 0) :
    originalLaurentValue E a r x T * (∑ j, originalLaurentValue E a r x (P.terms j)) =
      ∑ j, (↑(originalMonomialCoefficient E T a r *
          originalMonomialCoefficient E (P.terms j) a r) : VFType (M := M)) *
        (T.powers + (P.terms j).powers).prod (fun i m => x i ^ m) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => originalLaurentValue_mul E a r x T (P.terms j) hx

end SpecialTransformations.Section7
