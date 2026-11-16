module

public import Section9.InfinitesimalMonomials
public import Section9.NestedGammaInfinitesimals

@[expose] public section

/-! Positive infinitesimal coordinates give a Gauss tuple for the
coarsening determined by the coefficient field's values. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

def coefficientThresholds (v : Valuation K Γ) (E : Subfield K) : Set Γ :=
  {t | t < 1 ∧ ∃ c : E, c ≠ 0 ∧ v (c : K) = t}

theorem coefficientThresholds_lt_one (v : Valuation K Γ) (E : Subfield K) :
    ∀ t ∈ coefficientThresholds v E, t < 1 := fun _ h => h.1

theorem coefficientThresholds_halve (v : Valuation K Γ) (E : Subfield K) [IsAlgClosed E] :
    ∀ t ∈ coefficientThresholds v E, ∃ s ∈ coefficientThresholds v E, t ≤ s * s := by
  rintro t ⟨ht, c, hc, hv⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0 < 2)
  have hr₀ : r ≠ 0 := fun h => hc (by rw [← hr, h]; norm_num)
  have hpow : v (r : K) ^ 2 = t := by
    rw [← map_pow]
    exact (congrArg (fun a : E => v (a : K)) hr).trans hv
  have hrVal : v (r : K) < 1 := lt_of_not_ge (fun h =>
    ht.not_ge (hpow ▸ (by simpa only [one_pow] using pow_le_pow_left' h 2)))
  refine ⟨v (r : K), ⟨hrVal, r, hr₀, rfl⟩, ?_⟩
  rw [← pow_two, hpow]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "VF" => VFType (M := M)

theorem exists_coarsened_gauss_tuple
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    {G : Type} [LinearOrderedCommGroupWithZero G]
    (v : Valuation VF G) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    (E : Subfield VF) [IsAlgClosed E] (hE : Cardinal.mk E < κ)
    (hne : (coefficientThresholds v E).Nonempty) (n : ℕ) :
    let w := (thresholdCoarsening v (coefficientThresholds v E) hne
      (coefficientThresholds_lt_one v E) (coefficientThresholds_halve v E)).valuation
    ∃ x : Fin n → VF, (∀ i, x i ≠ 0 ∧ v (x i) < 1 ∧ w (x i) = 1) ∧
      IsGaussEvaluation (E := E) w x ∧ AlgebraicIndependent E x := by
  classical
  let T := coefficientThresholds v E
  let ht := coefficientThresholds_lt_one v E
  let hh := coefficientThresholds_halve v E
  let w := (thresholdCoarsening v T hne ht hh).valuation
  obtain ⟨x, B, hB, hEB, hprev, hx₀, hx, hsmall⟩ :=
    exists_nested_positive_infinitesimals hκ hs v hv E hE n
  have hunit (i : Fin n) : w (x i) = 1 := by
    let a : v.valuationSubring := ⟨x i, (Valuation.mem_valuationSubring_iff v _).mpr (hx i).le⟩
    apply (thresholdCoarsening_value_eq_one_iff v T hne ht hh a).mpr
    rintro t ⟨ht, c, hc, rfl⟩
    let c' : B i := ⟨c, hEB i c.property⟩
    exact hsmall i c' (fun h => hc (Subtype.ext h)) ht
  have hmon (d : Fin n →₀ ℕ) (c : E) :
      v (aeval x (monomial d c)) = v (c : VF) * ∏ i, v (x i) ^ d i := by
    rw [aeval_monomial, map_mul, Finsupp.prod, map_prod]
    simp only [map_pow]
    congr 1
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  have hGauss : IsGaussEvaluation (E := E) w x := by
    apply isGaussEvaluation_of_distinct_fine_values v w
      (thresholdCoarsening_le_of_fine_le v T hne ht hh) x hunit
    intro P d e hd he hne
    rw [hmon, hmon]
    have hd₀ : ((P.coeff d : E) : VF) ≠ 0 := fun h => (mem_support_iff.mp hd) (Subtype.ext h)
    have he₀ : ((P.coeff e : E) : VF) ≠ 0 := fun h => (mem_support_iff.mp he) (Subtype.ext h)
    exact distinct_monomial_values_of_nested_infinitesimals v E x B hB hEB hprev hx₀ hx hsmall
      (P.coeff d) (P.coeff e) hd₀ he₀ d e (fun h => hne (Finsupp.ext (congrFun h)))
  exact ⟨x, fun i => ⟨hx₀ i, hx i, hunit i⟩, hGauss, algebraicIndependent_of_isGaussEvaluation w x hGauss⟩

end SpecialTransformations.Section9
