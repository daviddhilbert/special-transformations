import ResiduePolynomialLift

/-!
The actual base residue subfield inside the ambient residue field.

It is the range of reduction on the integral elements of F. Inverse closure
is proved from the valuation, so neither inclusion nor residue surjectivity
is an extra hypothesis. Ordinary transcendence over this subfield implies
the finite-expression residue transcendence used by the transport proof.
-/

namespace ResidueAlgebraicTransport

open scoped BigOperators
open Polynomial ResidueTranscendentalTransport

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem baseResidueHom_range_inv (v : Valuation K Γ) (F : Subfield K)
    (x : Residue v) (hx : x ∈ (baseResidueHom v F).range) :
    x⁻¹ ∈ (baseResidueHom v F).range := by
  obtain ⟨a, rfl⟩ := hx
  by_cases hz : baseResidueHom v F a = 0
  · rw [hz, inv_zero]
    exact ⟨0, map_zero _⟩
  have ha : v ((a : F) : K) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff v _).mp a.property
  have hunit : v ((a : F) : K) = 1 := by
    apply le_antisymm ha
    apply le_of_not_gt
    intro hlt
    exact hz ((M7.vres_eq_zero_iff v _ ha).mpr hlt)
  have ha0 : (a : F) ≠ 0 := by
    intro heq
    have hzero : a = 0 := Subtype.ext heq
    exact hz (by rw [hzero, map_zero])
  have hb : v (((a : F)⁻¹ : F) : K) ≤ 1 := by
    change v (((a : F) : K)⁻¹) ≤ 1
    rw [map_inv₀, hunit, inv_one]
  let b : BaseIntegers v F :=
    ⟨(a : F)⁻¹, (Valuation.mem_valuationSubring_iff v _).mpr hb⟩
  have hba : b * a = 1 := Subtype.ext (inv_mul_cancel₀ ha0)
  refine ⟨b, ?_⟩
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, hba, map_one]

noncomputable def baseResidueField (v : Valuation K Γ) (F : Subfield K) :
    Subfield (Residue v) where
  toSubring := (baseResidueHom v F).range
  inv_mem' := baseResidueHom_range_inv v F

theorem mem_baseResidueField_iff (v : Valuation K Γ) (F : Subfield K) (x : Residue v) :
    x ∈ baseResidueField v F ↔
      ∃ a : F, ∃ ha : v (a : K) ≤ 1, M7.vres v (a : K) ha = x := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(a : F), (Valuation.mem_valuationSubring_iff v _).mp a.property, ?_⟩
    exact ha
  · rintro ⟨a, ha, hx⟩
    refine ⟨⟨a, (Valuation.mem_valuationSubring_iff v _).mpr ha⟩, ?_⟩
    exact hx

theorem baseResidueField_contains (v : Valuation K Γ) (F : Subfield K)
    (a : F) (ha : v (a : K) ≤ 1) : M7.vres v (a : K) ha ∈ baseResidueField v F :=
  (mem_baseResidueField_iff v F _).mpr ⟨a, ha, rfl⟩

theorem baseResidueField_surjective (v : Valuation K Γ) (F : Subfield K)
    (z : baseResidueField v F) :
    ∃ a : F, ∃ ha : v (a : K) ≤ 1,
      M7.vres v (a : K) ha = (baseResidueField v F).subtype z :=
  (mem_baseResidueField_iff v F _).mp z.property

theorem residueTranscendental_of_transcendental (v : Valuation K Γ) (F : Subfield K)
    {u : K} (hu : v u = 1)
    (htrans : Transcendental (baseResidueField v F) (M7.vres v u hu.le)) :
    M7.ResidueTranscendental v F hu := by
  classical
  intro n c m hm hc hz i
  let κ := baseResidueField v F
  let z := M7.vres v u hu.le
  let cκ : Fin n → κ := fun j =>
    ⟨M7.vres v (c j : K) (hc j), baseResidueField_contains v F (c j) (hc j)⟩
  let p : Polynomial κ := ∑ j, Polynomial.monomial (m j) (cκ j)
  have hcκ : ∀ j, algebraMap κ (Residue v) (cκ j) = M7.vres v (c j : K) (hc j) :=
    fun j => rfl
  have hp : Polynomial.aeval z p = 0 := by
    simpa only [p, map_sum, Polynomial.aeval_monomial, Algebra.smul_def, hcκ] using hz
  have hp0 : p = 0 := transcendental_iff.mp htrans p hp
  have hci := congrArg (fun q : Polynomial κ => q.coeff (m i)) hp0
  have hi : cκ i = 0 := by
    simpa [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hm.eq_iff] using hci
  exact congrArg Subtype.val hi

/-- Algebraic and transcendental residue cases are exhaustive for the actual
base residue field, rather than separate assumptions on an abstract interface. -/
theorem residue_cases (v : Valuation K Γ) (F : Subfield K)
    {u : K} (hu : v u = 1) :
    IsIntegral (baseResidueField v F) (M7.vres v u hu.le) ∨
      M7.ResidueTranscendental v F hu := by
  by_cases halg : IsAlgebraic (baseResidueField v F) (M7.vres v u hu.le)
  · exact Or.inl halg.isIntegral
  · exact Or.inr (residueTranscendental_of_transcendental v F hu halg)

end ResidueAlgebraicTransport

#print axioms ResidueAlgebraicTransport.baseResidueHom_range_inv
#print axioms ResidueAlgebraicTransport.mem_baseResidueField_iff
#print axioms ResidueAlgebraicTransport.baseResidueField_contains
#print axioms ResidueAlgebraicTransport.baseResidueField_surjective
#print axioms ResidueAlgebraicTransport.residueTranscendental_of_transcendental
#print axioms ResidueAlgebraicTransport.residue_cases
