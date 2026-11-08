import Section7.SimpleResidueExtraction

/-!
# Varying one coordinate inside a fixed value fibre

Specialization of the normalized valuation-ring polynomial describes the
weighted root test as the last residue coordinate varies. The scaled RV
classes of nonzero residue coordinates are injective. These are the
evaluation and finiteness bridges for Lemma 7.4's root extraction.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem valuationRing_value_one_of_residue_ne_zero (v : Valuation K Γ)
    (x : v.valuationSubring) (hx : residue v.valuationSubring x ≠ 0) : v (x : K) = 1 :=
  (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.valuationSubring.integers v)).mp
    ((residue_ne_zero_iff_isUnit x).mp hx)

theorem scaledRV_eq_iff_residue_eq (v : Valuation K Γ) {c : K} (hc : c ≠ 0)
    (x y : v.valuationSubring) (hx : residue v.valuationSubring x ≠ 0)
    (hy : residue v.valuationSubring y ≠ 0) :
    RVCalc.rv v (c * (x : K)) = RVCalc.rv v (c * (y : K)) ↔
      residue v.valuationSubring x = residue v.valuationSubring y := by
  have hxv := valuationRing_value_one_of_residue_ne_zero v x hx
  have hyv := valuationRing_value_one_of_residue_ne_zero v y hy
  have hx0 : (x : K) ≠ 0 := (Valuation.ne_zero_iff v).mp (hxv.symm ▸ one_ne_zero)
  have hy0 : (y : K) ≠ 0 := (Valuation.ne_zero_iff v).mp (hyv.symm ▸ one_ne_zero)
  have hcv : 0 < v c := (zero_lt_iff).mpr ((Valuation.ne_zero_iff v).mpr hc)
  rw [RVCalc.rv_eq_iff (mul_ne_zero hc hx0) (mul_ne_zero hc hy0),
    show c * (x : K) - c * (y : K) = c * ((x : K) - (y : K)) by ring,
    map_mul, map_mul, hxv, mul_lt_mul_iff_right₀ hcv]
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  rfl

theorem valuation_eval_lt_iff_specialized_residue (v : Valuation K Γ) {n : ℕ}
    {α : Γ} (c : Fin n → K) (e : K) (he : v e * α = 1)
    (F : MvPolynomial (Fin n) K) (H : MvPolynomial (Fin n) v.valuationSubring)
    (hH : H.map v.valuationSubring.subtype = normalizePolynomial c e F)
    (i : Fin n) (z : v.valuationSubring) :
    v (F.eval (fun j => c j * (Function.update (fun _ => (1 : v.valuationSubring)) i z j : K))) < α ↔
      (specializeVariable (residue v.valuationSubring) (fun _ => 1) i H).IsRoot
        (residue v.valuationSubring z) := by
  let a := Function.update (fun _ : Fin n => (1 : v.valuationSubring)) i z
  let π := residue v.valuationSubring
  have hupdate : Function.update (fun _ : Fin n => (1 : ResidueField v.valuationSubring)) i (π z) =
      fun j => π (a j) := by
    funext j
    by_cases hj : j = i <;> simp [a, Function.update, hj]
  have hred : eval₂ π (fun j => π (a j)) H = π (H.eval a) := by
    rw [← MvPolynomial.eval_map]
    exact (MvPolynomial.map_eval π a H).symm
  have heval : v.valuationSubring.subtype (H.eval a) =
      e * F.eval (fun j => c j * (a j : K)) := by
    rw [MvPolynomial.map_eval, hH, eval_normalizePolynomial]
    rfl
  have he0 : v e ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he
    exact zero_ne_one he
  have hepos : 0 < v e := (zero_lt_iff).mpr he0
  rw [Polynomial.IsRoot, eval_specializeVariable, hupdate, hred]
  change _ ↔ residue v.valuationSubring (H.eval a) = 0
  rw [residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change _ ↔ v (v.valuationSubring.subtype (H.eval a)) < 1
  rw [heval, map_mul, ← he, mul_lt_mul_iff_right₀ hepos]

end SpecialTransformations.Section7
