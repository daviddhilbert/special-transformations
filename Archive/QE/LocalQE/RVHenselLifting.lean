import RVClassEquality
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Root-lifting proofs extracted from QE/RV_henselian.lean at fa3867c. -/
namespace RVCalc
open Polynomial
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
theorem one_le_multiset_prod {s : Multiset Γ₀} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.prod_cons]
      exact one_le_mul (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- **Hensel lifting over an algebraically closed valued field.**
A monic polynomial that has a root modulo the maximal ideal has a genuine root which is
congruent to it modulo the maximal ideal. -/
theorem exists_root_of_eval_lt_one [IsAlgClosed K] (v : Valuation K Γ₀) {f : K[X]}
    (hf : f.Monic) {a₀ : K} (h : v (f.eval a₀) < 1) :
    ∃ b : K, f.IsRoot b ∧ v (a₀ - b) < 1 := by
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.1 (IsAlgClosed.splits f)
  rw [hf.leadingCoeff, map_one, one_mul] at hm
  have hev : ∀ c : K, f.eval c = (m.map fun r => c - r).prod := by
    intro c
    rw [hm, Polynomial.eval_multiset_prod]
    simp [Multiset.map_map, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hex : ∃ r ∈ m, v (a₀ - r) < 1 := by
    by_contra hc
    have hc' : ∀ r ∈ m, 1 ≤ v (a₀ - r) := by
      intro r hr
      by_contra h1
      exact hc ⟨r, hr, not_le.1 h1⟩
    have h1 : 1 ≤ (m.map fun r => v (a₀ - r)).prod := by
      refine one_le_multiset_prod ?_
      intro a ha
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 ha
      exact hc' r hr
    have h2 : v (f.eval a₀) = (m.map fun r => v (a₀ - r)).prod := by
      rw [hev a₀, map_multiset_prod]
      simp [Multiset.map_map]
    rw [h2] at h
    exact absurd h (not_lt.2 h1)
  obtain ⟨r, hr, hrv⟩ := hex
  refine ⟨r, ?_, hrv⟩
  rw [Polynomial.IsRoot.def, hev r]
  refine Multiset.prod_eq_zero_iff.2 ?_
  have := Multiset.mem_map_of_mem (f := fun r' => r - r') hr
  simpa using this


theorem exists_root_rv_eq [IsAlgClosed K] (v : Valuation K Γ₀) {f : K[X]} (hf : f.Monic)
    {a₀ : K} (h : v (f.eval a₀) < 1) (hu : v a₀ = 1) :
    ∃ b : K, f.IsRoot b ∧ rv v b = rv v a₀ := by
  obtain ⟨b, hb, hbc⟩ := exists_root_of_eval_lt_one v hf h
  have ha₀ : a₀ ≠ 0 := by rintro rfl; rw [Valuation.map_zero] at hu; exact zero_ne_one hu
  have hbv : v (b - a₀) < 1 := by
    rw [show b - a₀ = -(a₀ - b) by ring, Valuation.map_neg v]; exact hbc
  have hb1 : v b = 1 := by
    have hsplit : b = (b - a₀) + a₀ := by ring
    rw [hsplit, Valuation.map_add_eq_of_lt_right v (by rw [hu]; exact hbv), hu]
  have hb0 : b ≠ 0 := by rintro rfl; rw [Valuation.map_zero] at hb1; exact zero_ne_one hb1
  refine ⟨b, hb, (rv_eq_iff hb0 ha₀).2 ?_⟩
  rw [hb1]
  exact hbv


end RVCalc
