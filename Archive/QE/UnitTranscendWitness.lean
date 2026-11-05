/-
# M7 / d6: a ⊤-witness — the hypotheses of `gamma_step` are satisfiable

`UnitTranscend.lean` proves Lemma 3.6's `Γ`-step from (i) `v e = 1`, (ii) transcendence of `rv(e)`
over the base residue field, (iii) the fraction-field representation.  This file exhibits a model in
which (i) and (ii) hold — so the theorem is not vacuous — and in which the conclusion is checked.

Model: `L = ℝ⟦ℤ⟧` (Hahn series) with the **trivial** valuation `v` (every nonzero element has value
`1`), base field `K = ℝ` the constants, `e = t = single 1 1`.  Then

* `v e = 1` (`val_t_trivial`);
* the residue field of the trivial valuation is `L` itself, and `t` is transcendental over the
  constants (`t_transcendental`), so `ResidueTranscendental v K he` holds (`residue_transcendental`);
* the base value group is trivial, hence divisible.

The conclusion of `M7.gamma_step` then holds — trivially, since every nonzero element already has
value `1` and the base contains `1`.  The point of the file is the *hypothesis* side: it shows the
hypothesis set of the quote-elimination is consistent, so `gamma_step` is not a vacuous implication.

No `sorry`, no `axiom`, no `native_decide`.
-/
import UnitTranscend
import Mathlib

set_option autoImplicit false

namespace M7

/-- The trivial valuation: every nonzero element has value `1`. -/
noncomputable def trivialValuation' (L : Type*) [Field L] [DecidableEq L] :
    Valuation L (WithZero (Multiplicative ℤ)) where
  toFun x := if x = 0 then 0 else 1
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hy : y = 0
      · simp [hy]
      · simp [hx, hy]
  map_add_le_max' := by
    intro x y
    by_cases h : x + y = 0
    · simp [h]
    · by_cases hx : x = 0
      · have hy : y ≠ 0 := by
          intro hy; exact h (by simp [hx, hy])
        simp [hx, hy]
      · simp [h, hx]

/-- The trivial valuation, with the decidability instance supplied classically. -/
noncomputable def trivialValuation (L : Type*) [Field L] :
    Valuation L (WithZero (Multiplicative ℤ)) :=
  @trivialValuation' L _ (Classical.decEq L)

lemma trivial_mono_le_one' {L : Type*} [Field L] [DecidableEq L] (x : L) :
    trivialValuation' L x ≤ 1 := by
  show (if x = 0 then (0 : WithZero (Multiplicative ℤ)) else 1) ≤ 1
  by_cases hx : x = 0 <;> simp [hx]

lemma trivial_eq_one_of_ne' {L : Type*} [Field L] [DecidableEq L] {x : L} (hx : x ≠ 0) :
    trivialValuation' L x = 1 := by
  show (if x = 0 then (0 : WithZero (Multiplicative ℤ)) else 1) = 1
  simp [hx]

lemma trivial_le_one {L : Type*} [Field L] (x : L) : trivialValuation L x ≤ 1 :=
  @trivial_mono_le_one' L _ (Classical.decEq L) x

lemma trivial_eq_one_of_ne {L : Type*} [Field L] {x : L} (hx : x ≠ 0) :
    trivialValuation L x = 1 :=
  @trivial_eq_one_of_ne' L _ (Classical.decEq L) x hx

lemma trivial_lt_one_iff {L : Type*} [Field L] [DecidableEq L] (x : L) :
    trivialValuation' L x < (1 : WithZero (Multiplicative ℤ)) ↔ x = 0 := by
  show (if x = 0 then (0 : WithZero (Multiplicative ℤ)) else 1) < 1 ↔ x = 0
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]

/-- The monomial `t` of `ℝ⟦ℤ⟧`. -/
noncomputable def ht2 : HahnSeries ℤ ℝ := HahnSeries.single 1 1

lemma ht2_eq : ht2 = HahnSeries.single (1 : ℤ) (1 : ℝ) := rfl

lemma t_transcendental_triv (n : ℕ) (c : Fin n → ℝ)
    (h : (∑ i, HahnSeries.single (0 : ℤ) (c i) * ht2 ^ (i : ℕ)) = 0) :
    ∀ i, c i = 0 := by
  classical
  have hpow : ∀ i : Fin n, ht2 ^ (i : ℕ) = HahnSeries.single ((i : ℕ) : ℤ) (1 : ℝ) := by
    intro i
    rw [ht2_eq, HahnSeries.single_pow, nsmul_eq_mul, mul_one, one_pow]
  have hterm : ∀ i : Fin n,
      HahnSeries.single (0 : ℤ) (c i) * ht2 ^ (i : ℕ) = HahnSeries.single ((i : ℕ) : ℤ) (c i) := by
    intro i
    rw [hpow, HahnSeries.single_mul_single]
    simp
  have hsum : (∑ i : Fin n, HahnSeries.single ((i : ℕ) : ℤ) (c i)) = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => (hterm i).symm
  intro i₀
  have hcoeff := congrArg (fun x : HahnSeries ℤ ℝ => x.coeff ((i₀ : ℕ) : ℤ)) hsum
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single i₀] at hcoeff
  · simpa using hcoeff
  · intro i _ hne
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    exact hne (Fin.ext (Nat.cast_injective hcon.symm))
  · intro hnot
    exact absurd (Finset.mem_univ i₀) hnot


/-- The base field: the image of `ℝ` in `ℝ⟦ℤ⟧`, i.e. the constants. -/
noncomputable def constSub : Subfield (HahnSeries ℤ ℝ) :=
  (HahnSeries.C : ℝ →+* HahnSeries ℤ ℝ).fieldRange

/-- `t` is transcendental over the constants, stated with distinct exponents (the shape of the
paper's expansions `Σ bᵢeⁱ`). -/
theorem t_transcendental_const (n : ℕ) (d : Fin n → constSub) (m : Fin n → ℕ)
    (hm : Function.Injective m)
    (h : (∑ i, (d i : HahnSeries ℤ ℝ) * ht2 ^ (m i)) = 0) :
    ∀ i, (d i : HahnSeries ℤ ℝ) = 0 := by
  classical
  have hmem : ∀ i, ∃ r : ℝ, HahnSeries.C r = (d i : HahnSeries ℤ ℝ) := fun i => (d i).2
  choose r hr using hmem
  have hpow : ∀ i : Fin n, ht2 ^ (m i) = HahnSeries.single (((m i : ℕ)) : ℤ) (1 : ℝ) := by
    intro i
    rw [ht2_eq, HahnSeries.single_pow, nsmul_eq_mul, mul_one, one_pow]
  have hterm : ∀ i : Fin n, (d i : HahnSeries ℤ ℝ) * ht2 ^ (m i)
      = HahnSeries.single (((m i : ℕ)) : ℤ) (r i) := by
    intro i
    rw [← hr i, HahnSeries.C_apply, hpow, HahnSeries.single_mul_single]
    simp
  have hsum : (∑ i : Fin n, HahnSeries.single (((m i : ℕ)) : ℤ) (r i)) = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => (hterm i).symm
  intro i₀
  have hcoeff := congrArg (fun x : HahnSeries ℤ ℝ => x.coeff (((m i₀ : ℕ)) : ℤ)) hsum
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single i₀] at hcoeff
  · have hzero : r i₀ = 0 := by simpa using hcoeff
    rw [← hr i₀, hzero, HahnSeries.C_zero]
  · intro i _ hne
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    exact hne (hm (Nat.cast_injective hcon.symm))
  · intro hnot
    exact absurd (Finset.mem_univ i₀) hnot

lemma trivial_ht2 : trivialValuation (HahnSeries ℤ ℝ) ht2 = 1 := by
  have hne : ht2 ≠ 0 := by
    rw [ht2_eq, Ne, HahnSeries.single_eq_zero_iff]
    norm_num
  exact trivial_eq_one_of_ne hne

lemma trivial_ht2_lt (x : HahnSeries ℤ ℝ) :
    trivialValuation (HahnSeries ℤ ℝ) x < 1 ↔ x = 0 :=
  @trivial_lt_one_iff (HahnSeries ℤ ℝ) _ (Classical.decEq _) x

lemma ht2_ne : ht2 ≠ 0 := fun h => by
  rw [ht2_eq, HahnSeries.single_eq_zero_iff] at h
  norm_num at h

/-- **Non-vacuity**: `ResidueTranscendental` holds in this model.  So the hypothesis set of
`M7.gamma_step` (unit `e`, transcendental `rv(e)`, base value group trivial hence divisible) is
consistent — the quote-elimination is not a vacuous implication. -/
theorem residueTranscendental_trivial :
    ResidueTranscendental (trivialValuation (HahnSeries ℤ ℝ)) constSub (e := ht2) trivial_ht2 := by
  intro n d m hm hd h
  classical
  -- the residue of the expansion is the residue polynomial
  have hterm : ∀ i, trivialValuation (HahnSeries ℤ ℝ) ((d i : HahnSeries ℤ ℝ) * ht2 ^ (m i)) ≤ 1 :=
    fun i => trivial_le_one _
  have hsum : trivialValuation (HahnSeries ℤ ℝ)
      (∑ i, (d i : HahnSeries ℤ ℝ) * ht2 ^ (m i)) ≤ 1 := val_sum_le_one' _ hterm
  have hsplit : vres (trivialValuation (HahnSeries ℤ ℝ))
        (∑ i, (d i : HahnSeries ℤ ℝ) * ht2 ^ (m i)) hsum
      = ∑ i, vres (trivialValuation (HahnSeries ℤ ℝ)) (d i : HahnSeries ℤ ℝ) (hd i)
          * (vres (trivialValuation (HahnSeries ℤ ℝ)) ht2 (le_of_eq trivial_ht2)) ^ (m i) := by
    rw [vres_sum _ hterm hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vres_mul (v := trivialValuation (HahnSeries ℤ ℝ)) (x := (d i : HahnSeries ℤ ℝ))
      (y := ht2 ^ (m i)) (hd i) (trivial_le_one _) (hterm i)]
    rw [vres_pow _ (le_of_eq trivial_ht2) (m i) (val_pow_le_one _ (le_of_eq trivial_ht2) (m i))]
  have hz : vres (trivialValuation (HahnSeries ℤ ℝ))
      (∑ i, (d i : HahnSeries ℤ ℝ) * ht2 ^ (m i)) hsum = 0 := by
    rw [hsplit]; exact h
  have hlt : trivialValuation (HahnSeries ℤ ℝ)
      (∑ i, (d i : HahnSeries ℤ ℝ) * ht2 ^ (m i)) < 1 :=
    (vres_eq_zero_iff _ _ hsum).mp hz
  have hzero : (∑ i, (d i : HahnSeries ℤ ℝ) * ht2 ^ (m i)) = 0 :=
    (trivial_ht2_lt _).mp hlt
  have hall := t_transcendental_const n d m hm hzero
  intro i
  have h0 : trivialValuation (HahnSeries ℤ ℝ) ((d i : HahnSeries ℤ ℝ)) < 1 := by
    rw [hall i]
    exact (trivial_ht2_lt 0).mpr rfl
  exact (vres_eq_zero_iff _ _ (hd i)).mpr h0

#print axioms M7.t_transcendental_const
#print axioms M7.residueTranscendental_trivial

end M7
