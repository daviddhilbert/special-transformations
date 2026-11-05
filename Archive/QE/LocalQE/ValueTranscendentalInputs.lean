import ValueTranscendentalTransport
import RVValueMap

/-!
Primitive inputs for the value-transcendental field extension.

The source condition says that no positive power of the new value belongs to
the base value group. The target comparison condition is derived from the
actual partial RV relation preserving and reflecting its value preorder.
No extension of a partial map to all RV classes or all values is assumed.
-/

namespace ValueTranscendentalTransport

open ResidueTranscendentalTransport
open scoped IntermediateField

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

def ValueTranscendental (v : Valuation K Γ) (F : Subfield K) (e : K) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a : F, (v e) ^ n ≠ v (a : K)

theorem monomial_value_ne_of_lt (v : Valuation K Γ) (F : Subfield K)
    {e : K} (he : e ≠ 0) (htrans : ValueTranscendental v F e)
    {a b : F} (hb : b ≠ 0) {i j : ℕ} (hij : i < j) :
    v ((a : K) * e ^ i) ≠ v ((b : K) * e ^ j) := by
  have heval : v e ≠ 0 := (Valuation.ne_zero_iff v).mpr he
  have hbval : v (b : K) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr (fun h => hb (Subtype.ext h))
  intro h
  rw [map_mul, map_mul, map_pow, map_pow,
    show j = i + (j - i) from (Nat.add_sub_of_le hij.le).symm, pow_add] at h
  have hcancel : v (a : K) = v (b : K) * (v e) ^ (j - i) := by
    apply mul_right_cancel₀ (pow_ne_zero i heval)
    calc
      v (a : K) * (v e) ^ i = v (b : K) * ((v e) ^ i * (v e) ^ (j - i)) := h
      _ = (v (b : K) * (v e) ^ (j - i)) * (v e) ^ i := by ac_rfl
  apply htrans (j - i) (Nat.sub_pos_of_lt hij) (a / b)
  change (v e) ^ (j - i) = v ((a : K) / (b : K))
  rw [Valuation.map_div, eq_div_iff hbval, mul_comm]
  exact hcancel.symm

theorem separated_of_valueTranscendental (v : Valuation K Γ) (F : Subfield K)
    {e : K} (he : e ≠ 0) (htrans : ValueTranscendental v F e) :
    SeparatedMonomials v F e := by
  intro a b i j ha hb hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact monomial_value_ne_of_lt v F he htrans hb hlt
  · exact (monomial_value_ne_of_lt v F he htrans ha hgt).symm

/-- Divisibility is required only for values already represented in the base. -/
def DivisibleBaseValues (v : Valuation K Γ) (F : Subfield K) : Prop :=
  ∀ (a : F) (n : ℕ), 0 < n → ∃ b : F, (v (b : K)) ^ n = v (a : K)

theorem valueTranscendental_of_new_value (v : Valuation K Γ) (F : Subfield K)
    (hdiv : DivisibleBaseValues v F) {e : K}
    (hnew : ∀ a : F, v e ≠ v (a : K)) : ValueTranscendental v F e := by
  intro n hn a heq
  obtain ⟨b, hb⟩ := hdiv a n hn
  exact hnew b ((pow_left_inj₀ zero_le zero_le (Nat.ne_of_gt hn)).mp (heq.trans hb.symm))

/-- Preservation/reflection of the RV value preorder gives all monomial cuts.
The input applies only to pairs in R, so it is appropriate for a partial map. -/
theorem monomialCutCompatible_of_rvOrder (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {d : L} (hed : R (RVCalc.rv v e) (RVCalc.rv w d))
    (horder : ∀ a b a' b', R a a' → R b b' →
      (RVCalc.vrv v a ≤ RVCalc.vrv v b ↔ RVCalc.vrv w a' ≤ RVCalc.vrv w b')) :
    MonomialCutCompatible v w F σ e d := by
  have hmon : ∀ (a : F) (i : ℕ),
      R (RVCalc.rv v ((a : K) * e ^ i)) (RVCalc.rv w (σ a * d ^ i)) := by
    intro a i
    rw [rv_mul_all, rv_mul_all]
    exact hmul _ _ _ _ (hbase a) (rv_power_relation v w F σ R hmul hbase hed i)
  intro a b i j
  have hab := horder _ _ _ _ (hmon a i) (hmon b j)
  have hba := horder _ _ _ _ (hmon b j) (hmon a i)
  simp only [RVCalc.vrv_rv] at hab hba
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hab, hba]

/-- The value-transcendental field extension from ordinary partial RV-map data
and a new value over a base with divisible value group. -/
theorem exists_field_embedding_of_new_value (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hinv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a'))
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {d : L} (hed : R (RVCalc.rv v e) (RVCalc.rv w d))
    (horder : ∀ a b a' b', R a a' → R b b' →
      (RVCalc.vrv v a ≤ RVCalc.vrv v b ↔ RVCalc.vrv w a' ≤ RVCalc.vrv w b'))
    (hdiv : DivisibleBaseValues v F)
    (hnew : ∀ a : F, v e ≠ v (a : K)) :
    ∃ g : F⟮e⟯ →+* L,
      Function.Injective g ∧
      (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
      g (IntermediateField.AdjoinSimple.gen F e) = d ∧
      ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  have he : e ≠ 0 := by
    intro hz
    exact hnew 0 (by simp [hz])
  have h0 : R (RVCalc.rv v 0) (RVCalc.rv w 0) := by simpa using hzero
  have hd : d ≠ 0 := by
    intro hz
    have hh := horder _ _ _ _ hed h0
    simp only [RVCalc.vrv_rv, hz, map_zero] at hh
    exact he ((Valuation.zero_iff v).mp (le_antisymm (hh.mpr le_rfl) zero_le))
  exact exists_field_embedding v w F σ R hzero hmul hinv hbase he hd hed
    (separated_of_valueTranscendental v F he (valueTranscendental_of_new_value v F hdiv hnew))
    (monomialCutCompatible_of_rvOrder v w F σ R hmul hbase hed horder)

end ValueTranscendentalTransport

#print axioms ValueTranscendentalTransport.monomial_value_ne_of_lt
#print axioms ValueTranscendentalTransport.separated_of_valueTranscendental
#print axioms ValueTranscendentalTransport.valueTranscendental_of_new_value
#print axioms ValueTranscendentalTransport.monomialCutCompatible_of_rvOrder
#print axioms ValueTranscendentalTransport.exists_field_embedding_of_new_value
