import Section9.CoarsenedGauss
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Nested positive infinitesimals have distinct fine values on
distinct monomials. At each step the coefficient field contains the
earlier coordinates and is closed under taking roots. -/

namespace SpecialTransformations.Section9

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

private theorem value_pow_ne_of_infinitesimal (v : Valuation K Γ)
    (B : Subfield K) [IsAlgClosed B] (x : K) (hx₀ : x ≠ 0) (hx : v x < 1)
    (h : ∀ c : B, (c : K) ≠ 0 → v (c : K) < 1 → v (c : K) < v x)
    (p : ℕ) (hp : 0 < p) (c : B) : v x ^ p ≠ v (c : K) := by
  intro he
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c hp
  have hr' : v (r : K) ^ p = v (c : K) := by
    rw [← map_pow]
    exact congrArg (fun z : B => v (z : K)) hr
  have hv : v (r : K) = v x := (pow_left_inj₀ zero_le zero_le hp.ne').mp (hr'.trans he.symm)
  have hr₀ : (r : K) ≠ 0 := v.ne_zero_iff.mp (hv.trans_ne (v.ne_zero_iff.mpr hx₀))
  exact (h r hr₀ (hv.trans_lt hx)).ne hv

private theorem no_value_balance_of_exponent_lt (v : Valuation K Γ)
    (B : Subfield K) [IsAlgClosed B] (x : K) (hx₀ : x ≠ 0) (hx : v x < 1)
    (h : ∀ c : B, (c : K) ≠ 0 → v (c : K) < 1 → v (c : K) < v x)
    (a b : B) (hb : (b : K) ≠ 0) {p q : ℕ} (hpq : p < q) :
    v (a : K) * v x ^ p ≠ v (b : K) * v x ^ q := by
  intro he
  let d := q - p
  have hd : 0 < d := Nat.sub_pos_of_lt hpq
  have hq : q = d + p := by omega
  have hcancel : v (a : K) = v (b : K) * v x ^ d := by
    apply mul_right_cancel₀ (pow_ne_zero p (v.ne_zero_iff.mpr hx₀))
    rw [mul_assoc, ← pow_add, ← hq]
    exact he
  apply value_pow_ne_of_infinitesimal v B x hx₀ hx h d hd (a / b)
  change v x ^ d = v ((a : K) / (b : K))
  rw [map_div₀]
  exact (eq_div_iff (v.ne_zero_iff.mpr hb)).mpr (by rw [mul_comm]; exact hcancel.symm)

theorem distinct_monomial_values_of_nested_infinitesimals
    (v : Valuation K Γ) (E : Subfield K) {n : ℕ} (x : Fin n → K)
    (B : Fin n → Subfield K) (hAlg : ∀ j, IsAlgClosed (B j))
    (hE : ∀ j, E ≤ B j) (hprev : ∀ i j, i < j → x i ∈ B j)
    (hx₀ : ∀ i, x i ≠ 0) (hx : ∀ i, v (x i) < 1)
    (hsmall : ∀ j (c : B j), (c : K) ≠ 0 → v (c : K) < 1 → v (c : K) < v (x j))
    (a b : E) (ha : (a : K) ≠ 0) (hb : (b : K) ≠ 0) (d e : Fin n → ℕ) (hne : d ≠ e) :
    v (a : K) * (∏ i, v (x i) ^ d i) ≠ v (b : K) * (∏ i, v (x i) ^ e i) := by
  classical
  induction n with
  | zero => exact (hne (Subsingleton.elim _ _)).elim
  | succ n ih =>
    intro he
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, ← mul_assoc, ← mul_assoc] at he
    let j := Fin.last n
    let da : Fin n → ℕ := d ∘ Fin.castSucc
    let ea : Fin n → ℕ := e ∘ Fin.castSucc
    let I := B j
    letI : IsAlgClosed I := hAlg j
    let c : I := ⟨(a : K) * ∏ i : Fin n, x i.castSucc ^ da i,
      I.mul_mem (hE j a.property) (I.prod_mem fun i _ => I.pow_mem (hprev _ j (Fin.castSucc_lt_last i)) _)⟩
    let f : I := ⟨(b : K) * ∏ i : Fin n, x i.castSucc ^ ea i,
      I.mul_mem (hE j b.property) (I.prod_mem fun i _ => I.pow_mem (hprev _ j (Fin.castSucc_lt_last i)) _)⟩
    have hc₀ : (c : K) ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero _ (hx₀ i.castSucc))
    have hf₀ : (f : K) ≠ 0 := mul_ne_zero hb (Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero _ (hx₀ i.castSucc))
    have hvals : v (c : K) * v (x j) ^ d j = v (f : K) * v (x j) ^ e j := by
      change v ((a : K) * ∏ i : Fin n, x i.castSucc ^ da i) * _ =
        v ((b : K) * ∏ i : Fin n, x i.castSucc ^ ea i) * _
      simpa only [map_mul, map_prod, map_pow, da, ea, Function.comp_apply, j] using he
    rcases lt_trichotomy (d j) (e j) with hlt | heq | hgt
    · exact no_value_balance_of_exponent_lt v I (x j) (hx₀ j) (hx j) (hsmall j) c f hf₀ hlt hvals
    · have hne' : da ≠ ea := by
        intro hd
        apply hne
        funext i
        refine Fin.lastCases heq (fun k => congrFun hd k) i
      apply ih (x ∘ Fin.castSucc) (B ∘ Fin.castSucc) (fun i => hAlg i.castSucc)
        (fun i => hE i.castSucc) (fun i j hij => hprev _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij))
        (fun i => hx₀ i.castSucc) (fun i => hx i.castSucc) (fun i => hsmall i.castSucc)
        da ea hne'
      change v (a : K) * (∏ i : Fin n, v (x i.castSucc) ^ da i) =
        v (b : K) * (∏ i : Fin n, v (x i.castSucc) ^ ea i)
      rw [heq] at he
      exact mul_right_cancel₀ (pow_ne_zero _ (v.ne_zero_iff.mpr (hx₀ j))) he
    · exact no_value_balance_of_exponent_lt v I (x j) (hx₀ j) (hx j) (hsmall j) f c hc₀ hgt hvals.symm

end SpecialTransformations.Section9
