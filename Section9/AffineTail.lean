import Section7.GeneralizedHensel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! The affine correction on the tail of the lift in Theorem 9.16.
Centres are supplied by the finite-family centre theorem in the eventual
definability argument. This file proves the fibre bijection and chooses
slopes with an exact product while keeping the original radii. -/

open SpecialTransformations.Section7
open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem rv_eq_centre_iff (v : Valuation K Γ) {a : K} (ha : a ≠ 0) (x : K) :
    RVCalc.rv v x = RVCalc.rv v a ↔ v (x - a) < v a := by
  by_cases hx : x = 0
  · subst x
    rw [RVCalc.rv_zero, zero_sub, v.map_neg]
    exact iff_of_false (fun h => RVCalc.rv_ne_none ha h.symm) (lt_irrefl _)
  · rw [eq_comm, RVCalc.rv_eq_iff ha hx, v.map_sub_swap]

private theorem rv_affine_iff (v : Valuation K Γ) {a b c : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : v c * v a = v b) (x : K) :
    RVCalc.rv v (b + c * (x - a)) = RVCalc.rv v b ↔ RVCalc.rv v x = RVCalc.rv v a := by
  rw [rv_eq_centre_iff v hb, rv_eq_centre_iff v ha]
  rw [show b + c * (x - a) - b = c * (x - a) by ring, map_mul, ← h]
  exact mul_lt_mul_iff_right₀ (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hc))

def affineTail {n : ℕ} (a b c : Fin n → K) (x : Fin n → K) : Fin n → K :=
  fun i => b i + c i * (x i - a i)

theorem affineTail_add_single {n : ℕ} (a b c x : Fin n → K) (i j : Fin n) (t : K) :
    affineTail a b c (x + Pi.single j t) i - affineTail a b c x i =
      (if i = j then c i else 0) * t := by
  classical
  by_cases h : i = j
  · subst j
    simp only [affineTail, Pi.add_apply, Pi.single_eq_same, if_true]
    ring
  · simp [affineTail, Pi.single_eq_of_ne h, h]

/-- Matching radii in each coordinate suffice for an actual bijection of
the entire product RV fibres, including the points at their centres. -/
theorem affineTail_bijOn (v : Valuation K Γ) {n : ℕ} (a b c : Fin n → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hval : ∀ i, v (c i) * v (a i) = v (b i)) :
    Set.BijOn (affineTail a b c) (RVFibre v (fun i => RVCalc.rv v (a i)))
      (RVFibre v (fun i => RVCalc.rv v (b i))) := by
  have hmem (x : Fin n → K) :
      affineTail a b c x ∈ RVFibre v (fun i => RVCalc.rv v (b i)) ↔
      x ∈ RVFibre v (fun i => RVCalc.rv v (a i)) :=
    forall_congr' (fun i => rv_affine_iff v (ha i) (hb i) (hc i) (hval i) (x i))
  refine ⟨fun x hx => (hmem x).mpr hx, ?_, ?_⟩
  · intro x _ y _ hxy
    funext i
    have he := congrFun hxy i
    change b i + c i * (x i - a i) = b i + c i * (y i - a i) at he
    have hsub := mul_left_cancel₀ (hc i) (add_left_cancel he)
    simpa only [sub_add_cancel] using congrArg (fun z : K => z + a i) hsub
  · intro y hy
    let x := fun i => a i + (y i - b i) / c i
    have he : affineTail a b c x = y := by
      funext i
      change b i + c i * (a i + (y i - b i) / c i - a i) = y i
      rw [show a i + (y i - b i) / c i - a i = (y i - b i) / c i by abel]
      rw [mul_comm (c i), div_mul_cancel₀ _ (hc i)]
      abel
    exact ⟨x, (hmem x).mp (he.symm ▸ hy), he⟩

def affineTailSlopes {n : ℕ} (a b : Fin n → K) (j : Fin n) (d : K) : Fin n → K :=
  Function.update (fun i => b i / a i) j (d / ∏ i ∈ Finset.univ.erase j, b i / a i)

theorem affineTailSlopes_eq_of_ne {n : ℕ} (a b : Fin n → K) (j : Fin n) (d : K)
    {i : Fin n} (hi : i ≠ j) : affineTailSlopes a b j d i = b i / a i :=
  Function.update_of_ne hi _ _

theorem eq_affineTailSlopes_of_equations {n : ℕ} (a b c : Fin n → K) (j : Fin n) (d : K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hfixed : ∀ i ≠ j, a i * c i = b i) (hprod : (∏ i, c i) = d) :
    c = affineTailSlopes a b j d := by
  classical
  have hc (i : Fin n) (hi : i ≠ j) : c i = b i / a i :=
    (eq_div_iff (ha i)).mpr ((mul_comm _ _).trans (hfixed i hi))
  let P := ∏ i ∈ Finset.univ.erase j, b i / a i
  have he : (∏ i ∈ Finset.univ.erase j, c i) = P := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hc i (Finset.ne_of_mem_erase hi)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => div_ne_zero (hb i) (ha i)
  have hj : c j * P = d := by
    rw [← he, Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact hprod
  funext i
  by_cases hi : i = j
  · subst i
    change c j = Function.update (fun i => b i / a i) j (d / P) j
    rw [Function.update_self]
    exact (eq_div_iff hP).mpr hj
  · exact (hc i hi).trans (affineTailSlopes_eq_of_ne a b j d hi).symm

/-- The explicit affine slopes have the prescribed product and send
the source RV fibre bijectively to the target fibre. -/
theorem affineTailSlopes_spec (v : Valuation K Γ) {n : ℕ}
    (a b : Fin n → K) (j : Fin n) (d : K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hval : v d = ∏ i, v (b i) / v (a i)) :
    let c := affineTailSlopes a b j d
    (∏ i, c i) = d ∧
      Set.BijOn (affineTail a b c) (RVFibre v (fun i => RVCalc.rv v (a i)))
        (RVFibre v (fun i => RVCalc.rv v (b i))) := by
  classical
  let f : Fin n → K := fun i => b i / a i
  let R : Finset (Fin n) := Finset.univ.erase j
  let D : K := ∏ i ∈ R, f i
  let c := Function.update f j (d / D)
  have hf (i : Fin n) : f i ≠ 0 := div_ne_zero (hb i) (ha i)
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hf i
  have hD : f j * D = ∏ i, f i := by
    simpa only [D, R] using
      (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j))
  have hv : v d = v (∏ i, f i) := by
    simpa only [map_prod, f, map_div₀] using hval
  have hcv (i : Fin n) : v (c i) = v (f i) := by
    by_cases hi : i = j
    · subst i
      change v (Function.update f j (d / D) j) = v (f j)
      rw [Function.update_self, map_div₀, hv, ← hD, map_mul,
        mul_div_cancel_right₀ _ (v.ne_zero_iff.mpr hD0)]
    · rw [show c i = f i from Function.update_of_ne hi _ _]
  have hc0 (i : Fin n) : c i ≠ 0 := by
    apply v.ne_zero_iff.mp
    rw [hcv]
    exact v.ne_zero_iff.mpr (hf i)
  change (∏ i, c i) = d ∧ _
  refine ⟨?_, affineTail_bijOn v a b c ha hb hc0 ?_⟩
  · change (∏ i, Function.update f j (d / D) i) = d
    rw [Finset.prod_update_of_mem (Finset.mem_univ j)]
    rw [Finset.sdiff_singleton_eq_erase]
    change d / D * D = d
    exact div_mul_cancel₀ d hD0
  · intro i
    rw [hcv]
    change v (b i / a i) * v (a i) = v (b i)
    rw [map_div₀, div_mul_cancel₀ _ (v.ne_zero_iff.mpr (ha i))]

/-- On a nonempty tail, the determinant of the diagonal linear part
can take any prescribed value with the required valuation. -/
theorem exists_affineTail_with_product (v : Valuation K Γ) {n : ℕ}
    (a b : Fin n → K) (j : Fin n) (d : K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hval : v d = ∏ i, v (b i) / v (a i)) :
    ∃ c : Fin n → K, (∏ i, c i) = d ∧
      Set.BijOn (affineTail a b c) (RVFibre v (fun i => RVCalc.rv v (a i)))
        (RVFibre v (fun i => RVCalc.rv v (b i))) :=
  ⟨affineTailSlopes a b j d, affineTailSlopes_spec v a b j d ha hb hval⟩

end SpecialTransformations.Section9
