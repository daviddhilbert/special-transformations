import Section6.HenselianTheory
import Mathlib.Algebra.Polynomial.Derivative
import VFValued

/-! Semantic polynomial and derivative calculations for the native
simple-root scheme. The same calculation is used in both directions of
the valued-field representation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.HenselianTheory

variable {K Γ M : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [LRV.Structure M]

structure FieldInterpretation (v : Valuation K Γ) where
  pack : K → M
  injective : Function.Injective pack
  sort : ∀ z, iVF z ↔ ∃ a, pack a = z
  zero : pack 0 = iVFZero
  one : pack 1 = iVFOne
  add : ∀ a b, pack (a + b) = iVFAdd (pack a) (pack b)
  neg : ∀ a, pack (-a) = iVFNeg (pack a)
  mul : ∀ a b, pack (a * b) = iVFMul (pack a) (pack b)
  rvOne : iRv (pack 1) = iRVOne
  compare : ∀ a b, iLe (iRv (pack b)) (iRv (pack a)) ↔ v a ≤ v b

variable {v : Valuation K Γ} (F : FieldInterpretation (M := M) v)

theorem FieldInterpretation.pack_sort (a : K) : iVF (F.pack a) :=
  (F.sort _).mpr ⟨a, rfl⟩

theorem realize_numeral {n : ℕ} (z : Empty ⊕ Fin n → M) (k : ℕ) :
    (tVFNumeral k : Tm n).realize z = F.pack (k : K) := by
  induction k with
  | zero => simpa only [tVFNumeral, realize_tVFZero, Nat.cast_zero] using F.zero.symm
  | succ k ih =>
    rw [tVFNumeral, realize_tVFAdd, ih, realize_tVFOne, ← F.one, ← F.add, Nat.cast_succ]

theorem realize_power {n : ℕ} (z : Empty ⊕ Fin n → M) (t : Tm n)
    (a : K) (ha : t.realize z = F.pack a) (k : ℕ) :
    (tVFPow t k).realize z = F.pack (a ^ k) := by
  induction k with
  | zero => simpa only [tVFPow, realize_tVFOne, pow_zero] using F.one.symm
  | succ k ih =>
    rw [tVFPow, realize_tVFMul, ih, ha, ← F.mul, pow_succ]

private theorem realize_sum {n : ℕ} {ι : Type} (z : Empty ⊕ Fin n → M)
    (l : List ι) (terms : ι → Tm n) (values : ι → K)
    (h : ∀ i, (terms i).realize z = F.pack (values i)) :
    ((l.map terms).foldr tVFAdd tVFZero).realize z =
      F.pack ((l.map values).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.foldr_nil, List.sum_nil, realize_tVFZero] using F.zero.symm
  | cons i l ih =>
    rw [List.map_cons, List.foldr_cons, realize_tVFAdd, h i, ih, ← F.add,
      List.map_cons, List.sum_cons]

def coefficientPolynomial {R : Type} [CommRing R] {n : ℕ}
    (c : Fin (n + 1) → R) : Polynomial R :=
  ∑ i : Fin (n + 1), Polynomial.C (c i) * Polynomial.X ^ i.val

theorem coefficientPolynomial_eval {R : Type} [CommRing R] {n : ℕ}
    (c : Fin (n + 1) → R) (a : R) :
    (coefficientPolynomial c).eval a = ∑ i : Fin (n + 1), c i * a ^ i.val := by
  simp [coefficientPolynomial, Polynomial.eval_finsetSum]

theorem coefficientPolynomial_derivative_eval {R : Type} [CommRing R] {n : ℕ}
    (c : Fin (n + 1) → R) (a : R) :
    (coefficientPolynomial c).derivative.eval a =
      ∑ i : Fin (n + 1), ((i.val : R) * c i) * a ^ (i.val - 1) := by
  rw [coefficientPolynomial, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.derivative_C_mul_X_pow]
  simp [mul_comm]

private theorem sum_finRange {R : Type} [AddCommMonoid R] {n : ℕ} (g : Fin n → R) :
    ((List.finRange n).map g).sum = ∑ i : Fin n, g i := by
  classical
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

theorem realize_polynomialTerm {n m : ℕ} (z : Empty ⊕ Fin m → M)
    (t : Fin (n + 1) → Tm m) (x : Tm m) (c : Fin (n + 1) → K) (a : K)
    (hc : ∀ i, (t i).realize z = F.pack (c i)) (hx : x.realize z = F.pack a) :
    (polynomialTerm t x).realize z = F.pack ((coefficientPolynomial c).eval a) := by
  rw [polynomialTerm, coefficientPolynomial_eval,
    realize_sum F z _ _ (fun i => c i * a ^ i.val)]
  · rw [sum_finRange]
  · intro i
    rw [realize_tVFMul, hc i, realize_power F z x a hx, ← F.mul]

theorem realize_derivativeTerm {n m : ℕ} (z : Empty ⊕ Fin m → M)
    (t : Fin (n + 1) → Tm m) (x : Tm m) (c : Fin (n + 1) → K) (a : K)
    (hc : ∀ i, (t i).realize z = F.pack (c i)) (hx : x.realize z = F.pack a) :
    (derivativeTerm t x).realize z = F.pack ((coefficientPolynomial c).derivative.eval a) := by
  rw [derivativeTerm, coefficientPolynomial_derivative_eval,
    realize_sum F z _ _ (fun i => ((i.val : K) * c i) * a ^ (i.val - 1))]
  · rw [sum_finRange]
  · intro i
    rw [realize_tVFMul, realize_tVFMul, realize_numeral F, hc i,
      realize_power F z x a hx, ← F.mul, ← F.mul]

theorem realize_integral {n : ℕ} (t : Tm n) (z : Fin n → M) (a : K)
    (ha : t.realize (Sum.elim default z) = F.pack a) :
    (integral t).Realize default z ↔ v a ≤ 1 := by
  rw [integral, realize_pLe, realize_tRv, ha, realize_tRVOne_T, ← F.rvOne,
    F.compare, map_one]

theorem realize_inMaximalIdeal {n : ℕ} (t : Tm n) (z : Fin n → M) (a : K)
    (ha : t.realize (Sum.elim default z) = F.pack a) :
    (inMaximalIdeal t).Realize default z ↔ v a < 1 := by
  simp only [inMaximalIdeal, pGtOne, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    realize_pLe, realize_tRv, realize_tRVOne_T, ha, ← F.rvOne, F.compare, map_one, not_le]
  exact ⟨And.right, fun h => ⟨h.le, h⟩⟩

theorem realize_valuationOne {n : ℕ} (t : Tm n) (z : Fin n → M) (a : K)
    (ha : t.realize (Sum.elim default z) = F.pack a) :
    (valuationOne t).Realize default z ↔ v a = 1 := by
  simp only [valuationOne, BoundedFormula.realize_inf, realize_pLe, realize_tRv,
    realize_tRVOne_T, ha, ← F.rvOne, F.compare, map_one]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

end SpecialTransformations.Section6.HenselianTheory
