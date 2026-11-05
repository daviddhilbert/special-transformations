import ValueTranscendentalInputs
import RVNthRootLifting
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Yin's finite value-degree step. A least positive value exponent gives
distinct monomial values below that degree. Consequently the binomial
X^n-a is the ordinary minimal polynomial, and a matching target root gives an
actual field embedding compatible with the prescribed partial RV relation. -/

namespace ValueAlgebraicTransport

open scoped BigOperators IntermediateField
open Polynomial ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

/-- No positive power below n is represented in the base value group. This is
only a condition on monomial values, not on polynomial evaluation. -/
def NoSmallerValuePower (v : Valuation K Γ) (F : Subfield K) (e : K) (n : ℕ) : Prop :=
  ∀ (i : ℕ), 0 < i → i < n → ∀ a : F, (v e) ^ i ≠ v (a : K)

theorem monomial_value_ne_of_lt (v : Valuation K Γ) (F : Subfield K)
    {e : K} {n : ℕ} (he : e ≠ 0) (hgap : NoSmallerValuePower v F e n)
    {a b : F} (hb : b ≠ 0) {i j : ℕ} (hij : i < j) (hjn : j < n) :
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
  apply hgap (j - i) (Nat.sub_pos_of_lt hij) (lt_of_le_of_lt (Nat.sub_le _ _) hjn) (a / b)
  change (v e) ^ (j - i) = v ((a : K) / (b : K))
  rw [Valuation.map_div, eq_div_iff hbval, mul_comm]
  exact hcancel.symm

theorem separated_below (v : Valuation K Γ) (F : Subfield K)
    {e : K} {n : ℕ} (he : e ≠ 0) (hgap : NoSmallerValuePower v F e n)
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) {i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    v ((a : K) * e ^ i) ≠ v ((b : K) * e ^ j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact monomial_value_ne_of_lt v F he hgap hb hlt hj
  · exact (monomial_value_ne_of_lt v F he hgap ha hgt hi).symm

/-- A nonzero bounded-degree sum has a unique leading monomial and is nonzero. -/
theorem leading_index (v : Valuation K Γ) (F : Subfield K)
    {e : K} {n m : ℕ} (he : e ≠ 0) (hgap : NoSmallerValuePower v F e n)
    (hmn : m ≤ n) {c : Fin m → F} (hne : ∃ i, c i ≠ 0) :
    ∃ j : Fin m, c j ≠ 0 ∧
      (∀ i : Fin m, i ≠ j → v ((c i : K) * e ^ (i : ℕ)) < v ((c j : K) * e ^ (j : ℕ))) ∧
      RVCalc.rv v (∑ i, (c i : K) * e ^ (i : ℕ)) = RVCalc.rv v ((c j : K) * e ^ (j : ℕ)) ∧
      (∑ i, (c i : K) * e ^ (i : ℕ)) ≠ 0 := by
  classical
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin m => v ((c i : K) * e ^ (i : ℕ))) (by
      obtain ⟨i, _⟩ := hne
      exact ⟨i, Finset.mem_univ _⟩)
  have hj : c j ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro hz
    have hb := hmax i (Finset.mem_univ _)
    simp only [hz, ZeroMemClass.coe_zero, zero_mul, map_zero] at hb
    have hterm : (c i : K) * e ^ (i : ℕ) ≠ 0 :=
      mul_ne_zero (fun h => hi (Subtype.ext h)) (pow_ne_zero _ he)
    exact hterm ((Valuation.zero_iff v).mp (le_antisymm hb zero_le))
  have hjK : (c j : K) * e ^ (j : ℕ) ≠ 0 :=
    mul_ne_zero (fun h => hj (Subtype.ext h)) (pow_ne_zero _ he)
  have hvj : v ((c j : K) * e ^ (j : ℕ)) ≠ 0 := (Valuation.ne_zero_iff v).mpr hjK
  have hlt : ∀ i : Fin m, i ≠ j →
      v ((c i : K) * e ^ (i : ℕ)) < v ((c j : K) * e ^ (j : ℕ)) := by
    intro i hij
    by_cases hi0 : c i = 0
    · simp only [hi0, ZeroMemClass.coe_zero, zero_mul, map_zero]
      exact zero_lt_iff.mpr hvj
    · exact lt_of_le_of_ne (hmax i (Finset.mem_univ _))
        (separated_below v F he hgap hi0 hj (lt_of_lt_of_le i.isLt hmn)
          (lt_of_lt_of_le j.isLt hmn) (fun h => hij (Fin.ext h)))
  have hlt' : ∀ i ∈ (Finset.univ : Finset (Fin m)) \ {j},
      v ((c i : K) * e ^ (i : ℕ)) < v ((c j : K) * e ^ (j : ℕ)) := by
    intro i hi
    exact hlt i (by simpa using (Finset.mem_sdiff.mp hi).2)
  have hs := Valuation.map_sum_eq_of_lt v (Finset.mem_univ j) hlt'
  refine ⟨j, hj, hlt, RVCalc.rv_sum_eq_of_lt (Finset.mem_univ j) hvj hlt', ?_⟩
  intro hz
  rw [hz, map_zero] at hs
  exact hvj hs.symm

theorem polynomial_nonvanishing (v : Valuation K Γ) (F : Subfield K)
    {e : K} {n : ℕ} (he : e ≠ 0) (hgap : NoSmallerValuePower v F e n)
    {p : Polynomial F} (hp : p ≠ 0) (hdegree : p.natDegree < n) :
    p.eval₂ F.subtype e ≠ 0 := by
  have hc : ∃ i : Fin (p.natDegree + 1), p.coeff (i : ℕ) ≠ 0 :=
    ⟨⟨p.natDegree, Nat.lt_succ_self _⟩, by
      simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hp⟩
  obtain ⟨_, _, _, _, hs⟩ := leading_index v F he hgap (Nat.succ_le_of_lt hdegree) hc
  rw [eval₂_eq_fin_sum]
  exact hs

theorem powers_linearIndependent (v : Valuation K Γ) (F : Subfield K)
    {e : K} {n : ℕ} (he : e ≠ 0) (hgap : NoSmallerValuePower v F e n) :
    LinearIndependent F (fun i : Fin n => e ^ (i : ℕ)) := by
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc i
  by_contra hci
  obtain ⟨_, _, _, _, hnz⟩ := leading_index v F he hgap le_rfl ⟨i, hci⟩
  have hcF : ∀ a : F, algebraMap F K a = (a : K) := fun a => rfl
  exact hnz (by simpa only [Algebra.smul_def, hcF] using hc)

theorem minpoly_eq_binomial (v : Valuation K Γ) (F : Subfield K)
    {e : K} {n : ℕ} (he : e ≠ 0) (hn : 0 < n)
    (hgap : NoSmallerValuePower v F e n) (a : F) (hroot : e ^ n = (a : K)) :
    minpoly F e = (X : Polynomial F) ^ n - C a := by
  apply minpoly.eq_of_linearIndependent F e (monic_X_pow_sub_C a hn.ne')
    (n := n) (hpn := degree_X_pow_sub_C hn a)
  · have ha : algebraMap F K a = (a : K) := rfl
    simp [hroot, ha]
  · exact powers_linearIndependent v F he hgap

/-- A bounded sum has the same leading monomial at any target respecting the
partial RV value order, so its RV class is transported by the given graph. -/
theorem rv_sum_relation (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {d : L} {n m : ℕ} (he : e ≠ 0) (hd : d ≠ 0)
    (hed : R (RVCalc.rv v e) (RVCalc.rv w d))
    (hgap : NoSmallerValuePower v F e n)
    (hcut : ValueTranscendentalTransport.MonomialCutCompatible v w F σ e d)
    (hmn : m ≤ n) (c : Fin m → F) :
    R (RVCalc.rv v (∑ i, (c i : K) * e ^ (i : ℕ)))
      (RVCalc.rv w (∑ i, σ (c i) * d ^ (i : ℕ))) := by
  classical
  by_cases hne : ∃ i, c i ≠ 0
  · obtain ⟨j, hj, hlt, hs, _⟩ := leading_index v F he hgap hmn hne
    have hjL : σ (c j) * d ^ (j : ℕ) ≠ 0 :=
      mul_ne_zero (fun h => hj (σ.injective (by simpa using h))) (pow_ne_zero _ hd)
    have hwj : w (σ (c j) * d ^ (j : ℕ)) ≠ 0 := (Valuation.ne_zero_iff w).mpr hjL
    have hlt' : ∀ i ∈ (Finset.univ : Finset (Fin m)) \ {j},
        w (σ (c i) * d ^ (i : ℕ)) < w (σ (c j) * d ^ (j : ℕ)) := by
      intro i hi
      exact (hcut (c i) (c j) i j).mp
        (hlt i (by simpa using (Finset.mem_sdiff.mp hi).2))
    have ht := RVCalc.rv_sum_eq_of_lt (Finset.mem_univ j) hwj hlt'
    rw [hs, ht, rv_mul_all, rv_mul_all]
    exact hmul _ _ _ _ (hbase (c j))
      (ValueTranscendentalTransport.rv_power_relation v w F σ R hmul hbase hed _)
  · have hz : ∀ i, c i = 0 := by
      intro i
      by_contra hi
      exact hne ⟨i, hi⟩
    simpa [hz] using hzero

/-- The finite value-degree field extension from a matching target root.
All polynomial noncancellation and the full field map are derived. -/
theorem exists_field_embedding (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {d : L} {n : ℕ} (he : e ≠ 0) (hn : 0 < n)
    (hed : R (RVCalc.rv v e) (RVCalc.rv w d))
    (horder : ∀ a b a' b', R a a' → R b b' →
      (RVCalc.vrv v a ≤ RVCalc.vrv v b ↔ RVCalc.vrv w a' ≤ RVCalc.vrv w b'))
    (hgap : NoSmallerValuePower v F e n) (a : F)
    (hepow : e ^ n = (a : K)) (hdpow : d ^ n = σ a) :
    ∃ g : F⟮e⟯ →+* L,
      Function.Injective g ∧
      (∀ b : F, g (algebraMap F F⟮e⟯ b) = σ b) ∧
      g (IntermediateField.AdjoinSimple.gen F e) = d ∧
      ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  letI : Algebra F L := σ.toAlgebra
  have hd : d ≠ 0 := by
    intro hz
    have h0 : R (RVCalc.rv v 0) (RVCalc.rv w 0) := by simpa using hzero
    have hh := horder _ _ _ _ hed h0
    simp only [RVCalc.vrv_rv, hz, map_zero] at hh
    exact he ((Valuation.zero_iff v).mp (le_antisymm (hh.mpr le_rfl) zero_le))
  let p : Polynomial F := X ^ n - C a
  have hp : p.Monic := monic_X_pow_sub_C a hn.ne'
  have hpe : p.eval₂ F.subtype e = 0 := by simp [p, hepow]
  have hpd : p.eval₂ σ d = 0 := by simp [p, hdpow]
  have heI : IsIntegral F e := ⟨p, hp, hpe⟩
  have hpmin : minpoly F e = p := minpoly_eq_binomial v F he hn hgap a hepow
  let pb : PowerBasis F F⟮e⟯ := IntermediateField.adjoin.powerBasis heI
  have hgenmin : minpoly F pb.gen = p := by
    change minpoly F (IntermediateField.AdjoinSimple.gen F e) = p
    rw [IntermediateField.minpoly_gen, hpmin]
  have hdroot : Polynomial.aeval d (minpoly F pb.gen) = 0 := by
    rw [hgenmin]
    exact hpd
  let g : F⟮e⟯ →ₐ[F] L := pb.lift d hdroot
  have hggen : g pb.gen = d := pb.lift_gen d hdroot
  have hdim : pb.dim = n := by
    change (minpoly F e).natDegree = n
    rw [hpmin]
    exact natDegree_X_pow_sub_C
  have hcut := ValueTranscendentalTransport.monomialCutCompatible_of_rvOrder
    v w F σ R hmul hbase hed horder
  refine ⟨g.toRingHom, g.injective, ?_, ?_, ?_⟩
  · intro b
    exact g.commutes b
  · exact hggen
  · intro x
    let c : Fin pb.dim → F := pb.basis.repr x
    have hx : (∑ i, (c i : K) * e ^ (i : ℕ)) = (x : K) := by
      have h := congrArg (F⟮e⟯).val (pb.basis.sum_repr x)
      have hcoeff : ∀ b : F, (F⟮e⟯).val (algebraMap F F⟮e⟯ b) = (b : K) := fun b => rfl
      have hvx : (F⟮e⟯).val x = (x : K) := rfl
      simpa only [map_sum, pb.basis_eq_pow, Algebra.smul_def, map_mul, map_pow, hcoeff, hvx, c,
        show (F⟮e⟯).val pb.gen = e from rfl] using h
    have hg : (∑ i, σ (c i) * d ^ (i : ℕ)) = g x := by
      have h := congrArg g (pb.basis.sum_repr x)
      have hcoeff : ∀ b : F, g (algebraMap F F⟮e⟯ b) = σ b := g.commutes
      simpa only [map_sum, pb.basis_eq_pow, Algebra.smul_def, map_mul, map_pow,
        hcoeff, hggen] using h
    change R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x))
    rw [← hx, ← hg]
    exact rv_sum_relation v w F σ R hzero hmul hbase he hd hed hgap hcut hdim.le c

/-- Root existence is also derived when the target field is algebraically
closed. Functionality of the partial RV graph identifies the required nth power. -/
theorem exists_field_embedding_of_rv_root [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hfun : ∀ x y z, R x y → R x z → y = z)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {c : L} {n : ℕ} (he : e ≠ 0) (hn : 0 < n)
    (hec : R (RVCalc.rv v e) (RVCalc.rv w c))
    (horder : ∀ a b a' b', R a a' → R b b' →
      (RVCalc.vrv v a ≤ RVCalc.vrv v b ↔ RVCalc.vrv w a' ≤ RVCalc.vrv w b'))
    (hgap : NoSmallerValuePower v F e n) (a : F) (hepow : e ^ n = (a : K)) :
    ∃ (d : L) (g : F⟮e⟯ →+* L),
      d ^ n = σ a ∧ RVCalc.rv w d = RVCalc.rv w c ∧ Function.Injective g ∧
      (∀ b : F, g (algebraMap F F⟮e⟯ b) = σ b) ∧
      g (IntermediateField.AdjoinSimple.gen F e) = d ∧
      ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  have ha : a ≠ 0 := by
    intro hz
    have h := hepow
    rw [hz, ZeroMemClass.coe_zero] at h
    exact pow_ne_zero n he h
  have haL : σ a ≠ 0 := fun h => ha (σ.injective (by simpa using h))
  have hc : c ≠ 0 := by
    intro hz
    have h0 : R (RVCalc.rv v 0) (RVCalc.rv w 0) := by simpa using hzero
    have hh := horder _ _ _ _ hec h0
    simp only [RVCalc.vrv_rv, hz, map_zero] at hh
    exact he ((Valuation.zero_iff v).mp (le_antisymm (hh.mpr le_rfl) zero_le))
  have hpow := ValueTranscendentalTransport.rv_power_relation v w F σ R hmul hbase hec n
  rw [hepow] at hpow
  have hclass : RVCalc.rv w (c ^ n) = RVCalc.rv w (σ a) :=
    hfun _ _ _ hpow (hbase a)
  obtain ⟨d, hd, hrv⟩ := RVCalc.nth_root_with_rv w hn haL hc hclass
  have hed : R (RVCalc.rv v e) (RVCalc.rv w d) := by rw [hrv]; exact hec
  obtain ⟨g, hg, hb, hegen, hRV⟩ :=
    exists_field_embedding v w F σ R hzero hmul hbase he hn hed horder hgap a hepow hd
  exact ⟨d, g, hd, hrv, hg, hb, hegen, hRV⟩

end ValueAlgebraicTransport

#print axioms ValueAlgebraicTransport.polynomial_nonvanishing
#print axioms ValueAlgebraicTransport.powers_linearIndependent
#print axioms ValueAlgebraicTransport.minpoly_eq_binomial
#print axioms ValueAlgebraicTransport.rv_sum_relation
#print axioms ValueAlgebraicTransport.exists_field_embedding
#print axioms ValueAlgebraicTransport.exists_field_embedding_of_rv_root
