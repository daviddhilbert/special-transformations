import RVLeadingSums
import ResidueTranscendentalFieldEmbedding

/-!
The value-transcendental one-generator extension, using only monomial data.

The input `SeparatedMonomials` states distinctness of the values of nonzero
monomials of different degrees. `MonomialCutCompatible` compares individual
monomials in the source and target.  Neither assumes a polynomial calculation,
polynomial nonvanishing, a field extension map, or saturation.

The proof finds the same unique leading term on both sides, then constructs
the actual field embedding F(e) → L with prescribed partial-RV-map agreement.
-/

namespace ValueTranscendentalTransport

open scoped BigOperators IntermediateField
open Polynomial ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

def SeparatedMonomials (v : Valuation K Γ) (F : Subfield K) (e : K) : Prop :=
  ∀ (a b : F) (i j : ℕ), a ≠ 0 → b ≠ 0 → i ≠ j →
    v ((a : K) * e ^ i) ≠ v ((b : K) * e ^ j)

def MonomialCutCompatible (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (e : K) (d : L) : Prop :=
  ∀ (a b : F) (i j : ℕ),
    v ((a : K) * e ^ i) < v ((b : K) * e ^ j) ↔
      w (σ a * d ^ i) < w (σ b * d ^ j)

/-- One and the same coefficient is the leading term in both fields. -/
theorem common_leading_index (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) {e : K} {d : L}
    (he : e ≠ 0) (hd : d ≠ 0)
    (hsep : SeparatedMonomials v F e)
    (hcut : MonomialCutCompatible v w F σ e d)
    {n : ℕ} {c : Fin n → F} {m : Fin n → ℕ}
    (hm : Function.Injective m) (hne : ∃ i, c i ≠ 0) :
    ∃ j : Fin n, c j ≠ 0 ∧
      RVCalc.rv v (∑ i, (c i : K) * e ^ m i) = RVCalc.rv v ((c j : K) * e ^ m j) ∧
      RVCalc.rv w (∑ i, σ (c i) * d ^ m i) = RVCalc.rv w (σ (c j) * d ^ m j) ∧
      (∑ i, (c i : K) * e ^ m i) ≠ 0 ∧ (∑ i, σ (c i) * d ^ m i) ≠ 0 := by
  classical
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => v ((c i : K) * e ^ m i)) (by
      obtain ⟨i, _⟩ := hne
      exact ⟨i, Finset.mem_univ _⟩)
  have hj : c j ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro hz
    have hb := hmax i (Finset.mem_univ _)
    simp only [hz, ZeroMemClass.coe_zero, zero_mul, map_zero] at hb
    have hterm : (c i : K) * e ^ m i ≠ 0 :=
      mul_ne_zero (fun h => hi (Subtype.ext h)) (pow_ne_zero _ he)
    exact hterm ((Valuation.zero_iff v).mp (le_antisymm hb zero_le))
  have hjK : (c j : K) * e ^ m j ≠ 0 :=
    mul_ne_zero (fun h => hj (Subtype.ext h)) (pow_ne_zero _ he)
  have hjL : σ (c j) * d ^ m j ≠ 0 :=
    mul_ne_zero (fun h => hj (σ.injective (by simpa using h))) (pow_ne_zero _ hd)
  have hvj : v ((c j : K) * e ^ m j) ≠ 0 := (Valuation.ne_zero_iff v).mpr hjK
  have hwj : w (σ (c j) * d ^ m j) ≠ 0 := (Valuation.ne_zero_iff w).mpr hjL
  have hlt : ∀ i ∈ (Finset.univ : Finset (Fin n)) \ {j},
      v ((c i : K) * e ^ m i) < v ((c j : K) * e ^ m j) := by
    intro i hi
    have hij : i ≠ j := by simpa using (Finset.mem_sdiff.mp hi).2
    by_cases hi0 : c i = 0
    · simp only [hi0, ZeroMemClass.coe_zero, zero_mul, map_zero]
      exact zero_lt_iff.mpr hvj
    · exact lt_of_le_of_ne (hmax i (Finset.mem_univ _))
        (hsep (c i) (c j) (m i) (m j) hi0 hj (fun h => hij (hm h)))
  have hlt' : ∀ i ∈ (Finset.univ : Finset (Fin n)) \ {j},
      w (σ (c i) * d ^ m i) < w (σ (c j) * d ^ m j) :=
    fun i hi => (hcut (c i) (c j) (m i) (m j)).mp (hlt i hi)
  have hs := Valuation.map_sum_eq_of_lt v (Finset.mem_univ j) hlt
  have ht := Valuation.map_sum_eq_of_lt w (Finset.mem_univ j) hlt'
  refine ⟨j, hj,
    RVCalc.rv_sum_eq_of_lt (Finset.mem_univ j) hvj hlt,
    RVCalc.rv_sum_eq_of_lt (Finset.mem_univ j) hwj hlt', ?_, ?_⟩
  · intro hz
    rw [hz, map_zero] at hs
    exact hvj hs.symm
  · intro hz
    rw [hz, map_zero] at ht
    exact hwj ht.symm

theorem rv_power_relation (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {d : L} (hed : R (RVCalc.rv v e) (RVCalc.rv w d)) (n : ℕ) :
    R (RVCalc.rv v (e ^ n)) (RVCalc.rv w (d ^ n)) := by
  induction n with
  | zero => simpa using hbase 1
  | succ n ih =>
      rw [pow_succ, pow_succ, rv_mul_all, rv_mul_all]
      exact hmul _ _ _ _ ih hed

theorem rv_sum_relation (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {d : L} (he : e ≠ 0) (hd : d ≠ 0)
    (hed : R (RVCalc.rv v e) (RVCalc.rv w d))
    (hsep : SeparatedMonomials v F e)
    (hcut : MonomialCutCompatible v w F σ e d)
    {n : ℕ} {c : Fin n → F} {m : Fin n → ℕ} (hm : Function.Injective m) :
    R (RVCalc.rv v (∑ i, (c i : K) * e ^ m i))
      (RVCalc.rv w (∑ i, σ (c i) * d ^ m i)) := by
  classical
  by_cases hne : ∃ i, c i ≠ 0
  · obtain ⟨j, _, hs, ht, _⟩ := common_leading_index v w F σ he hd hsep hcut hm hne
    rw [hs, ht, rv_mul_all, rv_mul_all]
    exact hmul _ _ _ _ (hbase (c j)) (rv_power_relation v w F σ R hmul hbase hed _)
  · have hz : ∀ i, c i = 0 := by
      intro i
      by_contra hi
      exact hne ⟨i, hi⟩
    simpa [hz] using hzero

theorem polynomial_nonvanishing (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) {e : K} {d : L}
    (he : e ≠ 0) (hd : d ≠ 0)
    (hsep : SeparatedMonomials v F e)
    (hcut : MonomialCutCompatible v w F σ e d)
    {p : Polynomial F} (hp : p ≠ 0) :
    p.eval₂ F.subtype e ≠ 0 ∧ p.eval₂ σ d ≠ 0 := by
  have hc : ∃ i : Fin (p.natDegree + 1), p.coeff (i : ℕ) ≠ 0 :=
    ⟨⟨p.natDegree, Nat.lt_succ_self _⟩, by
      simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hp⟩
  obtain ⟨_, _, _, _, hs, ht⟩ := common_leading_index v w F σ he hd hsep hcut
    (c := fun i : Fin (p.natDegree + 1) => p.coeff i)
    (m := fun i => (i : ℕ)) (fun _ _ h => Fin.ext h) hc
  rw [eval₂_eq_fin_sum, eval₂_eq_fin_sum]
  exact ⟨hs, ht⟩

theorem rv_polynomial_relation (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {d : L} (he : e ≠ 0) (hd : d ≠ 0)
    (hed : R (RVCalc.rv v e) (RVCalc.rv w d))
    (hsep : SeparatedMonomials v F e)
    (hcut : MonomialCutCompatible v w F σ e d) (p : Polynomial F) :
    R (RVCalc.rv v (p.eval₂ F.subtype e)) (RVCalc.rv w (p.eval₂ σ d)) := by
  rw [eval₂_eq_fin_sum, eval₂_eq_fin_sum]
  exact rv_sum_relation v w F σ R hzero hmul hbase he hd hed hsep hcut
    (fun _ _ h => Fin.ext h)

/-- The genuine field extension and its prescribed partial-RV compatibility,
from separation and monomial cut data alone. -/
theorem exists_field_embedding (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hinv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a'))
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    {e : K} {d : L} (he : e ≠ 0) (hd : d ≠ 0)
    (hed : R (RVCalc.rv v e) (RVCalc.rv w d))
    (hsep : SeparatedMonomials v F e)
    (hcut : MonomialCutCompatible v w F σ e d) :
    ∃ g : F⟮e⟯ →+* L,
      Function.Injective g ∧
      (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
      g (IntermediateField.AdjoinSimple.gen F e) = d ∧
      ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  letI : Algebra F L := σ.toAlgebra
  have heT : Transcendental F e := by
    rintro ⟨p, hp, hz⟩
    exact (polynomial_nonvanishing v w F σ he hd hsep hcut hp).1 hz
  have hdT : Transcendental F d := by
    rintro ⟨p, hp, hz⟩
    exact (polynomial_nonvanishing v w F σ he hd hsep hcut hp).2 hz
  let src : RatFunc F ≃ₐ[F] F⟮e⟯ := RatFunc.algEquivOfTranscendental e heT
  let dst : RatFunc F ≃ₐ[F] F⟮d⟯ := RatFunc.algEquivOfTranscendental d hdT
  let E : F⟮e⟯ ≃ₐ[F] F⟮d⟯ := src.symm.trans dst
  let g : F⟮e⟯ →ₐ[F] L := (F⟮d⟯).val.comp E.toAlgHom
  refine ⟨g.toRingHom, g.injective, ?_, ?_, ?_⟩
  · intro a
    exact g.commutes a
  · change ((dst (src.symm (IntermediateField.AdjoinSimple.gen F e)) : F⟮d⟯) : L) = d
    simp [src, dst]
  · intro x
    let r : RatFunc F := src.symm x
    have hx : (x : K) = (r.num.eval₂ F.subtype e) / (r.denom.eval₂ F.subtype e) := by
      have h := RatFunc.algEquivOfTranscendental_apply e heT r
      change ((src r : F⟮e⟯) : K) = _ at h
      rw [show src r = x from src.apply_symm_apply x] at h
      exact h
    have hg : g x = (r.num.eval₂ σ d) / (r.denom.eval₂ σ d) := by
      change ((dst r : F⟮d⟯) : L) = _
      exact RatFunc.algEquivOfTranscendental_apply d hdT r
    change R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x))
    rw [hx, hg]
    apply rv_div_relation v w R hmul hinv
    · exact rv_polynomial_relation v w F σ R hzero hmul hbase he hd hed hsep hcut r.num
    · exact rv_polynomial_relation v w F σ R hzero hmul hbase he hd hed hsep hcut r.denom

end ValueTranscendentalTransport

#print axioms ValueTranscendentalTransport.common_leading_index
#print axioms ValueTranscendentalTransport.rv_power_relation
#print axioms ValueTranscendentalTransport.rv_sum_relation
#print axioms ValueTranscendentalTransport.polynomial_nonvanishing
#print axioms ValueTranscendentalTransport.rv_polynomial_relation
#print axioms ValueTranscendentalTransport.exists_field_embedding
