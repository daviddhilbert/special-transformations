import ResidueTranscendentalTransport
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.BigOperators.Field

/-!
An actual field embedding for Yin's residue-transcendental case.
The field and RV maps on the base are given; source residue transcendence proves
nonvanishing on BOTH sides, so the field extension is constructed rather than
assumed.  No saturation and no extension of the partial RV map to the entire
ambient RV group are required.
-/

namespace ResidueTranscendentalTransport

open scoped BigOperators IntermediateField
open Polynomial

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem sum_normalize {F E : Type*} [Field F] [Field E]
    (ι : F →+* E) {n : ℕ} (c : Fin n → F) (m : Fin n → ℕ) (e : E) (a : F) :
    (∑ i, ι (c i / a) * e ^ m i) = (∑ i, ι (c i) * e ^ m i) / ι a := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_div₀, div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem nonzero_sums (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    {n : ℕ} {c : Fin n → F} {m : Fin n → ℕ} {e : K} {d : L}
    (he : v e = 1) (hd : w d = 1)
    (hT : M7.ResidueTranscendental v F he) (hm : Function.Injective m)
    (hne : ∃ i, c i ≠ 0)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    (∑ i, (c i : K) * e ^ m i) ≠ 0 ∧ (∑ i, σ (c i) * d ^ m i) ≠ 0 := by
  obtain ⟨a, _, hs, ht, _⟩ :=
    normalized_sums v w F σ ρ hintegral hres he hd hT hm hne hvar
  constructor
  · intro hz
    have hnorm := sum_normalize F.subtype c m e a
    change (∑ i, ((c i / a : F) : K) * e ^ m i) =
      (∑ i, (c i : K) * e ^ m i) / (a : K) at hnorm
    rw [hnorm, hz, zero_div, map_zero] at hs
    exact zero_ne_one hs
  · intro hz
    rw [sum_normalize σ c m d a, hz, zero_div, map_zero] at ht
    exact zero_ne_one ht

theorem eval₂_eq_fin_sum {F E : Type*} [Field F] [Field E]
    (ι : F →+* E) (p : Polynomial F) (e : E) :
    p.eval₂ ι e = ∑ i : Fin (p.natDegree + 1), ι (p.coeff i) * e ^ (i : ℕ) := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => ι (p.coeff i) * e ^ i) _).symm

theorem polynomial_nonvanishing (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    {e : K} {d : L} (he : v e = 1) (hd : w d = 1)
    (hT : M7.ResidueTranscendental v F he)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le)
    {p : Polynomial F} (hp : p ≠ 0) :
    p.eval₂ F.subtype e ≠ 0 ∧ p.eval₂ σ d ≠ 0 := by
  rw [eval₂_eq_fin_sum, eval₂_eq_fin_sum]
  apply nonzero_sums v w F σ ρ hintegral hres he hd hT
    (fun _ _ h => Fin.ext h) _ hvar
  exact ⟨⟨p.natDegree, Nat.lt_succ_self _⟩, by
    simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hp⟩

theorem rv_polynomial_relation (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    (hunit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le →
        R (RVCalc.rv v x) (RVCalc.rv w y))
    {e : K} {d : L} (he : v e = 1) (hd : w d = 1)
    (hT : M7.ResidueTranscendental v F he)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) (p : Polynomial F) :
    R (RVCalc.rv v (p.eval₂ F.subtype e)) (RVCalc.rv w (p.eval₂ σ d)) := by
  rw [eval₂_eq_fin_sum, eval₂_eq_fin_sum]
  exact rv_sum_relation v w F σ ρ R hzero hmul hintegral hres hbase hunit he hd hT
    (fun _ _ h => Fin.ext h) hvar

/-- The field-map half of Yin's Claim (*), with prescribed RV compatibility on
the entire one-generator field.  This constructs the map on the actual field
`F(e)`, not merely a compatible image for each element separately. -/
theorem exists_field_embedding (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hinv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a'))
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    (hunit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le →
        R (RVCalc.rv v x) (RVCalc.rv w y))
    {e : K} {d : L} (he : v e = 1) (hd : w d = 1)
    (hT : M7.ResidueTranscendental v F he)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    ∃ g : F⟮e⟯ →+* L,
      Function.Injective g ∧
      (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
      g (IntermediateField.AdjoinSimple.gen F e) = d ∧
      ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  letI : Algebra F L := σ.toAlgebra
  have heT : Transcendental F e := by
    rintro ⟨p, hp, hz⟩
    exact (polynomial_nonvanishing v w F σ ρ hintegral hres he hd hT hvar hp).1 hz
  have hdT : Transcendental F d := by
    rintro ⟨p, hp, hz⟩
    exact (polynomial_nonvanishing v w F σ ρ hintegral hres he hd hT hvar hp).2 hz
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
    · exact rv_polynomial_relation v w F σ ρ R hzero hmul hintegral hres hbase hunit
        he hd hT hvar r.num
    · exact rv_polynomial_relation v w F σ ρ R hzero hmul hintegral hres hbase hunit
        he hd hT hvar r.denom

end ResidueTranscendentalTransport

#print axioms ResidueTranscendentalTransport.nonzero_sums
#print axioms ResidueTranscendentalTransport.polynomial_nonvanishing
#print axioms ResidueTranscendentalTransport.rv_polynomial_relation
#print axioms ResidueTranscendentalTransport.exists_field_embedding
