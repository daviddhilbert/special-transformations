import ResidueTranscendentalFieldEmbedding

/-!
Finite residue-degree calculation for the local algebraic unit case of Yin 3.4.
The residue minimality input is ordinary linear independence below a given
residue degree. Normalization and transport of reduced expressions are proved.
No field-embedding or RV-transport conclusion is assumed.
-/

namespace ResidueAlgebraicTransport

open scoped BigOperators IntermediateField
open Polynomial ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

/-- Independence of powers below the residue degree, with coefficients from
the residues of integral base-field elements. -/
def ResidueIndependent (v : Valuation K Γ) (F : Subfield K)
    {e : K} (he : v e = 1) (N : ℕ) : Prop :=
  ∀ (c : Fin N → F) (hc : ∀ i, v (c i : K) ≤ 1),
    (∑ i, M7.vres v (c i : K) (hc i) * (M7.vres v e he.le) ^ (i : ℕ)) = 0 →
      ∀ i, M7.vres v (c i : K) (hc i) = 0

/-- The residue input follows from the usual minimal-polynomial degree over
the base residue subfield. -/
theorem residueIndependent_of_minpoly (v : Valuation K Γ) (F : Subfield K)
    (κ : Subfield (Residue v))
    (hκ : ∀ (a : F) (ha : v (a : K) ≤ 1), M7.vres v (a : K) ha ∈ κ)
    {e : K} (he : v e = 1) {N : ℕ}
    (hdegree : (minpoly κ (M7.vres v e he.le)).natDegree = N) :
    ResidueIndependent v F he N := by
  intro c hc hz i
  let cκ : Fin N → κ := fun i => ⟨M7.vres v (c i : K) (hc i), hκ (c i) (hc i)⟩
  have hind := linearIndependent_pow (K := κ) (M7.vres v e he.le)
  rw [hdegree] at hind
  have hcκ : ∀ i, algebraMap κ (Residue v) (cκ i) = M7.vres v (c i : K) (hc i) :=
    fun i => rfl
  have hs : ∑ i, cκ i • (M7.vres v e he.le) ^ (i : ℕ) = 0 := by
    simpa only [Algebra.smul_def, hcκ] using hz
  have hi := Fintype.linearIndependent_iff.mp hind cκ hs i
  exact congrArg Subtype.val hi

theorem normalized_sums (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    {N : ℕ} {c : Fin N → F} {e : K} {d : L}
    (he : v e = 1) (hd : w d = 1) (hI : ResidueIndependent v F he N)
    (hne : ∃ i, c i ≠ 0)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    ∃ a : F, a ≠ 0 ∧
      v (∑ i, ((c i / a : F) : K) * e ^ (i : ℕ)) = 1 ∧
      w (∑ i, σ (c i / a) * d ^ (i : ℕ)) = 1 ∧
      ∃ (hs : v (∑ i, ((c i / a : F) : K) * e ^ (i : ℕ)) ≤ 1)
        (ht : w (∑ i, σ (c i / a) * d ^ (i : ℕ)) ≤ 1),
        ρ (M7.vres v _ hs) = M7.vres w _ ht := by
  classical
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin N => v (c i : K)) (by
      obtain ⟨i, _⟩ := hne
      exact ⟨i, Finset.mem_univ _⟩)
  have ha : c i₀ ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro hzero
    have hb := hmax i (Finset.mem_univ _)
    simp only [hzero, ZeroMemClass.coe_zero, map_zero] at hb
    have hz : (c i : K) = 0 := (Valuation.zero_iff v).mp (le_antisymm hb zero_le)
    exact hi (Subtype.ext hz)
  have haK : (c i₀ : K) ≠ 0 := fun h => ha (Subtype.ext h)
  have hvpos : 0 < v (c i₀ : K) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr haK)
  have hc : ∀ i, v ((c i / c i₀ : F) : K) ≤ 1 := by
    intro i
    change v ((c i : K) / (c i₀ : K)) ≤ 1
    rw [Valuation.map_div, div_le_one₀ hvpos]
    exact hmax i (Finset.mem_univ _)
  have hc' : ∀ i, w (σ (c i / c i₀)) ≤ 1 := fun i => hintegral _ (hc i)
  have hs : v (∑ i, ((c i / c i₀ : F) : K) * e ^ (i : ℕ)) = 1 := by
    apply M7.val_sum_eq_one v he hc
    · exact ⟨i₀, by simp [div_self ha]⟩
    · exact hI (fun i => c i / c i₀) hc
  have hcoeff := fun i => hres (c i / c i₀) (hc i) (hc' i)
  refine ⟨c i₀, ha, hs,
    target_sum_value_one v w ρ hc hc' he hd hcoeff hvar hs,
    sum_integral v hc he, sum_integral w hc' hd, ?_⟩
  exact residue_sum_transport v w ρ hc hc' he hd hcoeff hvar

theorem nonzero_sums (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    {N : ℕ} {c : Fin N → F} {e : K} {d : L}
    (he : v e = 1) (hd : w d = 1) (hI : ResidueIndependent v F he N)
    (hne : ∃ i, c i ≠ 0)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    (∑ i, (c i : K) * e ^ (i : ℕ)) ≠ 0 ∧ (∑ i, σ (c i) * d ^ (i : ℕ)) ≠ 0 := by
  obtain ⟨a, _, hs, ht, _⟩ := normalized_sums v w F σ ρ hintegral hres he hd hI hne hvar
  constructor
  · intro hz
    have hnorm := sum_normalize F.subtype c (fun i => (i : ℕ)) e a
    change (∑ i, ((c i / a : F) : K) * e ^ (i : ℕ)) =
      (∑ i, (c i : K) * e ^ (i : ℕ)) / (a : K) at hnorm
    rw [hnorm, hz, zero_div, map_zero] at hs
    exact zero_ne_one hs
  · intro hz
    rw [sum_normalize σ c (fun i => (i : ℕ)) d a, hz, zero_div, map_zero] at ht
    exact zero_ne_one ht

theorem rv_sum_relation (v : Valuation K Γ) (w : Valuation L Δ)
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
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le → R (RVCalc.rv v x) (RVCalc.rv w y))
    {N : ℕ} {c : Fin N → F} {e : K} {d : L}
    (he : v e = 1) (hd : w d = 1) (hI : ResidueIndependent v F he N)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    R (RVCalc.rv v (∑ i, (c i : K) * e ^ (i : ℕ)))
      (RVCalc.rv w (∑ i, σ (c i) * d ^ (i : ℕ))) := by
  classical
  by_cases hne : ∃ i, c i ≠ 0
  · obtain ⟨a, ha, hs, ht, hsle, htle, hnormal⟩ :=
      normalized_sums v w F σ ρ hintegral hres he hd hI hne hvar
    let x : K := ∑ i, ((c i / a : F) : K) * e ^ (i : ℕ)
    let y : L := ∑ i, σ (c i / a) * d ^ (i : ℕ)
    have hx : v x = 1 := hs
    have hy : w y = 1 := ht
    have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
    have haL : σ a ≠ 0 := fun h => ha (σ.injective (by simpa using h))
    have hxy : R (RVCalc.rv v x) (RVCalc.rv w y) := hunit x y hx hy hnormal
    have hsprod : (a : K) * x = ∑ i, (c i : K) * e ^ (i : ℕ) := by
      dsimp [x]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (a : K) * (((c i : K) / (a : K)) * e ^ (i : ℕ)) = _
      field_simp [haK]
    have htprod : σ a * y = ∑ i, σ (c i) * d ^ (i : ℕ) := by
      dsimp [y]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_div₀]
      field_simp [haL]
    rw [← hsprod, ← htprod, rv_mul_all, rv_mul_all]
    exact hmul _ _ _ _ (hbase a) hxy
  · have hz : ∀ i, c i = 0 := by
      intro i
      by_contra hi
      exact hne ⟨i, hi⟩
    simpa [hz] using hzero

end ResidueAlgebraicTransport

#print axioms ResidueAlgebraicTransport.residueIndependent_of_minpoly
#print axioms ResidueAlgebraicTransport.normalized_sums
#print axioms ResidueAlgebraicTransport.nonzero_sums
#print axioms ResidueAlgebraicTransport.rv_sum_relation
