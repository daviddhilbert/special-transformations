import ResidueTransportCore

/-!
The two-field calculation for Yin's residue-transcendental case.

This file does not use the current overbroad `RelUnit` slot.  Its base is an actual
subfield, its transcendence hypothesis is on the residue, and the residue map is
a ring homomorphism.  The RV map in the final theorem is a homomorphism between
the canonical groups K*/(1+m); compatibility on value-one elements expresses
that its restriction to residue-field units is the supplied residue map.

No saturation, QE, extension-existence, or polynomial-transport hypothesis is
assumed.  `UnitTranscend` supplies the already proved one-field calculation.
The two valuations may have different value groups.  On the base field only
preservation of the valuation ring is needed, rather than numerical equality of
valuations in a common group.
-/

namespace ResidueTranscendentalTransport

open scoped BigOperators

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

abbrev Residue (v : Valuation K Γ) := IsLocalRing.ResidueField v.valuationSubring

/-- An integral polynomial expression is integral. -/
theorem sum_integral (v : Valuation K Γ) {n : ℕ} {c : Fin n → K}
    {e : K} {m : Fin n → ℕ} (hc : ∀ i, v (c i) ≤ 1) (he : v e = 1) :
    v (∑ i, c i * e ^ m i) ≤ 1 :=
  M7.val_sum_le_one' v (fun i => by simpa [map_mul, map_pow, he] using hc i)

/-- Transport of a normalized residue polynomial.  The coefficient and variable
compatibilities are pointwise; the polynomial conclusion is proved. -/
theorem residue_sum_transport (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) {n : ℕ} {c : Fin n → K} {c' : Fin n → L}
    {e : K} {d : L} {m : Fin n → ℕ}
    (hc : ∀ i, v (c i) ≤ 1) (hc' : ∀ i, w (c' i) ≤ 1)
    (he : v e = 1) (hd : w d = 1)
    (hcoeff : ∀ i, ρ (M7.vres v (c i) (hc i)) = M7.vres w (c' i) (hc' i))
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    ρ (M7.vres v (∑ i, c i * e ^ m i) (sum_integral v hc he)) =
      M7.vres w (∑ i, c' i * d ^ m i) (sum_integral w hc' hd) := by
  have ht : ∀ i, v (c i * e ^ m i) ≤ 1 :=
    fun i => by simpa [map_mul, map_pow, he] using hc i
  have ht' : ∀ i, w (c' i * d ^ m i) ≤ 1 :=
    fun i => by simpa [map_mul, map_pow, hd] using hc' i
  rw [M7.vres_sum v ht, M7.vres_sum w ht', map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [M7.vres_mul v (hc i) (M7.val_pow_le_one v he.le (m i)),
    M7.vres_mul w (hc' i) (M7.val_pow_le_one w hd.le (m i)),
    M7.vres_pow v he.le, M7.vres_pow w hd.le, map_mul, map_pow,
    hcoeff i, hvar]

/-- A nonzero normalized residue polynomial stays a unit in the target. -/
theorem target_sum_value_one (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) {n : ℕ} {c : Fin n → K} {c' : Fin n → L}
    {e : K} {d : L} {m : Fin n → ℕ}
    (hc : ∀ i, v (c i) ≤ 1) (hc' : ∀ i, w (c' i) ≤ 1)
    (he : v e = 1) (hd : w d = 1)
    (hcoeff : ∀ i, ρ (M7.vres v (c i) (hc i)) = M7.vres w (c' i) (hc' i))
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le)
    (hsource : v (∑ i, c i * e ^ m i) = 1) :
    w (∑ i, c' i * d ^ m i) = 1 := by
  have hs := sum_integral v (m := m) hc he
  have ht := sum_integral w (m := m) hc' hd
  have hz : M7.vres v (∑ i, c i * e ^ m i) hs ≠ 0 := by
    intro hzero
    have hlt := (M7.vres_eq_zero_iff v _ hs).mp hzero
    rw [hsource] at hlt
    exact lt_irrefl 1 hlt
  have hz' : M7.vres w (∑ i, c' i * d ^ m i) ht ≠ 0 := by
    rw [← residue_sum_transport v w ρ hc hc' he hd hcoeff hvar]
    exact fun h => hz (ρ.injective (by simpa using h))
  exact le_antisymm ht (le_of_not_gt (fun h => hz' ((M7.vres_eq_zero_iff w _ ht).mpr h)))

section BaseField

variable (v : Valuation K Γ) (w : Valuation L Δ) (F : Subfield K)
  (σ : F →+* L) (ρ : Residue v →+* Residue w)
  (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
  (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
    ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)

include hintegral hres

/-- Choose a maximal coefficient and normalize both polynomial expressions by
that same coefficient.  The target unit conclusion follows from the source's
residue transcendence and residue transport; target transcendence is not assumed. -/
theorem normalized_sums {n : ℕ} {c : Fin n → F} {m : Fin n → ℕ}
    {e : K} {d : L} (he : v e = 1) (hd : w d = 1)
    (hT : M7.ResidueTranscendental v F he) (hm : Function.Injective m)
    (hne : ∃ i, c i ≠ 0)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    ∃ a : F, a ≠ 0 ∧
      v (∑ i, ((c i / a : F) : K) * e ^ m i) = 1 ∧
      w (∑ i, σ (c i / a) * d ^ m i) = 1 ∧
      ∃ (hs : v (∑ i, ((c i / a : F) : K) * e ^ m i) ≤ 1)
        (ht : w (∑ i, σ (c i / a) * d ^ m i) ≤ 1),
        ρ (M7.vres v _ hs) = M7.vres w _ ht := by
  classical
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => v (c i : K)) (by
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
  have hc' : ∀ i, w (σ (c i / c i₀)) ≤ 1 := by
    intro i
    exact hintegral _ (hc i)
  have hs : v (∑ i, ((c i / c i₀ : F) : K) * e ^ m i) = 1 := by
    apply M7.val_sum_eq_one v he hc
    · exact ⟨i₀, by simp [div_self ha]⟩
    · exact hT n (fun i => c i / c i₀) m hm hc
  have hcoeff := fun i => hres (c i / c i₀) (hc i) (hc' i)
  refine ⟨c i₀, ha, hs,
    target_sum_value_one v w ρ hc hc' he hd hcoeff hvar hs,
    sum_integral v hc he, sum_integral w hc' hd, ?_⟩
  exact residue_sum_transport v w ρ hc hc' he hd hcoeff hvar

end BaseField

/-- The extension by zero of a homomorphism of canonical RV groups is multiplicative. -/
theorem map_rvMul (v : Valuation K Γ) (w : Valuation L Δ)
    (τ : RVCalc.RVUnit v →* RVCalc.RVUnit w) (x y : RVCalc.RV v) :
    Option.map τ (RVCalc.rvMul v x y) =
      RVCalc.rvMul w (Option.map τ x) (Option.map τ y) := by
  cases x <;> cases y <;> simp [RVCalc.rvMul, map_mul]

/-- Two-field RV transport for a polynomial in a unit with transcendental
residue.  `hunit` is the compatibility square between the supplied RV and residue
homomorphisms on residue-field units; `hbase` says the base-field map induces the
given RV map.  Neither assumes transport of polynomial expressions.

The resulting identity fixes the prescribed RV map, which mere preservation of
valuation would not establish. -/
theorem rv_sum_transport (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (τ : RVCalc.RVUnit v →* RVCalc.RVUnit w)
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    (hbase : ∀ a : F, Option.map τ (RVCalc.rv v (a : K)) = RVCalc.rv w (σ a))
    (hunit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le →
        Option.map τ (RVCalc.rv v x) = RVCalc.rv w y)
    {n : ℕ} {c : Fin n → F} {m : Fin n → ℕ} {e : K} {d : L}
    (he : v e = 1) (hd : w d = 1)
    (hT : M7.ResidueTranscendental v F he) (hm : Function.Injective m)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    Option.map τ (RVCalc.rv v (∑ i, (c i : K) * e ^ m i)) =
      RVCalc.rv w (∑ i, σ (c i) * d ^ m i) := by
  classical
  by_cases hne : ∃ i, c i ≠ 0
  · obtain ⟨a, ha, hs, ht, hsle, htle, hnormal⟩ :=
      normalized_sums v w F σ ρ hintegral hres he hd hT hm hne hvar
    let x : K := ∑ i, ((c i / a : F) : K) * e ^ m i
    let y : L := ∑ i, σ (c i / a) * d ^ m i
    have hx : v x = 1 := hs
    have hy : w y = 1 := ht
    have hx0 : x ≠ 0 := by
      intro h
      simpa [h] using hx
    have hy0 : y ≠ 0 := by
      intro h
      simpa [h] using hy
    have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
    have haL : σ a ≠ 0 := fun h => ha (σ.injective (by simpa using h))
    have hxy : Option.map τ (RVCalc.rv v x) = RVCalc.rv w y :=
      hunit x y hx hy hnormal
    have hsprod : (a : K) * x = ∑ i, (c i : K) * e ^ m i := by
      dsimp [x]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (a : K) * (((c i : K) / (a : K)) * e ^ m i) = _
      field_simp [haK]
    have htprod : σ a * y = ∑ i, σ (c i) * d ^ m i := by
      dsimp [y]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_div₀]
      field_simp [haL]
    calc
      Option.map τ (RVCalc.rv v (∑ i, (c i : K) * e ^ m i)) =
          Option.map τ (RVCalc.rv v ((a : K) * x)) := by rw [hsprod]
      _ = RVCalc.rvMul w (Option.map τ (RVCalc.rv v (a : K)))
          (Option.map τ (RVCalc.rv v x)) := by
        rw [RVCalc.rv_mul haK hx0, map_rvMul]
      _ = RVCalc.rvMul w (RVCalc.rv w (σ a)) (RVCalc.rv w y) := by rw [hbase, hxy]
      _ = RVCalc.rv w (σ a * y) := (RVCalc.rv_mul haL hy0).symm
      _ = RVCalc.rv w (∑ i, σ (c i) * d ^ m i) := by rw [htprod]
  · have hz : ∀ i, c i = 0 := by
      intro i
      by_contra hi
      exact hne ⟨i, hi⟩
    simp [hz]

/-- The domain-sensitive version.  Take `R` to be the graph of a prescribed
partial RV homomorphism: `R t u` records both that `t` belongs to its domain and
that its image is `u`.  Closure under multiplication, the base classes, and the
residue units suffice.  No homomorphism on all of `RV(K)` is required.

Thus the conclusion proves polynomial RV membership and transport together. -/
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
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le →
        R (RVCalc.rv v x) (RVCalc.rv w y))
    {n : ℕ} {c : Fin n → F} {m : Fin n → ℕ} {e : K} {d : L}
    (he : v e = 1) (hd : w d = 1)
    (hT : M7.ResidueTranscendental v F he) (hm : Function.Injective m)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    R (RVCalc.rv v (∑ i, (c i : K) * e ^ m i))
      (RVCalc.rv w (∑ i, σ (c i) * d ^ m i)) := by
  classical
  by_cases hne : ∃ i, c i ≠ 0
  · obtain ⟨a, ha, hs, ht, hsle, htle, hnormal⟩ :=
      normalized_sums v w F σ ρ hintegral hres he hd hT hm hne hvar
    let x : K := ∑ i, ((c i / a : F) : K) * e ^ m i
    let y : L := ∑ i, σ (c i / a) * d ^ m i
    have hx : v x = 1 := hs
    have hy : w y = 1 := ht
    have hx0 : x ≠ 0 := by
      intro h
      simpa [h] using hx
    have hy0 : y ≠ 0 := by
      intro h
      simpa [h] using hy
    have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
    have haL : σ a ≠ 0 := fun h => ha (σ.injective (by simpa using h))
    have hxy : R (RVCalc.rv v x) (RVCalc.rv w y) := hunit x y hx hy hnormal
    have hsprod : (a : K) * x = ∑ i, (c i : K) * e ^ m i := by
      dsimp [x]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (a : K) * (((c i : K) / (a : K)) * e ^ m i) = _
      field_simp [haK]
    have htprod : σ a * y = ∑ i, σ (c i) * d ^ m i := by
      dsimp [y]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_div₀]
      field_simp [haL]
    rw [← hsprod, ← htprod, RVCalc.rv_mul haK hx0, RVCalc.rv_mul haL hy0]
    exact hmul _ _ _ _ (hbase a) hxy
  · have hz : ∀ i, c i = 0 := by
      intro i
      by_contra hi
      exact hne ⟨i, hi⟩
    simpa [hz] using hzero

/-- Inversion of the canonical RV sort, with zero fixed. -/
def rvInv (v : Valuation K Γ) : RVCalc.RV v → RVCalc.RV v
  | none => none
  | some a => some a⁻¹

theorem rv_inv (v : Valuation K Γ) (x : K) :
    RVCalc.rv v x⁻¹ = rvInv v (RVCalc.rv v x) := by
  by_cases hx : x = 0
  · simp [hx, rvInv]
  · rw [RVCalc.rv_inv hx, RVCalc.rv_of_ne hx]
    rfl

theorem rv_mul_all (v : Valuation K Γ) (x y : K) :
    RVCalc.rv v (x * y) = RVCalc.rvMul v (RVCalc.rv v x) (RVCalc.rv v y) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  exact RVCalc.rv_mul hx hy

theorem rv_div (v : Valuation K Γ) (x y : K) :
    RVCalc.rv v (x / y) = RVCalc.rvMul v (RVCalc.rv v x) (rvInv v (RVCalc.rv v y)) := by
  rw [div_eq_mul_inv, rv_mul_all, rv_inv]

/-- Multiplication and inverse closure of a partial-map graph transport quotients. -/
theorem rv_div_relation (v : Valuation K Γ) (w : Valuation L Δ)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hinv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a'))
    {x y : K} {x' y' : L}
    (hx : R (RVCalc.rv v x) (RVCalc.rv w x'))
    (hy : R (RVCalc.rv v y) (RVCalc.rv w y')) :
    R (RVCalc.rv v (x / y)) (RVCalc.rv w (x' / y')) := by
  rw [rv_div, rv_div]
  exact hmul _ _ _ _ hx (hinv _ _ hy)

/-- RV membership and prescribed-image transport for every rational expression
in a residue-transcendental unit.  Inverse closure is the ordinary subgroup law
for the domain of the partial RV map; no total RV-map extension is assumed. -/
theorem rv_quotient_relation (v : Valuation K Γ) (w : Valuation L Δ)
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
    {n k : ℕ} {c : Fin n → F} {q : Fin k → F}
    {m : Fin n → ℕ} {s : Fin k → ℕ} {e : K} {d : L}
    (he : v e = 1) (hd : w d = 1)
    (hT : M7.ResidueTranscendental v F he)
    (hm : Function.Injective m) (hs : Function.Injective s)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    R (RVCalc.rv v ((∑ i, (c i : K) * e ^ m i) / (∑ j, (q j : K) * e ^ s j)))
      (RVCalc.rv w ((∑ i, σ (c i) * d ^ m i) / (∑ j, σ (q j) * d ^ s j))) := by
  apply rv_div_relation v w R hmul hinv
  · exact rv_sum_relation v w F σ ρ R hzero hmul hintegral hres hbase hunit he hd hT hm hvar
  · exact rv_sum_relation v w F σ ρ R hzero hmul hintegral hres hbase hunit he hd hT hs hvar

end ResidueTranscendentalTransport

#print axioms ResidueTranscendentalTransport.residue_sum_transport
#print axioms ResidueTranscendentalTransport.target_sum_value_one
#print axioms ResidueTranscendentalTransport.normalized_sums
#print axioms ResidueTranscendentalTransport.map_rvMul
#print axioms ResidueTranscendentalTransport.rv_sum_transport
#print axioms ResidueTranscendentalTransport.rv_sum_relation
#print axioms ResidueTranscendentalTransport.rv_div_relation
#print axioms ResidueTranscendentalTransport.rv_quotient_relation

