import Mathlib

/-!
# Yin's Lemma 3.2 (`rv:root:lift:vf`): lifting an `RV`-root to a `VF`-root

Source: Yimu Yin, *Special transformations in algebraically closed valued fields*
(arXiv:1006.2467), Lemma 2.3/3.2; the companion paper (arXiv:1006.1393, `qe.tex`),
Lemma `rv:root:lift:vf` in Section 3.

The paper's statement, decoded into valuation-theoretic terms.  `(K, v)` is a valued field,
`F ∈ K[X]`, `F(X) = Σ_i b_i X^i`.  Choose `t ∈ RV` (Yin's quotient `K^×/(1+𝔪)`, with `∞`
for `rv 0`) and let `I ⊆ supp F` be the support of the `RV`-polynomial
`F̄ = Σ_i t_i X^i`, i.e. the set of `i` with `t_i ≠ 0`; for those `i`, `t_i = rv b_i`, and the
side condition says that for `i ∉ I` the term `rv b_i · t^i` lies in the maximal ideal.  Then

  `F̄(t) = 0  ⟹  ∃ b' ∈ t,  F(b') = 0`,

i.e. an `RV`-root of the reduction lifts to a `VF`-root.  Passing to a representative `b` of
`t` (`rv b = t`), and writing `t_i t^i` as the residue class of `b_i b^i`:

* `v (b_i b^i) = 1` for `i ∈ I` (each surviving term is a residue-field unit);
* `v (b_i b^i) < 1` for `i ∈ supp F ∖ I` (Yin's side condition `vrv (rv b_i · t^i) > 0`);
* `v (Σ_{i∈I} b_i b^i) < 1` is exactly `F̄(t) = 0` (a sum of residue classes vanishes iff the
  sum of representatives is in the maximal ideal);
* the conclusion `∃ b', rv b' = rv b ∧ F.IsRoot b'` is `∃ b' ∈ t, F(b') = 0`
  (see `rv_eq_iff`).

## What is proved here

* `root_integral` — a root of a polynomial with integral coefficients and unit leading
  coefficient is integral.
* `exists_root_residue_one` — the residue-root-lifting core: if `g` splits, has integral
  coefficients, unit leading coefficient, and `v (g 1) < 1`, then `g` has a root `β` with
  `v β = 1` and `v (1 - β) < 1`, i.e. `rv β = rv 1`.  No Hensel property, completeness,
  residue-field algebraicity or Newton polygon is used.
* Yin's `RV` sort: `princUnits`, `RV`, `rv`, `rvMul`, `vrv`, with `rv_mul`, `vrv_rv`
  (axiom 6) and the class condition `rv_eq_iff`
  (`rv b' = rv b ↔ v b' = v b ∧ v (b'/b - 1) < 1`).
* `rv_root_lift_of_support_all` — Lemma 3.2 in the case `I = supp F` (no coefficient of `F̄`
  dropped), proved directly from `exists_root_residue_one`.
* The Gauss norm `Mb b P = max_j v (P.coeff j · b^j)`: `Mb_mul` (multiplicativity, by the
  minimal-index argument), `Mb_C`, `Mb_X_sub_C`, `Mb_multiset_prod`.
* `v_sub_eq_max` — elements outside a common `rv`-class are at distance `max` of the values.
* `noCancellation` — the Newton-polygon identity `v (F b) = max_j v (F.coeff j · b^j)`
  when no root of `F` shares the `rv`-class of `b`.
* `rv_root_lift_general`, and its unconditional form **`rv_root_lift`** — **Yin's Lemma 3.2 in
  full generality**: with `I` the support of `F̄ ⊆ supp F`, `v (b_i b^i) = 1` on `I`,
  `v (b_i b^i) < 1` on `supp F ∖ I`, `2 ≤ |I|` and `v (Σ_{i∈I} b_i b^i) < 1`, there is a root
  `b'` of `F` with `rv b' = rv b`.  `rv_root_lift_rv` is the same statement with `t ∈ RV` in
  the conclusion.
* `rv_eq_of_val_eq` — the first half of Remark 3.1 (`L:v:and:L:RV`): `rv` is determined by the
  valuation, so an `L_v`-embedding of valued fields preserves `rv`-classes.

No `sorry`, no `axiom`, no `admit`; `import Mathlib` is the only import.
-/

open Polynomial

namespace YinRV

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]









/-- Roots of a polynomial with integral coefficients and unit leading coefficient are integral. -/
theorem root_integral (v : Valuation K Γ₀) {g : K[X]} (_hg : g ≠ 0)
    (hint : ∀ j, v (g.coeff j) ≤ 1) (hlc : v g.leadingCoeff = 1)
    {α : K} (hα : g.IsRoot α) : v α ≤ 1 := by
  by_contra hcon
  simp only [not_le] at hcon
  have hsum : ∑ j ∈ Finset.range (g.natDegree + 1), g.coeff j * α ^ j = 0 := by
    have h := hα
    rw [Polynomial.IsRoot, Polynomial.eval_eq_sum_range] at h
    exact h
  have hmem : g.natDegree ∈ Finset.range (g.natDegree + 1) := Finset.self_mem_range_succ _
  have hcoeff : g.coeff g.natDegree = g.leadingCoeff := Polynomial.coeff_natDegree (p := g)
  have hzero : v (g.coeff g.natDegree * α ^ g.natDegree) = v α ^ g.natDegree := by
    rw [map_mul, map_pow, hcoeff, hlc, one_mul]
  have hkey : v (∑ j ∈ Finset.range (g.natDegree + 1), g.coeff j * α ^ j)
      = v (g.coeff g.natDegree * α ^ g.natDegree) := by
    refine v.map_sum_eq_of_lt hmem ?_
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hj
    obtain ⟨hjr, hjn⟩ := hj
    have hjd : j < g.natDegree := by omega
    have e1 : v (g.coeff j * α ^ j) = v (g.coeff j) * v α ^ j := by rw [map_mul, map_pow]
    rw [e1, hzero]
    calc v (g.coeff j) * v α ^ j ≤ 1 * v α ^ j := by
          simpa only [mul_comm, mul_one] using mul_le_mul_right (hint j) (v α ^ j)
      _ = v α ^ j := one_mul _
      _ < v α ^ g.natDegree := pow_lt_pow_right₀ hcon hjd
  rw [hsum, map_zero, hzero] at hkey
  exact (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hcon))) hkey.symm




/-- **Residue root lifting.**  If a splitting polynomial over a valued field has all
coefficients integral and leading coefficient a unit, and reduces to a polynomial vanishing
at `1`, then it has a root whose `rv`-class is that of `1`. -/
theorem exists_root_residue_one (v : Valuation K Γ₀) {g : K[X]} (hspl : g.Splits)
    (hint : ∀ j, v (g.coeff j) ≤ 1) (hlc : v g.leadingCoeff = 1)
    (h1 : v (g.eval 1) < 1) :
    ∃ β ∈ g.roots, v β = 1 ∧ v (1 - β) < 1 := by
  have hg : g ≠ 0 := by rintro rfl; simp at hlc
  have hfac : g.eval 1 = g.leadingCoeff * (g.roots.map (fun β => 1 - β)).prod :=
    hspl.eval_eq_prod_roots 1
  have hfactor : v (g.eval 1) = (g.roots.map (fun β => v (1 - β))).prod := by
    rw [hfac, map_mul, hlc, one_mul, map_multiset_prod, Multiset.map_map]
    rfl
  have hsmall : ∃ β ∈ g.roots, v (1 - β) < 1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hone : 1 ≤ (g.roots.map (fun β => v (1 - β))).prod :=
      Multiset.one_le_prod (fun a ha => by
        obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp ha
        exact hcon β hβ)
    rw [← hfactor] at hone
    exact absurd h1 (not_lt.mpr hone)
  obtain ⟨β, hβ, hb⟩ := hsmall
  have hintβ : v β ≤ 1 := root_integral v hg hint hlc (Polynomial.isRoot_of_mem_roots hβ)
  have hne : v β = 1 := by
    rcases lt_trichotomy (v β) 1 with h | h | h
    · rw [v.map_one_sub_of_lt h] at hb
      exact absurd hb (lt_irrefl 1)
    · exact h
    · have hval : v (1 - β) = v β := by
        rw [show (1 : K) - β = -(β - 1) by ring, v.map_neg]
        exact v.map_sub_eq_of_lt_left (by simpa using h)
      rw [hval] at hb
      exact absurd hb (not_lt.mpr h.le)
  exact ⟨β, hβ, hne, hb⟩






/-- The principal unit group `1 + 𝔪` of the valuation ring, as a subgroup of `Kˣ`. -/
def princUnits (v : Valuation K Γ₀) : Subgroup Kˣ where
  carrier := {u | v ((u : K) - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred] at ha hb ⊢
    have hva : v (a : K) = 1 := by
      have h1 : (a : K) = 1 + ((a : K) - 1) := by ring
      rw [h1, v.map_one_add_of_lt ha]
    have h : ((a * b : Kˣ) : K) - 1 = ((a : K) - 1) + (a : K) * ((b : K) - 1) := by
      push_cast; ring
    rw [h]
    refine v.map_add_lt ha ?_
    rw [map_mul, hva, one_mul]
    exact hb
  one_mem' := by
    rw [Set.mem_ofPred]
    simp
  inv_mem' := by
    intro a ha
    rw [Set.mem_ofPred] at ha ⊢
    have hva : v (a : K) = 1 := by
      have h1 : (a : K) = 1 + ((a : K) - 1) := by ring
      rw [h1, v.map_one_add_of_lt ha]
    have h : ((a⁻¹ : Kˣ) : K) - 1 = -(((a : K) - 1) / (a : K)) := by
      push_cast
      field_simp
      ring
    have hdiv : v (((a : K) - 1) / (a : K)) = v ((a : K) - 1) := by
      rw [div_eq_mul_inv, map_mul, Valuation.map_inv v, hva, inv_one, mul_one]
    rw [h, v.map_neg, hdiv]
    exact ha

/-- Yin's `RV×`: `Kˣ/(1+𝔪)`. -/
abbrev RVUnit (v : Valuation K Γ₀) : Type _ := Kˣ ⧸ princUnits v

/-- Yin's `RV`-sort: `RV× ∪ {∞}`, with `∞` the value of `rv 0`. -/
abbrev RV (v : Valuation K Γ₀) : Type _ := Option (RVUnit v)

/-- Yin's `rv : VF → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (v : Valuation K Γ₀) (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk' _ (Units.mk0 x h))

/-- The paper's `∞`. -/
abbrev rvInfty (v : Valuation K Γ₀) : RV v := none

variable {v : Valuation K Γ₀}

theorem rv_zero : rv v (0 : K) = rvInfty v := by
  classical exact dif_pos rfl

theorem rv_of_ne {x : K} (h : x ≠ 0) : rv v x = some (QuotientGroup.mk' _ (Units.mk0 x h)) := by
  classical exact dif_neg h

theorem rv_eq_none_iff {x : K} : rv v x = rvInfty v ↔ x = 0 := by
  classical
  unfold rv rvInfty
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · simp [h]

/-- Multiplication in `RV×`, extended by `∞` absorbing. -/
def rvMul : RV v → RV v → RV v
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a * b)

theorem rv_mul (x y : K) : rv v (x * y) = rvMul (rv v x) (rv v y) := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, rv_zero]
    cases rv v y with
    | none => rfl
    | some q => rfl
  by_cases hy : y = 0
  · rw [hy, mul_zero, rv_zero]
    cases rv v x with
    | none => rfl
    | some q => rfl
  rw [rv_of_ne hx, rv_of_ne hy, rv_of_ne (mul_ne_zero hx hy)]
  have hdef : rvMul (some (QuotientGroup.mk' _ (Units.mk0 x hx)) : RV v)
      (some (QuotientGroup.mk' _ (Units.mk0 y hy)) : RV v)
      = some (QuotientGroup.mk' _ (Units.mk0 x hx) * QuotientGroup.mk' _ (Units.mk0 y hy)) := rfl
  rw [hdef, ← map_mul]
  rw [show (Units.mk0 (x * y) (mul_ne_zero hx hy) : Kˣ) = Units.mk0 x hx * Units.mk0 y hy
      from Units.ext rfl]

/-- `1` of the `RV`-sort. -/
theorem rv_one : rv v (1 : K) = some (QuotientGroup.mk' _ (1 : Kˣ)) := by
  rw [rv_of_ne one_ne_zero]
  congr 2
  exact Units.ext rfl

/-- `rv` is surjective onto `RV ∖ {∞}`. -/
theorem rv_surjective {t : RV v} (h : t ≠ rvInfty v) : ∃ x : K, x ≠ 0 ∧ rv v x = t := by
  cases t with
  | none => exact absurd rfl h
  | some q =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (princUnits v) q
    exact ⟨(u : K), Units.ne_zero u, by
      rw [rv_of_ne (Units.ne_zero u)]
      congr 2
      exact Units.ext rfl⟩

/-- The valuation, as a monoid homomorphism on the units of `K`. -/
noncomputable def vUnits (v : Valuation K Γ₀) : Kˣ →* Γ₀ˣ where
  toFun u := Units.mk0 (v (u : K)) (by rw [Valuation.ne_zero_iff]; exact Units.ne_zero u)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [Valuation.map_mul]

theorem vUnits_ker (v : Valuation K Γ₀) : princUnits v ≤ (vUnits v).ker := by
  intro x hx
  have hx' : v ((x : K) - 1) < 1 := hx
  rw [MonoidHom.mem_ker, Units.ext_iff]
  show v ((x : Kˣ) : K) = 1
  have h1 : (x : K) = 1 + ((x : K) - 1) := by ring
  rw [h1, v.map_one_add_of_lt hx']

/-- `vrv` on `RV×`, induced by the valuation. -/
noncomputable def vrvUnit (v : Valuation K Γ₀) : RVUnit v →* Γ₀ˣ :=
  QuotientGroup.lift _ (vUnits v) (vUnits_ker v)

/-- Yin's `vrv : RV → Γ ∪ {∞}` (with `∞` read as `0`; the paper's order on `Γ ∪ {∞}` is the
reverse of Mathlib's order on `Γ₀`). -/
noncomputable def vrv (v : Valuation K Γ₀) : RV v → Γ₀
  | none => 0
  | some q => (vrvUnit v q : Γ₀)

theorem vrv_mk (u : Kˣ) : vrv v (some (QuotientGroup.mk' _ u)) = v (u : K) := by
  show (((vrvUnit v) (QuotientGroup.mk' _ u) : Γ₀ˣ) : Γ₀) = v (u : K)
  rw [vrvUnit]
  rfl

/-- `vv = vrv ∘ rv` (Yin, axiom 6). -/
theorem vrv_rv (x : K) : vrv v (rv v x) = v x := by
  by_cases h : x = 0
  · rw [h, rv_zero, map_zero]
    rfl
  · rw [rv_of_ne h]
    exact vrv_mk (Units.mk0 x h)

/-- **The class condition**, `b' ∈ t` in field terms: two nonzero elements have the same
`rv`-class iff they have the same valuation and their quotient is a principal unit. -/
theorem rv_eq_iff {x y : K} (hy : y ≠ 0) :
    rv v x = rv v y ↔ v x = v y ∧ v (x / y - 1) < 1 := by
  have hxne : x ≠ 0 → y / x ≠ 0 := by
    intro hx h0
    rw [div_eq_zero_iff] at h0
    tauto
  constructor
  · rintro h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [rv_zero, rv_of_ne hy] at h
      exact absurd h (by simp)
    rw [rv_of_ne hx, rv_of_ne hy, Option.some_inj] at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
    have hmem := QuotientGroup.eq.mp h
    have hmem' : v ((((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) - 1) < 1 := hmem
    have hpush : (((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) = y / x := by
      simp [div_eq_mul_inv, mul_comm]
    rw [hpush] at hmem'
    have hunit : v (y / x) = 1 := by
      have h1 : y / x = 1 + (y / x - 1) := by ring
      rw [h1, v.map_one_add_of_lt hmem']
    have hvy : v y = v x := by
      have h2 : v (y / x) = v y / v x := Valuation.map_div v y x
      rw [h2] at hunit
      rcases eq_or_ne (v x) 0 with h0 | h0
      · rw [h0, div_zero] at hunit
        exact absurd hunit (by simp)
      · calc v y = v y / v x * v x := (div_mul_cancel₀ _ h0).symm
          _ = 1 * v x := by rw [hunit]
          _ = v x := one_mul _
    refine ⟨hvy.symm, ?_⟩
    have h3 : (y / x)⁻¹ - 1 = -((y / x - 1) / (y / x)) := by
      field_simp
      ring
    have h4 : v ((y / x - 1) / (y / x)) = v (y / x - 1) := by
      rw [div_eq_mul_inv, map_mul, Valuation.map_inv v, hunit, inv_one, mul_one]
    have h5 : (y / x)⁻¹ = x / y := by
      field_simp
    have h6 : v ((y / x)⁻¹ - 1) < 1 := by
      rw [h3, v.map_neg, h4]
      exact hmem'
    rwa [h5] at h6
  · rintro ⟨hval, hlt⟩
    have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_div, zero_sub, v.map_neg, map_one] at hlt
      exact absurd hlt (lt_irrefl 1)
    rw [rv_of_ne hx, rv_of_ne hy, Option.some_inj,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : ((((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K)) = y / x := by
      simp [div_eq_mul_inv, mul_comm]
    show v ((((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) - 1) < 1
    rw [h1]
    have hv : v (y / x) = 1 := by
      have h2 : v (y / x) = v y / v x := Valuation.map_div v y x
      rw [h2, ← hval]
      exact div_self ((Valuation.ne_zero_iff v).2 hx)
    have h5 : x / y = (y / x)⁻¹ := by
      field_simp
    rw [h5] at hlt
    have heq : v ((y / x)⁻¹ - 1) = v (y / x - 1) := by
      have h3 : (y / x)⁻¹ - 1 = -((y / x - 1) / (y / x)) := by
        field_simp
        ring
      rw [h3, v.map_neg, div_eq_mul_inv, map_mul, Valuation.map_inv v, hv, inv_one, mul_one]
    rwa [heq] at hlt


section Main

variable (v : Valuation K Γ₀)

/-- Evaluation as a sum over the support. -/
theorem eval_eq_sum_support {R : Type*} [Semiring R] (p : R[X]) (x : R) :
    p.eval x = ∑ i ∈ p.support, p.coeff i * x ^ i := by
  conv_lhs => rw [p.as_sum_support]
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl (fun i _ => by simp [Polynomial.eval_monomial])

/-- Yin's Lemma 3.2 (`rv:root:lift:vf`), **in the case where no coefficient of the
`RV`-polynomial is dropped** (`I = supp`): every `RV`-coefficient is nonzero, i.e.
`vrv (rv b_i · t^i) = 1` for every `i`.  This case is proved directly from
`exists_root_residue_one`, without the Newton-polygon identity. -/
theorem rv_root_lift_of_support_all [IsAlgClosed K] {F : K[X]} (hF : F ≠ 0) {b : K} (hb : b ≠ 0)
    (huniv : ∀ i ∈ F.support, v (F.coeff i * b ^ i) = 1)
    (hred : v (∑ i ∈ F.support, F.coeff i * b ^ i) < 1) :
    ∃ b' : K, rv v b' = rv v b ∧ F.IsRoot b' := by
  set G : K[X] := ∑ i ∈ F.support, Polynomial.monomial i (F.coeff i * b ^ i) with hGdef
  have hm : F.natDegree ∈ F.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hF)
  have hGcoeff : ∀ k, G.coeff k = if k ∈ F.support then F.coeff k * b ^ k else 0 := by
    intro k
    rw [hGdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hGle : ∀ k, v (G.coeff k) ≤ 1 := by
    intro k
    rw [hGcoeff k]
    split_ifs with hk
    · rw [huniv k hk]
    · simp
  have hcomp : ∀ x : K, G.eval x = F.eval (b * x) := by
    intro x
    rw [hGdef, Polynomial.eval_finsetSum, eval_eq_sum_support]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Polynomial.eval_monomial]
    rw [mul_pow]
    ring
  have hGlead : G.leadingCoeff = F.leadingCoeff * b ^ F.natDegree := by
    have hzero : ∀ k > F.natDegree, G.coeff k = 0 := by
      intro k hk
      rw [hGcoeff k, if_neg]
      intro hmem
      have := Polynomial.mem_support_iff.mp hmem
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk] at this
      exact this rfl
    have hdeg : G.natDegree = F.natDegree :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
        (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hzero) (by
          rw [hGcoeff, if_pos hm, Polynomial.coeff_natDegree (p := F)]
          exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hF) (pow_ne_zero _ hb))
    rw [Polynomial.leadingCoeff, hdeg, hGcoeff, if_pos hm, Polynomial.coeff_natDegree (p := F)]
  have hG1 : v (G.eval 1) < 1 := by
    rw [hcomp, mul_one, eval_eq_sum_support]
    exact hred
  obtain ⟨β, hβmem, hβ1, hβ2⟩ :=
    exists_root_residue_one v (IsAlgClosed.splits G) hGle
      (by
        rw [hGlead, map_mul, ← Polynomial.coeff_natDegree (p := F), ← map_mul]
        exact huniv F.natDegree hm) hG1
  refine ⟨b * β, ?_, ?_⟩
  · rw [rv_eq_iff hb]
    refine ⟨by rw [map_mul, hβ1, mul_one], ?_⟩
    have hdiv : (b * β) / b - 1 = β - 1 := by
      rw [mul_div_cancel_left₀ _ hb]
    rw [hdiv, show β - 1 = -(1 - β) by ring, v.map_neg]
    exact hβ2
  · show F.eval (b * β) = 0
    rw [← hcomp β]
    exact Polynomial.isRoot_of_mem_roots hβmem

end Main


section GaussNorm

variable {v : Valuation K Γ₀} {b : K}




/-- The Gauss norm `max_j v (P.coeff j · b^j)` of `P` at `b`. -/
noncomputable def Mb (v : Valuation K Γ₀) (b : K) (P : K[X]) : Γ₀ :=
  P.support.sup (fun j => v (P.coeff j * b ^ j))



lemma Mb_zero : Mb v b 0 = 0 := by
  rw [Mb, Polynomial.support_zero, Finset.sup_empty]
  exact bot_eq_zero

lemma mb_le_sup {P : K[X]} {j : ℕ} (hj : j ∈ P.support) :
    v (P.coeff j * b ^ j) ≤ Mb v b P :=
  Finset.le_sup (f := fun j => v (P.coeff j * b ^ j)) hj

lemma Mb_C (c : K) : Mb v b (C c) = v c := by
  have hsub : (C c).support ⊆ {0} := by
    intro j hj
    rw [Finset.mem_singleton]
    by_contra h
    rw [Polynomial.mem_support_iff] at hj
    exact hj (by rw [Polynomial.coeff_C]; simp [h])
  have h0 : (C c).coeff 0 = c := by rw [Polynomial.coeff_C]; simp
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le (fun j hj => ?_)
    rw [Finset.mem_singleton.mp (hsub hj), h0, pow_zero, mul_one]
  · rcases eq_or_ne c 0 with hc | hc
    · rw [hc, map_zero]
      exact zero_le
    · have hmem : (0 : ℕ) ∈ (C c).support := by
        rw [Polynomial.mem_support_iff, h0]; exact hc
      have := mb_le_sup (v := v) (b := b) (P := C c) hmem
      rwa [h0, pow_zero, mul_one] at this

lemma Mb_X_sub_C (β : K) : Mb v b (X - C β) = max (v b) (v β) := by
  have hdeg : (X - C β).natDegree ≤ 1 := by
    have h := Polynomial.natDegree_sub_le (X : K[X]) (C β)
    have hX : (X : K[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
    have hC : (C β).natDegree ≤ 1 := by rw [Polynomial.natDegree_C]; norm_num
    exact h.trans (max_le hX hC)
  have hsub : (X - C β).support ⊆ {0, 1} := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_contra hcon
    push_neg at hcon
    rw [Polynomial.mem_support_iff] at hj
    exact hj (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have h0 : (X - C β).coeff 0 = -β := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have h1 : (X - C β).coeff 1 = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le (fun j hj => ?_)
    rcases Finset.mem_insert.mp (hsub hj) with rfl | hj1
    · rw [h0, pow_zero, mul_one, v.map_neg]
      exact le_max_right (v b) (v β)
    · rw [Finset.mem_singleton.mp hj1, h1, one_mul, pow_one]
      exact le_max_left (v b) (v β)
  · have hmem : (1 : ℕ) ∈ (X - C β).support := by
      rw [Polynomial.mem_support_iff, h1]; simp
    have hb1 := mb_le_sup (v := v) (b := b) (P := X - C β) hmem
    rw [h1, one_mul, pow_one] at hb1
    have hb0 : v β ≤ Mb v b (X - C β) := by
      by_cases hβ : β = 0
      · rw [hβ, map_zero]; exact zero_le
      · have hmem0 : (0 : ℕ) ∈ (X - C β).support := by
          rw [Polynomial.mem_support_iff, h0]
          simpa using hβ
        have h := mb_le_sup (v := v) (b := b) (P := X - C β) hmem0
        rwa [h0, pow_zero, mul_one, v.map_neg] at h
    exact max_le hb1 hb0







lemma mb_le (P : K[X]) (j : ℕ) : v (P.coeff j * b ^ j) ≤ Mb v b P := by
  by_cases h : j ∈ P.support
  · exact Finset.le_sup (f := fun j => v (P.coeff j * b ^ j)) h
  · rw [Polynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul, map_zero]
    exact zero_le

lemma mul_lt_mul_of_lt_of_le' {a b c d : Γ₀} (h1 : a < b) (h2 : c ≤ d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a * c < b * d := by
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, mul_zero]
    exact zero_lt_iff.mpr (mul_ne_zero hb hd)
  · calc a * c < b * c := mul_lt_mul_of_pos_right h1 (zero_lt_iff.mpr hc)
      _ ≤ b * d := mul_le_mul_right h2 b

lemma Mb_mul (hb : b ≠ 0) (P Q : K[X]) :
    Mb v b (P * Q) = Mb v b P * Mb v b Q := by
  rcases eq_or_ne P 0 with hP | hP
  · rw [hP, zero_mul, Mb_zero, zero_mul]
  rcases eq_or_ne Q 0 with hQ | hQ
  · rw [hQ, mul_zero, Mb_zero, mul_zero]
  have hPne : P.support.Nonempty := Polynomial.support_nonempty.mpr hP
  have hQne : Q.support.Nonempty := Polynomial.support_nonempty.mpr hQ
  have hMP0 : Mb v b P ≠ 0 := by
    obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_sup P.support hPne
      (fun j => v (P.coeff j * b ^ j))
    rw [Mb, hie]
    exact (Valuation.ne_zero_iff v).mpr
      (mul_ne_zero (Polynomial.mem_support_iff.mp hi) (pow_ne_zero _ hb))
  have hMQ0 : Mb v b Q ≠ 0 := by
    obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_sup Q.support hQne
      (fun j => v (Q.coeff j * b ^ j))
    rw [Mb, hie]
    exact (Valuation.ne_zero_iff v).mpr
      (mul_ne_zero (Polynomial.mem_support_iff.mp hi) (pow_ne_zero _ hb))
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le (fun k _ => ?_)
    rw [Polynomial.coeff_mul, Finset.sum_mul]
    refine v.map_sum_le (fun x hx => ?_)
    have hx' : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have heq : (P.coeff x.1 * Q.coeff x.2) * b ^ k
        = (P.coeff x.1 * b ^ x.1) * (Q.coeff x.2 * b ^ x.2) := by
      rw [← hx', pow_add]; ring
    rw [heq, map_mul]
    exact mul_le_mul (mb_le (v := v) (b := b) P x.1) (mb_le (v := v) (b := b) Q x.2) zero_le zero_le
  · -- lower bound: the minimal index at which the maximum is attained
    set SP := P.support.filter (fun a => v (P.coeff a * b ^ a) = Mb v b P) with hSPdef
    have hSPne : SP.Nonempty := by
      obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_sup P.support hPne
        (fun j => v (P.coeff j * b ^ j))
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hie.symm⟩⟩
    set SQ := Q.support.filter (fun a => v (Q.coeff a * b ^ a) = Mb v b Q) with hSQdef
    have hSQne : SQ.Nonempty := by
      obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_sup Q.support hQne
        (fun j => v (Q.coeff j * b ^ j))
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hie.symm⟩⟩
    set i0 := SP.min' hSPne with hi0def
    set j0 := SQ.min' hSQne with hj0def
    have hi0SP : i0 ∈ SP := Finset.min'_mem SP hSPne
    have hj0SQ : j0 ∈ SQ := Finset.min'_mem SQ hSQne
    have hi0mem : i0 ∈ P.support := (Finset.mem_filter.mp hi0SP).1
    have hj0mem : j0 ∈ Q.support := (Finset.mem_filter.mp hj0SQ).1
    have hi0max : v (P.coeff i0 * b ^ i0) = Mb v b P := (Finset.mem_filter.mp hi0SP).2
    have hj0max : v (Q.coeff j0 * b ^ j0) = Mb v b Q := (Finset.mem_filter.mp hj0SQ).2
    have hi0min : ∀ a ∈ P.support, a < i0 → v (P.coeff a * b ^ a) < Mb v b P := by
      intro a ha halt
      rcases eq_or_ne (v (P.coeff a * b ^ a)) (Mb v b P) with heq | hne
      · exact absurd (Finset.min'_le SP a (Finset.mem_filter.mpr ⟨ha, heq⟩)) (by omega)
      · exact lt_of_le_of_ne (mb_le P a) hne
    have hj0min : ∀ a ∈ Q.support, a < j0 → v (Q.coeff a * b ^ a) < Mb v b Q := by
      intro a ha halt
      rcases eq_or_ne (v (Q.coeff a * b ^ a)) (Mb v b Q) with heq | hne
      · exact absurd (Finset.min'_le SQ a (Finset.mem_filter.mpr ⟨ha, heq⟩)) (by omega)
      · exact lt_of_le_of_ne (mb_le Q a) hne
    have hRval : v ((P.coeff i0 * Q.coeff j0) * b ^ (i0 + j0)) = Mb v b P * Mb v b Q := by
      have hp : (P.coeff i0 * Q.coeff j0) * b ^ (i0 + j0)
          = (P.coeff i0 * b ^ i0) * (Q.coeff j0 * b ^ j0) := by
        rw [pow_add]; ring
      rw [hp, map_mul, hi0max, hj0max]
    have hkey : v ((P * Q).coeff (i0 + j0) * b ^ (i0 + j0)) = Mb v b P * Mb v b Q := by
      rw [Polynomial.coeff_mul, Finset.sum_mul, ← hRval]
      refine v.map_sum_eq_of_lt (s := Finset.HasAntidiagonal.antidiagonal (i0 + j0))
        (j := (i0, j0)) ?hmem ?hother
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
      · intro x hx
        rw [show v ((P.coeff (i0, j0).1 * Q.coeff (i0, j0).2) * b ^ (i0 + j0))
            = Mb v b P * Mb v b Q from hRval]
        have hx2' : x ∈ Finset.HasAntidiagonal.antidiagonal (i0 + j0) ∧ x ≠ (i0, j0) := by
          simpa only [Finset.mem_sdiff, Finset.mem_singleton] using hx
        obtain ⟨hxmem, hxne⟩ := hx2'
        have hx' : x.1 + x.2 = i0 + j0 := Finset.HasAntidiagonal.mem_antidiagonal.mp hxmem
        have heq : (P.coeff x.1 * Q.coeff x.2) * b ^ (i0 + j0)
            = (P.coeff x.1 * b ^ x.1) * (Q.coeff x.2 * b ^ x.2) := by
          rw [← hx', pow_add]; ring
        rw [heq, map_mul]
        rcases lt_trichotomy x.1 i0 with hlt | heq1 | hgt
        · have hP' : v (P.coeff x.1 * b ^ x.1) < Mb v b P := by
            by_cases hmem : x.1 ∈ P.support
            · exact hi0min x.1 hmem hlt
            · rw [Polynomial.mem_support_iff, not_not] at hmem
              rw [hmem, zero_mul, map_zero]
              exact zero_lt_iff.mpr hMP0
          exact mul_lt_mul_of_lt_of_le' hP' (mb_le (v := v) (b := b) Q x.2) hMP0 hMQ0
        · exact absurd (Prod.ext heq1 (by omega)) hxne
        · have hx2 : x.2 < j0 := by omega
          have hQ' : v (Q.coeff x.2 * b ^ x.2) < Mb v b Q := by
            by_cases hmem : x.2 ∈ Q.support
            · exact hj0min x.2 hmem hx2
            · rw [Polynomial.mem_support_iff, not_not] at hmem
              rw [hmem, zero_mul, map_zero]
              exact zero_lt_iff.mpr hMQ0
          have hlt2 := mul_lt_mul_of_lt_of_le' hQ' (mb_le (v := v) (b := b) P x.1) hMQ0 hMP0
          simpa [mul_comm] using hlt2
    have hmem : (i0 + j0) ∈ (P * Q).support := by
      rw [Polynomial.mem_support_iff]
      intro h0
      have hz : v ((P * Q).coeff (i0 + j0) * b ^ (i0 + j0)) = 0 := by
        rw [h0, zero_mul, map_zero]
      rw [hkey] at hz
      exact mul_ne_zero hMP0 hMQ0 hz
    have hfin := mb_le (v := v) (b := b) (P * Q) (i0 + j0)
    rwa [hkey] at hfin







lemma Mb_one : Mb v b (1 : K[X]) = 1 := by
  rw [show (1 : K[X]) = C (1 : K) by simp, Mb_C, map_one]

lemma Mb_multiset_prod (hb : b ≠ 0) (m : Multiset K[X]) :
    Mb v b m.prod = (m.map (Mb v b)).prod := by
  induction m using Multiset.induction_on with
  | empty => rw [Multiset.prod_zero, Mb_one, Multiset.map_zero, Multiset.prod_zero]
  | cons a s ih =>
    rw [Multiset.prod_cons, Mb_mul hb, ih, Multiset.map_cons, Multiset.prod_cons]

/-- Two elements with the same valuation but different `rv`-classes are at distance
`v b` from each other. -/
lemma v_sub_eq_max {α : K} (h : ¬(v α = v b ∧ v (α / b - 1) < 1)) :
    v (b - α) = max (v b) (v α) := by
  rcases eq_or_ne b 0 with hb0 | hb0
  · rw [hb0, zero_sub, v.map_neg, map_zero]
    exact (max_eq_right zero_le).symm
  rcases lt_trichotomy (v b) (v α) with hlt | heq | hgt
  · rw [v.map_sub_swap, max_eq_right hlt.le]
    exact v.map_sub_eq_of_lt_left hlt
  · have hvα : v α = v b := heq.symm
    have hge : 1 ≤ v (α / b - 1) := by
      by_contra hc
      exact h ⟨hvα, not_le.mp hc⟩
    have hdiv : v (α / b) = 1 := by
      rw [Valuation.map_div v, hvα, div_self]
      exact (Valuation.ne_zero_iff v).mpr hb0
    have hle : v (α / b - 1) ≤ 1 := by
      refine le_trans (v.map_sub _ _) (max_le ?_ ?_)
      · rw [hdiv]
      · rw [Valuation.map_one]
    have hone : v (α / b - 1) = 1 := le_antisymm hle hge
    have hfac : b - α = b * (1 - α / b) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hb0]
    rw [hfac, map_mul, heq, max_self]
    have : v (1 - α / b) = 1 := by
      rw [show (1 : K) - α / b = -(α / b - 1) by ring, v.map_neg, hone]
    rw [this, mul_one]
  · rw [v.map_sub_swap, max_eq_left hgt.le]
    exact v.map_sub_eq_of_lt_right hgt







end GaussNorm

section General

variable (v : Valuation K Γ₀)

/-- The step of Yin's Lemma 3.2 that needs the Newton polygon with residues, isolated as an
explicit `Prop`.  Let `H` be the polynomial `F(bX)` obtained by rescaling `F` at `b`; its
coefficients are `F.coeff i * b^i`.  The `Finset I` is the support of Yin's `RV`-polynomial
`F̄`: the indices whose coefficient is a unit (`t_i ≠ 0`), the others lying in the maximal
ideal (his side condition `vrv (rv b_i · t^i) > 0`).  The assertion is that among the roots
of `H` with `v = 1` — there are `max I - min I` of them, by the Newton polygon — one has
residue `1`, because the reduction of `H` vanishes at `1` (this is `hred`).  This is the only
input of `rv_root_lift_general` not proved in this file; the lemma
`exists_root_residue_one` proves the conclusion in the case `I = supp H`, where no
coefficient is dropped. -/
def NewtonPolygonRoot (v : Valuation K Γ₀) : Prop :=
  ∀ (H : K[X]), H ≠ 0 → H.Splits → (∀ j, v (H.coeff j) ≤ 1) →
    ∀ I : Finset ℕ, I ⊆ H.support → 2 ≤ I.card →
      (∀ j ∈ I, v (H.coeff j) = 1) →
      (∀ j ∈ H.support, j ∉ I → v (H.coeff j) < 1) →
      v (H.eval 1) < 1 →
      ∃ β ∈ H.roots, v β = 1 ∧ v (1 - β) < 1

/-- **Yin's Lemma 3.2 (`rv:root:lift:vf`) in full generality**, modulo the explicitly named
hypothesis `NewtonPolygonRoot v`: an `RV`-root `t` of an `RV`-polynomial whose coefficients
are the `rv`-classes of the coefficients of `F`, and whose reduction vanishes at `t`, lifts
to a root `b'` of `F` with `rv b' = rv b`.

The hypotheses are the paper's, decoded: `I` is the support of `F̄` (the indices `i` with
`t_i ≠ 0`); `huniv` is `t_i = rv b_i` together with `vrv (t_i t^i) = 1` (each surviving term
lies in the residue field `K^×`); `hsmall` is the paper's side condition
`vrv (rv b_i · t^i) > 0` for the dropped coefficients; and `hred` is `F̄(t) = 0`, since a sum
of residue classes vanishes exactly when the sum of the representatives drops into the
maximal ideal. -/
theorem rv_root_lift_general [IsAlgClosed K] (hNP : NewtonPolygonRoot v)
    {F : K[X]} (hF : F ≠ 0) {b : K} (hb : b ≠ 0) (I : Finset ℕ)
    (hIsub : ∀ i ∈ I, i ∈ F.support)
    (huniv : ∀ i ∈ I, v (F.coeff i * b ^ i) = 1)
    (hsmall : ∀ i ∈ F.support, i ∉ I → v (F.coeff i * b ^ i) < 1)
    (hI : 2 ≤ I.card)
    (hred : v (∑ i ∈ I, F.coeff i * b ^ i) < 1) :
    ∃ b' : K, rv v b' = rv v b ∧ F.IsRoot b' := by
  set H : K[X] := ∑ i ∈ F.support, Polynomial.monomial i (F.coeff i * b ^ i) with hHdef
  have hHcoeff : ∀ k, H.coeff k = if k ∈ F.support then F.coeff k * b ^ k else 0 := by
    intro k
    rw [hHdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hHmem : ∀ k, k ∈ H.support ↔ (k ∈ F.support ∧ F.coeff k * b ^ k ≠ 0) := by
    intro k
    rw [Polynomial.mem_support_iff, hHcoeff k]
    split_ifs with hk
    · simp [hk]
    · simp [hk]
  have hHcomp : ∀ x : K, H.eval x = F.eval (b * x) := by
    intro x
    rw [hHdef, Polynomial.eval_finsetSum, eval_eq_sum_support]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Polynomial.eval_monomial]
    rw [mul_pow]
    ring
  have hHle : ∀ j, v (H.coeff j) ≤ 1 := by
    intro j
    rw [hHcoeff j]
    split_ifs with hj
    · by_cases hJI : j ∈ I
      · rw [huniv j hJI]
      · exact le_of_lt (hsmall j hj hJI)
    · simp
  have hHunit : ∀ j ∈ I, v (H.coeff j) = 1 := by
    intro j hj
    rw [hHcoeff j, if_pos (hIsub j hj)]
    exact huniv j hj
  have hHsmall : ∀ j ∈ H.support, j ∉ I → v (H.coeff j) < 1 := by
    intro j hj hjI
    have hjs : j ∈ F.support := ((hHmem j).mp hj).1
    rw [hHcoeff j, if_pos hjs]
    exact hsmall j hjs hjI
  have hHred : v (H.eval 1) < 1 := by
    rw [hHcomp, mul_one, eval_eq_sum_support]
    have hsplit : ∑ x ∈ F.support, F.coeff x * b ^ x
        = ∑ x ∈ F.support \ I, F.coeff x * b ^ x + ∑ x ∈ I, F.coeff x * b ^ x := by
      rw [← Finset.sum_sdiff hIsub]
    rw [hsplit]
    refine v.map_add_lt ?_ hred
    exact v.map_sum_lt one_ne_zero
      (fun i hi => hsmall i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2)
  have hm : F.natDegree ∈ F.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hF)
  have hHne : H ≠ 0 := by
    intro h0
    have h1 : H.coeff F.natDegree = F.leadingCoeff * b ^ F.natDegree := by
      rw [hHcoeff, if_pos hm, Polynomial.coeff_natDegree (p := F)]
    rw [h0] at h1
    simp only [Polynomial.coeff_zero] at h1
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hF) (pow_ne_zero _ hb) h1.symm
  have hInz : ∀ j ∈ I, F.coeff j * b ^ j ≠ 0 := by
    intro j hj h0
    have h1 := huniv j hj
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨β, hβmem, hβ1, hβ2⟩ :=
    hNP H hHne (IsAlgClosed.splits H) hHle I
      (fun j hj => (hHmem j).mpr ⟨hIsub j hj, hInz j hj⟩) hI hHunit hHsmall hHred
  refine ⟨b * β, ?_, ?_⟩
  · rw [rv_eq_iff hb]
    refine ⟨by rw [map_mul, hβ1, mul_one], ?_⟩
    have hdiv : (b * β) / b - 1 = β - 1 := by rw [mul_div_cancel_left₀ _ hb]
    rw [hdiv, show β - 1 = -(1 - β) by ring, v.map_neg]
    exact hβ2
  · show F.eval (b * β) = 0
    rw [← hHcomp β]
    exact Polynomial.isRoot_of_mem_roots hβmem

end General




section Gap

variable (v : Valuation K Γ₀)

/-- **The no-cancellation identity (Newton polygon).**  If no root of `F` lies in the `rv`-class
of `b`, the terms `F.coeff j · b^j` do not cancel at the maximal valuation, so `v (F b)` is the
maximum of `v (F.coeff j · b^j)`.

This is the single analytic input of Yin's Lemma 3.2 that is not proved in this file.  It is
the Newton polygon theorem at the slope `-v b`: the polygon of `F` at `b` has its lower
endpoint at a term of maximal valuation, with slope `-v b` (see Yin's proof, where
`(m, vv (b_m/b_n))`, `(l, vv (b_l/b_n))` are adjacent vertices).  We isolate it because
everything else in Lemma 3.2 reduces to it by elementary manipulations (below). -/
def NoCancellation (v : Valuation K Γ₀) : Prop :=
  ∀ (F : K[X]) (b : K), F ≠ 0 → b ≠ 0 → F.Splits →
    (∀ r ∈ F.roots, rv v r ≠ rv v b) →
    v (F.eval b) = F.support.sup (fun j => v (F.coeff j * b ^ j))

variable {v}

/-- `NewtonPolygonRoot` follows from the no-cancellation identity, with no further input:
if `H`'s reduction vanishes at `1` then `v (H 1) < 1`, but if no root of `H` has the
`rv`-class of `1` then `v (H 1)` equals the maximum of `v (H.coeff j)`, which is `1` because
`I` is nonempty and consists of unit coefficients. -/
theorem newtonPolygonRoot_of_noCancellation (h : NoCancellation v) : NewtonPolygonRoot v := by
  intro H hH0 hspl hHle I hIsub hI hIunit hIsmall hred
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hno : ∀ r ∈ H.roots, rv v r ≠ rv v (1 : K) := by
    intro r hr hr_eq
    obtain ⟨h1, h2⟩ := (rv_eq_iff (one_ne_zero : (1 : K) ≠ 0)).mp hr_eq
    rw [div_one] at h2
    have h2' : v (1 - r) < 1 := by
      rw [show (1 : K) - r = -(r - 1) by ring, v.map_neg]
      exact h2
    exact hcon r hr (by simpa using h1) h2'
  have hsup : H.support.sup (fun j => v (H.coeff j * (1 : K) ^ j)) = 1 := by
    refine le_antisymm (Finset.sup_le (fun j _ => by simpa using hHle j)) ?_
    obtain ⟨j, hjI, k, hk, hjk⟩ := Finset.one_lt_card.mp (show 1 < I.card from hI)
    have hjs : j ∈ H.support := hIsub hjI
    have h1 : v (H.coeff j * (1 : K) ^ j) = 1 := by simpa using hIunit j hjI
    rw [← h1]
    exact Finset.le_sup (f := fun j => v (H.coeff j * (1 : K) ^ j)) hjs
  have hval := h H (1 : K) hH0 one_ne_zero hspl hno
  rw [hsup] at hval
  rw [hval] at hred
  exact absurd hred (lt_irrefl 1)

/-- **The no-cancellation identity, proved.**  If no root of `F` lies in the `rv`-class of `b`,
then `Gauss norm at `b` equals `v (F b)`: the `Gauss` norm `max_j v (F.coeff j · b^j)` is
multiplicative (`Mb_mul`), and `v (b - r) = max (v b) (v r)` for a root `r` outside the class of
`b` (`v_sub_eq_max`). -/
theorem noCancellation (v : Valuation K Γ₀) : NoCancellation v := by
  intro F b hF hb hspl hno
  have h1 : v (F.eval b) = v F.leadingCoeff * (F.roots.map (fun r => v (b - r))).prod := by
    rw [hspl.eval_eq_prod_roots b, map_mul, map_multiset_prod, Multiset.map_map]
    rfl
  have h2 : F.roots.map (fun r => v (b - r)) = F.roots.map (fun r => max (v b) (v r)) := by
    refine Multiset.map_congr rfl (fun r hr => ?_)
    exact v_sub_eq_max (fun hh => hno r hr ((rv_eq_iff hb).mpr hh))
  have h3 : Mb v b F = v F.leadingCoeff * (F.roots.map (fun r => max (v b) (v r))).prod := by
    conv_lhs => rw [hspl.eq_prod_roots]
    rw [Mb_mul hb, Mb_C, Mb_multiset_prod hb, Multiset.map_map]
    simp only [Function.comp_def]
    have hmap : (F.roots.map fun r => Mb v b (X - C r)) = F.roots.map (fun r => max (v b) (v r)) :=
      Multiset.map_congr rfl (fun r _ => Mb_X_sub_C r)
    rw [hmap]
  rw [h1, h2, ← h3]
  rfl



end Gap

section Transfer

/-- **Remark 3.1, first half (`L:v:and:L:RV`), at the level of `rv`.**  An `L_v`-embedding of
valued fields — a field map `f` preserving the valuation and its order, which is what the two
hypotheses `hval`, `hsmall` encode — preserves `rv`-classes.  Hence the `RV`-structure is
determined by the `L_v`-structure, and an `L_v`-monomorphism whose domain is VF-generated is
an `L_RV`-monomorphism (the Remark's "two valued fields are monomorphic as `L_RV`-structures
iff as `L_v`-structures"). -/
theorem rv_eq_of_val_eq {L Γ₀' : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀']
    (w : Valuation L Γ₀') (f : K →+* L)
    (hval : ∀ x y : K, w (f x) = w (f y) ↔ v x = v y)
    (hsmall : ∀ x : K, w (f x) < 1 ↔ v x < 1)
    {x y : K} (hxy : rv v x = rv v y) : rv w (f x) = rv w (f y) := by
  rcases eq_or_ne y 0 with hy0 | hy
  · have hx0 : x = 0 := by
      rw [hy0, rv_zero] at hxy
      exact rv_eq_none_iff.mp hxy
    rw [hx0, hy0, map_zero, rv_zero]
  have hfyn : f y ≠ 0 := fun h => hy (f.injective (by rw [h, map_zero]))
  obtain ⟨h1, h2⟩ := (rv_eq_iff hy).mp hxy
  refine (rv_eq_iff (v := w) hfyn).mpr ⟨(hval x y).mpr h1, ?_⟩
  have hdiv : f x / f y - 1 = f (x / y - 1) := by rw [map_sub, map_div₀, map_one]
  rw [hdiv]
  exact (hsmall _).mpr h2

end Transfer


section Wrap

variable (v : Valuation K Γ₀)

/-- **Yin's Lemma 3.2 (`rv:root:lift:vf`), in full generality** — no unproved input: the
Newton-polygon content is the identity `noCancellation`, which is proved above. -/
theorem rv_root_lift [IsAlgClosed K]
    {F : K[X]} (hF : F ≠ 0) {b : K} (hb : b ≠ 0) (I : Finset ℕ)
    (hIsub : ∀ i ∈ I, i ∈ F.support)
    (huniv : ∀ i ∈ I, v (F.coeff i * b ^ i) = 1)
    (hsmall : ∀ i ∈ F.support, i ∉ I → v (F.coeff i * b ^ i) < 1)
    (hI : 2 ≤ I.card)
    (hred : v (∑ i ∈ I, F.coeff i * b ^ i) < 1) :
    ∃ b' : K, rv v b' = rv v b ∧ F.IsRoot b' :=
  rv_root_lift_general v (newtonPolygonRoot_of_noCancellation (noCancellation v))
    hF hb I hIsub huniv hsmall hI hred

/-- Lemma 3.2 in the `RV`-form of the paper: the conclusion is stated with `t ∈ RV`. -/
theorem rv_root_lift_rv [IsAlgClosed K] {F : K[X]} (hF : F ≠ 0) {b : K} {t : RV v}
    (ht : t ≠ rvInfty v) (hb : rv v b = t)
    (huniv : ∀ i ∈ F.support, v (F.coeff i * b ^ i) = 1)
    (hred : v (∑ i ∈ F.support, F.coeff i * b ^ i) < 1) :
    ∃ b' : K, rv v b' = t ∧ F.IsRoot b' := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [rv_zero] at hb
    exact ht hb.symm
  obtain ⟨b', hb', hroot⟩ := rv_root_lift_of_support_all v hF hb0 huniv hred
  exact ⟨b', by rw [hb', hb], hroot⟩

end Wrap

end YinRV

#print axioms YinRV.root_integral
#print axioms YinRV.exists_root_residue_one
#print axioms YinRV.rv_eq_iff
#print axioms YinRV.noCancellation
#print axioms YinRV.newtonPolygonRoot_of_noCancellation
#print axioms YinRV.rv_root_lift_of_support_all
#print axioms YinRV.rv_root_lift
#print axioms YinRV.rv_root_lift_rv
#print axioms YinRV.rv_eq_of_val_eq
