/-
# Yin, Lemma 3.8 (`lift:value:full`): the `RV` half

Reference: Yimu Yin, Section 3 of arXiv:1006.2467 (LaTeX source `qe.tex`, l. 803).
`QE/Lemma37_transcendental.lean` proves the *value* half of Lemmas 3.7/3.8
(`vv(b(e)) = vv(b*(d))` when `vv(d) = vv(e)`, under `Γ(Ŝ)` divisible).  Its header records the
gap this file fills:

> the `RV`-sort (`rv = vv`-fibres) is not formalized here either.

Lemma 3.8's claim (⋆) is *not* only about values: it says

  `RV(⟨Ŝ, e⟩) = ⟨RV(Ŝ), rv(e)⟩` and `f` extends to `f* : ⟨Ŝ, e⟩ → N` with `f*(rv e) = f(rv e)`,

i.e. the extension `e ↦ d` must preserve the `RV`-class (value **and** residue), not merely the
value.  That is exactly what the choice `rv(d) = f(rv(e))` in Yin's proof buys, and it is the
hypothesis under which Remark 3.1 converts a valued-field embedding into an `L_RV`-monomorphism.

## What is formalized

`rv` itself is a quotient `Lˣ/(1+𝔪)` (plus `0`).  Over a field it can be eliminated: two nonzero
elements lie in the same `RV`-class iff they have the same value and their difference is
*strictly more divisible* than that value:

  `SameRV v x y  :↔  v x = v y ∧ v (x - y) < v x`

(`v` takes values in a multiplicative `Γ₀` in which `≤` is divisibility and `0` is the bottom, so
"`∈ 𝔪`" is `< 1`, and "same class" is `x - y` having value below `v x`).  This is a genuine
`def`, not a named `Prop`: everything below is proved.

Main results (all in a single valued field, which is the form the residue comparison takes — a
cross-field `rv` equality has no meaning until one fixes the identification of residue fields
that `f` provides, and Yin's proof supplies it by placing `f(bᵢ)` and `d` in `N`):

* `sameRV_vfSum` — **Lemma 3.8's rv half, at `rv(d) = rv(e)`**: if `v e` has infinite order
  modulo `Γ(VF(Ŝ))` (which divisibility of `Γ(Ŝ)` plus `vv(e) ∉ Γ(Ŝ)` gives,
  `YinLemma37.infiniteOrderMod_of_divisible`), `e, d` transcendental over `VF(Ŝ)`, and
  `SameRV v e d`, then corresponding polynomial expansions have the *same `RV`-class*:
  `SameRV (∑ bᵢeⁱ) (∑ bᵢdⁱ)`.  Yin's `vv(b) = vv(b*)` is the value projection of this.
* `SameRV.vfSum_dominant`, `map_sum_lt` — the two devices: a sum of terms with values below `g`
  has value below `g`, so the class of a sum is the class of a strictly dominant monomial
  (Yin's "`rv(∑ bᵢeⁱ) = rv(bⱼeʲ)` for some `j`", qe.tex:645).

## Relation to the frozen `LRV` encoding (why this is the missing half, and when it is needed)

In the frozen encoding `rv` is a *function symbol* (`iRv`), so an `LRV`-embedding preserves `rv`
automatically; and the frozen `Claim (⋆)` statements (`M5L34_36.ClassStepP`, `M8Stars.RVcontrol`)
are phrased with `Cls t y :↔ iLe t y ∧ iLe y t` — the *Γ-class*, not `rv` — which is legitimate
because `Assembly.Standing S` carries `KEqTop S` and a class-equal nonzero `RV`-element differs
from any representative by a *unit* (`M8Stars.mem_of_cls`, `M5L34_36.mem_of_cls_mem`).  So the
residue half is **not** a bottleneck for `M5.RVStepP`: at the frozen level it is absorbed by
`KEqTop`, and the real residual there is realisation of the atomic type of `m` over `S`
(`Realize.RealizesAtomic`, from saturation).

What *does* need the residue half is the honest valued-field statement that the extension
`e ↦ d` preserves `RV` and not merely `vv` — the `f*(rv e) = f(rv e)` in Yin's Claim (⋆), or
equivalently that `e ↦ d` "induces a valued field embedding" of residue fields, which is the
hypothesis Remark 3.1 consumes.  That is what this file proves; nothing in it is a `Prop`
hypothesis standing in for a theorem.

## Faithfulness and non-vacuity

* Hypotheses are Yin's, with `K = VF(Ŝ)` a `Subfield L` and `SameRV v e d` the residue-level
  content of `rv(d) = f(rv e)` after `f` identifies `VF(Ŝ)` with `f(VF(Ŝ))` inside one field
  (Yin's proof places both `f(bᵢ)` and `d` in `N`, so this is a faithful reading, not a
  weakening).  `InfiniteOrderMod v e K` is exactly `YinLemma37`'s hypothesis, supplied there by
  `infiniteOrderMod_of_divisible` from divisibility of `Γ(Ŝ)` and `vv(e) ∉ Γ(Ŝ)`.
* `SameRV` is satisfiable with *distinct* arguments: `sameRV_one_add` gives
  `SameRV v 1 (1 + m)` for any `m ∈ 𝔪`.
* Transcendence of `e` is a hypothesis (as in `YinLemma37.e_transc_aeval`), not derived: deriving
  it from `vv(e) ∉ Γ(Ŝ)` needs the fundamental inequality of valuation theory, which the tree
  quotes elsewhere and which is not needed for the `rv` computation itself.

No `sorry`, no `axiom`, no `native_decide`; each headline theorem's `#print axioms` is
`[propext, Classical.choice, Quot.sound]` (see the end of the file).
-/
import Lemma37_transcendental

open Valuation

namespace YinLemma38

open YinLemma37

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ## 1. `SameRV`: equality of `RV`-classes, expressed through the valuation -/

/-- **`x` and `y` lie in the same `RV`-class.**  Both are nonzero, have the same value, and their
difference is strictly more divisible than that value.  For nonzero `x, y` this is
`x/y ∈ 1 + 𝔪` under `v x = v y`, i.e. `rv x = rv y` in `RV = Lˣ/(1+𝔪) ∪ {0}`. -/
def SameRV (v : Valuation L Γ₀) (x y : L) : Prop :=
  v x = v y ∧ v (x - y) < v x

theorem SameRV.ne_zero_left {v : Valuation L Γ₀} {x y : L} (h : SameRV v x y) : x ≠ 0 := by
  rintro rfl
  rw [SameRV, Valuation.map_zero] at h
  exact absurd h.2 (not_lt_of_ge (zero_le : (0 : Γ₀) ≤ v (0 - y)))

theorem SameRV.ne_zero_right {v : Valuation L Γ₀} {x y : L} (h : SameRV v x y) : y ≠ 0 := by
  rintro rfl
  obtain ⟨h1, h2⟩ := h
  rw [Valuation.map_zero] at h1
  rw [h1] at h2
  exact absurd h2 (not_lt_of_ge (zero_le : (0 : Γ₀) ≤ v (x - 0)))

theorem SameRV.value_eq {v : Valuation L Γ₀} {x y : L} (h : SameRV v x y) : v x = v y := h.1

/-- **Reflexivity**: an element is in its own `RV`-class. -/
theorem sameRV_refl (v : Valuation L Γ₀) {x : L} (hx : x ≠ 0) : SameRV v x x := by
  refine ⟨rfl, ?_⟩
  rw [sub_self, Valuation.map_zero]
  exact zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hx)

theorem SameRV.symm {v : Valuation L Γ₀} {x y : L} (h : SameRV v x y) : SameRV v y x := by
  obtain ⟨hxy, hlt⟩ := h
  refine ⟨hxy.symm, ?_⟩
  rw [show y - x = -(x - y) by ring, Valuation.map_neg]
  exact hxy ▸ hlt

/-- **Transitivity**: `1 + 𝔪` is a subgroup. -/
theorem SameRV.trans {v : Valuation L Γ₀} {x y z : L} (h1 : SameRV v x y) (h2 : SameRV v y z) :
    SameRV v x z := by
  obtain ⟨hxy, h1'⟩ := h1
  obtain ⟨hyz, h2'⟩ := h2
  refine ⟨hxy.trans hyz, ?_⟩
  have h2x : v (y - z) < v x := h2'.trans_le (le_of_eq hxy.symm)
  have hxz : x - z = (x - y) + (y - z) := by ring
  rw [hxz]
  exact lt_of_le_of_lt (v.map_add _ _) (max_lt h1' h2x)

/-- **Multiplication is well defined on `RV`-classes.** -/
theorem SameRV.mul {v : Valuation L Γ₀} {x y z w : L} (h1 : SameRV v x y) (h2 : SameRV v z w) :
    SameRV v (x * z) (y * w) := by
  obtain ⟨hxy, h1'⟩ := h1
  obtain ⟨hzw, h2'⟩ := h2
  have hx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr (SameRV.ne_zero_left ⟨hxy, h1'⟩)
  have hz0 : v z ≠ 0 := (Valuation.ne_zero_iff v).mpr (SameRV.ne_zero_left ⟨hzw, h2'⟩)
  have hval : v (x * z) = v (y * w) := by
    rw [Valuation.map_mul, Valuation.map_mul, hxy, hzw]
  refine ⟨hval, ?_⟩
  have hkey : x * z - y * w = x * (z - w) + (x - y) * w := by ring
  have hxz : v (x * z) = v x * v z := Valuation.map_mul v x z
  rw [hkey, hxz]
  calc v (x * (z - w) + (x - y) * w)
      ≤ max (v (x * (z - w))) (v ((x - y) * w)) := v.map_add _ _
    _ < v x * v z := by
        rw [Valuation.map_mul, Valuation.map_mul, ← hzw]
        exact max_lt (mul_lt_mul_of_pos_left h2' (zero_lt_iff.mpr hx0))
          (mul_lt_mul_of_pos_right h1' (zero_lt_iff.mpr hz0))

/-- **Scaling**: multiplying by a nonzero `u` multiplies both classes by `rv u`. -/
theorem SameRV.mul_right {v : Valuation L Γ₀} {x y : L} (h : SameRV v x y) {u : L} (hu : u ≠ 0) :
    SameRV v (x * u) (y * u) :=
  SameRV.mul h (sameRV_refl v hu)

/-- **Cancellation**: if `x·u` and `y·u` are in the same class and `u ≠ 0`, so are `x` and `y`. -/
theorem SameRV.of_mul_right {v : Valuation L Γ₀} {x y : L} {u : L} (hu : u ≠ 0)
    (h : SameRV v (x * u) (y * u)) : SameRV v x y := by
  obtain ⟨hval, hlt⟩ := h
  have hvu : v u ≠ 0 := (Valuation.ne_zero_iff v).mpr hu
  have hval' : v x * v u = v y * v u := by
    rw [← Valuation.map_mul, ← Valuation.map_mul]; exact hval
  refine ⟨mul_right_cancel₀ hvu hval', ?_⟩
  have hdiff : x * u - y * u = (x - y) * u := by ring
  rw [hdiff, Valuation.map_mul, Valuation.map_mul] at hlt
  exact lt_of_mul_lt_mul_right hlt zero_le

/-- **Powers preserve `RV`-classes.** -/
theorem SameRV.pow {v : Valuation L Γ₀} {x y : L} (h : SameRV v x y) (n : ℕ) :
    SameRV v (x ^ n) (y ^ n) := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    simp only [pow_zero, sub_self, Valuation.map_zero, Valuation.map_one]
    exact zero_lt_iff.mpr one_ne_zero
  | succ n ih =>
    have h1 : SameRV v (x ^ n * x) (y ^ n * y) := SameRV.mul ih h
    simpa [pow_succ] using h1

/-- **Principal units have the class of `1`.**  If `v m < 1` (i.e. `m ∈ 𝔪`) then `rv (1 + m) = rv 1`.
This is the elementary instance showing `SameRV` has distinct arguments (`1` and `1 + m`), so the
hypothesis `SameRV v e d` used below is not an equality in disguise. -/
theorem sameRV_one_add (v : Valuation L Γ₀) {m : L} (hm : v m < 1) : SameRV v 1 (1 + m) := by
  have hm1 : v m < v (1 : L) := by simpa using hm
  refine ⟨?_, ?_⟩
  · exact (Valuation.map_add_eq_of_lt_left v hm1).symm
  · have hsub : (1 : L) - (1 + m) = -m := by ring
    rw [hsub, Valuation.map_neg]
    exact hm1

/-! ## 2. A strictly dominated sum has the class of its dominant term

This is Yin's `rv (∑ bᵢeⁱ) = rv (bⱼeʲ)` (qe.tex:645), with the "some `j`" made explicit. -/

/-- **A sum of elements whose values are all below `g ≠ 0` has value below `g`.**  (The step that
makes the class of a polynomial expansion the class of its dominant monomial.) -/
theorem map_sum_lt {v : Valuation L Γ₀} {ι : Type*} [DecidableEq ι] :
    ∀ (t : Finset ι) {f : ι → L} {g : Γ₀}, g ≠ 0 → (∀ i ∈ t, v (f i) < g) → v (∑ i ∈ t, f i) < g := by
  intro t
  induction t using Finset.induction_on with
  | empty =>
    intro f g hg _
    rw [Finset.sum_empty, Valuation.map_zero]
    exact zero_lt_iff.mpr hg
  | insert a t ha ih =>
    intro f g hg h
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt (h a (Finset.mem_insert_self a t)) (ih hg ?_))
    intro i hi
    exact h i (Finset.mem_insert_of_mem hi)

/-- **The class of a sum is the class of a strictly dominant term.**  Hypothesis: the term at `j`
strictly dominates every other term (`f i = 0` included, since `v 0 = 0`). -/
theorem sameRV_sum_of_dominant {v : Valuation L Γ₀} {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → L} {j : ι} (hj : j ∈ s) (hfj : f j ≠ 0)
    (hmax : ∀ i ∈ s, i ≠ j → v (f i) < v (f j)) :
    SameRV v (∑ i ∈ s, f i) (f j) := by
  have hg : v (f j) ≠ 0 := (Valuation.ne_zero_iff v).mpr hfj
  have hval : v (∑ i ∈ s, f i) = v (f j) :=
    Valuation.map_sum_eq_of_lt v hj (fun i hi => by
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact hmax i hi.1 hi.2)
  refine ⟨hval, ?_⟩
  have hsplit : (∑ i ∈ s, f i) - f j = ∑ i ∈ s.erase j, f i :=
    (Finset.sum_erase_eq_sub hj).symm
  rw [hsplit, hval]
  refine map_sum_lt (s.erase j) (f := f) (g := v (f j)) hg ?_
  intro i hi
  rw [Finset.mem_erase] at hi
  exact hmax i hi.2 hi.1

/-! ## 3. Lemma 3.8 (`lift:value:full`), `RV` half: `rv(d) = rv(e)` transfers to expansions -/

/-- An element with the same `RV`-class as `e` has the same "infinite order" property: the
hypothesis only mentions `v e`. -/
theorem infiniteOrderMod_of_sameRV {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hord : InfiniteOrderMod v e K) (h : SameRV v e d) : InfiniteOrderMod v d K := by
  intro n hn a ha ha0
  rw [← h.1]
  exact hord n hn a ha ha0

/-- **A sum with a strictly dominant monomial has the class of that monomial.**  This is the
`rv`-level form of `YinLemma37.e_transc`: the value part is the paper's
`vv(b) = min{vv(bᵢeⁱ)}`, and the residue part is new (and is what the extension `e ↦ d` needs). -/
theorem sameRV_vfSum_dominant {v : Valuation L Γ₀} {e : L} {m j : ℕ} {b : ℕ → L}
    (hj : j ≤ m) (hbj : b j ≠ 0) (he : e ≠ 0)
    (hmax : ∀ i ≤ m, i ≠ j → v (b i * e ^ i) < v (b j * e ^ j)) :
    SameRV v (∑ i ∈ Finset.range (m + 1), (b i * e ^ i)) (b j * e ^ j) := by
  have hfj : b j * e ^ j ≠ 0 := mul_ne_zero hbj (pow_ne_zero j he)
  refine sameRV_sum_of_dominant (s := Finset.range (m + 1)) (f := fun i => b i * e ^ i)
    (j := j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hfj ?_
  intro i hi hij
  exact hmax i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hij

/-- **Lemma 3.8 (`lift:value:full`), `RV` half.**  Let `K = VF(Ŝ)`, let `v e` have infinite
order modulo `Γ(K)` (divisibility of `Γ(Ŝ)` plus `vv(e) ∉ Γ(Ŝ)` gives this:
`YinLemma37.infiniteOrderMod_of_divisible`), let `e, d` be transcendental over `K`, and suppose
`d` has the same `RV`-class as `e` — `SameRV v e d`, which is what `rv(d) = f(rv(e))` says after
`f` has been used to identify `VF(Ŝ)` with `f(VF(Ŝ))`.

Then for every polynomial expansion `∑_{i ≤ m} bᵢeⁱ` with `bᵢ ∈ K`, the two expansions
`b = ∑ bᵢeⁱ` and `b* = ∑ bᵢdⁱ` have the *same `RV`-class*: `SameRV v b b*`.  Yin's
`vv(b) = vv(b*)` (Lemma 3.8 / `YinLemma37.value_transfer_sum`) is the value projection; the new
content is the residue half, which is what makes `e ↦ d` an `L_RV`-monomorphism after Remark 3.1. -/
theorem sameRV_vfSum {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hord : InfiniteOrderMod v e K) (he : e ≠ 0) (hsame : SameRV v e d)
    {m : ℕ} {b : ℕ → L} (hb : ∀ i ≤ m, b i ∈ K)
    (hsum : ∑ i ∈ Finset.range (m + 1), (b i * e ^ i) ≠ 0) :
    SameRV v (∑ i ∈ Finset.range (m + 1), (b i * e ^ i))
      (∑ i ∈ Finset.range (m + 1), (b i * d ^ i)) := by
  have hd0 : d ≠ 0 := SameRV.ne_zero_right hsame
  obtain ⟨j, hjm, hbj, _hval, hle⟩ := e_transc hord he hb hsum
  -- every monomial has the same value on both sides, because `v d = v e`
  have hveq : ∀ i : ℕ, v (b i * e ^ i) = v (b i * d ^ i) := by
    intro i
    rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hsame.1]
  -- the dominant monomial on the `e` side
  have hde : SameRV v (∑ i ∈ Finset.range (m + 1), (b i * e ^ i)) (b j * e ^ j) := by
    refine sameRV_vfSum_dominant hjm hbj he ?_
    intro i him hij
    by_cases hbi : b i = 0
    · rw [hbi, zero_mul, Valuation.map_zero]
      exact zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (mul_ne_zero hbj (pow_ne_zero j he)))
    · exact lt_of_le_of_ne (hle i him hbi)
        (v_mul_pow_ne' hord he hij (hb i him) (hb j hjm) hbi hbj)
  -- the same index dominates on the `d` side
  have hdd : SameRV v (∑ i ∈ Finset.range (m + 1), (b i * d ^ i)) (b j * d ^ j) := by
    refine sameRV_vfSum_dominant hjm hbj hd0 ?_
    intro i him hij
    rw [← hveq i, ← hveq j]
    by_cases hbi : b i = 0
    · rw [hbi, zero_mul, Valuation.map_zero]
      exact zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (mul_ne_zero hbj (pow_ne_zero j he)))
    · exact lt_of_le_of_ne (hle i him hbi)
        (v_mul_pow_ne' hord he hij (hb i him) (hb j hjm) hbi hbj)
  -- corresponding monomials have the same class, since `rv` is multiplicative
  have hmono : SameRV v (b j * e ^ j) (b j * d ^ j) :=
    SameRV.mul (sameRV_refl v hbj) (SameRV.pow hsame j)
  exact SameRV.trans hde (SameRV.trans hmono (SameRV.symm hdd))


/-- **Inverses preserve `RV`-classes.** -/
theorem SameRV.inv {v : Valuation L Γ₀} {x y : L} (h : SameRV v x y) : SameRV v x⁻¹ y⁻¹ := by
  have hx0 : x ≠ 0 := SameRV.ne_zero_left h
  have hy0 : y ≠ 0 := SameRV.ne_zero_right h
  have hu : x⁻¹ * y⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hx0) (inv_ne_zero hy0)
  have hm : SameRV v (x * (x⁻¹ * y⁻¹)) (y * (x⁻¹ * y⁻¹)) := SameRV.mul_right h hu
  have hx : x * (x⁻¹ * y⁻¹) = y⁻¹ := by field_simp
  have hy : y * (x⁻¹ * y⁻¹) = x⁻¹ := by field_simp
  rw [hx, hy] at hm
  exact SameRV.symm hm

/-- **Division is well defined on `RV`-classes.** -/
theorem SameRV.div {v : Valuation L Γ₀} {x y z w : L} (h1 : SameRV v x y)
    (h2 : SameRV v z w) : SameRV v (x / z) (y / w) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact SameRV.mul h1 (SameRV.inv h2)

/-! ## 4. The polynomial and field forms: `e ↦ d` is `RV`-preserving on `VF(Ŝ)(e)` -/

/-- `Polynomial.aeval` as the explicit expansion, uniformly in the point. -/
theorem aeval_eq_sum {K : Subfield L} (r : Polynomial ↥K) (x : L) :
    (Polynomial.aeval x) r =
      ∑ i ∈ Finset.range (r.natDegree + 1), (((r.coeff i : ↥K) : L) * x ^ i) := by
  rw [Polynomial.aeval_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]; rfl

/-- **Lemma 3.8 (`lift:value:full`), `RV` half, polynomial form.**  Under the hypotheses of
`sameRV_vfSum` (with `e` transcendental, so that `0 ≠ r ∈ K[X]` gives `b(e) ≠ 0`), the classes of
`b(e)` and `b(d)` agree for every nonzero `b ∈ K[X]`. -/
theorem sameRV_aeval {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hord : InfiniteOrderMod v e K) (he : e ≠ 0) (hsame : SameRV v e d)
    (htrans : Transcendental ↥K e) {r : Polynomial ↥K} (hr : r ≠ 0) :
    SameRV v ((Polynomial.aeval e) r) ((Polynomial.aeval d) r) := by
  classical
  have hsum : ∑ i ∈ Finset.range (r.natDegree + 1), (((r.coeff i : ↥K) : L) * e ^ i) ≠ 0 := by
    intro h
    apply hr
    refine (transcendental_iff.mp htrans) r ?_
    rw [aeval_eq_sum (K := K) r e, h]
  have h := sameRV_vfSum (v := v) hord he hsame (m := r.natDegree)
    (b := fun i => ((r.coeff i : ↥K) : L)) (fun i _ => (r.coeff i).2) hsum
  rw [aeval_eq_sum (K := K) r e, aeval_eq_sum (K := K) r d]
  exact h

/-- The value projection of `sameRV_aeval`: this is Yin's Lemma 3.8 computation
`vv(b) = vv(b*)`, here with `d` given by `rv(d) = rv(e)` instead of a separate transfer
isomorphism (`YinLemma37.value_transfer_sum`). -/
theorem value_transfer_rv {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hord : InfiniteOrderMod v e K) (he : e ≠ 0) (hsame : SameRV v e d)
    (htrans : Transcendental ↥K e) {r : Polynomial ↥K} (hr : r ≠ 0) :
    v ((Polynomial.aeval e) r) = v ((Polynomial.aeval d) r) :=
  (sameRV_aeval hord he hsame htrans hr).1

/-- **`e ↦ d` is `RV`-preserving on the whole of `VF(Ŝ)(e)`.**  This is the statement that makes
`e ↦ d` an `L_RV`-monomorphism after Remark 3.1: the assignment
`b(e)/c(e) ↦ b(d)/c(d)` preserves values *and* residues everywhere, so it induces an isomorphism
of the residue fields and an isomorphism `RV(VF(Ŝ)(e)) → RV(VF(Ŝ)(d))`.  Yin's claim (⋆) at the
element `e` is exactly this with `f` supplied by the identification `VF(Ŝ) ≅ f(VF(Ŝ))`. -/
theorem sameRV_aeval_div {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hord : InfiniteOrderMod v e K) (he : e ≠ 0) (hsame : SameRV v e d)
    (htrans : Transcendental ↥K e) (htransd : Transcendental ↥K d)
    {p q : Polynomial ↥K} (hp : p ≠ 0) (hq : q ≠ 0) :
    SameRV v ((Polynomial.aeval e) p / (Polynomial.aeval e) q)
      ((Polynomial.aeval d) p / (Polynomial.aeval d) q) := by
  have hd0 : d ≠ 0 := SameRV.ne_zero_right hsame
  have hordd : InfiniteOrderMod v d K := infiniteOrderMod_of_sameRV hord hsame
  refine SameRV.div (sameRV_aeval hord he hsame htrans hp) ?_
  exact SameRV.symm (sameRV_aeval (e := d) (d := e) hordd hd0 (SameRV.symm hsame) htransd hq)

/-! ## 5. Claim (⋆), second half: `RV(⟨Ŝ, e⟩) = ⟨RV(Ŝ), rv(e)⟩` -/

/-- **A polynomial expansion has the `RV`-class of its dominant monomial.**  The `rv`-level form of
`YinLemma37.e_transc_aeval`; this is the paper's `rv (∑ bᵢeⁱ) = rv (bⱼeʲ)`. -/
theorem exists_sameRV_aeval_dominant {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    (hord : InfiniteOrderMod v e K) (he : e ≠ 0) (htrans : Transcendental ↥K e)
    {r : Polynomial ↥K} (hr : r ≠ 0) :
    ∃ j, r.coeff j ≠ 0 ∧
      SameRV v ((Polynomial.aeval e) r) (((r.coeff j : ↥K) : L) * e ^ j) := by
  classical
  have hsum : ∑ i ∈ Finset.range (r.natDegree + 1), (((r.coeff i : ↥K) : L) * e ^ i) ≠ 0 := by
    intro h
    apply hr
    refine (transcendental_iff.mp htrans) r ?_
    rw [aeval_eq_sum (K := K) r e, h]
  obtain ⟨j, hjm, hbj, _hval, hle⟩ :=
    e_transc hord he (fun i _ => (r.coeff i).2) hsum
  refine ⟨j, fun h => hbj (by simp [h]), ?_⟩
  have hd : SameRV v (∑ i ∈ Finset.range (r.natDegree + 1), (((r.coeff i : ↥K) : L) * e ^ i))
      (((r.coeff j : ↥K) : L) * e ^ j) := by
    refine sameRV_vfSum_dominant hjm hbj he ?_
    intro i him hij
    by_cases hbi : ((r.coeff i : ↥K) : L) = 0
    · rw [hbi, zero_mul, Valuation.map_zero]
      exact zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (mul_ne_zero hbj (pow_ne_zero j he)))
    · exact lt_of_le_of_ne (hle i him hbi)
        (v_mul_pow_ne' hord he hij (r.coeff i).2 (r.coeff j).2 hbi hbj)
  rw [aeval_eq_sum (K := K) r e]
  exact hd

/-- **Claim (⋆), second half, at the valuation level**: every `RV`-element of the field
`VF(Ŝ)(e)` is `rv(a)·rv(e)^n` with `a ∈ VF(Ŝ)`, `n ∈ ℤ` — i.e.
`RV(⟨Ŝ, e⟩) = ⟨RV(Ŝ), rv(e)⟩`.  This is `YinLemma37.value_mem_of_adjoin` upgraded from values to
`RV`-classes (the residue half, which is what a `Γ`-only computation cannot see). -/
theorem sameRV_mem_adjoin {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    (hord : InfiniteOrderMod v e K) (he : e ≠ 0) (htrans : Transcendental ↥K e)
    {x : L} (hx : x ∈ IntermediateField.adjoin ↥K {e}) (hx0 : x ≠ 0) :
    ∃ a : L, a ∈ K ∧ a ≠ 0 ∧ ∃ n : ℤ, SameRV v x (a * e ^ n) := by
  classical
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff ↥K x).mp hx
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero] at hrs
    exact hx0 hrs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hrs
    exact hx0 hrs
  obtain ⟨jr, hcr0, hrv⟩ := exists_sameRV_aeval_dominant hord he htrans hr0
  obtain ⟨js, hcs0, hsv⟩ := exists_sameRV_aeval_dominant hord he htrans hs0
  have hcr : ((r.coeff jr : ↥K) : L) ≠ 0 := fun h => hcr0 (Subtype.coe_injective (by simpa using h))
  have hcs : ((s.coeff js : ↥K) : L) ≠ 0 := fun h => hcs0 (Subtype.coe_injective (by simpa using h))
  have hdiv : SameRV v (((r.coeff jr : ↥K) : L) * e ^ jr / (((s.coeff js : ↥K) : L) * e ^ js))
      ((((r.coeff jr : ↥K) : L) / ((s.coeff js : ↥K) : L)) * e ^ ((jr : ℤ) - (js : ℤ))) := by
    rw [zpow_sub₀ he, zpow_natCast, zpow_natCast, div_mul_div_comm]
    exact sameRV_refl v (div_ne_zero (mul_ne_zero hcr (pow_ne_zero jr he))
      (mul_ne_zero hcs (pow_ne_zero js he)))
  have hquot : SameRV v (x) (((r.coeff jr : ↥K) : L) * e ^ jr /
      (((s.coeff js : ↥K) : L) * e ^ js)) := by
    have h := SameRV.div hrv hsv
    rwa [← hrs] at h
  refine ⟨((r.coeff jr : ↥K) : L) / ((s.coeff js : ↥K) : L),
    K.div_mem (r.coeff jr).2 (s.coeff js).2, div_ne_zero hcr hcs, (jr : ℤ) - (js : ℤ), ?_⟩
  exact SameRV.trans hquot hdiv

end YinLemma38

/-! ## Axiom audit -/

#print axioms YinLemma38.sameRV_vfSum
#print axioms YinLemma38.sameRV_aeval
#print axioms YinLemma38.sameRV_aeval_div
#print axioms YinLemma38.sameRV_mem_adjoin
#print axioms YinLemma38.sameRV_one_add
#print axioms YinLemma38.value_transfer_rv
