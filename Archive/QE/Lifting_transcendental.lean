/-
Copyright: none.  Ultramath swarm smw081ptp, member m2.

# Lemma 3.8 of arXiv:1006.1393 (Lemma 2.3 of arXiv:1006.2467), §3: `lift:value:full`

The paper proves QE for `ACVF` in `L_RV` by Shoenfield's test.  Lemma 3.8
(`lift:value:full`) is the step that handles an `e ∈ VF(M)` whose value generates a new part of
the value group: if `K(Ŝ) = K(M)` and `Γ(Ŝ)` is divisible, then the one-element extension
`Ŝ ⊆ ⟨Ŝ,e⟩` can be matched in the target.  Its proof uses Lemma 3.7 (`e:transc`, the
no-cancellation formula `vv(b) = min_i vv(b_i e^i)`) and the observation that the *leading index*
is the same on both sides, so the residues match too, making `e ↦ d` a valued field embedding.

This file formalises that algebraic content over `Mathlib`'s `Valuation K Γ₀`, with two frames
`F ⊆ K` and `F' ⊆ L` (`Algebra` instances) and a value-preserving isomorphism `σ : F ≃+* F'`:

* `infiniteOrderMod_of_divisible` — `Γ(F)` divisible and `v e ∉ Γ(F)` imply that `v e` has
  infinite order modulo `Γ(F)` (first line of the proof of Lemma 3.8);
* `value_eval₂` — the leading term formula (Lemma 3.7): the value of a polynomial is the
  supremum of the values of its terms, when `v e` has infinite order;
* `transcendental_of_infiniteOrderMod` — then `e` is transcendental over `F`;
* `exists_leading_index` — the index of the leading term is unique;
* `infiniteOrderMod_map` — the infinite order condition is transported to the target;
* `eval₂_value_eq` — `e ↦ d` preserves the values of all polynomials;
* `residue_relation_transfer` / `rv_relation_transfer` — it preserves the residue information,
  in the `L_v`-quantifier-free form `vv (x - c) > vv x` (Mathlib's multiplicative convention
  makes this `v (x - c) < v x`), for constants and for arbitrary pairs of elements of `F[e]`;
* `eval₂_div_value_eq` / `rv_relation_transfer_div` (`div_sub_lt_iff`) — the same two facts for
  *all* elements of `F(e)`, written as quotients `p(e)/q(e)`.  Together these say that
  `p(e)/q(e) ↦ p(d)/q(d)` matches the whole quantifier-free `L_v`-type of `F(e)`;
* `leading_index_transfer` — the leading index is the same on the two sides; hence `rv` of an
  element of `F[e]` is `rv` of its leading coefficient times `rv(e)^i`, matched on the target
  (this is `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩`);
* `lift_value_full` / `lift_value_full_of_divisible` — the bundle, in the paper's hypothesis
  shape (`Γ` divisible, `v e` outside the value group);
* `divHull` / `le_divHull` / `divHull_divisible` / `divHull_divisible_rat` / `divHull_le` and
  `nsmul_surjective_of_rat` — the group-theoretic core of Lemma 3.3: the internal divisible hull
  `{γ | n·γ ∈ Γ(S)}` of a subgroup of a divisible group is divisible, contains `Γ(S)`, and is
  contained in every divisible subgroup containing `Γ(S)` (`n`-th roots supply the target side),
  which is what makes the iterative construction of `S*` close up inside `Γ(M)`.

Not formalised here (it is the model-theoretic half of Lemma 3.8): the ambient structures
`S ⊆ M ⊨ ACVF`, saturation of `N`, the `L_v`/`L_RV` encoding, and the passage from an
`L_RV`-monomorphism to a valued field embedding.  Those belong to the reduction
(`Remark 3.1`, `Shoenfield's test`), not to this algebraic lemma.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace Ultramath.M2

open Polynomial

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ## 1. Values of infinite order -/

/-- `e` has value of infinite order modulo the value group of `F`: no positive power of `v e`
is the value of a nonzero element of `F`. -/
def InfiniteOrderMod (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K]
    (v : Valuation K Γ₀) (e : K) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a : F, a ≠ 0 → v e ^ n ≠ v (algebraMap F K a)

/-- The value of `e` does not lie in the value group of `F`. -/
def NotInValueGroup (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K]
    (v : Valuation K Γ₀) (e : K) : Prop :=
  ∀ a : F, a ≠ 0 → v e ≠ v (algebraMap F K a)

/-- The value group of `F` is divisible: every value of a nonzero element of `F` has `n`-th
roots in the value group of `F`. -/
def ValueGroupDivisible (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K]
    (v : Valuation K Γ₀) : Prop :=
  ∀ (a : F), a ≠ 0 → ∀ (n : ℕ), 0 < n →
    ∃ b : F, b ≠ 0 ∧ v (algebraMap F K b) ^ n = v (algebraMap F K a)

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
variable {F' : Type*} [Field F'] {L : Type*} [Field L] [Algebra F' L]

/-- A nonzero element of the base field has nonzero value. -/
theorem val_algebraMap_ne_zero (v : Valuation K Γ₀) {a : F} (ha : a ≠ 0) :
    v (algebraMap F K a) ≠ 0 := by
  intro h
  have h0 : algebraMap F K a = 0 := (Valuation.zero_iff v).mp h
  have h1 : (1 : K) = 0 := by
    rw [← map_one (algebraMap F K), ← mul_inv_cancel₀ ha, map_mul, h0, zero_mul]
  exact one_ne_zero h1

/-- A nonzero element of the field has nonzero value. -/
theorem val_ne_zero_of_ne_zero (v : Valuation K Γ₀) {e : K} (he : e ≠ 0) : v e ≠ 0 := by
  intro h
  exact he ((Valuation.zero_iff v).mp h)

/-- If the value group of `F` is divisible, then an element whose value is outside it has value
of infinite order modulo it.  This is the first line of the proof of Lemma 3.8
(`lift:value:full`): `Γ(Ŝ)` divisible forces `vv(e)` to have infinite order mod `Γ(Ŝ)`. -/
theorem infiniteOrderMod_of_divisible (v : Valuation K Γ₀) (e : K)
    (hdiv : ValueGroupDivisible F v) (hnot : NotInValueGroup F v e) :
    InfiniteOrderMod F v e := by
  intro n hn a ha h
  obtain ⟨b, hb, hbn⟩ := hdiv a ha n hn
  have h' : v e ^ n = v (algebraMap F K b) ^ n := by rw [h, hbn]
  have hne : v e ≠ v (algebraMap F K b) := hnot b hb
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := pow_lt_pow_left₀ hlt (zero_le : (0 : Γ₀) ≤ v e) hn.ne'
    rw [h'] at this
    exact lt_irrefl _ this
  · have := pow_lt_pow_left₀ hlt (zero_le : (0 : Γ₀) ≤ v (algebraMap F K b)) hn.ne'
    rw [h'] at this
    exact lt_irrefl _ this

/-! ## 2. Distinct monomials have distinct values -/

/-- Distinct monomials of the form `(algebraMap a) * e ^ i` with nonzero coefficients have
distinct values, when `v e` has infinite order modulo the value group of `F` and `e ≠ 0`. -/
theorem val_mul_pow_ne (v : Valuation K Γ₀) {e : K} (he : InfiniteOrderMod F v e)
    (he0 : e ≠ 0) {i j : ℕ} (hij : i ≠ j) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    v (algebraMap F K a * e ^ i) ≠ v (algebraMap F K b * e ^ j) := by
  rintro h
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow] at h
  have hve : v e ≠ 0 := val_ne_zero_of_ne_zero v he0
  have hvb : v (algebraMap F K b) ≠ 0 := val_algebraMap_ne_zero v hb
  have hva : v (algebraMap F K a) ≠ 0 := val_algebraMap_ne_zero v ha
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · have hpos : 0 < j - i := Nat.sub_pos_of_lt hij'
    have hpowe : (v e) ^ i ≠ 0 := pow_ne_zero i hve
    have h1 : v (algebraMap F K a) * (v e) ^ i
        = (v (algebraMap F K b) * (v e) ^ (j - i)) * (v e) ^ i := by
      rw [mul_assoc, ← pow_add, show j - i + i = j from by omega]
      exact h
    have h2 : v (algebraMap F K a) = v (algebraMap F K b) * (v e) ^ (j - i) :=
      mul_right_cancel₀ hpowe h1
    have h3 : (v e) ^ (j - i) * v (algebraMap F K b) = v (algebraMap F K a) := by
      rw [h2, mul_comm]
    have h4 : v (algebraMap F K (a / b)) * v (algebraMap F K b) = v (algebraMap F K a) := by
      rw [← Valuation.map_mul, ← map_mul (algebraMap F K), div_mul_cancel₀ a hb]
    have h5 : (v e) ^ (j - i) = v (algebraMap F K (a / b)) :=
      mul_right_cancel₀ hvb (h3.trans h4.symm)
    exact he (j - i) hpos (a / b) (div_ne_zero ha hb) h5
  · have hpos : 0 < i - j := Nat.sub_pos_of_lt hij'
    have hpowe : (v e) ^ j ≠ 0 := pow_ne_zero j hve
    have h1 : (v (algebraMap F K a) * (v e) ^ (i - j)) * (v e) ^ j
        = v (algebraMap F K b) * (v e) ^ j := by
      rw [mul_assoc, ← pow_add, show (i - j) + j = i from by omega]
      exact h
    have h2 : v (algebraMap F K a) * (v e) ^ (i - j) = v (algebraMap F K b) :=
      mul_right_cancel₀ hpowe h1
    have h3 : (v e) ^ (i - j) * v (algebraMap F K a) = v (algebraMap F K b) := by
      rw [mul_comm ((v e) ^ (i - j)) (v (algebraMap F K a)), h2]
    have h4 : v (algebraMap F K (b / a)) * v (algebraMap F K a) = v (algebraMap F K b) := by
      rw [← Valuation.map_mul, ← map_mul (algebraMap F K), div_mul_cancel₀ b ha]
    have h5 : (v e) ^ (i - j) = v (algebraMap F K (b / a)) :=
      mul_right_cancel₀ hva (h3.trans h4.symm)
    exact he (i - j) hpos (b / a) (div_ne_zero hb ha) h5

/-- The infinite order condition is transported to the target: `w d = v e` and `σ` value
preserving force `w d` to have infinite order modulo the value group of `F'`. -/
theorem infiniteOrderMod_map (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (hev : InfiniteOrderMod F v e) : InfiniteOrderMod F' w d := by
  intro n hn a' ha'
  have ha : σ.symm a' ≠ 0 := fun h0 => ha' (by rw [← σ.apply_symm_apply a', h0, map_zero])
  have h2 : w (algebraMap F' L a') = v (algebraMap F K (σ.symm a')) := by
    conv_lhs => rw [← σ.apply_symm_apply a']
    rw [← hσ (σ.symm a')]
  rw [hd, h2]
  exact hev n hn (σ.symm a') ha

/-! ## 3. The leading term formula (Lemma 3.7, `e:transc`) -/

/-- The supremum of the values of the terms of `p`. -/
def termSup (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K]
    (v : Valuation K Γ₀) (e : K) (p : Polynomial F) : Γ₀ :=
  p.support.sup fun i => v (algebraMap F K (p.coeff i) * e ^ i)

/-- **The leading term formula** (Lemma 3.7 of arXiv:1006.1393, `e:transc`): if `v e` has
infinite order modulo the value group of `F`, then the value of a polynomial is the supremum
of the values of its terms — there is no cancellation. -/
theorem value_eval₂ (v : Valuation K Γ₀) {e : K} (he : InfiniteOrderMod F v e)
    (he0 : e ≠ 0) (p : Polynomial F) :
    v (p.eval₂ (algebraMap F K) e) = termSup F v e p := by
  rcases eq_or_ne p 0 with hp | hp
  · subst hp
    simp only [eval₂_zero, map_zero, termSup, support_zero, Finset.sup_empty]
    exact bot_eq_zero.symm
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  obtain ⟨j, hjs, hjmax⟩ := Finset.exists_max_image p.support
    (fun i => v (algebraMap F K (p.coeff i) * e ^ i)) hne
  have hlt : ∀ i ∈ p.support \ {j},
      v (algebraMap F K (p.coeff i) * e ^ i) < v (algebraMap F K (p.coeff j) * e ^ j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    obtain ⟨his, hij⟩ := hi
    exact lt_of_le_of_ne (hjmax i his)
      (val_mul_pow_ne v he he0 hij (Polynomial.mem_support_iff.mp his)
        (Polynomial.mem_support_iff.mp hjs))
  have hsup : termSup F v e p = v (algebraMap F K (p.coeff j) * e ^ j) := by
    rw [termSup]
    refine le_antisymm ?_ (Finset.le_sup (f := fun i => v (algebraMap F K (p.coeff i) * e ^ i)) hjs)
    rw [Finset.sup_le_iff]
    exact fun i hi => hjmax i hi
  rw [eval₂_eq_sum, Polynomial.sum_def, Valuation.map_sum_eq_of_lt v hjs hlt, hsup]

/-- **`e` is transcendental over `F`** when its value has infinite order modulo the value
group of `F`.  (In Lemma 3.8 this is the observation that `e ∉ 𝒪` forces `e` transcendental.) -/
theorem transcendental_of_infiniteOrderMod (v : Valuation K Γ₀) {e : K}
    (he : InfiniteOrderMod F v e) (he0 : e ≠ 0) {p : Polynomial F} (hp : p ≠ 0) :
    p.eval₂ (algebraMap F K) e ≠ 0 := by
  intro h0
  have hv : v (p.eval₂ (algebraMap F K) e) = 0 := by rw [h0, map_zero]
  rw [value_eval₂ v he he0 p] at hv
  obtain ⟨j, hjs, -⟩ := Finset.exists_max_image p.support
    (fun i => v (algebraMap F K (p.coeff i) * e ^ i)) (Polynomial.support_nonempty.mpr hp)
  have hle : v (algebraMap F K (p.coeff j) * e ^ j) ≤ termSup F v e p :=
    Finset.le_sup (f := fun i => v (algebraMap F K (p.coeff i) * e ^ i)) hjs
  rw [hv] at hle
  have hne : v (algebraMap F K (p.coeff j) * e ^ j) ≠ 0 := by
    rw [Valuation.map_mul, Valuation.map_pow]
    exact mul_ne_zero (val_algebraMap_ne_zero v (Polynomial.mem_support_iff.mp hjs))
      (pow_ne_zero _ (val_ne_zero_of_ne_zero v he0))
  exact hne (le_antisymm hle (zero_le : (0 : Γ₀) ≤ v (algebraMap F K (p.coeff j) * e ^ j)))


/-! ## 4. The one-element extension: value and residue transport -/

/-- Corresponding monomials have the same value: the coefficient map `σ` is value preserving
and `d` matches `e` in value. -/
theorem term_value_eq (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (a : F) (i : ℕ) :
    v (algebraMap F K a * e ^ i) = w (algebraMap F' L (σ a) * d ^ i) := by
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hσ a, hd]

/-- The supremum of the values of the terms is transported by the coefficient map. -/
theorem termSup_map (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (p : Polynomial F) :
    termSup F v e p = termSup F' w d (p.map σ.toRingHom) := by
  rw [termSup, termSup, Polynomial.support_map_of_injective p σ.injective]
  refine Finset.sup_congr rfl ?_
  intro i _
  rw [Polynomial.coeff_map]
  exact term_value_eq v w σ hσ hd (p.coeff i) i

/-- **The value half of Lemma 3.8 (`lift:value:full`).**  Let `σ : F ≃+* F'` be an
isomorphism of valued fields (`v (a) = w (σ a)`), let `v e` have infinite order modulo the
value group of `F`, and let `d` be an element of the target with `w d = v e`.  Then every
polynomial in `e` with coefficients in `F` takes, after transporting its coefficients by `σ`
and substituting `d`, the same value. -/
theorem eval₂_value_eq (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (hev : InfiniteOrderMod F v e) (he0 : e ≠ 0) (p : Polynomial F) :
    v (p.eval₂ (algebraMap F K) e) = w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d) := by
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 : w d = 0 := by rw [h0, map_zero]
    rw [hd] at h1
    exact val_ne_zero_of_ne_zero v he0 h1
  have hdv : InfiniteOrderMod F' w d := infiniteOrderMod_map v w σ hσ hd hev
  rw [value_eval₂ v hev he0 p, value_eval₂ w hdv hd0 (p.map σ.toRingHom),
    termSup_map v w σ hσ hd p]

/-- Comparing values is transported as well: no polynomial inequality is lost. -/
theorem value_lt_transfer (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (hev : InfiniteOrderMod F v e) (he0 : e ≠ 0) (r p : Polynomial F) :
    (v (r.eval₂ (algebraMap F K) e) < v (p.eval₂ (algebraMap F K) e)) ↔
      (w ((r.map σ.toRingHom).eval₂ (algebraMap F' L) d) <
        w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d)) := by
  rw [eval₂_value_eq v w σ hσ hd hev he0 r,
    eval₂_value_eq v w σ hσ hd hev he0 p]

/-- **The residue half of Lemma 3.8 (`lift:value:full`), in the language `L_v`.**  The residue
information `res x = res c` is expressed in `L_v` by the quantifier-free formula
`vv (x - c) < vv x`; the lemma says this relation is preserved by the assignment `e ↦ d`.
Hence the one-element extension matches all quantifier-free `L_v`-data of `F(e)`. -/
theorem residue_relation_transfer (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (hev : InfiniteOrderMod F v e) (he0 : e ≠ 0) (p q : Polynomial F) (a : F) :
    (v (p.eval₂ (algebraMap F K) e - algebraMap F K a * q.eval₂ (algebraMap F K) e)
        < v (p.eval₂ (algebraMap F K) e)) ↔
      (w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d -
            algebraMap F' L (σ a) * (q.map σ.toRingHom).eval₂ (algebraMap F' L) d)
          < w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d)) := by
  have h1 : (p - Polynomial.C a * q).eval₂ (algebraMap F K) e
      = p.eval₂ (algebraMap F K) e - algebraMap F K a * q.eval₂ (algebraMap F K) e := by
    rw [eval₂_sub, eval₂_mul, eval₂_C]
  have h1' : ((p - Polynomial.C a * q).map σ.toRingHom).eval₂ (algebraMap F' L) d
      = (p.map σ.toRingHom).eval₂ (algebraMap F' L) d -
        algebraMap F' L (σ a) * (q.map σ.toRingHom).eval₂ (algebraMap F' L) d := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, eval₂_sub, eval₂_mul,
      eval₂_C]
    rfl
  rw [← h1, ← h1']
  exact value_lt_transfer v w σ hσ hd hev he0 _ _

/-- **`RV`-equality of two elements of `F[e]` is preserved.**  For `x, y` in a valued field,
`v (x - y) < v x` is exactly `rv x = rv y` (same leading term).  The lemma says that this
relation holds for a pair of polynomials in `e` if and only if it holds for the transported pair
in `d`: the assignment `e ↦ d` is an isomorphism of the `RV`-structure of `F[e]` onto that of
`F'[d]`.  This is the precise content of `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩` at the level of
`L_v`-quantifier-free data. -/
theorem rv_relation_transfer (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (hev : InfiniteOrderMod F v e) (he0 : e ≠ 0) (p q : Polynomial F) :
    (v ((p - q).eval₂ (algebraMap F K) e) < v (p.eval₂ (algebraMap F K) e)) ↔
      (w (((p - q).map σ.toRingHom).eval₂ (algebraMap F' L) d)
        < w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d)) :=
  value_lt_transfer v w σ hσ hd hev he0 (p - q) p

/-- **The value of every element of `F(e)`.**  Every element of `F(e)` is `p(e)/q(e)`; the
assignment `e ↦ d` preserves its value.  (No side condition on `q`: the identity is also true
when `q(e) = 0`, both sides being `0`.) -/
theorem eval₂_div_value_eq (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (hev : InfiniteOrderMod F v e) (he0 : e ≠ 0)
    (p q : Polynomial F) :
    v (p.eval₂ (algebraMap F K) e / q.eval₂ (algebraMap F K) e)
      = w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d /
          (q.map σ.toRingHom).eval₂ (algebraMap F' L) d) := by
  rw [Valuation.map_div, Valuation.map_div, eval₂_value_eq v w σ hσ hd hev he0 p,
    eval₂_value_eq v w σ hσ hd hev he0 q]

/-- Clearing denominators: for a valued field, comparing `x / y` with `u / z` is comparing
`x * z` with `u * y`. -/
theorem div_sub_lt_iff (v : Valuation K Γ₀) {x y u z : K} (hy : y ≠ 0) (hz : z ≠ 0) :
    (v (x / y - u / z) < v (x / y)) ↔ (v (x * z - u * y) < v (x * z)) := by
  have hyz : y * z ≠ 0 := mul_ne_zero hy hz
  have hpos : (0 : Γ₀) < v (y * z) :=
    lt_of_le_of_ne zero_le (Ne.symm (val_ne_zero_of_ne_zero v hyz))
  have h1 : x / y - u / z = (x * z - u * y) / (y * z) := by
    field_simp
  have h2 : x / y = x * z / (y * z) := by
    field_simp
  rw [h1, h2, Valuation.map_div, Valuation.map_div, div_lt_div_iff_of_pos_right hpos]

/-- **The quantifier-free `L_v`-data of any two elements of `F(e)`** is preserved: for
`x = p/q` and `u = r/s` in `F(e)`, the relation `rv x = rv u`, written `v (x - u) < v x`, holds
after the assignment `e ↦ d` if and only if it holds before.  Together with
`eval₂_div_value_eq` this says the assignment `p(e)/q(e) ↦ p'(d)/q'(d)` matches the whole
quantifier-free `L_v`-type of `F(e)`. -/
theorem rv_relation_transfer_div (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (hev : InfiniteOrderMod F v e) (he0 : e ≠ 0)
    (p q r s : Polynomial F) (hq : q ≠ 0) (hs : s ≠ 0) :
    (v (p.eval₂ (algebraMap F K) e / q.eval₂ (algebraMap F K) e
          - r.eval₂ (algebraMap F K) e / s.eval₂ (algebraMap F K) e)
        < v (p.eval₂ (algebraMap F K) e / q.eval₂ (algebraMap F K) e)) ↔
      (w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d /
              (q.map σ.toRingHom).eval₂ (algebraMap F' L) d
            - (r.map σ.toRingHom).eval₂ (algebraMap F' L) d /
              (s.map σ.toRingHom).eval₂ (algebraMap F' L) d)
          < w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d /
              (q.map σ.toRingHom).eval₂ (algebraMap F' L) d)) := by
  have hdv : InfiniteOrderMod F' w d := infiniteOrderMod_map v w σ hσ hd hev
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 : w d = 0 := by rw [h0, map_zero]
    rw [hd] at h1
    exact val_ne_zero_of_ne_zero v he0 h1
  have hqK : q.eval₂ (algebraMap F K) e ≠ 0 := transcendental_of_infiniteOrderMod v hev he0 hq
  have hsK : s.eval₂ (algebraMap F K) e ≠ 0 := transcendental_of_infiniteOrderMod v hev he0 hs
  have hqL : (q.map σ.toRingHom).eval₂ (algebraMap F' L) d ≠ 0 :=
    transcendental_of_infiniteOrderMod w hdv hd0 ((Polynomial.map_ne_zero_iff σ.injective).mpr hq)
  have hsL : (s.map σ.toRingHom).eval₂ (algebraMap F' L) d ≠ 0 :=
    transcendental_of_infiniteOrderMod w hdv hd0 ((Polynomial.map_ne_zero_iff σ.injective).mpr hs)
  have e1 : ((p * s - r * q).eval₂ (algebraMap F K) e)
      = p.eval₂ (algebraMap F K) e * s.eval₂ (algebraMap F K) e
        - r.eval₂ (algebraMap F K) e * q.eval₂ (algebraMap F K) e := by
    rw [eval₂_sub, eval₂_mul, eval₂_mul]
  have e2 : ((p * s).eval₂ (algebraMap F K) e)
      = p.eval₂ (algebraMap F K) e * s.eval₂ (algebraMap F K) e := by
    rw [eval₂_mul]
  have e1' : (((p * s - r * q).map σ.toRingHom).eval₂ (algebraMap F' L) d)
      = (p.map σ.toRingHom).eval₂ (algebraMap F' L) d *
          (s.map σ.toRingHom).eval₂ (algebraMap F' L) d
        - (r.map σ.toRingHom).eval₂ (algebraMap F' L) d *
          (q.map σ.toRingHom).eval₂ (algebraMap F' L) d := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, eval₂_sub, eval₂_mul,
      eval₂_mul]
  have e2' : (((p * s).map σ.toRingHom).eval₂ (algebraMap F' L) d)
      = (p.map σ.toRingHom).eval₂ (algebraMap F' L) d *
        (s.map σ.toRingHom).eval₂ (algebraMap F' L) d := by
    rw [Polynomial.map_mul, eval₂_mul]
  have stepv := div_sub_lt_iff (x := p.eval₂ (algebraMap F K) e)
    (u := r.eval₂ (algebraMap F K) e) v hqK hsK
  have stepw := div_sub_lt_iff (x := (p.map σ.toRingHom).eval₂ (algebraMap F' L) d)
    (u := (r.map σ.toRingHom).eval₂ (algebraMap F' L) d) w hqL hsL
  have key := rv_relation_transfer v w σ hσ hd hev he0 (p * s) (r * q)
  rw [e1, e2, e1', e2'] at key
  exact stepv.trans (key.trans stepw.symm)

/-- **Lemma 3.8 (`lift:value:full`), algebraic content.**  Bundles: equal values of all
polynomials (`eval₂_value_eq`), preservation of the residue (`L_v`-quantifier-free) relation
(`residue_relation_transfer`), and transcendence of `e` over `F`. -/
theorem lift_value_full (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (hev : InfiniteOrderMod F v e) (he0 : e ≠ 0) :
    (∀ p : Polynomial F,
        v (p.eval₂ (algebraMap F K) e) = w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d)) ∧
    (∀ (p q : Polynomial F) (a : F),
        (v (p.eval₂ (algebraMap F K) e - algebraMap F K a * q.eval₂ (algebraMap F K) e)
            < v (p.eval₂ (algebraMap F K) e)) ↔
          (w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d -
                algebraMap F' L (σ a) * (q.map σ.toRingHom).eval₂ (algebraMap F' L) d)
              < w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d))) ∧
    (∀ p : Polynomial F, p ≠ 0 → p.eval₂ (algebraMap F K) e ≠ 0) :=
  ⟨fun p => eval₂_value_eq v w σ hσ hd hev he0 p,
   fun p q a => residue_relation_transfer v w σ hσ hd hev he0 p q a,
   fun _ hp => transcendental_of_infiniteOrderMod v hev he0 hp⟩


/-- **Lemma 3.8 (`lift:value:full`) with the paper's hypotheses.**  If the value groups of
both sides are divisible (`Γ(Ŝ)` divisible, and the divisibility of `Γ(N)`), and `v e` lies
outside the value group of `F`, then `e ↦ d` matches the value and remainder data.  This is the
form in which the paper applies Lemma 3.8: divisibility of `Γ(Ŝ)` gives the infinite order
condition (`infiniteOrderMod_of_divisible`) and everything else is `lift_value_full`. -/
theorem lift_value_full_of_divisible (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) (he0 : e ≠ 0)
    (hdiv : ValueGroupDivisible F v) (hnot : NotInValueGroup F v e) :
    (∀ p : Polynomial F,
        v (p.eval₂ (algebraMap F K) e) = w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d)) ∧
    (∀ (p q : Polynomial F) (a : F),
        (v (p.eval₂ (algebraMap F K) e - algebraMap F K a * q.eval₂ (algebraMap F K) e)
            < v (p.eval₂ (algebraMap F K) e)) ↔
          (w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d -
                algebraMap F' L (σ a) * (q.map σ.toRingHom).eval₂ (algebraMap F' L) d)
              < w ((p.map σ.toRingHom).eval₂ (algebraMap F' L) d))) ∧
    (∀ p : Polynomial F, p ≠ 0 → p.eval₂ (algebraMap F K) e ≠ 0) :=
  lift_value_full v w σ hσ hd (infiniteOrderMod_of_divisible v e hdiv hnot) he0

/-- Normalisation lemma: the ring hom underlying a ring equivalence is the equivalence itself. -/
theorem ringEquiv_toRingHom_apply {F' : Type*} [Field F'] (σ : F ≃+* F') (a : F) :
    σ.toRingHom a = σ a := rfl

/-! ## 5. The leading index is well defined and transferred -/

/-- The leading term of a polynomial in `e`: there is an index at which the maximum value of
the terms is attained, and that index is unique.  This is what makes `rv` of `p(e)` a product
`rv (leading coefficient) * rv(e)^i`. -/
theorem exists_leading_index (v : Valuation K Γ₀) {e : K} (he : InfiniteOrderMod F v e)
    (he0 : e ≠ 0) {p : Polynomial F} (hp : p ≠ 0) :
    ∃ i ∈ p.support, ∀ j ∈ p.support, j ≠ i →
      v (algebraMap F K (p.coeff j) * e ^ j) < v (algebraMap F K (p.coeff i) * e ^ i) := by
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image p.support
    (fun i => v (algebraMap F K (p.coeff i) * e ^ i)) (Polynomial.support_nonempty.mpr hp)
  refine ⟨i, hi, fun j hj hji => lt_of_le_of_ne (himax j hj) ?_⟩
  exact fun h => absurd h (val_mul_pow_ne v he he0 hji (Polynomial.mem_support_iff.mp hj)
    (Polynomial.mem_support_iff.mp hi))

/-- **The `RV` content of Lemma 3.8.**  The leading index of a polynomial in `e` is the same
index for the transported polynomial in `d`.  Hence `rv (p(e))` is `rv` of the leading
coefficient times `rv(e)^i`, and it is matched by `rv (p'(d)) = rv(σ leading coefficient) *
rv(d)^i` with the same `i` — i.e. `RV(⟨Ŝ,e⟩)` is generated over `RV(Ŝ)` by `rv(e)`. -/
theorem leading_index_transfer (v : Valuation K Γ₀) (w : Valuation L Γ₀) (σ : F ≃+* F')
    {e : K} {d : L} (hσ : ∀ a : F, v (algebraMap F K a) = w (algebraMap F' L (σ a)))
    (hd : w d = v e) {p : Polynomial F} {i : ℕ} (hi : i ∈ p.support)
    (himax : ∀ j ∈ p.support, j ≠ i →
      v (algebraMap F K (p.coeff j) * e ^ j) < v (algebraMap F K (p.coeff i) * e ^ i)) :
    i ∈ (p.map σ.toRingHom).support ∧
      ∀ j ∈ (p.map σ.toRingHom).support, j ≠ i →
        w (algebraMap F' L ((p.map σ.toRingHom).coeff j) * d ^ j)
          < w (algebraMap F' L ((p.map σ.toRingHom).coeff i) * d ^ i) := by
  have hsupp : (p.map σ.toRingHom).support = p.support :=
    Polynomial.support_map_of_injective p σ.injective
  refine ⟨hsupp ▸ hi, ?_⟩
  intro j hj hji
  rw [hsupp] at hj
  rw [Polynomial.coeff_map, Polynomial.coeff_map, ringEquiv_toRingHom_apply,
    ringEquiv_toRingHom_apply, ← term_value_eq v w σ hσ hd (p.coeff j) j,
    ← term_value_eq v w σ hσ hd (p.coeff i) i]
  exact himax j hj hji

/-! ## 6. Lemma 3.3 (`S*`): the divisible hull of the value group

Lemma 3.3 builds an intermediate structure `S*` with `VF(S*) = VF(S)`, `K(S*) = K(M)` and
`Γ(S*)` the divisible hull of `Γ(S)`.  Only the group-theoretic core is formalised here: the
divisible hull `{γ | n·γ ∈ Γ(S) for some n > 0}` of a subgroup of a divisible ordered abelian
group is itself divisible, so the iterative construction of Lemma 3.3 (adjoining one `n`-th
root at a time) closes up inside `Γ(M)`.
-/

/-- The divisible hull of a subgroup of an abelian group. -/
def divHull {G : Type*} [AddCommGroup G] (S : AddSubgroup G) : AddSubgroup G where
  carrier := {g | ∃ n : ℕ, 0 < n ∧ n • g ∈ S}
  zero_mem' := ⟨1, Nat.one_pos, by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm, hma⟩ ⟨n, hn, hnb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have e1 : (m * n) • a = n • (m • a) := by rw [mul_comm m n, ← smul_smul]
    have e2 : (m * n) • b = m • (n • b) := by rw [← smul_smul]
    have h1 : (m * n) • (a + b) = n • (m • a) + m • (n • b) := by rw [smul_add, e1, e2]
    rw [h1]
    exact S.add_mem (S.nsmul_mem hma n) (S.nsmul_mem hnb m)
  neg_mem' := by
    rintro a ⟨m, hm, hma⟩
    exact ⟨m, hm, by rw [smul_neg]; exact S.neg_mem hma⟩

/-- **The group-theoretic content of Lemma 3.3**: in a group where every element has `n`-th
roots, the divisible hull of a subgroup is divisible. -/
theorem divHull_divisible {G : Type*} [AddCommGroup G]
    (hdiv : ∀ (g : G) (n : ℕ), 0 < n → ∃ h : G, n • h = g) (S : AddSubgroup G) :
    ∀ g ∈ divHull S, ∀ n : ℕ, 0 < n → ∃ h ∈ divHull S, n • h = g := by
  rintro g ⟨m, hm, hmg⟩ n hn
  obtain ⟨h, hh⟩ := hdiv g n hn
  refine ⟨h, ⟨m * n, Nat.mul_pos hm hn, ?_⟩, hh⟩
  have h1 : (m * n) • h = m • g := by rw [← smul_smul, hh]
  rw [h1]
  exact hmg

/-- In a group that is a `ℚ`-vector space every element has `n`-th roots: the divisibility
used in Lemma 3.3 to find `r` with `rⁿ = f₁(tⁿ)`. -/
theorem nsmul_surjective_of_rat {G : Type*} [AddCommGroup G] [Module ℚ G]
    (n : ℕ) (hn : 0 < n) (g : G) : ∃ h : G, n • h = g := by
  refine ⟨((n : ℚ))⁻¹ • g, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'),
    one_smul]

/-- The divisible hull of a subgroup of a `ℚ`-vector space is divisible (Lemma 3.3's iteration
closes up). -/
theorem divHull_divisible_rat {G : Type*} [AddCommGroup G] [Module ℚ G] (S : AddSubgroup G) :
    ∀ g ∈ divHull S, ∀ n : ℕ, 0 < n → ∃ h ∈ divHull S, n • h = g :=
  divHull_divisible (fun g n hn => nsmul_surjective_of_rat n hn g) S

/-- `S` is contained in its divisible hull. -/
theorem le_divHull {G : Type*} [AddCommGroup G] (S : AddSubgroup G) : S ≤ divHull S := by
  intro x hx
  exact ⟨1, Nat.one_pos, by simpa using hx⟩

/-- **Universal property of the divisible hull**: any divisible subgroup containing `S` contains
the divisible hull of `S`.  With `le_divHull` and `divHull_divisible` this says that `divHull S`
is exactly the divisible hull of `S`. -/
theorem divHull_le {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]
    {S T : AddSubgroup G} (hST : S ≤ T)
    (hT : ∀ g ∈ T, ∀ n : ℕ, 0 < n → ∃ h ∈ T, n • h = g) : divHull S ≤ T := by
  rintro x ⟨n, hn, hnx⟩
  obtain ⟨h, hhT, hh⟩ := hT (n • x) (hST hnx) n hn
  have h0 : n • (h - x) = n • (0 : G) := by rw [smul_sub, hh, sub_self, smul_zero]
  have h1 : h - x = 0 := nsmul_right_injective hn.ne' h0
  have hx : h = x := sub_eq_zero.mp h1
  rwa [hx] at hhT

end Ultramath.M2

/-! ## Axiom check -/

#print axioms Ultramath.M2.infiniteOrderMod_of_divisible
#print axioms Ultramath.M2.val_mul_pow_ne
#print axioms Ultramath.M2.value_eval₂
#print axioms Ultramath.M2.transcendental_of_infiniteOrderMod
#print axioms Ultramath.M2.eval₂_value_eq
#print axioms Ultramath.M2.residue_relation_transfer
#print axioms Ultramath.M2.rv_relation_transfer
#print axioms Ultramath.M2.eval₂_div_value_eq
#print axioms Ultramath.M2.rv_relation_transfer_div
#print axioms Ultramath.M2.lift_value_full
#print axioms Ultramath.M2.lift_value_full_of_divisible
#print axioms Ultramath.M2.exists_leading_index
#print axioms Ultramath.M2.leading_index_transfer
#print axioms Ultramath.M2.divHull_divisible
#print axioms Ultramath.M2.nsmul_surjective_of_rat
#print axioms Ultramath.M2.divHull_divisible_rat
#print axioms Ultramath.M2.le_divHull
#print axioms Ultramath.M2.divHull_le
