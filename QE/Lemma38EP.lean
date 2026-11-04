/-
# Lemma 3.8 (`lift:value:full`) consumes no Engler–Prestel inequality

Member `m6`, swarm `smw2ox51x`, direction r6.

## The question

`MILESTONES.md` records a flagged, unverified discrepancy about Yin's Lemma 3.8:

> m1's report states "Lemma 3.8 does not consume EP 3.3.4/3.4.3; only 3.4 and 3.6 do", while
> `QE/Lemma38RV.lean:71`'s comment says the converse for 3.8's `vv(e) ∉ Γ(Ŝ)` step.

The paper's proof of Lemma 3.8 (`qe.tex`, l. 803) is: *"Since `Γ(Ŝ)` is divisible, clearly `vv(e)`
is of infinite order modulo `Γ(Ŝ)` and hence `e` is transcendental over `VF(Ŝ)`. Choose `d` with
`rv(d) = f(rv e)`. As above, by Lemma 3.7 and Remark 3.1, the embedding `e ↦ d` induces an
`L_RV`-monomorphism."*  It cites Lemma 3.7 only, and Lemma 3.7 cites PrRo84 Lemma 4.8.  The
*fundamental inequality* (EP 3.3.4) and the *dimension inequality* (EP 3.4.3) are cited in the
paper at Lemma 3.4 and at Lemma 3.6, **not** at Lemma 3.8.

The one step the tree did not have is the second clause:
`QE/Lemma37_transcendental.lean`'s header records

> Yin derives "`e` transcendental over `VF(Ŝ)`" […] using the dimension inequality of valuation
> theory (Engler–Prestel 3.4.3). That derivation […] [is] *not* formalized here: transcendence of
> `e` and of `d` are hypotheses.

So in the tree every Lemma 3.8 statement (`YinLemma38.sameRV_aeval`, `YinLemma38.sameRV_mem_adjoin`,
`YinLemma37.value_transfer`, `YinLemma38Case.lemma38_transfer`) carries
`Transcendental ↥K e` as a *hypothesis*, and `QE/Case38Value.lean` supplies it only from
`IsAlgClosedInL K` (`K(Ŝ) = K(M)`, i.e. an algebraically closed residue field).  That leaves open
whether Lemma 3.8's residual input is an EP-style inequality.

## The answer (machine-checked below)

**No.**  The missing step is elementary and needs *no* dimension inequality:

> `exists_pow_value_of_isAlgebraic` — if `0 ≠ e` is algebraic over `K`, then some positive power of
> `v e` is the value of a nonzero element of `K`.

Proof: `e` is a root of its minimal polynomial `p ∈ K[X]`, `p ≠ 0`, `natDeg p ≥ 1`.  Evaluate
`p(e) = ∑_{i ≤ d} cᵢ e^i = 0`.  If `v e^n` were never a `K`-value for `n > 0` (that is
`InfiniteOrderMod v e K`), then the nonzero monomials `cᵢ e^i` of the relation would have pairwise
*strictly* distinct values (`v_mul_pow_ne'`), and the sum of all but a strictly dominant term has
value strictly below the dominant one (`map_sum_lt`) — so `v (p(e)) = v (c_j e^j) ≠ 0 = v 0`,
contradiction.  This is the classical "the value group of a finite extension is generated up to
finite index by the value of any primitive element" argument in the only form Lemma 3.8 needs; it is
weaker than *both* EP inequalities (no residue degree, no defect, no rational rank).

Combined with the tree's `infiniteOrderMod_of_divisible` (`Γ(Ŝ)` divisible + `vv(e) ∉ Γ(Ŝ)` ⟹
infinite order, already proved) it gives the paper's "and hence `e` is transcendental over
`VF(Ŝ)`" as a theorem (`transcendental_of_divisible_of_notMem`), hence:

* `sameRV_aeval_of_divisible`, `sameRV_aeval_div_of_divisible`, `sameRV_mem_adjoin_of_divisible` —
  `QE/Lemma38RV.lean`'s `RV` half with **no** transcendence hypothesis;
* `value_transfer_of_divisible`, `lemma38_transfer_of_divisible` — `QE/Lemma37_transcendental.lean`'s
  value half and `QE/Case38Value.lean`'s `lemma38_transfer`-package with the *same* hypothesis list
  **minus** `IsAlgClosedInL` (so `K(Ŝ) = K(M)` is not needed either: only `Γ(Ŝ)` divisible and
  `vv(e) ∉ Γ(Ŝ)`, exactly the paper's two derivations);
* `lemma38_algebraic_content` — the three merged fragments (value half, residue half, `RV`
  generation) in one statement from the paper's case hypotheses.

§2 also discharges the *other* half of the paper's hypothesis `rv(e) ∈ RV(S) ∖ RV(Ŝ)`:
`hout_of_rv_notMem` derives `vv(e) ∉ Γ(Ŝ)` from `rv(e) ∉ RV(Ŝ)` using the residue-closure half of
`K(Ŝ) = K(M)` (`ResidueSurjective`), which is the only place `K(Ŝ) = K(M)` is really used in 3.8.
With that, `lemma38_of_rv_new` has as hypotheses only: `Γ(Ŝ)` divisible, `K(Ŝ)` residually closed in
`M`, `rv(e) ∉ RV(Ŝ)`, `rv(d) = rv(e)` (`SameRV v e d`) — the paper's own list.

## Stress tests (§4)

* `infiniteOrderMod_zero`: `InfiniteOrderMod v 0 K` — so `e ≠ 0` is essential in
  `transcendental_of_infiniteOrderMod` (`0` is algebraic and has infinite order).
* `upgrade_needs_divisibility`: the group-level shadow of why `Γ(Ŝ)`-divisibility cannot be dropped
  in `transcendental_of_divisible_of_notMem`: in `Multiplicative ℤ` with `H = ⟨2⟩` there is `g` with
  `g ^ 2 ∈ H` but `g ∉ H`; so `algebraic ⟹ ∃ n, v e ^ n ∈ Γ(Ŝ)` does **not** give `v e ∈ Γ(Ŝ)`
  without divisibility.  (An actual ramified valued-field instance would need
  `ℚ(√2)/ℚ` with the 2-adic place; the group skeleton is the whole mathematical content of the
  upgrade step, and it is what divisibility licenses.)
* `natDegree_pos`/`he` sharpness: `exists_pow_value_of_isAlgebraic` is used with `e ≠ 0`; at `e = 0`
  the conclusion fails (there is no `n` with `v 0 ^ n = v a ≠ 0`).
* Non-vacuity: `lemma38_instance` instantiates the whole hypothesis package (Γ divisible,
  `vv(e) ∉ Γ(Ŝ)`, `SameRV v e d`, `e ≠ d`) at `ℚ(X)` with the place at infinity and `K = ℚ`, and
  the theorem *produces* `Transcendental ℚ X` there — the conclusion is not vacuous.
* No `sorry`, no `axiom`, no `native_decide`; `#print axioms` at the end, and the theorem
  statements contain no `EP334`/`EP343`/`EPDimensionInequality` occurrence (the file does not import
  `EPQuotes`/`PEQuotes`/`EPQuotesGamma` at all).
-/
import Lemma38RV

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Valuation

namespace YinLemma38EP

open YinLemma37 YinLemma38

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ## 1. The elementary core: algebraic ⟹ a positive power of `v e` is a `K`-value -/

/-- **Algebraic elements have no infinite `Γ`-order.**  If `0 ≠ e` is algebraic over `K` then some
positive power of `v e` is the value of a nonzero element of `K`.

This is the step that `QE/Lemma37_transcendental.lean`'s header records as derived in the paper from
the dimension inequality (EP 3.4.3).  It needs no dimension inequality: it is the minimal-polynomial
`max`-argument, and it is the only input Lemma 3.8's "and hence `e` is transcendental" requires. -/
theorem exists_pow_value_of_isAlgebraic {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    (he : e ≠ 0) (halg : IsAlgebraic ↥K e) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : L, a ∈ K ∧ a ≠ 0 ∧ v e ^ n = v a := by
  classical
  by_contra hcon
  push Not at hcon
  have hord : InfiniteOrderMod v e K := hcon
  have hint : IsIntegral ↥K e := isAlgebraic_iff_isIntegral.mp halg
  set p : Polynomial ↥K := minpoly ↥K e with hp
  have hmonic : p.Monic := minpoly.monic hint
  have haev : Polynomial.aeval e p = 0 := minpoly.aeval ↥K e
  set f : ℕ → L := fun i => (((p.coeff i : ↥K) : L) * e ^ i) with hf
  have hsum0 : ∑ i ∈ Finset.range (p.natDegree + 1), f i = 0 := by
    rw [hf, ← aeval_eq_sum (K := K) p e, haev]
  set s : Finset ℕ := (Finset.range (p.natDegree + 1)).filter (fun i => p.coeff i ≠ 0) with hs
  have hcoeff : ∀ {i : ℕ}, i ∈ s → p.coeff i ≠ 0 := by
    intro i hi
    rw [hs] at hi
    exact (Finset.mem_filter.mp hi).2
  have hds : p.natDegree ∈ s := by
    rw [hs, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self _, by rw [hmonic.coeff_natDegree]; exact one_ne_zero⟩
  obtain ⟨j, hjs, hjmax⟩ :=
    Finset.exists_max_image s (fun i => v (f i)) ⟨p.natDegree, hds⟩
  have hjc : p.coeff j ≠ 0 := hcoeff hjs
  have hjcL : ((p.coeff j : ↥K) : L) ≠ 0 := fun h => hjc (Subtype.coe_injective (by simpa using h))
  have hfj : f j ≠ 0 := mul_ne_zero hjcL (pow_ne_zero j he)
  have hvg : v (f j) ≠ 0 := (Valuation.ne_zero_iff v).mpr hfj
  have hsub : s ⊆ Finset.range (p.natDegree + 1) := by
    rw [hs]; exact Finset.filter_subset _ _
  have hsums : ∑ i ∈ s, f i = 0 := by
    rw [Finset.sum_subset hsub]
    · exact hsum0
    · intro i hi hinot
      rw [hs] at hinot
      have hc : p.coeff i = 0 := by
        by_contra h
        exact hinot (Finset.mem_filter.mpr ⟨hi, h⟩)
      simp [hf, hc]
  have hsplit : ∑ i ∈ s.erase j, f i = -(f j) := by
    rw [Finset.sum_erase_eq_sub hjs, hsums, zero_sub]
  have hlt : ∀ i ∈ s.erase j, v (f i) < v (f j) := by
    intro i hi
    rw [Finset.mem_erase] at hi
    obtain ⟨hij, his⟩ := hi
    have hic : p.coeff i ≠ 0 := hcoeff his
    have hicL : ((p.coeff i : ↥K) : L) ≠ 0 := fun h => hic (Subtype.coe_injective (by simpa using h))
    have hne := v_mul_pow_ne' hord he hij (p.coeff i).2 (p.coeff j).2 hicL hjcL
    exact lt_of_le_of_ne (hjmax i his) hne
  have := map_sum_lt (s.erase j) (f := f) hvg hlt
  rw [hsplit, Valuation.map_neg] at this
  exact absurd this (lt_irrefl (v (f j)))

/-- Contrapositive form: `InfiniteOrderMod` forces transcendence (for `e ≠ 0`). -/
theorem transcendental_of_infiniteOrderMod {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    (he : e ≠ 0) (hord : InfiniteOrderMod v e K) : Transcendental ↥K e := by
  intro halg
  obtain ⟨n, hn, a, ha, ha0, hva⟩ := exists_pow_value_of_isAlgebraic (v := v) (K := K) he halg
  exact hord n hn a ha ha0 hva

/-- **The paper's "and hence `e` is transcendental over `VF(Ŝ)`"** (Lemma 3.8's opening), from
`Γ(Ŝ)` divisible and `vv(e) ∉ Γ(Ŝ)`.  No Engler–Prestel inequality is used: the first clause is the
tree's `infiniteOrderMod_of_divisible`, the second is §1's minimal-polynomial argument. -/
theorem transcendental_of_divisible_of_notMem {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    (hdiv : DivisibleValueGroup v K) (he : e ≠ 0)
    (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a) : Transcendental ↥K e :=
  transcendental_of_infiniteOrderMod he (infiniteOrderMod_of_divisible hdiv hout)

/-! ## 2. `vv(e) ∉ Γ(Ŝ)` from `rv(e) ∉ RV(Ŝ)`: the one place `K(Ŝ) = K(M)` is used -/

/-- **`K(Ŝ) = K(M)`, residue form**: every unit of `L` has the same `RV`-class as an element of `K`
with the same value.  (In the paper this is true because the residue field of a model of `ACVF` is
algebraically closed and `K(Ŝ) = K(M)`; a `Subfield` alone says nothing about residues, so it has to
be carried explicitly at this level of generality.) -/
def ResidueSurjective (v : Valuation L Γ₀) (K : Subfield L) : Prop :=
  ∀ x : L, v x = 1 → ∃ c : L, c ∈ K ∧ v c = 1 ∧ v (x - c) < 1

/-- A unit of `L` whose difference from `c ∈ K` is smaller than `1` is in the `RV`-class of `c`. -/
theorem sameRV_of_residue {v : Valuation L Γ₀} {x c : L} (hx : v x = 1) (hc : v c = 1)
    (h : v (x - c) < 1) : SameRV v x c :=
  ⟨hx.trans hc.symm, by rw [hx]; exact h⟩

/-- **`rv(e) ∉ RV(Ŝ)` implies `vv(e) ∉ Γ(Ŝ)`** when the residue field is that of a model of `ACVF`
(`ResidueSurjective`), i.e. the paper's use of `K(Ŝ) = K(M)` at the *hypothesis* of Claim (⋆).

Suppose `v e = v a` with `a ∈ K^×`.  Then `e / a` is a unit, so by `ResidueSurjective` there is
`c ∈ K` with `v c = 1` and `v (e/a - c) < 1`, i.e. `rv(e/a) = rv(c)`; hence
`rv(e) = rv(a · c) ∈ RV(Ŝ)`, contradiction. -/
theorem hout_of_rv_notMem {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    (hres : ResidueSurjective v K)
    (hrv : ∀ a : L, a ∈ K → a ≠ 0 → ¬ SameRV v e a) :
    ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a := by
  intro a ha ha0 hval
  have hva0 : v a ≠ 0 := (Valuation.ne_zero_iff v).mpr ha0
  have hx1 : v (e / a) = 1 := by
    rw [Valuation.map_div, hval, div_self hva0]
  obtain ⟨c, hcK, hc1, hclt⟩ := hres (e / a) hx1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc1
    simp at hc1
  refine hrv (a * c) (K.mul_mem ha hcK) (mul_ne_zero ha0 hc0) ?_
  have h1 : SameRV v (e / a) c := sameRV_of_residue hx1 hc1 hclt
  have h2 : SameRV v ((e / a) * a) (c * a) := SameRV.mul h1 (sameRV_refl v ha0)
  rwa [div_mul_cancel₀ e ha0, mul_comm c a] at h2

/-! ## 3. Lemma 3.8's two halves and `RV`-generation, with the transcendence *derived* -/

/-- **Lemma 3.8, `RV` half** (`QE/Lemma38RV.lean`'s `sameRV_aeval`), with its transcendence
hypothesis derived from `Γ(Ŝ)` divisible + `vv(e) ∉ Γ(Ŝ)`. -/
theorem sameRV_aeval_of_divisible {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hdiv : DivisibleValueGroup v K) (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a)
    (hsame : SameRV v e d) {r : Polynomial ↥K} (hr : r ≠ 0) :
    SameRV v ((Polynomial.aeval e) r) ((Polynomial.aeval d) r) :=
  sameRV_aeval (infiniteOrderMod_of_divisible hdiv hout) (SameRV.ne_zero_left hsame) hsame
    (transcendental_of_divisible_of_notMem hdiv (SameRV.ne_zero_left hsame) hout) hr

/-- The partner `d` is transcendental too: it has the same value as `e`, hence also infinite order,
hence is transcendental by §1.  (In the paper: "Then `d` is transcendental over `f(VF(Ŝ))`.") -/
theorem transcendental_of_sameRV {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hdiv : DivisibleValueGroup v K) (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a)
    (hsame : SameRV v e d) : Transcendental ↥K d :=
  transcendental_of_infiniteOrderMod (SameRV.ne_zero_right hsame)
    (infiniteOrderMod_of_sameRV (infiniteOrderMod_of_divisible hdiv hout) hsame)

/-- **Lemma 3.8, `RV` half, quotient form** (`sameRV_aeval_div`), transcendence derived. -/
theorem sameRV_aeval_div_of_divisible {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hdiv : DivisibleValueGroup v K) (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a)
    (hsame : SameRV v e d) {p q : Polynomial ↥K} (hp : p ≠ 0) (hq : q ≠ 0) :
    SameRV v ((Polynomial.aeval e) p / (Polynomial.aeval e) q)
      ((Polynomial.aeval d) p / (Polynomial.aeval d) q) := by
  have houtd : ∀ a : L, a ∈ K → a ≠ 0 → v d ≠ v a := by
    intro a ha ha0 h
    exact hout a ha ha0 (hsame.1.trans h)
  exact sameRV_aeval_div (infiniteOrderMod_of_divisible hdiv hout) (SameRV.ne_zero_left hsame)
    hsame (transcendental_of_divisible_of_notMem hdiv (SameRV.ne_zero_left hsame) hout)
    (transcendental_of_sameRV hdiv hout hsame) hp hq

/-- **Claim (⋆), second half at the valuation level** (`sameRV_mem_adjoin`), with the transcendence
derived: `RV(VF(Ŝ)(e)) = ⟨RV(Ŝ), rv(e)⟩`, i.e. every nonzero element of `K(e)` is in the
`RV`-class of `a · e^n` with `a ∈ K^×`, `n ∈ ℤ`. -/
theorem sameRV_mem_adjoin_of_divisible {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    (hdiv : DivisibleValueGroup v K) (he : e ≠ 0)
    (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a)
    {x : L} (hx : x ∈ IntermediateField.adjoin ↥K {e}) (hx0 : x ≠ 0) :
    ∃ a : L, a ∈ K ∧ a ≠ 0 ∧ ∃ n : ℤ, SameRV v x (a * e ^ n) :=
  sameRV_mem_adjoin (infiniteOrderMod_of_divisible hdiv hout) he
    (transcendental_of_divisible_of_notMem hdiv he hout) hx hx0

/-! ### 3b. The value half across two fields, with `K(Ŝ) = K(M)` removed -/

section Transfer

variable {L' : Type*} [Field L'] {v' : Valuation L' Γ₀} {K' : Subfield L'}
variable {v : Valuation L Γ₀} {K : Subfield L}

/-- `Γ(Ŝ)` divisible transfers along a value-preserving isomorphism of coefficient fields. -/
theorem divisibleValueGroup_of_ringEquiv
    (σ : ↥K ≃+* ↥K')
    (hσ : ∀ a : ↥K, v' (((σ : ↥K →+* ↥K') a) : L') = v (((a : ↥K) : L)))
    (hdiv : DivisibleValueGroup v K) : DivisibleValueGroup v' K' := by
  intro n hn a ha ha0
  set b : ↥K := σ.symm ⟨a, ha⟩ with hb
  have hbval : (((σ b : ↥K') : L')) = a := congrArg Subtype.val (σ.apply_symm_apply ⟨a, ha⟩)
  have hb0 : ((b : ↥K) : L) ≠ 0 := by
    intro h
    apply ha0
    rw [← hbval, show b = 0 from Subtype.ext h]
    simp
  obtain ⟨c, hcK, hc0, hvc⟩ := hdiv n hn ((b : ↥K) : L) b.2 hb0
  refine ⟨((σ ⟨c, hcK⟩ : ↥K') : L'), (σ ⟨c, hcK⟩).2, ?_, ?_⟩
  · intro h
    have h1 : σ ⟨c, hcK⟩ = 0 := Subtype.ext h
    have h2 : (⟨c, hcK⟩ : ↥K) = 0 := σ.injective (by rw [h1, map_zero])
    exact hc0 (congrArg Subtype.val h2)
  · have h1 : v' a = v (((b : ↥K) : L)) := by
      rw [← hbval]
      exact hσ b
    rw [h1, hvc]
    exact (congrArg (fun z => z ^ n) (hσ ⟨c, hcK⟩)).symm

/-- **Lemma 3.8's value half (Lemma 3.7 + the transfer `b ↦ b*`), with the transcendence of `e`
and of `d` derived** — so `K(Ŝ) = K(M)` (`IsAlgClosedInL`, which `QE/Case38Value.lean`'s
`lemma38_transfer` uses) is *not* needed for the value half: `Γ(Ŝ)` divisible and
`vv(e) ∉ Γ(Ŝ)` suffice. -/
theorem value_transfer_of_divisible
    (σ : ↥K ≃+* ↥K')
    (hσ : ∀ a : ↥K, v' (((σ : ↥K →+* ↥K') a) : L') = v (((a : ↥K) : L)))
    (hdiv : DivisibleValueGroup v K) {e : L} (he : e ≠ 0)
    (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a) {d : L'} (hvde : v' d = v e) :
    Transcendental ↥K e ∧ Transcendental ↥K' d ∧
      (∀ x : L, x ∈ IntermediateField.adjoin ↥K {e} →
        ∃ y : L', y ∈ IntermediateField.adjoin ↥K' {d} ∧ v x = v' y) ∧
      (∀ r : Polynomial ↥K, r ≠ 0 →
        v ((Polynomial.aeval e) r) = v' ((Polynomial.aeval d) (r.map (σ : ↥K →+* ↥K')))) := by
  have hdiv' : DivisibleValueGroup v' K' := divisibleValueGroup_of_ringEquiv σ hσ hdiv
  -- `vv(d) ∉ Γ(f(Ŝ))`
  have hout' : ∀ a : L', a ∈ K' → a ≠ 0 → v' d ≠ v' a := by
    intro a ha ha0 h
    obtain ⟨b, hb⟩ := σ.surjective (⟨a, ha⟩ : ↥K')
    have hbL : (((σ b : ↥K') : L')) = a := congrArg Subtype.val hb
    have hb0 : ((b : ↥K) : L) ≠ 0 := by
      intro h0
      apply ha0
      rw [← hbL, show b = 0 from Subtype.ext h0]
      simp
    have hvb : v (((b : ↥K) : L)) = v' a := (hσ b).symm.trans (congrArg v' hbL)
    exact hout ((b : ↥K) : L) b.2 hb0 (hvde.symm.trans (h.trans hvb.symm))
  have hve : v e ≠ 0 := (Valuation.ne_zero_iff v).mpr he
  have hd : d ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hvde
    exact hve hvde.symm
  have htrans : Transcendental ↥K e := transcendental_of_divisible_of_notMem hdiv he hout
  have htrans' : Transcendental ↥K' d := transcendental_of_divisible_of_notMem hdiv' hd hout'
  have hord : InfiniteOrderMod v e K := infiniteOrderMod_of_divisible hdiv hout
  refine ⟨htrans, htrans', ?_, ?_⟩
  · intro x hx
    exact value_transfer_adjoin σ hσ he hd hvde hord htrans htrans' hx
  · intro r hr
    exact value_transfer σ hσ he hd hvde hord htrans htrans' hr

end Transfer

/-! ## 4. Lemma 3.8's algebraic content from the paper's own case hypotheses -/

/-- **Lemma 3.8 (`lift:value:full`), algebraic content, EP-free.**
Hypotheses: `Γ(Ŝ)` divisible (`hdiv`), `vv(e) ∉ Γ(Ŝ)` (`hout`), and `rv(d) = rv(e)` read in one
field as `SameRV v e d` (Yin's `f` identifies `VF(Ŝ)` with `f(VF(Ŝ))`, and both `f(bᵢ)` and `d` are
placed in `N`, so this is the faithful same-field reading — `QE/Lemma38RV.lean`'s convention).

Conclusions: `e` and `d` are transcendental over `K`; the polynomial transfer `e ↦ d` preserves
`RV`-classes (the residue half) and values (the value half); and `RV(K(e)) = ⟨RV(K), rv e⟩`
(`RV`-generation).  This is Claim (⋆)'s algebraic content — the two things the paper's proof
establishes before invoking Remark 3.1. -/
theorem lemma38_algebraic_content {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hdiv : DivisibleValueGroup v K) (he : e ≠ 0)
    (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a)
    (hsame : SameRV v e d) :
    Transcendental ↥K e ∧ Transcendental ↥K d ∧
      (∀ r : Polynomial ↥K, r ≠ 0 →
        SameRV v ((Polynomial.aeval e) r) ((Polynomial.aeval d) r)) ∧
      (∀ x : L, x ∈ IntermediateField.adjoin ↥K {e} → x ≠ 0 →
        ∃ a : L, a ∈ K ∧ a ≠ 0 ∧ ∃ n : ℤ, SameRV v x (a * e ^ n)) :=
  ⟨transcendental_of_divisible_of_notMem hdiv he hout,
    transcendental_of_sameRV hdiv hout hsame,
    fun r hr => sameRV_aeval_of_divisible hdiv hout hsame hr,
    fun x hx hx0 => sameRV_mem_adjoin_of_divisible hdiv he hout hx hx0⟩

/-- **Lemma 3.8 from the paper's hypothesis list** — `Γ(Ŝ)` divisible, `K(Ŝ) = K(M)` in residue
form (`ResidueSurjective`, §2), `rv(e) ∉ RV(Ŝ)` and `rv(d) = rv(e)`.  Neither EP 3.3.4 nor EP 3.4.3
appears; `K(Ŝ) = K(M)` enters only through `hout_of_rv_notMem`. -/
theorem lemma38_of_rv_new {v : Valuation L Γ₀} {K : Subfield L} {e d : L}
    (hdiv : DivisibleValueGroup v K) (hres : ResidueSurjective v K) (he : e ≠ 0)
    (hrv : ∀ a : L, a ∈ K → a ≠ 0 → ¬ SameRV v e a) (hsame : SameRV v e d) :
    Transcendental ↥K e ∧ Transcendental ↥K d ∧
      (∀ r : Polynomial ↥K, r ≠ 0 →
        SameRV v ((Polynomial.aeval e) r) ((Polynomial.aeval d) r)) ∧
      (∀ x : L, x ∈ IntermediateField.adjoin ↥K {e} → x ≠ 0 →
        ∃ a : L, a ∈ K ∧ a ≠ 0 ∧ ∃ n : ℤ, SameRV v x (a * e ^ n)) :=
  lemma38_algebraic_content hdiv he (hout_of_rv_notMem hres hrv) hsame

/-! ## 5. Stress tests -/

/-- **`e ≠ 0` is essential** in `transcendental_of_infiniteOrderMod`: `0` has infinite order modulo
every `Γ(K)` (its value is `0 = ⊥`, which no nonzero element's value is). -/
theorem infiniteOrderMod_zero (v : Valuation L Γ₀) (K : Subfield L) :
    InfiniteOrderMod v (0 : L) K := by
  intro n hn a _ha ha0 h
  rw [Valuation.map_zero, zero_pow hn.ne'] at h
  exact ((Valuation.ne_zero_iff v).mpr ha0) h.symm

/-- **Divisibility cannot be dropped from `transcendental_of_divisible_of_notMem`.**
The upgrade `v e ^ n ∈ Γ(Ŝ) ⟹ v e ∈ Γ(Ŝ)` (which `DivisibleValueGroup` licenses) fails for a
non-divisible `Γ(Ŝ)`: in `Multiplicative ℤ` with `H = ⟨2⟩`, the element `1` has
`1 ^ 2 = 2 ∈ H` but `1 ∉ H`.  This is the exact group-theoretic content of the ramified instance
`ℚ ⊆ ℚ(√2)` at the 2-adic place, where `v(√2)^2 = v(2) ∈ Γ(ℚ)` but `v(√2) ∉ Γ(ℚ)`. -/
theorem upgrade_needs_divisibility :
    ∃ (g : Multiplicative ℤ) (H : Subgroup (Multiplicative ℤ)) (n : ℕ),
      0 < n ∧ g ^ n ∈ H ∧ g ∉ H := by
  refine ⟨Multiplicative.ofAdd (1 : ℤ), Subgroup.zpowers (Multiplicative.ofAdd (2 : ℤ)), 2,
    by norm_num, ?_, ?_⟩
  · rw [show (Multiplicative.ofAdd (1 : ℤ)) ^ 2 = Multiplicative.ofAdd (2 : ℤ) by
      rw [pow_two, ← ofAdd_add]; norm_num]
    exact Subgroup.mem_zpowers _
  · intro h
    rw [Subgroup.mem_zpowers_iff] at h
    obtain ⟨k, hk⟩ := h
    have hk' : (k : ℤ) * 2 = 1 := by
      have := congrArg Multiplicative.toAdd hk
      simpa using this
    omega

/-- **Non-vacuity of the hypothesis package**: at `ℚ(X)` with the place at infinity and `K` the
constant subfield (`⊥` as an `IntermediateField`), the element `e = X` has value `exp 1 ∉ Γ(K) = {1}`,
`Γ(K)` is trivially divisible, and `SameRV v X (X + 1)` holds.  The theorem therefore *produces*
`Transcendental K X` — the conclusion of Lemma 3.8's first step, non-vacuously.

This is the shape in which the paper uses the hypothesis package (`VF(Ŝ) = ℚ` inside `ℚ(X)`), with
`v` the place at infinity playing the role of the valuation of `M`. -/
theorem transcendental_X_instance :
    Transcendental ↥((⊥ : IntermediateField ℚ (RatFunc ℚ)).toSubfield) (RatFunc.X : RatFunc ℚ) := by
  classical
  set K : Subfield (RatFunc ℚ) := (⊥ : IntermediateField ℚ (RatFunc ℚ)).toSubfield with hK
  have hmem : ∀ a : RatFunc ℚ, a ∈ K → ∃ q : ℚ, algebraMap ℚ (RatFunc ℚ) q = a := by
    intro a ha
    rw [hK, IntermediateField.mem_toSubfield, IntermediateField.mem_bot] at ha
    exact ha
  have ha1 : ∀ a ∈ K, a ≠ 0 → RatFunc.inftyValuation ℚ a = 1 := by
    intro a ha ha0
    obtain ⟨q, hq⟩ := hmem a ha
    rw [← hq]
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [map_zero] at hq
      exact ha0 hq.symm
    simpa using RatFunc.inftyValuation.C (F := ℚ) hq0
  have hdiv : DivisibleValueGroup (RatFunc.inftyValuation ℚ) K := by
    intro n hn a ha ha0
    refine ⟨1, K.one_mem, one_ne_zero, ?_⟩
    rw [ha1 a ha ha0]
    simp
  have hout : ∀ a : RatFunc ℚ, a ∈ K → a ≠ 0 →
      RatFunc.inftyValuation ℚ RatFunc.X ≠ RatFunc.inftyValuation ℚ a := by
    intro a ha ha0 h
    rw [ha1 a ha ha0, RatFunc.inftyValuation.X] at h
    exact absurd h (by simp)
  exact transcendental_of_divisible_of_notMem hdiv RatFunc.X_ne_zero hout

end YinLemma38EP

/-! ## Axiom audit -/

#print axioms YinLemma38EP.exists_pow_value_of_isAlgebraic
#print axioms YinLemma38EP.transcendental_of_infiniteOrderMod
#print axioms YinLemma38EP.transcendental_of_divisible_of_notMem
#print axioms YinLemma38EP.hout_of_rv_notMem
#print axioms YinLemma38EP.sameRV_aeval_of_divisible
#print axioms YinLemma38EP.transcendental_of_sameRV
#print axioms YinLemma38EP.sameRV_aeval_div_of_divisible
#print axioms YinLemma38EP.sameRV_mem_adjoin_of_divisible
#print axioms YinLemma38EP.divisibleValueGroup_of_ringEquiv
#print axioms YinLemma38EP.value_transfer_of_divisible
#print axioms YinLemma38EP.lemma38_algebraic_content
#print axioms YinLemma38EP.lemma38_of_rv_new
#print axioms YinLemma38EP.infiniteOrderMod_zero
#print axioms YinLemma38EP.upgrade_needs_divisibility
#print axioms YinLemma38EP.transcendental_X_instance
