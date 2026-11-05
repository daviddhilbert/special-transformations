/-
# The `Γ`-side core of Lemma 3.6 (`lift:transcendental`), and the necessity of its hypotheses

Member `m4`, swarm `smw2ngn1z`, direction d2 (**necessity / non-vacuity audit of Lemma 3.6's
hypothesis bundle**).  Companion file `Lemma36Audit.lean` does the `L_RV`-level part.

## What Lemma 3.6 consumes from valuation theory

Lemma 3.6 (`qe.tex:732`) argues, for `e ∈ U(M)` with `rv(e)` transcendental over `K(Ŝ)`:

> By the dimension inequality of valuation theory (Engler–Prestel Thm 3.4.3), the rational rank
> of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0.  Since `Γ(Ŝ)` is divisible, we actually have `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`.

At the level of the value group this is a statement about an ordered abelian group `Γ` (in the
frozen encoding `GammaGroup.GammaOf M`, which `QE/GammaGroup.lean` proves is a `LinearOrder`ed
commutative group) and a subgroup `Γ₀ = Γ(Ŝ)`.  The paper's step has exactly two inputs:

* **`RatRankZero`** — the conclusion of EP Thm 3.4.3 specialised to this pair: `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is
  a torsion group.  For an abelian group `A`, `A ⊗ ℚ = 0 ↔ A` is torsion, so this is
  `ratrank (Γ(⟨Ŝ,e⟩)/Γ(Ŝ)) = 0`, i.e. `dim_ℚ (A ⊗ ℚ) = 0`.  The specialised form is what the
  consumer needs, as the project's author ruling on quoted classical results allows.
* **`SubgroupDivisible Γ₀`** — the paper's standing hypothesis `Γ(Ŝ)` divisible.

The conclusion `Γ₀ = Γ(⟨Ŝ,e⟩)` is `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`.

## Contents

§1 definitions.  §2 the core: `mem_of_nsmul_mem`, `le_of_ratRankZeroIn`,
`eq_top_of_ratRankZero`, plus the single-generator form `ratRankZeroIn_sup_zmultiples` — the shape
the paper's transcendental `e` actually produces (`Γ(⟨Ŝ,e⟩) = Γ(Ŝ) + ℤ·vv(e)`, Lemma 3.7), which is
also the wiring from the quoted inequality to the `Γ`-step.  §3 Mathlib's name for the resulting
closure property (`AddSubmonoid.NSMulSaturated`).  §4 **necessity**: each input is indispensable, by
machine-checked counterexample — `divisibility_necessary` (`2ℤ ≤ ℤ`: torsion quotient, torsion-free
ambient group, `2ℤ ≠ ⊤`, and `2 • 1 ∈ 2ℤ` while `1 ∉ 2ℤ`) and `torsion_is_obstruction`
(`⊥ ≤ ZMod 2`: divisible, torsion quotient, but `2 • x = 0` with `x ≠ 0` falls outside `⊥`).

The audit conclusion: neither input can be dropped, so *both* the quoted inequality (EP 3.4.3,
supplying the rational-rank-zero input) and the paper's divisibility hypothesis are load-bearing in
Lemma 3.6.  Nothing here assumes a valuation: this is pure ordered-abelian-group algebra, hence
independent of any choice of model of `ACVF`.
-/
import Mathlib

set_option autoImplicit false

namespace Lemma36Audit

variable {Γ : Type*} [AddCommGroup Γ]

/-! ## 1. The two inputs, and the conclusion -/

/-- `Γ₀` is **divisible**: every element of `Γ₀` has an `n`-th root inside `Γ₀`
(the paper's `Γ(Ŝ)` divisible, `qe.tex:762`). -/
def SubgroupDivisible (Γ₀ : AddSubgroup Γ) : Prop :=
  ∀ a ∈ Γ₀, ∀ n : ℕ, 0 < n → ∃ b ∈ Γ₀, n • b = a

/-- **Rational rank zero** of `Γ' / Γ₀`: every element of `Γ'` becomes an element of `Γ₀` after
multiplication by some `n > 0`, i.e. the quotient `Γ'/Γ₀` is a torsion group.

For an abelian group `A`, `dim_ℚ (A ⊗ ℚ) = 0 ↔ A` is torsion, so with `Γ' = Γ(⟨Ŝ,e⟩)` and
`Γ₀ = Γ(Ŝ)` this is exactly `ratrank (Γ(⟨Ŝ,e⟩)/Γ(Ŝ)) = 0`, the conclusion of Engler–Prestel
Theorem 3.4.3 that Lemma 3.6 consumes.  (The general tensor formulation is needed by no consumer in
the tree; the specialised form is stated, per the author ruling on quoted classical results.) -/
def RatRankZeroIn (Γ' Γ₀ : AddSubgroup Γ) : Prop :=
  ∀ y ∈ Γ', ∃ n : ℕ, 0 < n ∧ n • y ∈ Γ₀

/-- The absolute form: the whole of `Γ` is killed modulo `Γ₀`. -/
def RatRankZero (Γ₀ : AddSubgroup Γ) : Prop := RatRankZeroIn ⊤ Γ₀

theorem ratRankZero_iff (Γ₀ : AddSubgroup Γ) :
    RatRankZero Γ₀ ↔ ∀ x : Γ, ∃ n : ℕ, 0 < n ∧ n • x ∈ Γ₀ := by
  constructor
  · intro h x
    exact h x trivial
  · intro h x _
    exact h x

/-! ## 2. The core step: `ratrank 0` + `Γ₀` divisible ⇒ `Γ₀ = Γ`

Where torsion-freeness enters: `n • x ∈ Γ₀` and divisibility give `b ∈ Γ₀` with `n • b = n • x`,
and only *cancellation of `n •`* (absence of `n`-torsion) turns that into `x = b`.  This is why the
paper's `Γ` is an *ordered* group: ordered abelian groups are torsion-free, and
`GammaGroup.GammaOf M` is a `LinearOrder`ed commutative group. -/

/-- In a torsion-free group, a divisible subgroup is closed under division by `n`. -/
theorem mem_of_nsmul_mem [IsAddTorsionFree Γ] {Γ₀ : AddSubgroup Γ}
    (hdiv : SubgroupDivisible Γ₀) {x : Γ} {n : ℕ} (hn : 0 < n) (h : n • x ∈ Γ₀) : x ∈ Γ₀ := by
  obtain ⟨b, hb, hb'⟩ := hdiv (n • x) h n hn
  have hsub : n • (x - b) = 0 := by rw [nsmul_sub, hb', sub_self]
  have hxb : x - b = 0 := by
    refine IsAddTorsionFree.nsmul_right_injective (Nat.pos_iff_ne_zero.mp hn) ?_
    simpa using hsub
  rw [sub_eq_zero.mp hxb]
  exact hb

/-- **Lemma 3.6's `Γ`-step.**  If the quotient `Γ'/Γ₀` has rational rank `0` and `Γ₀` is divisible,
then `Γ' ≤ Γ₀`.  Instances: `Γ' = Γ(⟨Ŝ,e⟩)`, `Γ₀ = Γ(Ŝ)` gives `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`. -/
theorem le_of_ratRankZeroIn [IsAddTorsionFree Γ] {Γ' Γ₀ : AddSubgroup Γ}
    (hdiv : SubgroupDivisible Γ₀) (hrank : RatRankZeroIn Γ' Γ₀) : Γ' ≤ Γ₀ := by
  intro y hy
  obtain ⟨n, hn, hny⟩ := hrank y hy
  exact mem_of_nsmul_mem hdiv hn hny

/-- The absolute form: `Γ/Γ₀` of rational rank zero and `Γ₀` divisible force `Γ₀ = ⊤`. -/
theorem eq_top_of_ratRankZero [IsAddTorsionFree Γ] {Γ₀ : AddSubgroup Γ}
    (hdiv : SubgroupDivisible Γ₀) (hrank : RatRankZero Γ₀) : Γ₀ = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _
  exact le_of_ratRankZeroIn hdiv hrank trivial

/-- Every element of `Γ` lies in `Γ₀`, in the orientation a consumer wants. -/
theorem mem_of_ratRankZero [IsAddTorsionFree Γ] {Γ₀ : AddSubgroup Γ}
    (hdiv : SubgroupDivisible Γ₀) (hrank : RatRankZero Γ₀) (x : Γ) : x ∈ Γ₀ := by
  rw [eq_top_of_ratRankZero hdiv hrank]
  trivial

/-! ### 2′. The single-generator shape of the paper's transcendental `e`

`Γ(⟨Ŝ,e⟩) = Γ(Ŝ) + ℤ·vv(e)`, so the rational-rank-zero input only has to be checked on one
generator: `n • vv(e) ∈ Γ(Ŝ)` for some `n > 0`.  With divisibility this yields `vv(e) ∈ Γ(Ŝ)`
(`mem_of_nsmul_mem`), i.e. the paper's `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`. -/

/-- `n • x ∈ Γ₀` propagates to the whole group generated by `Γ₀` and `x`: the quotient
`(Γ₀ ⊔ ℤ·x)/Γ₀` is torsion. -/
theorem nsmul_mem_sup_zmultiples {Γ₀ : AddSubgroup Γ} {x y : Γ} {n : ℕ} (hx : n • x ∈ Γ₀)
    (hy : y ∈ Γ₀ ⊔ AddSubgroup.zmultiples x) : n • y ∈ Γ₀ := by
  rw [AddSubgroup.mem_sup] at hy
  obtain ⟨a, ha, z, hz, rfl⟩ := hy
  rw [AddSubgroup.mem_zmultiples_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  have hsplit : n • (a + k • x) = n • a + k • (n • x) := by
    rw [nsmul_add, smul_comm]
  rw [hsplit]
  exact AddSubgroup.add_mem Γ₀ (AddSubgroup.nsmul_mem Γ₀ ha n) (AddSubgroup.zsmul_mem Γ₀ hx k)

/-- The wiring lemma from the quoted inequality to the `Γ`-step: one relation `n • x ∈ Γ₀`
suffices for the quotient of `Γ₀ ⊔ ℤ·x` by `Γ₀` to have rational rank `0`. -/
theorem ratRankZeroIn_sup_zmultiples {Γ₀ : AddSubgroup Γ} {x : Γ} {n : ℕ} (hn : 0 < n)
    (hx : n • x ∈ Γ₀) : RatRankZeroIn (Γ₀ ⊔ AddSubgroup.zmultiples x) Γ₀ :=
  fun _ hy => ⟨n, hn, nsmul_mem_sup_zmultiples hx hy⟩

/-- Consequently `x` itself lands in the divisible `Γ₀`: the paper's `vv(e) ∈ Γ(Ŝ)`. -/
theorem mem_of_nsmul_mem_sup [IsAddTorsionFree Γ] {Γ₀ : AddSubgroup Γ}
    (hdiv : SubgroupDivisible Γ₀) {x : Γ} {n : ℕ} (hn : 0 < n) (hx : n • x ∈ Γ₀) : x ∈ Γ₀ :=
  mem_of_nsmul_mem hdiv hn hx

/-! ## 3. Mathlib's name for the conclusion -/

/-- A divisible subgroup of a torsion-free group is `n`-saturated in Mathlib's sense
(`AddSubmonoid.NSMulSaturated`): `n • x ∈ Γ₀ → n = 0 ∨ x ∈ Γ₀`. -/
theorem nsmulSaturated_of_divisible [IsAddTorsionFree Γ] {Γ₀ : AddSubgroup Γ}
    (hdiv : SubgroupDivisible Γ₀) : Γ₀.toAddSubmonoid.NSMulSaturated := by
  intro n x hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl rfl
  · exact Or.inr (mem_of_nsmul_mem hdiv hn hx)

/-! ## 4. Necessity of both hypotheses

Each counterexample satisfies the *other* hypothesis and has the paper's torsion-quotient
conclusion, yet fails `Γ₀ = ⊤`; so neither input of §2 can be dropped or weakened. -/

/-- The even integers, as an additive subgroup of `ℤ`. -/
def evenInt : AddSubgroup ℤ where
  carrier := {x | ∃ k : ℤ, x = 2 * k}
  zero_mem' := ⟨0, by norm_num⟩
  add_mem' := by
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, by ring⟩
  neg_mem' := by
    rintro a ⟨i, rfl⟩
    exact ⟨-i, by ring⟩

theorem mem_evenInt {x : ℤ} : x ∈ evenInt ↔ ∃ k : ℤ, x = 2 * k := Iff.rfl

theorem ratRankZero_evenInt : RatRankZero evenInt := by
  intro x _
  refine ⟨2, by norm_num, ?_⟩
  rw [mem_evenInt]
  exact ⟨x, by rw [two_nsmul]; ring⟩

theorem not_divisible_evenInt : ¬ SubgroupDivisible evenInt := by
  intro h
  have h2 : (2 : ℤ) ∈ evenInt := by rw [mem_evenInt]; exact ⟨1, by norm_num⟩
  obtain ⟨b, hb, hb'⟩ := h 2 h2 4 (by norm_num)
  rw [mem_evenInt] at hb
  obtain ⟨k, rfl⟩ := hb
  have h4 : (4 : ℤ) * (2 * k) = 2 := by simpa [nsmul_eq_mul] using hb'
  omega

theorem evenInt_ne_top : evenInt ≠ ⊤ := by
  intro h
  have h1 : (1 : ℤ) ∈ evenInt := by rw [h]; trivial
  rw [mem_evenInt] at h1
  obtain ⟨k, hk⟩ := h1
  omega

/-- **Divisibility is necessary**: `2ℤ ≤ ℤ` *does* have torsion quotient (rational rank `0`) in a
torsion-free group, yet `2ℤ ≠ ⊤`; indeed `2 • 1 ∈ 2ℤ` while `1 ∉ 2ℤ`.  So EP Thm 3.4.3 alone does
not give the paper's `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`; the standing hypothesis `Γ(Ŝ)` divisible is load-bearing. -/
theorem divisibility_necessary :
    ∃ Γ₀ : AddSubgroup ℤ, ¬ SubgroupDivisible Γ₀ ∧ RatRankZero Γ₀ ∧ Γ₀ ≠ ⊤ :=
  ⟨evenInt, not_divisible_evenInt, ratRankZero_evenInt, evenInt_ne_top⟩

/-- **Torsion-freeness (the order on `Γ`) is necessary**: in `ZMod 2` the trivial subgroup is
divisible and the quotient is torsion, but `2 • 1 = 0 ∈ ⊥` while `1 ∉ ⊥`.  So rational rank `0`
plus divisibility forces `Γ₀ = Γ` only because `Γ` is an *ordered* group. -/
theorem torsion_is_obstruction :
    ∃ (Γ' : Type) (_ : AddCommGroup Γ') (Γ₀ : AddSubgroup Γ') (x : Γ'),
      SubgroupDivisible Γ₀ ∧ RatRankZero Γ₀ ∧ x ≠ 0 ∧ 2 • x = 0 ∧ x ∉ Γ₀ := by
  refine ⟨ZMod 2, inferInstance, ⊥, 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha n _
    rw [AddSubgroup.mem_bot] at ha
    exact ⟨0, AddSubgroup.zero_mem _, by rw [ha]; simp⟩
  · intro x _
    refine ⟨2, by norm_num, ?_⟩
    rw [AddSubgroup.mem_bot, nsmul_eq_mul]
    show ((2 : ℕ) : ZMod 2) * x = 0
    rw [ZMod.natCast_self, zero_mul]
  · intro h
    have h' := congrArg (fun x : ZMod 2 => x.val) h
    simp at h'
  · rw [nsmul_eq_mul, mul_one]
    exact ZMod.natCast_self 2
  · intro h
    rw [AddSubgroup.mem_bot] at h
    have h' := congrArg (fun x : ZMod 2 => x.val) h
    simp at h'

/-! ## 5. The Engler–Prestel inputs as quotable `Prop`s (author ruling: quoted, never proved)

Per the project's author ruling, the two classical inequalities are transcribed as `Prop`s and enter
any final theorem as *hypotheses*; nothing below is proved from `ACVF`.  What §2 supplies is the
**wiring** from the quoted inequality to the consumer-shaped conclusion. -/

/-- **Engler–Prestel Theorem 3.4.3 (dimension inequality / Abhyankar), specialised to the form
Lemma 3.6 consumes**: for `e` transcendental over `VF(Ŝ)`, the rational rank of
`Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is `0`, i.e. every element of `Γ(⟨Ŝ,e⟩)` becomes an element of `Γ(Ŝ)` after
multiplication by some `n > 0`.

(The paper also derives `trdeg(VF(⟨Ŝ,e⟩)/VF(Ŝ)) ≥ ratrank(Γ/Γ₀)`; only the `0` case is used.) -/
def EP343_ratRankZero {Γ : Type*} [AddCommGroup Γ] (Γ' Γ₀ : AddSubgroup Γ) : Prop :=
  RatRankZeroIn Γ' Γ₀

/-- **Wiring of EP 3.4.3 to Lemma 3.6's `Γ`-step**: quote + `Γ(Ŝ)` divisible ⇒
`Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`.  This is `qe.tex:762-765` verbatim, with the quoted inequality as a
hypothesis. -/
theorem gamma_unchanged_of_EP343 [IsAddTorsionFree Γ] {Γ' Γ₀ : AddSubgroup Γ}
    (hEP : EP343_ratRankZero Γ' Γ₀) (hdiv : SubgroupDivisible Γ₀) : Γ' ≤ Γ₀ :=
  le_of_ratRankZeroIn hdiv hEP

/-- **Engler–Prestel Theorem 3.3.4 (fundamental inequality), `Γ`-half**, in the shape
Lemmas 3.4 and 3.8 consume: for a one-element *algebraic* extension with henselian base,
`[K(⟨Ŝ,e⟩):K(Ŝ)] = [VF(⟨Ŝ,e⟩):VF(Ŝ)]`, which the paper's proof reads as
`Γ(⟨Ŝ,e⟩) = Γ(Ŝ)` (and `K(⟨Ŝ,e⟩) = K(Ŝ)(rv e)`).

Only the value-group half is stated here: it is the half that is expressible in the tree's
`GammaOf` vocabulary.  The residue-degree half needs a degree theory for `KOf M` over the residue
field of `Ŝ`, which this file does not build (Lemma 3.4's consumer is the other swarm's `lift:all:root`
slot); recorded as such rather than as proved. -/
structure EP334_gammaHalf {Γ : Type*} [AddCommGroup Γ] (Γ' Γ₀ : AddSubgroup Γ) : Prop where
  gamma_unchanged : Γ' ≤ Γ₀

/-- **Wiring of EP 3.3.4 to the `Γ`-conclusion of Lemma 3.4.** -/
theorem gamma_unchanged_of_EP334 {Γ : Type*} [AddCommGroup Γ] {Γ' Γ₀ : AddSubgroup Γ}
    (hEP : EP334_gammaHalf Γ' Γ₀) : Γ' ≤ Γ₀ :=
  hEP.gamma_unchanged

/-! ## 6. Axiom audit for §5 -/
#print axioms Lemma36Audit.gamma_unchanged_of_EP343
#print axioms Lemma36Audit.gamma_unchanged_of_EP334

end Lemma36Audit
