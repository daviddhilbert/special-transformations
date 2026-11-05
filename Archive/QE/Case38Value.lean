/-
# Direction e4, part 1: Lemma 3.8 (`lift:value:full`) at pair level, value side, from the paper's
own case hypotheses

Member `m4`, swarm `smw2jkpn4`.  Reference: Yimu Yin, *Special transformations in algebraically
closed valued fields*, §3.1, `qe.tex` l. 803:

> **Lemma 3.8** (`lift:value:full`).  If `K(Ŝ) = K(M)` and `Γ(Ŝ)` is divisible, then Claim (⋆)
> holds.

with, for `e ∈ VF(M)` such that `rv(e) ∈ RV(S) ∖ RV(Ŝ)`,

> **Claim (⋆)**.  `RV(⟨Ŝ, e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`, and the monomorphism `f ↾ Ŝ` extends to
> `f* : ⟨Ŝ, e⟩ → N` with `f*(rv e) = f(rv e)`.

## What already exists in the tree, and what this file adds

The two *algebraic halves* of Lemma 3.8 are proved in the tree, in the Mathlib `Valuation` language
(the `RV`-sort and the packaging of a value-preserving embedding as an `L_RV`-monomorphism are
Remark 3.1's job and are not part of either statement):

* **value half** (`QE/Lemma37_transcendental.lean`): `value_transfer`, `value_transfer_eq_one`,
  `value_transfer_adjoin`, `value_transfer_sum_of_divisible` — under `InfiniteOrderMod v e K`, i.e.
  "`vv(e)` is of infinite order modulo `Γ(Ŝ)`";
* **residue half** (`QE/Lemma38RV.lean`): `SameRV` (`v x = v y ∧ v (x - y) < v x`, which over a field
  is `x/y ∈ 1 + 𝔪`), `sameRV_aeval`, `sameRV_aeval_div`, `sameRV_mem_adjoin` — `rv`, not only `vv`,
  is preserved by `e ↦ d`.

What neither file does is start from the **paper's hypotheses of the case** and *derive* the
hypotheses of those theorems.  The paper's derivation is two lines:

> Since `Γ(Ŝ)` is divisible, clearly `vv(e)` is of infinite order modulo `Γ(Ŝ)` and hence `e` is
> transcendental over `VF(Ŝ)`.

The first clause is `YinLemma37.infiniteOrderMod_of_divisible` (already in the tree).  The second is
*not* in the tree (`QE/Lemma37_transcendental.lean`'s header records it as an unformalized
hypothesis, derived there from the dimension inequality of valuation theory), and it is where
`K(Ŝ) = K(M)` is used: `K(Ŝ) = K(M)` says `K(Ŝ)` is the residue field of a model of `ACVF`, hence
algebraically closed, so an element of `M` algebraic over `K(Ŝ)` already lies in `K(Ŝ)`; if moreover
`vv(e)` is not a value of `K(Ŝ)^×` then `e ∉ K(Ŝ)`, hence `e` is transcendental.  This file

* transcribes `K(Ŝ) = K(M)` as `IsAlgClosedInL K` and proves the derivation
  (`transcendental_of_isAlgClosedInL`);
* proves that an algebraically closed residue field has divisible value group
  (`divisibleValueGroup_of_isAlgClosed`), so the paper's two hypotheses of the case meet;
* packages the *whole* of Lemma 3.8's algebraic content from the paper's hypotheses
  (`lemma38_transfer`: transcendence of `e` **and** of its partner `d`, the polynomial value transfer,
  and the isometry of the value groups `Γ(⟨Ŝ,e⟩) → Γ(⟨f(Ŝ),d⟩)`), and the residue half
  (`lemma38_sameRV`);
* stress-tests the split: the residue half is *not* a consequence of the value half
  (`sameRV_not_implied_by_value`, a concrete machine-checked instance in `ℚ(X)` with the place at
  infinity where `v X = v (2X)` but `¬ SameRV v X (2X)`), and the hypothesis package is satisfiable
  (`isAlgClosedInL_top`, `divisibleValueGroup_of_isAlgClosed`, `sameRV_one_add` of
  `QE/Lemma38RV.lean` for same-`RV`-class distinct arguments).

## What this file does *not* do

The extension `f*` itself (`Claim (⋆)`'s second half) is a statement about the frozen `LRV`
encoding: an embedding of substructures.  At the frozen level the residue half is absorbed by
`Assembly.Standing S`'s `KEqTop` (`QE/Lemma38RV.lean`'s header, `M5L.mem_of_cls_mem`), and the
remaining obligation there is the realisation of the atomic type of the new element, i.e. the `N`-side
`saturation` — not value theory.  This file therefore proves the *value-theoretic* content of Lemma
3.8 and nothing that belongs to Remark 3.1 or to saturation.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import Lemma38RV

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Valuation

namespace YinLemma38Case

open YinLemma37 YinLemma38

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ## 1. `K(Ŝ) = K(M)`, and the transcendence it forces -/

/-- **`K(Ŝ) = K(M)`**: the residue field in play is the residue field of a model of `ACVF`, i.e. it
is algebraically closed *inside* `M` — every element of `L` algebraic over `K` already lies in `K`.
(`ACF` model completeness is quoted: `QE/KAlgClosedQuote.lean`.) -/
def IsAlgClosedInL (K : Subfield L) : Prop := ∀ x : L, IsAlgebraic ↥K x → x ∈ K

/-- The hypothesis is satisfiable (`K = L`). -/
theorem isAlgClosedInL_top : IsAlgClosedInL (⊤ : Subfield L) := fun _ _ => Subfield.mem_top _

/-- **`IsAlgClosed ↥K` implies `IsAlgClosedInL K`**: an element of `L` algebraic over an
algebraically closed `K` lies in `K` (the algebraic closure of `K` in `L` is `K`;
`IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`).  So `IsAlgClosedInL` is the faithful
transcription of `K(Ŝ) = K(M)` — the residue field is algebraically closed — and not a stronger
condition. -/
theorem isAlgClosedInL_of_isAlgClosed {K : Subfield L} (hK : IsAlgClosed ↥K) : IsAlgClosedInL K := by
  intro x hx
  have hint : IsIntegral ↥K x := isAlgebraic_iff_isIntegral.mp hx
  have halg : Algebra.IsAlgebraic ↥K ↥(IntermediateField.adjoin ↥K ({x} : Set L)) :=
    IntermediateField.isAlgebraic_adjoin (S := ({x} : Set L)) (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hint)
  haveI := halg
  have hbot : IntermediateField.adjoin ↥K ({x} : Set L) = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (k := ↥K) (K := L) _
  have hxE : x ∈ IntermediateField.adjoin ↥K ({x} : Set L) :=
    IntermediateField.subset_adjoin ↥K ({x} : Set L) (Set.mem_singleton x)
  rw [hbot, IntermediateField.mem_bot] at hxE
  obtain ⟨y, hy⟩ := hxE
  rw [← hy]
  exact y.2

/-- **An algebraically closed residue field has divisible value group.**  `Γ(Ŝ)` divisible is the
second hypothesis of Lemma 3.8; when `K` is algebraically closed it is automatic: `a ∈ K^×` has an
`n`-th root `b ∈ K`, and `v a = (v b)^n`. -/
theorem divisibleValueGroup_of_isAlgClosed (v : Valuation L Γ₀) (K : Subfield L)
    (hK : IsAlgClosed ↥K) : DivisibleValueGroup v K := by
  intro n hn a ha ha0
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (⟨a, ha⟩ : ↥K) hn
  have hbL : ((b : ↥K) : L) ^ n = a := by
    have := congrArg (Subtype.val) hb
    simpa using this
  have hb0 : ((b : ↥K) : L) ≠ 0 := by
    intro h
    apply ha0
    rw [← hbL, h]
    exact zero_pow hn.ne'
  refine ⟨((b : ↥K) : L), b.2, hb0, ?_⟩
  rw [← hbL, Valuation.map_pow]

/-- **`e` is transcendental over `K(Ŝ)`.**  The paper's "and hence `e` is transcendental over
`VF(Ŝ)`", from `K(Ŝ) = K(M)` (algebraically closed) and `vv(e) ∉ Γ(Ŝ)`.

The hypothesis `he0 : e ≠ 0` is not removable in this form: `0` is algebraic over everything and
`vv(0) = ∞` is not a value of `K^×`, so the paper's `rv(e) ∉ RV(Ŝ)` (which implies `e ≠ 0`) is part
of the hypothesis. -/
theorem transcendental_of_isAlgClosedInL (v : Valuation L Γ₀) {K : Subfield L}
    (hK : IsAlgClosedInL K) {e : L} (he0 : e ≠ 0)
    (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a) : Transcendental ↥K e := by
  intro halg
  exact hout e (hK e halg) he0 rfl

/-! ## 2. Lemma 3.8 at pair level, from the paper's hypotheses -/

section Pair

variable {v : Valuation L Γ₀} {K : Subfield L}
variable {L' : Type*} [Field L'] {v' : Valuation L' Γ₀} {K' : Subfield L'}

/-- **Lemma 3.8 (`lift:value:full`), value side, at pair level** — the algebraic content of Claim (⋆)
from the paper's own hypotheses:

* `hdiv`  : `Γ(Ŝ)` divisible;
* `hout`  : `vv(e) ∉ Γ(Ŝ)`, i.e. `vv(e)` is not the value of a nonzero element of `VF(Ŝ)` (the
  value-level part of `rv(e) ∉ RV(Ŝ)`);
* `hK`, `hK'` : `K(Ŝ) = K(M)` for `Ŝ` and for its image under `f` (algebraically closed);
* `σ`, `hσ` : the value-preserving isomorphism `VF(Ŝ) → f(VF(Ŝ))` induced by `f`;
* `hvde` : `v' d = v e`, which in the paper is `rv(d) = f(rv(e))` (`SameRV`/`rv` equality is
  stronger, and the residue half is `lemma38_sameRV` and `YinLemma38.sameRV_aeval_div`).

Conclusion: `e` and `d` are transcendental over their coefficient fields, corresponding polynomials
have the same value (`b ↦ b*`), and every element of `VF(⟨Ŝ,e⟩) = K(e)` has the same value as some
element of `K'(d)` — `e ↦ d` is an isometry of valued fields, i.e. `Γ(⟨Ŝ,e⟩) = Γ(⟨f(Ŝ),d⟩)` as
ordered groups. -/
theorem lemma38_transfer
    (σ : ↥K ≃+* ↥K')
    (hσ : ∀ a : ↥K, v' (((σ : ↥K →+* ↥K') a) : L') = v (((a : ↥K) : L)))
    (hdiv : DivisibleValueGroup v K) (hK : IsAlgClosedInL K) (hK' : IsAlgClosedInL K')
    {e : L} (he0 : e ≠ 0) (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a)
    {d : L'} (hd0 : d ≠ 0) (hvde : v' d = v e) :
    Transcendental ↥K e ∧ Transcendental ↥K' d ∧
      (∀ x : L, x ∈ IntermediateField.adjoin ↥K {e} →
        ∃ y : L', y ∈ IntermediateField.adjoin ↥K' {d} ∧ v x = v' y) ∧
      (∀ r : Polynomial ↥K, r ≠ 0 →
        v ((Polynomial.aeval e) r) = v' ((Polynomial.aeval d) (r.map (σ : ↥K →+* ↥K')))) := by
  have htrans : Transcendental ↥K e := transcendental_of_isAlgClosedInL v hK he0 hout
  -- `vv(d)` is not a value of `K'^×` either, because `σ` preserves values and `v' d = v e`
  have hout' : ∀ a : L', a ∈ K' → a ≠ 0 → v' d ≠ v' a := by
    intro a ha ha0 h
    obtain ⟨b, hb⟩ := σ.surjective (⟨a, ha⟩ : ↥K')
    have hbL : (((σ b : ↥K') : L')) = a := congrArg Subtype.val hb
    have hb0 : ((b : ↥K) : L) ≠ 0 := by
      intro h0
      apply ha0
      rw [← hbL, show b = 0 from Subtype.ext h0]
      simp
    have hvb : v (((b : ↥K) : L)) = v' a :=
      (hσ b).symm.trans (congrArg v' hbL)
    exact hout ((b : ↥K) : L) b.2 hb0 (hvde.symm.trans (h.trans hvb.symm))
  have htrans' : Transcendental ↥K' d := transcendental_of_isAlgClosedInL v' hK' hd0 hout'
  have hord : InfiniteOrderMod v e K := infiniteOrderMod_of_divisible hdiv hout
  refine ⟨htrans, htrans', ?_, ?_⟩
  · intro x hx
    exact value_transfer_adjoin σ hσ he0 hd0 hvde hord htrans htrans' hx
  · intro r hr
    exact value_transfer σ hσ he0 hd0 hvde hord htrans htrans' hr

/-- **Lemma 3.8 (`lift:value:full`), value side, in the paper's case**: `K(Ŝ) = K(M)` is
transcribed as `IsAlgClosed ↥K` (`hKal` gives both `IsAlgClosedInL` and divisibility of `Γ(Ŝ)`). -/
theorem lemma38_transfer_of_isAlgClosed
    (σ : ↥K ≃+* ↥K')
    (hσ : ∀ a : ↥K, v' (((σ : ↥K →+* ↥K') a) : L') = v (((a : ↥K) : L)))
    (hKal : IsAlgClosed ↥K) (hKal' : IsAlgClosed ↥K')
    {e : L} (he0 : e ≠ 0) (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a)
    {d : L'} (hd0 : d ≠ 0) (hvde : v' d = v e) :
    Transcendental ↥K e ∧ Transcendental ↥K' d ∧
      (∀ x : L, x ∈ IntermediateField.adjoin ↥K {e} →
        ∃ y : L', y ∈ IntermediateField.adjoin ↥K' {d} ∧ v x = v' y) ∧
      (∀ r : Polynomial ↥K, r ≠ 0 →
        v ((Polynomial.aeval e) r) = v' ((Polynomial.aeval d) (r.map (σ : ↥K →+* ↥K')))) :=
  lemma38_transfer σ hσ (divisibleValueGroup_of_isAlgClosed v K hKal)
    (isAlgClosedInL_of_isAlgClosed hKal) (isAlgClosedInL_of_isAlgClosed hKal') he0 hout hd0 hvde

end Pair

/-! ## 3. The residue half of Lemma 3.8, from the paper's hypotheses -/

/-- **Lemma 3.8's Claim (⋆) with `rv`, not only `vv`**: if `d` is in the same `RV`-class as `e`
(`YinLemma38.SameRV v e d`, which is `rv(d) = rv(e)` after `f` identifies `VF(Ŝ)` with `f(VF(Ŝ))`),
`Γ(Ŝ)` is divisible and `vv(e) ∉ Γ(Ŝ)`, then the polynomial transfer `e ↦ d` preserves `RV`-classes.
This is `YinLemma38.sameRV_aeval` with its infinite-order hypothesis derived from the case
hypotheses. -/
theorem lemma38_sameRV {v : Valuation L Γ₀} {K : Subfield L} (hdiv : DivisibleValueGroup v K)
    {e : L} (he0 : e ≠ 0) (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a)
    {d : L} (hsame : SameRV v e d) (htrans : Transcendental ↥K e) :
    ∀ r : Polynomial ↥K, r ≠ 0 → SameRV v ((Polynomial.aeval e) r) ((Polynomial.aeval d) r) :=
  fun r hr => sameRV_aeval (infiniteOrderMod_of_divisible hdiv hout) he0 hsame htrans hr

/-- The value projection of `lemma38_sameRV` — the value side follows from the residue side, and the
converse fails (`sameRV_not_implied_by_value`). -/
theorem lemma38_value_of_sameRV {v : Valuation L Γ₀} {K : Subfield L}
    (hdiv : DivisibleValueGroup v K) {e : L} (he0 : e ≠ 0)
    (hout : ∀ a : L, a ∈ K → a ≠ 0 → v e ≠ v a) {d : L} (hsame : SameRV v e d)
    (htrans : Transcendental ↥K e) {r : Polynomial ↥K} (hr : r ≠ 0) :
    v ((Polynomial.aeval e) r) = v ((Polynomial.aeval d) r) :=
  (lemma38_sameRV hdiv he0 hout hsame htrans r hr).1

/-! ## 4. Stress test: the residue half is *not* a consequence of the value half

Yin's Claim (⋆) asks for `rv`-control, not only for values.  The concrete instance below (`ℚ(X)` with
the place at infinity) shows that `SameRV` genuinely adds content: `X` and `2X` have the same value
(the place at infinity sees only the degree) but different residues, so `¬ SameRV v X (2X)` although
`v X = v (2X)`.  Hence `lemma38_sameRV` is not implied by `lemma38_transfer`'s polynomial value
transfer. -/

section Concrete

open RatFunc

/-- The place at infinity on `ℚ(X)`. -/
noncomputable def inftyVQ : Valuation (RatFunc ℚ) (WithZero (Multiplicative ℤ)) := by
  classical exact RatFunc.inftyValuation ℚ

/-- The place at infinity is trivial on the constants. -/
theorem inftyVQ_const (q : ℚ) (hq : q ≠ 0) :
    inftyVQ (algebraMap ℚ (RatFunc ℚ) q) = 1 := by
  classical
  have h1 : (algebraMap ℚ (RatFunc ℚ)) q =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C q) := by
    rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ)]
    simp
  rw [h1]
  show RatFunc.inftyValuation ℚ (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C q)) = 1
  rw [RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation.polynomial (F := ℚ) (p := Polynomial.C q) (by simpa using hq)]
  simp

/-- The value of the constant `2`. -/
theorem inftyVQ_two : inftyVQ (2 : RatFunc ℚ) = 1 := by
  have h2 : (2 : RatFunc ℚ) = algebraMap ℚ (RatFunc ℚ) (2 : ℚ) := by simp
  rw [h2]
  exact inftyVQ_const 2 (by norm_num)

/-- **The value half does not give the residue half.**  In `ℚ(X)` with the place at infinity,
`v X = v (2X)` (both have degree `1`) but `X` and `2X` are *not* in the same `RV`-class: they differ
by the unit `1 - 2 = -1`, which does not lie in `1 + 𝔪`. -/
theorem sameRV_not_implied_by_value :
    ∃ (v : Valuation (RatFunc ℚ) (WithZero (Multiplicative ℤ))) (x y : RatFunc ℚ),
      v x = v y ∧ ¬ SameRV v x y := by
  classical
  refine ⟨inftyVQ, RatFunc.X, (2 : RatFunc ℚ) * RatFunc.X, ?_, ?_⟩
  · rw [map_mul, inftyVQ_two, one_mul]
  · intro h
    have hsub : RatFunc.X - (2 : RatFunc ℚ) * RatFunc.X = -(RatFunc.X) := by ring
    have h2 : inftyVQ (RatFunc.X - (2 : RatFunc ℚ) * RatFunc.X) = inftyVQ RatFunc.X := by
      rw [hsub, Valuation.map_neg]
    exact absurd h.2 (by rw [h2]; exact lt_irrefl _)

end Concrete

end YinLemma38Case

/-! ## Axiom audit -/

#print axioms YinLemma38Case.isAlgClosedInL_top
#print axioms YinLemma38Case.divisibleValueGroup_of_isAlgClosed
#print axioms YinLemma38Case.transcendental_of_isAlgClosedInL
#print axioms YinLemma38Case.lemma38_transfer
#print axioms YinLemma38Case.lemma38_sameRV
#print axioms YinLemma38Case.isAlgClosedInL_of_isAlgClosed
#print axioms YinLemma38Case.lemma38_transfer_of_isAlgClosed
#print axioms YinLemma38Case.inftyVQ_const
#print axioms YinLemma38Case.inftyVQ_two
#print axioms YinLemma38Case.sameRV_not_implied_by_value
