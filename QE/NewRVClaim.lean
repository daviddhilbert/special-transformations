/-
# Claim (⋆) for the *new-`rv`* case (Lemmas 3.7 / 3.8, `e:transc`, `lift:value:full`)

Member `m1`, swarm `smw2ngn1z`.  Reference: Yimu Yin, *Special transformations in algebraically
closed valued fields*, §3.1, `qe.tex` l. 733-816.

## The gap this file closes

`QE/M5L34_36.lean` §2 proves the paper's Claim (⋆) in `Γ`-class form for the **old-`rv`** case
(Lemmas 3.4 / 3.5 / 3.6, where `rv(e) ∈ RV(Ŝ)`): `M5L.ResidualClasses` says every `RV`-element of
the generated `T` is class-equal to a class *of an element of `S`*, i.e. `RV(⟨Ŝ,e⟩) ⊆ Γ(Ŝ)`.

The paper's other branch — Lemma 3.7 (`e:transc`) and Lemma 3.8 (`lift:value:full`),
`qe.tex` l. 733-816, where `e` is added with `rv(e) ∉ RV(Ŝ)` and `vv(e)` of infinite order modulo
`Γ(Ŝ)` — has a *different* conclusion:

> `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩`   (`qe.tex:816`)

i.e. the classes of the new substructure are the classes of `S` **times a power of `rv e`**, not
classes of `S`.  Nothing in the tree states that case in the frozen encoding: every
`ResidualClasses`-shaped lemma is the old-`rv` one (`M5L.ResidualClasses_of_VFGen`), and
`M5.OneStepRVNew` — the frozen slot for this branch — asks for more than Claim (⋆) (it demands
`Standing T`, i.e. a *divisible* `Γ(T)`, which forces the divisible hull of `Γ(S) + ℤ·vv(m)` into
`T` at the same step).  Also missing: `QE/Lemma37.lean`'s header lists "the second half of Lemma 3.7
(`Γ(⟨Ŝ,e⟩) = Γ(Ŝ) ⊕ ℤ·vv(e)`)" as not formalized — `ResidualClassesNew` below is that statement in
the frozen encoding's `Γ`-class vocabulary.

`L_RV` has **no inverse symbol on the `RV` sort** (`Milestone0/Encoding.lean`), so membership in the
group `⟨RV(S), rv e⟩` is written inverse-free by allowing *two* witnesses `s, t ∈ S ∩ VF`:

> `y · rv s · (rv e)^j` is in the same class as `rv t · (rv e)^k`

(`StarMem S e y`).  This is exactly `y ∈ ⟨RV(S), rv(e)⟩`: multiplying by `(rv e)^{-j}`, it says
`y ∈ ⟨RV(S)⟩ · (rv e)^{k-j}`, and conversely any `y` of that shape has such a pair.  Crucially, the
pair form needs **no inverse closure of `S`** (compare `M5L.VFInvClosedOn`, which
`M5L.ResidualClasses_of_VFGen` must assume and which `QE/OneStepCases.lean` flags as a
strengthening of the frozen slot): the quotient step below clears the denominator by *moving* the
top coefficient of `q` to the left-hand side instead of inverting it.

## What is proved

* `vfMul_mem_sub` — substructure closure on the `VF` sort (the tree had `vfAdd_mem_sub` only).
* `rvQuotExpansion_star` — **the quotient step of the new-`rv` case**: for `x ≠ 0` with
  `x·q = p`, `p = Σ_{i≤M} b_i e^i`, `q = Σ_{j≤N} c_j e^j` nonvanishing expansions over `S ∩ VF`,
  `vv(e)` of infinite order modulo `Γ(S)` (`M5L.Separated S e`), one has `StarMem S e (rv x)`.
  `M5L.cls_vsum_monomial` gives `rv p ~ rv(b_J)(rv e)^J` and `rv q ~ rv(c_L)(rv e)^L`; multiplying
  `rv x = rv p / rv q` by `rv(c_L)·(rv e)^L` gives the claim with witnesses `(c_L, b_J)`.
* `ResidualClassesNew_of_VFGen` — **Claim (⋆), new-`rv` branch, in class form**:
  `RV(T) ⊆ ⟨RV(S), rv e⟩ ∪ {rv 0}` for a `VF`-generated `T` whose `VF`-part is represented by
  quotients of expansions over `S`, from the paper's hypotheses of the case (`IsVFGen` is Remark 3.1,
  `QuotExpansions` is `qe.tex:645`).
* `ClaimStarNewRV` — the same as a single `∀`-statement, the shape a case hypothesis takes in
  `QE/OneStepCases.lean`.
* `starMem_self`, `not_starMem_rvZero`, `starMem_mul_rvpow`, `starMem_mono`,
  `residualClassesNew_top`, `not_separated_top` — the stress tests (§3, §5b).

## Stress tests, and the `⊤`-witness

* `residualClassesNew_top`: the *conclusion* holds at `S = T = ⊤` in every model.
* `not_separated_top`: the *hypothesis* `M5L.Separated S e` is **unsatisfiable at `S = ⊤`** for
  `e ≠ 0` (take `x = 1`, `y = e^k`).  So the `⊤`-witness test for the case hypotheses of Lemmas
  3.5-3.8 is necessarily negative: they are statements about substructures with room, and no
  satisfiability check of them can be run at `⊤`.
* `not_starMem_rvZero`: `StarMem` never contains `rv 0`, so the disjunct `y = rv 0` in
  `ResidualClassesNew` is *necessary* — the absorbing element has no class representative.
* `starMem_self`: `StarMem` contains `rv s` for every `s ∈ S ∩ VF`, `s ≠ 0`: the notion is inhabited
  on every substructure.
* `starMem_mul_rvpow`, `starMem_mono`: `StarMem` is closed under `(rv e)^ℕ` and monotone in `S`, as
  membership in a multiplicative set must be.
* The theorem does **not** assume `rv e ∈ S` (that is the old-`rv` case) nor `VFInvClosedOn S`.

## What this file does *not* do

The frozen `M5.OneStepRVNew` also demands `Standing T`, hence `GammaDivisible T`, whose witnesses
lie in `T`: that is the paper's separate hull construction (`qe.tex:795-816` and the phase-3
iteration in Proposition 3.9), not the class computation.  This file proves exactly Claim (⋆)'s
`RV`-containment, and leaves `Standing T` to the hull step, as the tree's docstrings already split
it.  The *symmetric* (image-side) statement needed by Lemma 3.6's last paragraph needs no extra
work here: the frozen theory `L_RV` is the same for `N`, so the same theorem instantiated at `N`
gives it.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import M5L34_36

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc
open SpecialTransformations.Milestone0.Transc

namespace SpecialTransformations.Milestone0
namespace M5LNewRV

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 0. Substructure closure on the `VF` sort -/

/-- `S` is closed under multiplication on the `VF` sort (the mate of `M5L.vfAdd_mem_sub`). -/
theorem vfMul_mem_sub (S : LRV.Substructure M) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    iVFMul x y ∈ S :=
  S.fun_mem Fn.vfMul ![x, y] (by
    intro i
    fin_cases i
    · simpa using hx
    · simpa using hy)

/-! ## 1. The class form of `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩`

`Γ = RV/Kˣ`, and `L_RV` has no inverse symbol on the `RV` sort, so membership in the group
`⟨RV(S), rv e⟩` is written with two `S`-witnesses and no inverse. -/

/-- **`y` lies in `⟨RV(S), rv(e)⟩`.**  There are `s, t ∈ S` of the `VF` sort, both nonzero, and
exponents `j, k`, with `y·rv(s)·(rv e)^j` in the same `Γ`-class as `rv(t)·(rv e)^k`.

Reading: multiply by `(rv e)^{-j}`; the statement is `y ∈ ⟨RV(S)⟩·(rv e)^{k-j}`, and since the pair
`(s,t)` ranges over `⟨RV(S)⟩ × ⟨RV(S)⟩` this is exactly `y ∈ ⟨RV(S), rv e⟩`.  The inverse-free form
is what the frozen encoding can state, and it needs no inverse closure of `S`. -/
def StarMem (S : LRV.Substructure M) (e y : M) : Prop :=
  ∃ (s t : M) (j k : ℕ), iVF s ∧ iVF t ∧ iRv s ∈ S ∧ iRv t ∈ S ∧
    s ≠ iVFZero ∧ t ≠ iVFZero ∧
    Transc.Cls (iRVMul y (iRVMul (iRv s) (rvpow (iRv e) j)))
      (iRVMul (iRv t) (rvpow (iRv e) k))

/-- **Claim (⋆)'s `RV`-containment for the new-`rv` case**: every `RV`-element of `T` lies in
`⟨RV(S), rv e⟩`, up to `rv 0` (which has no class representative, `not_starMem_rvZero`). -/
def ResidualClassesNew (S T : LRV.Substructure M) (e : M) : Prop :=
  ∀ y : M, y ∈ T → iRV y → StarMem S e y ∨ y = iRVZero

/-! ## 2. The quotient step of the new-`rv` case -/

/-- **The quotient step.**  Let `x ≠ 0` satisfy `x·q = p` where `p`, `q` are nonvanishing
expansions `Σ b_i e^i`, `Σ c_j e^j` with coefficients in `S ∩ VF`.  If `vv(e)` is of infinite
order modulo `Γ(S)` (`M5L.Separated S e`), then `rv(x) ∈ ⟨RV(S), rv e⟩`.

The paper's `qe.tex:805-816` gets this from `e:transc`: `rv(p)` is the class of one monomial
`rv(b_J)(rv e)^J` (`M5L.cls_vsum_monomial`) and `rv(q)` that of `rv(c_L)(rv e)^L`.  From
`rv(x)·rv(q) = rv(p)` and `rv(q) ~ rv(c_L)(rv e)^L` we get

  `rv(x)·rv(c_L)·(rv e)^L ~ rv(b_J)·(rv e)^J`,

which is `StarMem` with witnesses `(s,t) = (c_L, b_J)`: the top coefficient of `q` is moved to the
left-hand side instead of being inverted.  Hence no inverse closure of `S` is needed here. -/
theorem rvQuotExpansion_star {S : LRV.Substructure M}
    {e : M} (he : iVF e) (he0 : e ≠ iVFZero) (hsep : M5L.Separated S e)
    {b c : ℕ → M} (hb : ∀ i, iVF (b i)) (hbS : ∀ i, b i ∈ S) (hb0 : ∀ i, b i ≠ iVFZero)
    (hc : ∀ i, iVF (c i)) (hcS : ∀ i, c i ∈ S) (hc0 : ∀ i, c i ≠ iVFZero)
    {mM mN : ℕ} {x : M} (hx : iVF x) (hx0 : x ≠ iVFZero)
    (hq0 : vsum (fun i => iVFMul (c i) (vpow e i)) (mN + 1) ≠ iVFZero)
    (hxq : iVFMul x (vsum (fun i => iVFMul (c i) (vpow e i)) (mN + 1))
      = vsum (fun i => iVFMul (b i) (vpow e i)) (mM + 1)) :
    StarMem S e (iRv x) := by
  set p := vsum (fun i => iVFMul (b i) (vpow e i)) (mM + 1) with hp
  set q := vsum (fun i => iVFMul (c i) (vpow e i)) (mN + 1) with hq
  have hxq' : iVFMul x q = p := by rw [hp, hq]; exact hxq
  have hq0' : q ≠ iVFZero := by rw [hq]; exact hq0
  have hpVF : iVF p := by
    rw [hp]
    exact iVF_vsum hM (fun i => vf_mul_mem hM (hb i) (iVF_vpow hM he i)) (mM + 1)
  have hqVF : iVF q := by
    rw [hq]
    exact iVF_vsum hM (fun i => vf_mul_mem hM (hc i) (iVF_vpow hM he i)) (mN + 1)
  have hp0 : p ≠ iVFZero := by
    intro h
    have hpq : iVFMul x q = iVFZero := by rw [hxq']; exact h
    exact (vf_mul_ne_zero hM hx hqVF hx0 hq0') hpq
  -- `RV`-side facts
  have heRV : iRV (iRv e) := rv_mem hM he
  have hE : ∀ k : ℕ, iRV (rvpow (iRv e) k) := fun k => iRV_rvpow hM heRV k
  have hrvx : iRV (iRv x) := rv_mem hM hx
  have hrvq : iRV (iRv q) := rv_mem hM hqVF
  -- pairwise distinct monomial classes, from the case hypothesis
  have hdisB : ∀ i j : ℕ, i ≠ j →
      ¬ Transc.Cls (iRv (iVFMul (b i) (vpow e i))) (iRv (iVFMul (b j) (vpow e j))) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact M5L.separated_dis hM he he0 hb hbS hb0 hsep h
    · exact fun hc' => M5L.separated_dis hM he he0 hb hbS hb0 hsep h (Transc.cls_symm hc')
  have hdisC : ∀ i j : ℕ, i ≠ j →
      ¬ Transc.Cls (iRv (iVFMul (c i) (vpow e i))) (iRv (iVFMul (c j) (vpow e j))) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact M5L.separated_dis hM he he0 hc hcS hc0 hsep h
    · exact fun hc' => M5L.separated_dis hM he he0 hc hcS hc0 hsep h (Transc.cls_symm hc')
  -- the class of each expansion is the class of one of its monomials
  obtain ⟨J, -, hJcls⟩ := M5L.cls_vsum_monomial hM he he0 hb hb0 hdisB (m := mM)
  obtain ⟨L, -, hLcls⟩ := M5L.cls_vsum_monomial hM he he0 hc hc0 hdisC (m := mN)
  rw [← hp] at hJcls
  rw [← hq] at hLcls
  -- `rv p = rv x · rv q`
  have hpv : iRv p = iRVMul (iRv x) (iRv q) := by
    rw [← hxq', rv_mul_hom_of_model hM hx hqVF]
  rw [hpv] at hJcls
  -- move the `q`-denominator to the left: `rv x · rv(c L) · (rv e)^L ~ rv x · rv q`
  have hrs : iRV (iRv (c L)) := rv_mem hM (hc L)
  have huL : iRV (rvpow (iRv e) L) := hE L
  have h1 : Transc.Cls (iRVMul (iRv x) (iRv q))
      (iRVMul (iRv x) (iRVMul (iRv (c L)) (rvpow (iRv e) L))) :=
    Transc.cls_mul_left hM hrvq (rv_mul_mem hM hrs huL) hrvx hLcls
  refine ⟨c L, b J, L, J, hc L, hb J, M5L.rv_mem_sub S (hcS L), M5L.rv_mem_sub S (hbS J),
    hc0 L, hb0 J, ?_⟩
  exact Transc.cls_trans hM (rv_mul_mem hM hrvx (rv_mul_mem hM hrs huL))
    (rv_mul_mem hM hrvx hrvq) (rv_mul_mem hM (rv_mem hM (hb J)) (hE J))
    (Transc.cls_symm h1) hJcls

/-! ## 3. `StarMem` is the right notion: inhabited, excludes `rv 0`, closed under `(rv e)^ℕ` -/

/-- **Every nonzero `VF`-element of `S` gives a `StarMem`-element** (witnesses `(s,t) = (1,s)`,
`j = k = 0`): the new notion is inhabited on every substructure, so the conclusion of
`ResidualClassesNew_of_VFGen` is not vacuous. -/
theorem starMem_self {S : LRV.Substructure M} {e : M} (he : iVF e) {s : M}
    (hsVF : iVF s) (hsRV : iRv s ∈ S) (hs0 : s ≠ iVFZero) : StarMem S e (iRv s) := by
  have honeVF : iVF (iVFOne (M := M)) := vf_one_mem hM
  have honeRV : iRv (iVFOne (M := M)) ∈ S := by
    rw [rv_one hM]; exact M5L.rvOne_mem_sub S
  have hrs : iRV (iRv s) := rv_mem hM hsVF
  refine ⟨iVFOne, s, 0, 0, honeVF, hsVF, honeRV, hsRV, ?_, hs0, ?_⟩
  · intro h
    exact rv_one_ne_zero hM (by rw [← rv_one hM, h, rv_zero_eq hM])
  · have hone : iRV (iRVOne (M := M)) := rv_one_mem (M := M) hM
    have hone0 : iRVOne (M := M) ≠ iRVZero := rv_one_ne_zero hM
    have hz : rvpow (iRv e) 0 = iRVOne := rfl
    rw [rv_one hM, hz, rv_one_mul_of_model hM hone hone0]
    exact Transc.cls_refl hM (rv_mul_mem hM hrs hone)

/-- **`rv 0` is not a `StarMem`-element.**  `rv 0·rv s·(rv e)^j = rv 0` while
`rv t·(rv e)^k ≠ rv 0` for `t ≠ 0`, so the disjunct `y = rv 0` in `ResidualClassesNew` cannot be
dropped: Claim (⋆)'s `RV(⟨Ŝ,e⟩) ⊆ ⟨RV(Ŝ), rv e⟩` genuinely needs the absorbing element handled
separately in the frozen encoding. -/
theorem not_starMem_rvZero {S : LRV.Substructure M} {e : M} (he : iVF e) (he0 : e ≠ iVFZero) :
    ¬ StarMem S e iRVZero := by
  rintro ⟨s, t, j, k, hsVF, htVF, -, -, hs0, ht0, hcls⟩
  have heRV : iRV (iRv e) := rv_mem hM he
  have heRV0 : iRv e ≠ iRVZero := fun h => he0 (vf_eq_zero_of_rv_eq_zero hM he h)
  have hzero : ∀ a : M, iRV a → iRVMul iRVZero a = iRVZero := by
    intro a ha
    rw [rv_mul_comm_of_model hM (rv_zero_mem hM) ha]
    exact rv_mul_zero_right_of_model hM ha
  have hL : iRVMul iRVZero (iRVMul (iRv s) (rvpow (iRv e) j)) = iRVZero :=
    hzero (iRVMul (iRv s) (rvpow (iRv e) j)) (rv_mul_mem hM (rv_mem hM hsVF) (iRV_rvpow hM heRV j))
  have hR0 : iRVMul (iRv t) (rvpow (iRv e) k) ≠ iRVZero :=
    rv_mul_ne_zero hM (rv_mem hM htVF) (iRV_rvpow hM heRV k)
      (fun h => ht0 (vf_eq_zero_of_rv_eq_zero hM htVF h))
      (rvpow_ne_zero hM heRV heRV0 k)
  rw [hL] at hcls
  exact hR0 (le_infty_eq hM (rv_mul_mem hM (rv_mem hM htVF) (iRV_rvpow hM heRV k)) hcls.1)

/-- **`StarMem` is closed under multiplication by `(rv e)^m`** — the reading of `StarMem` as
membership in the multiplicatively closed set generated by `RV(S)` and `rv e`. -/
theorem starMem_mul_rvpow {S : LRV.Substructure M} {e : M} (he : iVF e) {y : M} (hy : iRV y)
    (h : StarMem S e y) (m : ℕ) : StarMem S e (iRVMul y (rvpow (iRv e) m)) := by
  obtain ⟨s, t, j, k, hsVF, htVF, hsRV, htRV, hs0, ht0, hcls⟩ := h
  have heRV : iRV (iRv e) := rv_mem hM he
  have hE : ∀ n : ℕ, iRV (rvpow (iRv e) n) := fun n => iRV_rvpow hM heRV n
  have hrs : iRV (iRv s) := rv_mem hM hsVF
  have hrt : iRV (iRv t) := rv_mem hM htVF
  refine ⟨s, t, j, k + m, hsVF, htVF, hsRV, htRV, hs0, ht0, ?_⟩
  have h1 : Transc.Cls (iRVMul (iRVMul y (iRVMul (iRv s) (rvpow (iRv e) j))) (rvpow (iRv e) m))
      (iRVMul (iRVMul (iRv t) (rvpow (iRv e) k)) (rvpow (iRv e) m)) :=
    Transc.cls_mul_right hM (rv_mul_mem hM hy (rv_mul_mem hM hrs (hE j)))
      (rv_mul_mem hM hrt (hE k)) (hE m) hcls
  have hL : iRVMul (iRVMul y (rvpow (iRv e) m)) (iRVMul (iRv s) (rvpow (iRv e) j))
      = iRVMul (iRVMul y (iRVMul (iRv s) (rvpow (iRv e) j))) (rvpow (iRv e) m) := by
    rw [rv_mul_assoc_of_model hM hy (hE m) (rv_mul_mem hM hrs (hE j))]
    rw [rv_mul_comm_of_model hM (hE m) (rv_mul_mem hM hrs (hE j))]
    rw [← rv_mul_assoc_of_model hM hy (rv_mul_mem hM hrs (hE j)) (hE m)]
  have hR : iRVMul (iRVMul (iRv t) (rvpow (iRv e) k)) (rvpow (iRv e) m)
      = iRVMul (iRv t) (rvpow (iRv e) (k + m)) := by
    rw [rv_mul_assoc_of_model hM hrt (hE k) (hE m), ← rvpow_add hM heRV k m]
  rw [hR] at h1
  rw [hL]
  exact h1

/-- **`StarMem` is monotone in `S`.** -/
theorem starMem_mono {S T : LRV.Substructure M} (hST : S ≤ T) {e y : M}
    (h : StarMem S e y) : StarMem T e y := by
  obtain ⟨s, t, j, k, hsVF, htVF, hsRV, htRV, hs0, ht0, hcls⟩ := h
  exact ⟨s, t, j, k, hsVF, htVF, hST hsRV, hST htRV, hs0, ht0, hcls⟩

/-! ## 4. Claim (⋆), new-`rv` branch -/

/-- **Claim (⋆), new-`rv` branch, in `Γ`-class form.**  If `T ⊇ S` is `VF`-generated, the `VF`-part
of `T` is represented by quotients of expansions in `e` over `S` (`M5L.QuotExpansions`), and
`vv(e)` is of infinite order modulo `Γ(S)` (`M5L.Separated`), then
`RV(T) ⊆ ⟨RV(S), rv e⟩ ∪ {rv 0}`.

This is the case-mate of `M5L.ResidualClasses_of_VFGen`: there the new class is *in* `Γ(S)`
(`rv(e) ∈ RV(Ŝ)`, Lemmas 3.4/3.5/3.6), here it is `rv e` times a class of `Γ(S)`
(Lemmas 3.7/3.8, `qe.tex:816`).  Note the hypothesis list: **no** `rv e ∈ S` and **no**
`M5L.VFInvClosedOn S`. -/
theorem ResidualClassesNew_of_VFGen {S T : LRV.Substructure M}
    {e : M} (he : iVF e) (he0 : e ≠ iVFZero)
    (hsep : M5L.Separated S e) (hVFGen : Assembly.IsVFGen T) (hquot : M5L.QuotExpansions S T e) :
    ResidualClassesNew S T e := by
  intro y hyT hyRV
  rcases hVFGen y hyT hyRV with ⟨x, hxT, hxVF, hxr⟩ | hz
  · by_cases hx0 : x = iVFZero
    · right
      rw [← hxr, hx0, rv_zero_eq hM]
    · left
      obtain ⟨b, c, mM, mN, hb, hbS, hb0, hc, hcS, hc0, hq0, hxq⟩ := hquot x hxT hxVF hx0
      obtain ⟨s, t, j, k, hsVF, htVF, hsRV, htRV, hs0, ht0, hcls⟩ :=
        rvQuotExpansion_star he he0 hsep hb hbS hb0 hc hcS hc0 hxVF hx0 hq0 hxq
      exact ⟨s, t, j, k, hsVF, htVF, hsRV, htRV, hs0, ht0, by rw [← hxr]; exact hcls⟩
  · exact Or.inr hz

/-- **Claim (⋆) for the new-`rv` branch, as a case hypothesis** in the shape of
`QE/OneStepCases.lean` (one `∀`-statement, no `M`/`N` gate). -/
def ClaimStarNewRV : Prop :=
  ∀ (S : LRV.Substructure M) (e : M), Assembly.KEqTop S → iVF e →
    e ≠ iVFZero → M5L.Separated S e → ∀ (T : LRV.Substructure M), S ≤ T →
      Assembly.IsVFGen T → M5L.QuotExpansions S T e → ResidualClassesNew S T e

theorem claimStarNewRV_holds : ClaimStarNewRV (M := M) :=
  fun S e _ he he0 hsep _ _ hVFGen hquot => ResidualClassesNew_of_VFGen he he0 hsep hVFGen hquot

/-! ## 5. Stress tests -/

/-- **The conclusion holds at `S = T = ⊤`** — a non-vacuity check for `ResidualClassesNew`: every
model of `ACVF` satisfies it uniformly in `e`, using `Assembly.RVeqRvVF_of_model`. -/
theorem residualClassesNew_top (e : M) (he : iVF e) :
    ResidualClassesNew (⊤ : LRV.Substructure M) (⊤ : LRV.Substructure M) e := by
  intro y _ hyRV
  by_cases hy0 : y = iRVZero
  · exact Or.inr hy0
  · rcases Assembly.RVeqRvVF_of_model (M := M) y hyRV with ⟨x, hxVF, hxr⟩ | hz
    · have hx0 : x ≠ iVFZero := by
        intro h
        exact hy0 (by rw [← hxr, h, rv_zero_eq hM])
      exact Or.inl (by
        rw [← hxr]
        exact starMem_self he hxVF (Substructure.mem_top _) hx0)
    · exact absurd hz hy0

/-! ## 5b. The `⊤`-witness of the case hypothesis is *negative* -/

/-- **The separation hypothesis of Lemmas 3.5/3.6/3.7/3.8 is unsatisfiable at `S = ⊤`.**

`M5L.Separated S e` says that no class `(rv e)^k · rv x` (`k > 0`, `x ∈ S ∩ VF`, `x ≠ 0`) is the
class of an element of `S ∩ VF`.  At `S = ⊤` take `x = 1` and `y = e^k`: then
`(rv e)^k · rv 1 = (rv e)^k = rv(e^k)`, so the hypothesis fails for every `e ≠ 0`.

Consequence for the swarm's stress-test ledger: the `⊤`-witness test for these case hypotheses comes
out **negative** — they hold only for substructures with room (the paper's `Ŝ = ⟨VF(S)⟩` with
`rv(e) ∉ RV(Ŝ)`), and no satisfiability check of them can be run at `S = ⊤`.  (The *conclusion*
`ResidualClassesNew` does hold at `⊤`: `residualClassesNew_top`.) -/
theorem not_separated_top {e : M} (he : iVF e) (he0 : e ≠ iVFZero) :
    ¬ M5L.Separated (⊤ : LRV.Substructure M) e := by
  intro hsep
  have heRV : iRV (iRv e) := rv_mem hM he
  have honeVF : iVF (iVFOne (M := M)) := vf_one_mem hM
  have hone0 : iVFOne (M := M) ≠ iVFZero := by
    intro h
    exact rv_one_ne_zero hM (by rw [← rv_one hM, h, rv_zero_eq hM])
  have hk : iVF (vpow e 1) := iVF_vpow hM he 1
  have hk0 : vpow e 1 ≠ iVFZero := vpow_ne_zero hM he he0 1
  refine hsep 1 (by norm_num) iVFOne (vpow e 1) honeVF hk (Substructure.mem_top _)
    (Substructure.mem_top _) hone0 hk0 ?_
  rw [rv_one hM, rv_vpow hM he 1, rv_mul_one_any_right hM (iRV_rvpow hM heRV 1)]
  exact Transc.cls_refl hM (iRV_rvpow hM heRV 1)

/-! ## 6. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M5LNewRV.vfMul_mem_sub
#print axioms SpecialTransformations.Milestone0.M5LNewRV.starMem_self
#print axioms SpecialTransformations.Milestone0.M5LNewRV.not_starMem_rvZero
#print axioms SpecialTransformations.Milestone0.M5LNewRV.starMem_mul_rvpow
#print axioms SpecialTransformations.Milestone0.M5LNewRV.starMem_mono
#print axioms SpecialTransformations.Milestone0.M5LNewRV.rvQuotExpansion_star
#print axioms SpecialTransformations.Milestone0.M5LNewRV.ResidualClassesNew_of_VFGen
#print axioms SpecialTransformations.Milestone0.M5LNewRV.claimStarNewRV_holds
#print axioms SpecialTransformations.Milestone0.M5LNewRV.residualClassesNew_top
#print axioms SpecialTransformations.Milestone0.M5LNewRV.not_separated_top

end M5LNewRV
end SpecialTransformations.Milestone0
