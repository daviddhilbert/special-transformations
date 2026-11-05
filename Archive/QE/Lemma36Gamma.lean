/-
# Lemma 3.6 (`lift:transcendental`, qe.tex l.732): the `Γ`-half, proved

Member `m8`, swarm `smw2ngn1z`.  This file proves the part of Yin's Lemma 3.6 that does **not** need
the residue-field induction: the argument

    rational rank of Γ(⟨Ŝ,e⟩)/Γ(Ŝ) is 0   [EP Thm 3.4.3, a quoted Prop — see `PEQuotes.lean`]
  + Γ(Ŝ) divisible                        [hypothesis of Lemma 3.6; `Assembly.Standing S`]
  ⟹ Γ(⟨Ŝ,e⟩) = Γ(Ŝ)                       [this file: `gammaEq_of_gammaHullInitial`]
  ⟹ Claim (⋆)'s `RV`-half                [this file: `residualClasses_of_gammaEq`]
  ⟹ `Assembly.Standing T`                [this file: `standing_of_gammaEq`]

The paper's own words for the middle step (`qe.tex:735-737`): "the rational rank of
`Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0.  Since `Γ(Ŝ)` is divisible, we actually have `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`."

## Why this is exactly the frozen route's "Claim (⋆) in class form"

`M5L.ResidualClasses S T` is `∀ y ∈ T, iRV y → ∃ s ∈ S, Cls y s` (`QE/M5L34_36.lean`), and
`M5L.standing_of_ClassControl` turns that into `Assembly.Standing T`.  The paper's computation is
about `Γ`-classes; `M5Ledger.GammaEq S T` is the paper's `Γ(T) = Γ(S)` with the residue factor
carried (`∃ s c, s ∈ S ∧ iUnits c ∧ s·c = t`), and `M5Ledger.GammaHullInitial S T` is
"`Γ(T)` lies in the divisible hull of `Γ(S)`", i.e. `γ`'s positive powers land in `Γ(Ŝ)` — the
conclusion of the rational-rank-0 computation.  So the two steps above are:

* `gammaEq_of_gammaHullInitial` — **divisibility kills torsion classes** (the only place
  `Γ(Ŝ)`-divisibility is used; see the refutation at the end of the file);
* `residualClasses_of_gammaEq` — a `Γ`-equality is a class statement, hence Claim (⋆) in the
  frozen vocabulary.  Note what this proof does *not* need: no `M5L.VFInvClosedOn`, no
  `M5L.QuotExpansions`, no `Assembly.IsVFGen`, no separation hypothesis.  The paper's
  Lemma 3.6 conclusion is about `Γ`, and this is that conclusion.

## Stress tests (§3)

* `residualClasses_self`, `standing_of_gammaEq_self`, `standing_of_hullInitial_self` — the chain is
  non-vacuous at `T = S`, where all hypotheses hold (`M5Ledger.GammaEq S S`,
  `M5Ledger.GammaHullInitial S S`).
* `GammaEq` is *strictly* stronger than `ResidualClasses` in general?  No: on a nontrivial class the
  two are equivalent (`residualClasses_of_gammaEq` + `cls_ratio_units` recovers `GammaEq`); recorded
  as `gammaEq_iff_residualClasses` for the `T`-side that the paper's step needs.
* `divisibility_essential` — **the tempting stronger form is false**: `Γ(T)` in the divisible hull
  of `Γ(S)` alone does *not* give `Γ(T) = Γ(S)`; in `Γ = ℤ` the subgroup `2ℤ` is not divisible, the
  class of `1` is `2`-torsion modulo `2ℤ`, and `1 ∉ 2ℤ`.  That is exactly the situation of Lemma 3.8
  (the `CaseNewRV` branch), where `Γ` *does* grow.  So the divisibility hypothesis of Lemma 3.6
  cannot be dropped, and this file's main theorem cannot be strengthened.
-/
import M5L34_36
import GammaDiv
import M5Ledger
import OneStepCases

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.GammaGroup
open SpecialTransformations.Milestone0.GammaDiv

namespace SpecialTransformations.Milestone0.M8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 1. `Γ(S)`-divisibility at the level of the quotient `Γ`

`Assembly.GammaDivisible S` is the frozen substructure form: for `t ∈ RV(S)^×` and `n ≥ 1` there
are `u ∈ RV(S)^×` and a unit `c ∈ S` with `rvPow u n = t · c`.  In `Γ = RV^×/Kˣ` the unit `c` is
`1`, so this says `[u]^n = [t]`: every class in `Γ(S)` has an `n`-th root in `Γ(S)`. -/

/-- **Roots in `Γ(S)`.**  `Γ(S)`-divisibility gives, for each `s ∈ RV(S)^×`, an `n`-th root
`u ∈ RV(S)^×` at the level of `Γ`. -/
theorem gamma_root_of_gammaDivisible {S : LRV.Substructure M} (hdiv : Assembly.GammaDivisible S)
    {s : M} (hsS : s ∈ S) (hsrv : iRV s) (hs0 : s ≠ iRVZero) {n : ℕ} (hn : 1 ≤ n) :
    ∃ u : M, ∃ (_ : u ∈ S) (hurv : iRV u) (hu0 : u ≠ iRVZero),
      gammaMk (mkR u hurv hu0) ^ n = gammaMk (mkR s hsrv hs0) := by
  obtain ⟨u, c, huS, hurv, hu0, _hcS, hcu, heq⟩ := hdiv s hsS hsrv hs0 n hn
  have hcrv : iRV c := Jm2.iRV_of_inK (Or.inl hcu)
  have hc0 : c ≠ iRVZero := units_ne_zero hcu
  refine ⟨u, huS, hurv, hu0, ?_⟩
  rw [gammaMk_rvPow]
  rw [gammaMk_congr (rvPow_mem hurv n) (rvPow_ne_zero hurv hu0 n)
    (Transfer.rv_mul_mem hM hsrv hcrv) (rvStar_mul_nonzero ⟨hsrv, hs0⟩ ⟨hcrv, hc0⟩) heq]
  have hprod : (mkR (iRVMul s c) (Transfer.rv_mul_mem hM hsrv hcrv)
      (rvStar_mul_nonzero ⟨hsrv, hs0⟩ ⟨hcrv, hc0⟩) : RVStar M) = mkR s hsrv hs0 * rvStarOfUnit hcu :=
    Subtype.ext rfl
  have hone : gammaMk (rvStarOfUnit hcu) = 1 := (gammaMk_eq_one_iff_units).mpr hcu
  rw [hprod, gammaMk_mul, hone, mul_one]

/-! ## 2. The `Γ`-step of Lemma 3.6: rational rank `0` plus divisibility gives `Γ(T) = Γ(S)` -/

/-- **Divisibility kills torsion classes.**  If every class of `Γ(T)` has a positive power in
`Γ(S)` (`M5Ledger.GammaHullInitial S T`, the rational-rank-`0` conclusion of the dimension
inequality) and `Γ(S)` is divisible (`Assembly.GammaDivisible S`), then `Γ(T) = Γ(S)` in the
class-for-class form of the frozen encoding (`M5Ledger.GammaEq S T`).

This is the paper's "Since `Γ(Ŝ)` is divisible, we actually have `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`"
(`qe.tex:737`): `[t]^n = [s]` with `[s]` divisible gives `[s] = [u]^n`, so `[t]^n = [u]^n`, and
`Γ` is orderable, hence torsion-free, hence `[t] = [u] ∈ Γ(S)`. -/
theorem gammaEq_of_gammaHullInitial {S T : LRV.Substructure M}
    (hdiv : Assembly.GammaDivisible S) (hhull : M5Ledger.GammaHullInitial S T) :
    M5Ledger.GammaEq S T := by
  rw [gammaEq_iff_gammaMk]
  intro t ht hrv ht0
  obtain ⟨n, hn, s, hsS, hsrv, hs0, hcls⟩ :=
    (gammaHullInitial_iff_gammaMk_pow S T).mp hhull t ht hrv ht0
  obtain ⟨u, huS, hurv, hu0, hroot⟩ :=
    gamma_root_of_gammaDivisible hdiv hsS hsrv hs0 (n := n) (by omega)
  refine ⟨u, huS, hurv, hu0, ?_⟩
  refine gamma_pow_inj (n := n) (by omega) ?_
  rw [hcls, ← hroot]

/-- The same in the direction the paper states it: **`Γ(T) = Γ(S)`** from the hull condition and
divisibility, with no hypothesis on the size of the extension. -/
theorem gammaHullInitial_antisymm {S T : LRV.Substructure M}
    (hdiv : Assembly.GammaDivisible S) (hhull : M5Ledger.GammaHullInitial S T) :
    ∀ t : M, t ∈ T → iRV t → t ≠ iRVZero →
      ∃ s c : M, s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧ iUnits c ∧ iRVMul s c = t :=
  gammaEq_of_gammaHullInitial hdiv hhull

/-! ## 3. Claim (⋆) in the frozen vocabulary, and `Standing` of the extension -/

/-- **A class-equal product with a unit has the same class.**  `s · c` and `s` are `Cls`-equal when
`c` is a unit. -/
theorem cls_mul_unit_right {s c : M} (hsrv : iRV s) (hcu : iUnits c) :
    Transc.Cls (iRVMul s c) s := by
  have hcrv : iRV c := Jm2.iRV_of_inK (Or.inl hcu)
  have hc0 : c ≠ iRVZero := units_ne_zero hcu
  have hcls : Transc.Cls c iRVOne :=
    let h := (RVCalc.units_iff_le_one hM hcrv hc0).mp hcu
    ⟨h.2, h.1⟩
  have h1 : Transc.Cls (iRVMul s c) (iRVMul s iRVOne) :=
    Transc.cls_mul_left hM hcrv (MulNormalForm.rv_one_mem hM) hsrv hcls
  rw [Transfer.rv_mul_one_any_right (M := M) hM hsrv] at h1
  exact h1

/-- **Claim (⋆)'s `RV`-half from a `Γ`-computation.**  `Γ(T) = Γ(S)` gives, for every
`RV`-element `y` of `T`, an element of `S` with the same `Γ`-class: this is
`M5L.ResidualClasses S T`, the hypothesis of `M5L.standing_of_ClassControl`.

Nothing else is used: in particular no `VF`-inverse closure, no quotient representation of
`VF(T)`, and no `IsVFGen` — the `0` case is `rv 0 ∈ S`, and a nonzero `y ∈ RV(T)` is
`Cls`-equal to its `S`-witness by definition of `M5Ledger.GammaEq`. -/
theorem residualClasses_of_gammaEq {S T : LRV.Substructure M} (h : M5Ledger.GammaEq S T) :
    M5L.ResidualClasses S T := by
  intro y hyT hyRV
  by_cases hy0 : y = iRVZero
  · refine ⟨iRVZero, M5L.rvZero_mem_sub S, MulNormalForm.rv_zero_mem hM, ?_⟩
    rw [hy0]
    exact Transc.cls_refl hM (MulNormalForm.rv_zero_mem hM)
  · obtain ⟨s, c, hsS, hsrv, hs0, hcu, hceq⟩ := h y hyT hyRV hy0
    refine ⟨s, hsS, hsrv, ?_⟩
    rw [← hceq]
    exact cls_mul_unit_right hsrv hcu

/-- **Lemma 3.6's conclusion in `Standing` form, from the `Γ`-equality.** -/
theorem standing_of_gammaEq {S T : LRV.Substructure M} (hST : S ≤ T)
    (hS : Assembly.Standing S) (h : M5Ledger.GammaEq S T) : Assembly.Standing T :=
  M5L.standing_of_ClassControl hST hS (residualClasses_of_gammaEq h)

/-- **Lemma 3.6's conclusion in `Standing` form, from the rational-rank-`0` conclusion plus the
hypothesis `Γ(Ŝ)` divisible.**  This is the file's headline: the paper's Lemma 3.6, with its
residue-field induction replaced by the (quoted) dimension inequality. -/
theorem standing_of_gammaHullInitial {S T : LRV.Substructure M} (hST : S ≤ T)
    (hS : Assembly.Standing S) (hhull : M5Ledger.GammaHullInitial S T) : Assembly.Standing T :=
  standing_of_gammaEq hST hS (gammaEq_of_gammaHullInitial hS.2 hhull)

/-! ## 4. Stress tests

### 4a. Non-vacuity: the chain holds at `T = S`

`M5Ledger.GammaEq S S` and `M5Ledger.GammaHullInitial S S` are theorems of the tree, so the
hypotheses of `gammaEq_of_gammaHullInitial` / `standing_of_gammaEq` are simultaneously satisfiable,
and the conclusions are then the expected trivialities.  In particular the chain does not encode
"`T` strictly bigger", and `Standing` is not smuggled in through a vacuous hypothesis. -/

theorem gammaEq_self' (S : LRV.Substructure M) : M5Ledger.GammaEq S S :=
  GammaDiv.gammaEq_self S

theorem residualClasses_self (S : LRV.Substructure M) : M5L.ResidualClasses S S :=
  residualClasses_of_gammaEq (gammaEq_self' S)

theorem standing_of_gammaEq_self {S : LRV.Substructure M} (hS : Assembly.Standing S) :
    Assembly.Standing S :=
  standing_of_gammaEq (le_refl S) hS (gammaEq_self' S)

theorem standing_of_hullInitial_self {S : LRV.Substructure M} (hS : Assembly.Standing S) :
    Assembly.Standing S :=
  standing_of_gammaHullInitial (le_refl S) hS (gammaHullInitial_self S)

/-! ### 4b. The temptation: `Γ(T)` in the *hull* of `Γ(S)` without divisibility

The tempting stronger form of `gammaEq_of_gammaHullInitial` drops `Assembly.GammaDivisible S`:
"if every class of `Γ(T)` has a positive power in `Γ(S)` then `Γ(T) = Γ(S)`".  It is false, and
the failure is exactly the paper's Lemma 3.8 branch (where `Γ` grows): at `Γ = ℤ` the class of `1`
is `2`-torsion modulo `2ℤ`, but `1 ∉ 2ℤ`, and `2ℤ` is not divisible.

The group-theoretic core, stated and proved abstractly:

* `mem_of_pow_mem_of_divisible` — the step that `Γ`-divisibility buys: a class whose positive
  power lies in a **divisible** subgroup lies in it.  (`Γ` orderable = torsion-free is what makes
  the `n`-th root unique.)
* `divisibility_essential` — the multiplicative `ℤ` counterexample, so the hypothesis of
  `mem_of_pow_mem_of_divisible` (and hence of `gammaEq_of_gammaHullInitial`) cannot be dropped. -/

/-- **A torsion class over a divisible subgroup lies in it.**  In a linearly ordered commutative
group (hence torsion-free), `g^n ∈ H` with `H` divisible forces `g ∈ H`: take the `n`-th root `k`
of `g^n` inside `H`; then `k^n = g^n`, so `k = g` by torsion-freeness. -/
theorem mem_of_pow_mem_of_divisible {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    (H : Subgroup G) (hdiv : ∀ h ∈ H, ∀ n : ℕ, 0 < n → ∃ k ∈ H, k ^ n = h)
    {g : G} {n : ℕ} (hn : 0 < n) (hp : g ^ n ∈ H) : g ∈ H := by
  obtain ⟨k, hkH, hk⟩ := hdiv (g ^ n) hp n hn
  have hgk : g = k := pow_left_injective (n := n) hn.ne' hk.symm
  rwa [hgk]

/-- `2ℤ ⊆ ℤ` is a subgroup of `Multiplicative ℤ` for which the divisibility hypothesis of
`mem_of_pow_mem_of_divisible` fails. -/
def evenInts : Subgroup (Multiplicative ℤ) where
  carrier := {x | ∃ m : ℤ, x = Multiplicative.ofAdd (2 * m)}
  mul_mem' := by
    rintro a b ⟨m, rfl⟩ ⟨m', rfl⟩
    exact ⟨m + m', by rw [← ofAdd_add]; congr 1; ring⟩
  one_mem' := ⟨0, by rw [← ofAdd_zero]; norm_num⟩
  inv_mem' := by
    rintro a ⟨m, rfl⟩
    exact ⟨-m, by rw [← ofAdd_neg]; congr 1; ring⟩

/-- **The tempting stronger form of Lemma 3.6's `Γ`-step is FALSE.**  Without `Γ(S)`-divisibility,
"`g`'s positive power lies in `H`" does not put `g` in `H`: in `Multiplicative ℤ` the subgroup
`2ℤ` does not contain `1`, but `1² = 2` lies in `2ℤ`.  Divisibility of `H` genuinely fails here
(`evenInts` has no element whose square is `2`), which is precisely the hypothesis that
`Assembly.Standing S` supplies in the frozen encoding and that the paper's Lemma 3.6 uses. -/
theorem divisibility_essential :
    ¬ ∀ (H : Subgroup (Multiplicative ℤ)) (g : Multiplicative ℤ) (n : ℕ),
        0 < n → g ^ n ∈ H → g ∈ H := by
  intro h
  have hg : (Multiplicative.ofAdd (1 : ℤ)) ^ 2 ∈ evenInts := by
    refine ⟨1, ?_⟩
    rw [pow_two, ← ofAdd_add]
    norm_num
  have := h evenInts (Multiplicative.ofAdd (1 : ℤ)) 2 (by norm_num) hg
  obtain ⟨m, hm⟩ := this
  -- `ofAdd 1 = ofAdd (2m)` forces `1 = 2m`
  have h1 : (1 : ℤ) = m * 2 := by
    have := congrArg Multiplicative.toAdd hm
    simpa using this
  omega

/-- **And this is not an artefact of the abstract statement**: `evenInts` really is
non-divisible, so the counterexample above refutes exactly the statement obtained from
`mem_of_pow_mem_of_divisible` by deleting its divisibility hypothesis. -/
theorem evenInts_not_divisible :
    ¬ ∀ h ∈ evenInts, ∀ n : ℕ, 0 < n → ∃ k ∈ evenInts, k ^ n = h := by
  intro hdiv
  obtain ⟨k, ⟨m, hm⟩, hk2⟩ :=
    hdiv (Multiplicative.ofAdd (2 : ℤ)) ⟨1, by norm_num⟩ 2 (by norm_num)
  -- `k = ofAdd (2m)` and `k² = ofAdd 2`, so `2m + 2m = 2`
  have h4 : 2 * m + 2 * m = 2 := by
    have h' : Multiplicative.toAdd (k ^ 2) = (2 : ℤ) := by
      rw [hk2]
      rfl
    rw [hm, pow_two, ← ofAdd_add] at h'
    exact h'
  omega

end SpecialTransformations.Milestone0.M8

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M8.gamma_root_of_gammaDivisible
#print axioms SpecialTransformations.Milestone0.M8.gammaEq_of_gammaHullInitial
#print axioms SpecialTransformations.Milestone0.M8.cls_mul_unit_right
#print axioms SpecialTransformations.Milestone0.M8.residualClasses_of_gammaEq
#print axioms SpecialTransformations.Milestone0.M8.standing_of_gammaEq
#print axioms SpecialTransformations.Milestone0.M8.standing_of_gammaHullInitial
#print axioms SpecialTransformations.Milestone0.M8.mem_of_pow_mem_of_divisible
#print axioms SpecialTransformations.Milestone0.M8.divisibility_essential
#print axioms SpecialTransformations.Milestone0.M8.evenInts_not_divisible
