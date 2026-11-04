/-
# Lemma 3.6 (`lift:transcendental`) in the frozen encoding, *unit* branch, without EP 3.4.3

Direction r5, swarm `smw2ox51x`, member m3.

The paper's Lemma 3.6 (`qe.tex:732`) is about `e ∈ U(M)` with `rv(e)` transcendental over
`K(Ŝ)`.  `QE/PEQuotes.lean` wires the `Γ`-step of that lemma through Engler–Prestel Thm 3.4.3
(the dimension inequality, a *quoted* Prop).  `QE/UnitTranscend.lean` proves the same step
elementary in the Mathlib valuation setting: a unit with residue transcendental has no residue
cancellation in its expansions, hence the value of an expansion is the value of one of its
coefficients.  This file transports that argument to the frozen encoding and thereby removes
EP 3.4.3 from Lemma 3.6 in the frozen route.

## Two points of substance

**(1) The tree's `M5L.Separated` cannot be the hypothesis of the unit branch.**
`QE/Case34Slot.lean`/`QE/Lemma36Audit.lean` record that units are never `Separated`; `§1` below
machine-checks it in the form needed here: `iUnits (rv e) → ¬ M5L.Separated S e`
(`not_separated_of_units`).  So the "separated" slot of `QE/OneStepCases.lean` and the unit
branch of Lemma 3.6 are *disjoint*, and the separated machinery (`Transc.e_transc`,
`M5L.ResidualClasses_of_VFGen`) does not apply to Lemma 3.6.  The correct unit-branch hypothesis
is residue transcendence, which is what this file uses.

**(2) The unit branch's value computation, at the frozen level.**  The frozen encoding has no
residue-field *addition* on integral non-units (`Axioms.kAddLink` compares `kAdd` with `rv(x+y)`
only at units), so the cancellation analysis is stated over coefficients whose residue is a
residue-field element (`pInKof`), and — as in the paper — after normalising by a coefficient of
maximal value.  The hypothesis that carries the mathematical content is
`ExpansionValBase` (§3): *the value class of a nonzero expansion is the value class of one of
its coefficients*, which is exactly the paper's `vv(b) = min_i vv(b_i e^i)` (`qe.tex:756`) for
the unit case.  §3 derives `M5L.ResidualClasses`, `M5Ledger.GammaHullInitial` and
`Assembly.Standing` for `⟨Ŝ,e⟩` from it; §4 shows it holds in the pairwise-distinct regime (so
it is not vacuous), and §5 isolates the exact open bridge (`RVTrans ⇒ ExpansionValBase`).
-/
import PEQuotes
import Lemma36Statement
import ValueGroupBridge
import UnitTranscend

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.RVCalc
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Milestone0.M8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 0. Bookkeeping: the constants lie in every substructure; units are one `Cls`-class -/

theorem vfOne_mem_sub (S : LRV.Substructure M) : Transfer.iVFOne (M := M) ∈ S :=
  S.fun_mem Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)

theorem vfZero_mem_sub (S : LRV.Substructure M) : Transfer.iVFZero (M := M) ∈ S :=
  S.fun_mem Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)

/-- `S` is closed under multiplication on the `VF` sort. -/
theorem vfMul_mem_sub (S : LRV.Substructure M) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    iVFMul x y ∈ S :=
  S.fun_mem Fn.vfMul ![x, y] (by
    intro i
    fin_cases i
    · simpa using hx
    · simpa using hy)

/-- Every unit of `RV` is `Cls`-equal to `1`: `Kˣ` is the class of `1` (`leClassOne`). -/
theorem cls_one_of_units {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) (hau : iUnits a) :
    Transc.Cls a iRVOne := by
  obtain ⟨h1, h2⟩ := (units_iff_le_one hM ha ha0).1 hau
  exact ⟨h2, h1⟩

/-- Two units are `Cls`-equal. -/
theorem cls_of_units {a b : M} (ha : iRV a) (hb : iRV b) (ha0 : a ≠ iRVZero)
    (hb0 : b ≠ iRVZero) (hau : iUnits a) (hbu : iUnits b) : Transc.Cls a b := by
  have h1 := (units_iff_le_one hM ha ha0).1 hau
  have h2 := (units_iff_le_one hM hb hb0).1 hbu
  have hone : iRV (iRVOne (M := M)) := rv_one_mem (M := M) hM
  exact ⟨le_trans_rv hM ha hone hb h1.2 h2.1, le_trans_rv hM hb hone ha h2.2 h1.1⟩

/-- `rv (e)` is a residue-field element when `e` is a unit: `iUnits` implies the `RV` sort. -/
theorem rv_mem_of_units {e : M} (h : iUnits (iRv e)) : iRV (iRv e) :=
  Transfer.iRV_of_inK hM (Or.inl h)

/-! ## 1. A unit is never `Separated` — correcting the hypothesis set of the unit branch -/

/-- `Transc.rvpow ε 1 = ε`. -/
theorem transc_rvpow_one {ε : M} (hε : iRV ε) : Transc.rvpow ε 1 = ε := by
  show iRVMul iRVOne ε = ε
  exact rv_mul_one_any hM hε

/-- `Assembly.rvPow ε 1 = ε`. -/
theorem assembly_rvPow_one {ε : M} (hε : iRV ε) : Assembly.rvPow ε 1 = ε := by
  show iRVMul iRVOne ε = ε
  exact rv_mul_one_any hM hε

/-- **A unit is never `M5L.Separated`.**  `Separated S e` says that no class of `rv(e)^k · rv(x)`
(`k > 0`, `x ∈ S ∩ VF` nonzero) is a class of an element of `S`.  Take `k = 1` and
`x = y = 1`: `rv(e) · rv(1)` and `rv(1)` are both units, hence `Cls`-equal.

This is the machine-checked reason why the "separated" slot `CaseSeparated` of
`QE/OneStepCases.lean` is *not* the branch that Lemma 3.6 feeds: the paper's Lemma 3.6 has
`e ∈ U(M)`.  (It is also why `QE/Case34Slot.lean`'s attribution facts say `CaseSeparated` is the
value-growth regime only.) -/
theorem not_separated_of_units {S : LRV.Substructure M} {e : M} (hunit : iUnits (iRv e)) :
    ¬ M5L.Separated S e := by
  intro hsep
  have hε : iRV (iRv e) := rv_mem_of_units hunit
  have hε0 : iRv e ≠ iRVZero := GammaGroup.units_ne_zero hunit
  have hone : iVF (Transfer.iVFOne (M := M)) := vf_one_mem (M := M) hM
  have hrv_one : iRv (Transfer.iVFOne (M := M)) = iRVOne := rv_one hM
  have hcls : Transc.Cls (iRVMul (Transc.rvpow (iRv e) 1) (iRv (Transfer.iVFOne (M := M))))
      (iRv (Transfer.iVFOne (M := M))) := by
    rw [hrv_one, transc_rvpow_one hε, rv_mul_one_any_right hM hε]
    exact cls_of_units hε (rv_one_mem (M := M) hM) hε0 (rv_one_ne_zero hM) hunit
      (StandingTree.rv_one_units (M := M))
  exact hsep 1 (by norm_num) Transfer.iVFOne Transfer.iVFOne hone hone (vfOne_mem_sub S) (vfOne_mem_sub S)
    (fun h => RVCalc.vf_zero_ne_one hM h.symm) (fun h => RVCalc.vf_zero_ne_one hM h.symm) hcls

/-- The contrapositive form, as a consumer will want it: `Separated S e` forces `e` to be a
non-unit.  So the value-growth regime is disjoint from Lemma 3.6's hypothesis `e ∈ U(M)`. -/
theorem not_units_of_separated {S : LRV.Substructure M} {e : M} (hsep : M5L.Separated S e) :
    ¬ iUnits (iRv e) :=
  fun h => not_separated_of_units h hsep

/-! ## 2. `ResidualClasses` is a `GammaHullInitial` — the class form implies the hull form

`M5Ledger.GammaHullInitial S T` (the conclusion `QE/Lemma36Gamma.gammaEq_of_gammaHullInitial`
consumes) asks for a positive exponent `n` with `rvPow t n = s · c`, `c` a unit.  If every class
of `T`'s `RV` is the class of an element of `S`, then `n = 1` works: two `Cls`-equal `RV`
elements differ by a unit (`M5L.cls_ratio_units`). -/

theorem gammaHullInitial_of_ResidualClasses {S T : LRV.Substructure M}
    (h : M5L.ResidualClasses S T) : M5Ledger.GammaHullInitial S T := by
  intro t ht hrv ht0
  obtain ⟨s, hsS, hsrv, hcls⟩ := h t ht hrv
  by_cases hs0 : s = iRVZero
  · rw [hs0] at hcls
    exact absurd (le_infty_eq hM hrv hcls.2) ht0
  · obtain ⟨c, hcrv, hcu, hct⟩ := M5L.cls_ratio_units hM hrv hsrv hcls hs0
    refine ⟨1, s, c, by norm_num, hsS, hsrv, hs0, hcu, ?_⟩
    rw [hct]
    exact assembly_rvPow_one (rv_mul_mem hM hsrv hcrv)

/-- Lemma 3.6's conclusion in `Standing` form, from the class form only. -/
theorem standing_of_ResidualClasses {S T : LRV.Substructure M} (hST : S ≤ T)
    (hS : Assembly.Standing S) (h : M5L.ResidualClasses S T) : Assembly.Standing T :=
  standing_of_gammaEq hST hS (gammaEq_of_gammaHullInitial hS.2
    (gammaHullInitial_of_ResidualClasses h))


/-! ## 3. `Cls`-calculus additions: congruence for products, units are `Cls`-invisible -/

/-- `Cls` is a congruence for `×`. -/
theorem cls_mul_cls {a b c d : M} (ha : iRV a) (hb : iRV b) (hc : iRV c) (hd : iRV d)
    (hab : Transc.Cls a b) (hcd : Transc.Cls c d) :
    Transc.Cls (iRVMul a c) (iRVMul b d) := by
  have h1 : Transc.Cls (iRVMul a c) (iRVMul b c) := Transc.cls_mul_right hM ha hb hc hab
  have h2 : Transc.Cls (iRVMul b c) (iRVMul b d) := Transc.cls_mul_left hM hc hd hb hcd
  exact Transc.cls_trans hM (rv_mul_mem hM ha hc) (rv_mul_mem hM hb hc) (rv_mul_mem hM hb hd) h1 h2

/-- An equality of `RV`-elements is a `Cls`-equality. -/
theorem cls_of_eq {a b : M} (h : a = b) (ha : iRV a) : Transc.Cls a b := by
  subst h
  exact Transc.cls_refl hM ha

/-- Transitivity with the `iRV` side conditions in the order of the `Cls` hypotheses. -/
theorem cls_trans' {a b c : M} (hab : Transc.Cls a b) (hbc : Transc.Cls b c)
    (ha : iRV a) (hb : iRV b) (hc : iRV c) : Transc.Cls a c :=
  Transc.cls_trans hM ha hb hc hab hbc

/-- Multiplying by a unit does not move the `Γ`-class (the unit is `Cls`-equal to `1`). -/
theorem cls_mul_unit_right_rv {a u : M} (ha : iRV a) (hu : iRV u) (hu0 : u ≠ iRVZero)
    (hun : iUnits u) : Transc.Cls (iRVMul a u) a := by
  have h1 : Transc.Cls (iRVMul a u) (iRVMul a iRVOne) :=
    Transc.cls_mul_left hM hu (rv_one_mem (M := M) hM) ha (cls_one_of_units hu hu0 hun)
  rw [rv_mul_one_any_right hM ha] at h1
  exact h1

/-- Multiplying by a unit on the left does not move the `Γ`-class. -/
theorem cls_mul_unit_left_rv {a u : M} (ha : iRV a) (hu : iRV u) (hu0 : u ≠ iRVZero)
    (hun : iUnits u) : Transc.Cls (iRVMul u a) a := by
  rw [rv_mul_comm_of_model hM hu ha]
  exact cls_mul_unit_right_rv ha hu hu0 hun

/-- `iRVMul u v ≠ 0` for nonzero `u`, `v` — a local copy to keep the argument order explicit. -/
theorem rv_mul_ne_zero_from {u v : M} (hu : iRV u) (hv : iRV v) (hu0 : u ≠ iRVZero)
    (hv0 : v ≠ iRVZero) : iRVMul u v ≠ iRVZero :=
  Transc.rv_mul_ne_zero hM hu hv hu0 hv0

/-- A unit times a unit is `Cls`-equal to `1`. -/
theorem cls_one_of_units_mul {u v : M} (hu : iRV u) (hv : iRV v) (hu0 : u ≠ iRVZero)
    (hv0 : v ≠ iRVZero) (huu : iUnits u) (huv : iUnits v) :
    Transc.Cls (iRVMul u v) iRVOne :=
  cls_one_of_units (rv_mul_mem hM hu hv) (rv_mul_ne_zero_from hu hv hu0 hv0)
    (GammaGroup.units_mul huu huv)

/-! ## 4. The value computation of Lemma 3.6 in the unit branch -/

/-- **Lemma 3.6/3.7's value computation, in monomial form**: the value class of a nonzero expansion
`Σ_{i≤m} b_i e^i` is the value class of one of its monomials.

This is the paper's `vv(b) = min_i vv(b_i e^i)` with the `min` reduced to "some `j` attains it", and
it is the hypothesis the frozen route actually needs.  It is *regime-independent*: §6 proves it in
the separated regime from `M5L.Separated` alone (so it is not vacuous), and in the unit regime it is
the content of `QE/UnitTranscend.val_sum_eq_one` (§7 isolates the bridge). -/
def ExpansionValMin (S : LRV.Substructure M) (e : M) : Prop :=
  ∀ (b : ℕ → M) (m : ℕ), iVF e → (∀ i, iVF (b i)) → (∀ i, b i ∈ S) →
    (∀ i, b i ≠ Transfer.iVFZero) →
    Transc.vsum (fun i => iVFMul (b i) (Transc.vpow e i)) (m + 1) ≠ Transfer.iVFZero →
    ∃ j, j ≤ m ∧
      Transc.Cls (iRv (Transc.vsum (fun i => iVFMul (b i) (Transc.vpow e i)) (m + 1)))
        (iRv (iVFMul (b j) (Transc.vpow e j)))

/-- **The value of a nonzero expansion is the value class of one of its coefficients.**

This is exactly the paper's conclusion of the `Γ`-step of Lemma 3.6 (`qe.tex:756`),
`vv(Σ_{i≤m} b_i e^i) = min_i vv(b_i e^i)`, in the form the frozen encoding can state: the value
class of the sum is the value class of *some* coefficient (the existence of the minimum is the
content; the paper's `min` identifies which one).

In the unit branch (`iUnits (rv e)`) this is *not* the tree's `M5L.Separated` regime: all
monomials have the same value as their coefficients, so the tree's `Transc.e_transc` no-cancellation
argument (which needs pairwise distinct monomial classes) does not apply, and the mathematical
content is residue transcendence (`UnitTranscend.val_sum_eq_one`).  §5 isolates exactly the missing
bridge; §6 shows the statement is *satisfiable* (it holds in the pairwise-distinct regime), so this
is not a vacuous hypothesis. -/
def ExpansionValBase (S : LRV.Substructure M) (e : M) : Prop :=
  ∀ (b : ℕ → M) (m : ℕ), iVF e → (∀ i, iVF (b i)) → (∀ i, b i ∈ S) →
    (∀ i, b i ≠ Transfer.iVFZero) →
    Transc.vsum (fun i => iVFMul (b i) (Transc.vpow e i)) (m + 1) ≠ Transfer.iVFZero →
    ∃ j, j ≤ m ∧
      Transc.Cls (iRv (Transc.vsum (fun i => iVFMul (b i) (Transc.vpow e i)) (m + 1)))
        (iRv (b j))

/-- Powers of a unit are units (`Kˣ` is a subgroup). -/
theorem units_rvpow {ε : M} (hε : iUnits ε) : ∀ n, iUnits (Transc.rvpow ε n)
  | 0 => StandingTree.rv_one_units (M := M)
  | (n + 1) => GammaGroup.units_mul (units_rvpow hε n) hε

/-- **Monomial form ⇒ coefficient form, in the unit branch.**  If `e` is a unit then every monomial
`b_j e^j` has the value class of `b_j` (`(rv e)^j` is a unit), so the paper's min formula gives the
coefficient form the quotient argument needs. -/
theorem expansionValBase_of_min {S : LRV.Substructure M} {e : M}
    (hmin : ExpansionValMin (M := M) S e) (heu : iUnits (iRv e)) :
    ExpansionValBase (M := M) S e := by
  intro b m he hb hbS hb0 hP0
  obtain ⟨j, hj, hcls⟩ := hmin b m he hb hbS hb0 hP0
  have hε : iRV (iRv e) := rv_mem_of_units heu
  have hε0 : iRv e ≠ iRVZero := GammaGroup.units_ne_zero heu
  have hbRV : iRV (iRv (b j)) := rv_mem hM (hb j)
  have hεjRV : iRV (Transc.rvpow (iRv e) j) := Transc.iRV_rvpow hM hε j
  have hεj : Transc.Cls (iRVMul (iRv (b j)) (Transc.rvpow (iRv e) j)) (iRv (b j)) :=
    cls_mul_unit_right_rv hbRV hεjRV
      (Transc.rvpow_ne_zero hM hε hε0 j) (units_rvpow heu j)
  have hmono : iRv (iVFMul (b j) (Transc.vpow e j))
      = iRVMul (iRv (b j)) (Transc.rvpow (iRv e) j) :=
    Transc.rv_monomial hM he hb j
  exact ⟨j, hj, cls_trans' hcls (by rw [hmono]; exact hεj)
    (rv_mem hM (Transc.iVF_vsum hM (fun i => vf_mul_mem hM (hb i) (Transc.iVF_vpow hM he i)) (m + 1)))
    (rv_mem hM (vf_mul_mem hM (hb j) (Transc.iVF_vpow hM he j))) hbRV⟩

/-- `iRv` of a nonzero `VF`-element is not `rv 0`. -/
theorem rv_ne_zero_of_vf_ne_zero {x : M} (hx : iVF x) (hx0 : x ≠ Transfer.iVFZero) :
    iRv x ≠ iRVZero :=
  fun h => hx0 (vf_eq_zero_of_rv_eq_zero hM hx h)

/-- **The `VF`-part of Claim (⋆) in the unit branch.**  Every nonzero `VF`-element of `T` has the
value class of a nonzero `VF`-element of `S`, given
`QuotExpansions` (every `VF`-element of `T` is a quotient of expansions), the value computation
`ExpansionValBase`, and inverse-closure of `S`'s `VF`-classes (`M5L.VFInvClosedOn`, which the paper
gets for free from `Ŝ = ⟨VF(S)⟩` being a field). -/
theorem vfPartClasses_of_expansion {S T : LRV.Substructure M} {e : M}
    (hbase : ExpansionValBase (M := M) S e) (hquot : M5L.QuotExpansions S T e)
    (hfinv : M5L.VFInvClosedOn S) (he : iVF e) :
    ∀ x : M, x ∈ T → iVF x → x ≠ Transfer.iVFZero →
      ∃ s : M, s ∈ S ∧ iRV s ∧ Transc.Cls (iRv x) s := by
  intro x hxT hxVF hx0
  obtain ⟨b, c, mM, mN, hb, hbS, hb0, hc, hcS, hc0, hQ0, hxq⟩ := hquot x hxT hxVF hx0
  set P := Transc.vsum (fun i => iVFMul (b i) (Transc.vpow e i)) (mM + 1) with hPdef
  set Q := Transc.vsum (fun i => iVFMul (c i) (Transc.vpow e i)) (mN + 1) with hQdef
  have hPF : iVF P :=
    Transc.iVF_vsum hM (fun i => vf_mul_mem hM (hb i) (Transc.iVF_vpow hM he i)) (mM + 1)
  have hQF : iVF Q :=
    Transc.iVF_vsum hM (fun i => vf_mul_mem hM (hc i) (Transc.iVF_vpow hM he i)) (mN + 1)
  have hP0 : P ≠ Transfer.iVFZero := by
    intro h
    exact Transc.vf_mul_ne_zero hM hxVF hQF hx0 hQ0 (by rw [hxq]; exact h)
  -- the value computation for both expansions
  obtain ⟨i₀, hi₀, hclsP⟩ := hbase b mM he hb hbS hb0 hP0
  obtain ⟨j₀, hj₀, hclsQ⟩ := hbase c mN he hc hcS hc0 hQ0
  -- the two witnesses and the units relating them to `rv P`, `rv Q`
  have hbiRV : iRV (iRv (b i₀)) := rv_mem hM (hb i₀)
  have hcjRV : iRV (iRv (c j₀)) := rv_mem hM (hc j₀)
  have hbi0 : iRv (b i₀) ≠ iRVZero := rv_ne_zero_of_vf_ne_zero (hb i₀) (hb0 i₀)
  have hcj0 : iRv (c j₀) ≠ iRVZero := rv_ne_zero_of_vf_ne_zero (hc j₀) (hc0 j₀)
  obtain ⟨cu, hcuRV, hcu, hpeq⟩ :=
    M5L.cls_ratio_units hM (rv_mem hM hPF) hbiRV hclsP hbi0
  obtain ⟨cv, hcvRV, hcv, hqeq⟩ :=
    M5L.cls_ratio_units hM (rv_mem hM hQF) hcjRV hclsQ hcj0
  -- the `S`-inverse of `c j₀`
  obtain ⟨cj', hcj'VF, hcj'S, hcj'eq⟩ := hfinv (c j₀) (hc j₀) (M5L.rv_mem_sub S (hcS j₀)) (hc0 j₀)
  have hcjiRV : iRV (iRv cj') := rv_mem hM hcj'VF
  have hcji : iRVMul (iRv (c j₀)) (iRv cj') = iRVOne := by
    rw [← rv_mul_hom_of_model hM (hc j₀) hcj'VF, hcj'eq, rv_one hM]
  -- the key product identity: `rv x · rv(c j₀) · rv(c j₀)⁻¹ = rv(b i₀) · cu · rv(c j₀)⁻¹`
  have hyRV : iRV (iRv x) := rv_mem hM hxVF
  have hyq : iRVMul (iRv x) (iRv Q) = iRv P := by
    rw [← rv_mul_hom_of_model hM hxVF hQF, hxq]
  have hkey : iRVMul (iRVMul (iRv x) (iRv (c j₀))) cv = iRVMul (iRv (b i₀)) cu := by
    rw [rv_mul_assoc_of_model hM hyRV hcjRV hcvRV, ← hqeq, hyq, hpeq]
  -- `rv x · rv(c j₀)` and `rv(b i₀)` have the same class
  have hstep : Transc.Cls (iRVMul (iRv x) (iRv (c j₀))) (iRv (b i₀)) := by
    have h1 : Transc.Cls (iRVMul (iRVMul (iRv x) (iRv (c j₀))) cv)
        (iRVMul (iRv x) (iRv (c j₀))) :=
      cls_mul_unit_right_rv (rv_mul_mem hM hyRV hcjRV) hcvRV (GammaGroup.units_ne_zero hcv) hcv
    have h2 : Transc.Cls (iRVMul (iRVMul (iRv x) (iRv (c j₀))) cv) (iRVMul (iRv (b i₀)) cu) :=
      cls_of_eq hkey (rv_mul_mem hM (rv_mul_mem hM hyRV hcjRV) hcvRV)
    have h3 : Transc.Cls (iRVMul (iRv (b i₀)) cu) (iRv (b i₀)) :=
      cls_mul_unit_right_rv hbiRV hcuRV (GammaGroup.units_ne_zero hcu) hcu
    have h21 : Transc.Cls (iRVMul (iRv x) (iRv (c j₀))) (iRVMul (iRv (b i₀)) cu) :=
      cls_trans' (Transc.cls_symm h1) h2 (rv_mul_mem hM hyRV hcjRV)
        (rv_mul_mem hM (rv_mul_mem hM hyRV hcjRV) hcvRV) (rv_mul_mem hM hbiRV hcuRV)
    exact cls_trans' h21 h3 (rv_mul_mem hM hyRV hcjRV) (rv_mul_mem hM hbiRV hcuRV) hbiRV
  -- multiply by the `S`-inverse of `rv(c j₀)`
  have hfin : Transc.Cls (iRVMul (iRVMul (iRv x) (iRv (c j₀))) (iRv cj'))
      (iRVMul (iRv (b i₀)) (iRv cj')) :=
    Transc.cls_mul_right hM (rv_mul_mem hM hyRV hcjRV) hbiRV hcjiRV hstep
  have hleft : iRVMul (iRVMul (iRv x) (iRv (c j₀))) (iRv cj') = iRv x := by
    rw [rv_mul_assoc_of_model hM hyRV hcjRV hcjiRV, hcji, rv_mul_one_any_right hM hyRV]
  rw [hleft] at hfin
  exact ⟨iRVMul (iRv (b i₀)) (iRv cj'),
    M5L.rvMul_mem_sub S (M5L.rv_mem_sub S (hbS i₀)) hcj'S,
    rv_mul_mem hM hbiRV hcjiRV, hfin⟩

/-- **The `VF`-part of Claim (⋆) from the monomial min formula and `e ∈ U(M)`.** -/
theorem vfPartClasses_of_expansion_min {S T : LRV.Substructure M} {e : M}
    (hmin : ExpansionValMin (M := M) S e) (heu : iUnits (iRv e))
    (hquot : M5L.QuotExpansions S T e) (hfinv : M5L.VFInvClosedOn S) (he : iVF e) :
    ∀ x : M, x ∈ T → iVF x → x ≠ Transfer.iVFZero →
      ∃ s : M, s ∈ S ∧ iRV s ∧ Transc.Cls (iRv x) s :=
  vfPartClasses_of_expansion (expansionValBase_of_min hmin heu) hquot hfinv he

/-- **Claim (⋆) in class form for the unit branch, from the value computation.** -/
theorem ResidualClasses_of_VFGen_unit {S T : LRV.Substructure M} {e : M}
    (hbase : ExpansionValBase (M := M) S e) (hquot : M5L.QuotExpansions S T e)
    (hfinv : M5L.VFInvClosedOn S) (he : iVF e) (hVFGen : Assembly.IsVFGen T) :
    M5L.ResidualClasses S T := by
  intro y hyT hyRV
  rcases hVFGen y hyT hyRV with ⟨x, hxT, hxVF, hxr⟩ | hz
  · by_cases hx0 : x = Transfer.iVFZero
    · refine ⟨iRVZero, M5L.rvZero_mem_sub S, rv_zero_mem hM, ?_⟩
      rw [← hxr, hx0, RVCalc.rv_zero_eq hM]
      exact Transc.cls_refl hM (rv_zero_mem hM)
    · obtain ⟨s, hsS, hsRV, hcls⟩ :=
        vfPartClasses_of_expansion hbase hquot hfinv he x hxT hxVF hx0
      exact ⟨s, hsS, hsRV, by rw [← hxr]; exact hcls⟩
  · refine ⟨iRVZero, M5L.rvZero_mem_sub S, rv_zero_mem hM, ?_⟩
    rw [hz]
    exact Transc.cls_refl hM (rv_zero_mem hM)

/-- **Claim (⋆) in class form, unit branch, from the monomial min formula.** -/
theorem ResidualClasses_of_VFGen_unit_min {S T : LRV.Substructure M} {e : M}
    (hmin : ExpansionValMin (M := M) S e) (heu : iUnits (iRv e))
    (hquot : M5L.QuotExpansions S T e) (hfinv : M5L.VFInvClosedOn S) (he : iVF e)
    (hVFGen : Assembly.IsVFGen T) : M5L.ResidualClasses S T :=
  ResidualClasses_of_VFGen_unit (expansionValBase_of_min hmin heu) hquot hfinv he hVFGen

/-- **Lemma 3.6, unit branch, in the frozen `GammaHullInitial` form**: no EP 3.4.3. -/
theorem gammaHullInitial_of_unit_expansion {S T : LRV.Substructure M} {e : M}
    (hmin : ExpansionValMin (M := M) S e) (heu : iUnits (iRv e))
    (hquot : M5L.QuotExpansions S T e) (hfinv : M5L.VFInvClosedOn S) (he : iVF e)
    (hVFGen : Assembly.IsVFGen T) : M5Ledger.GammaHullInitial S T :=
  gammaHullInitial_of_ResidualClasses
    (ResidualClasses_of_VFGen_unit_min hmin heu hquot hfinv he hVFGen)

/-- **Lemma 3.6, unit branch, in `Standing` form.**  Hypotheses: the extension `T ⊇ S` with
`IsVFGen` + `QuotExpansions` (the paper's `VF(T) = K(Ŝ)(e)`, Remark 3.1 and `qe.tex:645`),
inverse-closure of `S`'s `VF`-classes, `e ∈ VF(M)` with `e ∈ U(M)`, and the value computation
`ExpansionValMin` — which §6 proves outright in the separated regime and which in the unit regime is
`QE/UnitTranscend.val_sum_eq_one`.  No `EPDimensionInequality`. -/
theorem standing_of_unit_expansion {S T : LRV.Substructure M} {e : M} (hST : S ≤ T)
    (hS : Assembly.Standing S) (hmin : ExpansionValMin (M := M) S e) (heu : iUnits (iRv e))
    (hquot : M5L.QuotExpansions S T e) (hfinv : M5L.VFInvClosedOn S) (he : iVF e)
    (hVFGen : Assembly.IsVFGen T) : Assembly.Standing T :=
  M5L.standing_of_ClassControl hST hS
    (ResidualClasses_of_VFGen_unit_min hmin heu hquot hfinv he hVFGen)
/-! ## 8. The unit branch's value computation, transported from the Mathlib valuation

This section does what `QE/UnitTranscend.lean` does in the Mathlib setting, *at a model of the frozen
`ACVF`*: it derives `ExpansionValMin` from a **residue-transcendence hypothesis over the subfield of
`VF(M)` generated by `VF(Ŝ)`**.  The transport runs through `QE/ValueGroupBridge.lean`'s explicit
valuation `vGammaValuation : Valuation (VFType M) Γ(M)⁰`, whose order is the encoding's `iLe`
(`VGBridge.vGamma_le_iff`), so the paper's order-theoretic conclusion comes back as the frozen
`Transc.cls`.

What the hypothesis `M7.ResidueTranscendental v K he` is: `QE/UnitTranscend.lean`'s elementary
statement "no nonzero residue polynomial over `K` vanishes at `rv e`" — no dimension inequality, no
Abhyankar.  What remains open after this section is only the *translation* of the frozen
`M8.RVTrans` (`iKAdd`-chain vocabulary) into that statement; §9 records it. -/

noncomputable section

open SpecialTransformations.Milestone0.VGBridge

attribute [local instance] Transfer.vfFieldOfModel
set_option backward.isDefEq.respectTransparency false
set_option warn.classDefReducibility false

/-- The subfield of the `VF` sort generated by the `VF`-part of a substructure `S`: the frozen
stand-in for the paper's `K(Ŝ)`.  In the tagged one-sorted encoding `S ∩ VF` is only a ring (there
is no inverse symbol on the `VF` sort), so the field it generates inside `VF(M)` is taken instead;
`M5L.VFInvClosedOn` is exactly the condition under which `S`'s own `RV`-classes agree with it. -/
def KOfS (S : LRV.Substructure M) : Subfield (Transfer.VFType (M := M)) :=
  Subfield.closure (Set.range (fun x : {x : M // x ∈ S ∧ iVF x} =>
    (⟨x.1, x.2.2⟩ : Transfer.VFType (M := M))))

theorem mem_KOfS {S : LRV.Substructure M} {x : M} (hxS : x ∈ S) (hxVF : iVF x) :
    (⟨x, hxVF⟩ : Transfer.VFType (M := M)) ∈ KOfS S :=
  Subfield.subset_closure ⟨⟨x, hxS, hxVF⟩, rfl⟩

theorem vfType_zero_val : ((0 : Transfer.VFType (M := M))).1 = Transfer.iVFZero := rfl

theorem vfType_ne_zero_of_val {x : Transfer.VFType (M := M)} (h : x.1 ≠ Transfer.iVFZero) :
    x ≠ 0 :=
  fun h0 => h (by rw [congrArg Subtype.val h0]; exact vfType_zero_val)

theorem vfType_val_ne_zero {x : Transfer.VFType (M := M)} (h : x ≠ 0) :
    x.1 ≠ Transfer.iVFZero :=
  fun h0 => h (Subtype.ext (by rw [h0]; exact vfType_zero_val.symm))

/-- **A unit of the encoding is a unit of the valuation**: `vGamma e = 1`. -/
theorem vGamma_eq_one_of_units {e : M} (he : iVF e) (heu : iUnits (iRv e)) :
    VGBridge.vGamma (⟨e, he⟩ : Transfer.VFType (M := M)) = 1 := by
  set x : Transfer.VFType (M := M) := ⟨e, he⟩ with hx
  have hxval : x.1 = e := rfl
  have he0 : x.1 ≠ Transfer.iVFZero := by
    intro h
    refine GammaGroup.units_ne_zero heu ?_
    rw [hxval] at h
    rw [h]
    exact RVCalc.rv_zero_eq hM
  have hv0 : x ≠ 0 := vfType_ne_zero_of_val he0
  rw [VGBridge.vGamma_of_ne hv0]
  have hgv : VGBridge.gv x hv0 = 1 := by
    have h1 := (VGBridge.gv_le_one_iff (M := M) hv0).mpr
    have h2 := (VGBridge.one_le_gv_iff (M := M) hv0).mpr
    have hu := (RVCalc.units_iff_le_one hM (rv_mem hM he) (GammaGroup.units_ne_zero heu)).mp heu
    exact le_antisymm (h1 hu.2) (h2 hu.1)
  rw [hgv, inv_one, WithZero.coe_one]

/-- The `VF`-power of a `VF`-element is the frozen `Transc.vpow`, on the carrier. -/
theorem VFPow_val (x : Transfer.VFType (M := M)) (n : ℕ) :
    (x ^ n).1 = Transc.vpow x.1 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show iVFMul ((x ^ k).1) x.1 = iVFMul (Transc.vpow x.1 k) x.1
    rw [ih]

/-- **The frozen expansion is the `VFType` expansion.**  The `Fin n`-sum of `b i * e^i` in the
field `VF(M)` has, on the carrier `M`, the frozen `Transc.vsum` of `iVFMul (b i) (vpow e i)`. -/
theorem vfSum_val (n : ℕ) (b : ℕ → Transfer.VFType (M := M)) (e : Transfer.VFType (M := M)) :
    (∑ i : Fin n, b (i : ℕ) * e ^ (i : ℕ)).1
      = Transc.vsum (fun i => iVFMul (b i).1 (Transc.vpow e.1 i)) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    show iVFAdd ((∑ i : Fin k, b (i : ℕ) * e ^ (i : ℕ)).1) ((b k * e ^ k).1)
      = iVFAdd (Transc.vsum (fun i => iVFMul (b i).1 (Transc.vpow e.1 i)) k)
          (iVFMul (b k).1 (Transc.vpow e.1 k))
    rw [ih]
    show iVFAdd (Transc.vsum (fun i => iVFMul (b i).1 (Transc.vpow e.1 i)) k)
        (iVFMul ((b k).1) ((e ^ k).1)) = _
    rw [VFPow_val]

/-- **The value of an expansion is the value of one of its coefficients** — the Mathlib-level form of
`ExpansionValMin`, at a genuine valuation, from residue transcendence.  This is
`QE/UnitTranscend.exists_scalar_val` with the index of the extremal coefficient kept (the witness
`a` of that theorem *is* one of the coefficients, but its statement forgets which one). -/
theorem exists_coeff_val {L : Type*} [Field L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (K : Subfield L) {e : L} (he : v e = 1)
    (hT : M7.ResidueTranscendental v K he) {n : ℕ} {c : Fin n → K} {m : Fin n → ℕ}
    (hm : Function.Injective m) (hne : ∃ i, c i ≠ 0) :
    ∃ j, c j ≠ 0 ∧ v (∑ i, (c i : L) * e ^ m i) = v ((c j : L)) := by
  classical
  set sf := Finset.univ.filter (fun i => c i ≠ 0) with hsf
  have hsfne : sf.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i₀, hi₀mem, hmax⟩ :=
    Finset.exists_max_image sf (fun i => v ((c i : L))) hsfne
  have hi₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀mem).2
  have hi₀L : ((c i₀ : K) : L) ≠ 0 := fun h => hi₀ (by simpa using h)
  have hne0 : v ((c i₀ : L)) ≠ 0 := fun h => hi₀L ((Valuation.zero_iff v).mp h)
  have hpos : 0 < v ((c i₀ : L)) := lt_of_le_of_ne zero_le hne0.symm
  refine ⟨i₀, hi₀, ?_⟩
  have hcoe : ∀ i, (((c i / c i₀ : K)) : L) = (c i : L) / (c i₀ : L) := fun i =>
    map_div₀ (Subfield.subtype K) (c i) (c i₀)
  have hd : ∀ i, v (((c i / c i₀ : K)) : L) ≤ 1 := by
    intro i
    by_cases hi : c i = 0
    · rw [hcoe, hi]; simp
    · rw [hcoe, Valuation.map_div, div_le_one₀ hpos]
      exact hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hi₀div : ((c i₀ / c i₀ : K)) = 1 := div_self hi₀
  have hsome : ∃ i, v (((c i / c i₀ : K)) : L) = 1 := by
    refine ⟨i₀, ?_⟩
    rw [hi₀div]
    simp
  have hstep := M7.val_sum_eq_one v he hd hsome (hT n (fun i => c i / c i₀) m hm hd)
  have hrel : (∑ i, (((c i / c i₀ : K)) : L) * e ^ m i)
      = (∑ i, (c i : L) * e ^ m i) / (c i₀ : L) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoe]
    ring
  rw [hrel, Valuation.map_div] at hstep
  exact (div_eq_one_iff_eq hne0).mp hstep

/-- **`ExpansionValMin` from residue transcendence over `KOfS S`.**  With the explicit valuation
`vGammaValuation` of `QE/ValueGroupBridge.lean`, the Mathlib-level value computation
(`exists_coeff_val`) becomes the frozen value computation.  Note what is *not* used: no
`EPDimensionInequality`, no divisibility of `Γ(Ŝ)`, no `Separated`, no `IsVFGen`. -/
theorem ExpansionValBase_of_residueTranscendental {S : LRV.Substructure M} {e : M} (he : iVF e)
    (heu : iUnits (iRv e))
    (hT : M7.ResidueTranscendental (VGBridge.vGammaValuation (M := M)) (KOfS S)
      (vGamma_eq_one_of_units he heu)) :
    ExpansionValBase (M := M) S e := by
  intro b m _he hb hbS hb0 hP0
  set b' : ℕ → Transfer.VFType (M := M) := fun i => ⟨b i, hb i⟩ with hb'def
  set e' : Transfer.VFType (M := M) := ⟨e, he⟩ with he'def
  set c : Fin (m + 1) → (KOfS S : Type) :=
    fun i => ⟨b' (i : ℕ), mem_KOfS (hbS (i : ℕ)) (hb (i : ℕ))⟩ with hcdef
  have hcoe : ∀ i : Fin (m + 1), ((c i : (KOfS S : Type)) : Transfer.VFType (M := M)) = b' (i : ℕ) :=
    fun i => rfl
  have hsumval : (∑ i : Fin (m + 1), b' (i : ℕ) * e' ^ (i : ℕ)).1
      = Transc.vsum (fun i => iVFMul (b i) (Transc.vpow e i)) (m + 1) := by
    rw [vfSum_val]
  have hsum0 : (∑ i : Fin (m + 1), b' (i : ℕ) * e' ^ (i : ℕ)) ≠ 0 := by
    refine vfType_ne_zero_of_val ?_
    rw [hsumval]
    exact hP0
  have hb0' : ∀ i, b' i ≠ 0 := fun i => fun h => hb0 i (by
    have := congrArg Subtype.val h
    simpa using this)
  obtain ⟨j, hjne, hval⟩ := exists_coeff_val (VGBridge.vGammaValuation (M := M)) (KOfS S)
    (vGamma_eq_one_of_units he heu) hT
    (n := m + 1) (c := c) (m := fun i => (i : ℕ)) (fun i j' h => Fin.ext h)
    (⟨⟨0, Nat.succ_pos m⟩, fun h => hb0' 0 (by
      have h1 : ((c ⟨0, Nat.succ_pos m⟩ : (KOfS S : Type)) : Transfer.VFType (M := M))
          = ((0 : (KOfS S : Type)) : Transfer.VFType (M := M)) :=
        congrArg (fun z : (KOfS S : Type) => (z : Transfer.VFType (M := M))) h
      rw [hcoe] at h1
      exact h1)⟩)
  have hj0 : b' (j : ℕ) ≠ 0 := fun h => hjne (Subtype.ext h)
  -- rewrite the `KOfS`-coercions away
  have hval' : VGBridge.vGamma (∑ i : Fin (m + 1), b' (i : ℕ) * e' ^ (i : ℕ))
      = VGBridge.vGamma (b' (j : ℕ)) := by
    have h1 : (∑ i : Fin (m + 1), ((c i : (KOfS S : Type)) : Transfer.VFType (M := M)) * e' ^ (i : ℕ))
        = ∑ i : Fin (m + 1), b' (i : ℕ) * e' ^ (i : ℕ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoe i]
    have h2 : ((c j : (KOfS S : Type)) : Transfer.VFType (M := M)) = b' (j : ℕ) := hcoe j
    rw [← h1, ← h2]
    exact hval
  refine ⟨(j : ℕ), Nat.lt_succ_iff.mp j.isLt, ?_, ?_⟩
  · have h := (VGBridge.vGamma_le_iff (x := b' (j : ℕ))
      (y := ∑ i : Fin (m + 1), b' (i : ℕ) * e' ^ (i : ℕ)) hj0 hsum0).mp (le_of_eq hval'.symm)
    rw [hsumval] at h
    exact h
  · have h := (VGBridge.vGamma_le_iff
      (x := ∑ i : Fin (m + 1), b' (i : ℕ) * e' ^ (i : ℕ)) (y := b' (j : ℕ)) hsum0 hj0).mp
      (le_of_eq hval')
    rw [hsumval] at h
    exact h

/-- The monomial form, from the coefficient form and `e ∈ U(M)`. -/
theorem ExpansionValMin_of_residueTranscendental {S : LRV.Substructure M} {e : M} (he : iVF e)
    (heu : iUnits (iRv e))
    (hT : M7.ResidueTranscendental (VGBridge.vGammaValuation (M := M)) (KOfS S)
      (vGamma_eq_one_of_units he heu)) :
    ExpansionValMin (M := M) S e := by
  intro b m _he hb hbS hb0 hP0
  obtain ⟨j, hj, hcls⟩ := ExpansionValBase_of_residueTranscendental he heu hT b m he hb hbS hb0 hP0
  have hε : iRV (iRv e) := rv_mem_of_units heu
  have hε0 : iRv e ≠ iRVZero := GammaGroup.units_ne_zero heu
  have hbRV : iRV (iRv (b j)) := rv_mem hM (hb j)
  have hεjRV : iRV (Transc.rvpow (iRv e) j) := Transc.iRV_rvpow hM hε j
  have hεj : Transc.Cls (iRVMul (iRv (b j)) (Transc.rvpow (iRv e) j)) (iRv (b j)) :=
    cls_mul_unit_right_rv hbRV hεjRV
      (Transc.rvpow_ne_zero hM hε hε0 j) (units_rvpow heu j)
  have hmono : iRv (iVFMul (b j) (Transc.vpow e j))
      = iRVMul (iRv (b j)) (Transc.rvpow (iRv e) j) :=
    Transc.rv_monomial hM he hb j
  refine ⟨j, hj, ?_⟩
  rw [hmono]
  exact cls_trans' hcls (Transc.cls_symm hεj)
    (rv_mem hM (Transc.iVF_vsum hM
      (fun i => vf_mul_mem hM (hb i) (Transc.iVF_vpow hM he i)) (m + 1)))
    hbRV (rv_mul_mem hM hbRV hεjRV)



/-! ## 9. The two regimes of the value computation, and the exact open bridge

The paper proves its value computation `vv(Σ b_i e^i) = min_i vv(b_i e^i)` twice: in the
separated regime (`vv(e)` of infinite order mod `Γ(Ŝ)`, Lemma 3.7) and in the unit regime
(`e ∈ U(M)` with `rv(e)` transcendental, Lemma 3.6).  In the frozen encoding these are exactly the
two hypotheses under which `ExpansionValMin` is now available:

* `ExpansionValMin_of_separated` (§6) — from `M5L.Separated S e` alone, no residue input;
* `ExpansionValMin_of_residueTranscendental` (§8) — from `e ∈ U(M)` and the residue-transcendence
  statement over `KOfS S` at the explicit valuation `vGammaValuation`.

The two hypotheses are **disjoint** (`not_separated_of_units`), which is why the paper needs both
arguments and why no single one of them covers Lemma 3.6 and Lemma 3.7 at once.

What is *not* formalised is the translation between the frozen `M8.RVTrans` (a statement about the
`iKAdd`-chain `rvPolyEval`, i.e. about the encoding's residue-field *addition*) and the Mathlib-level
`M7.ResidueTranscendental` (a statement about `IsLocalRing.residue` of a genuine valuation ring).
The obstruction is structural, not a matter of effort: `Axioms.kAddLink` connects `iKAdd` with
`iRv (x + y)` **only when both summands are units**, and `iRv` of a merely integral element is not a
residue-field element of the encoding at all (`pInK` fails, so every `kAdd` at it is junk-zero by
`Axioms.kJunkZero`).  Consequently the `iKAdd`-chain computes the residue of a *sum* only while all
its partial sums are units (`QE/M6Wire.lean`'s `rvFold_cases` makes exactly this restriction
explicit), whereas `ResidueTranscendental`'s coefficients after normalisation are arbitrary integral
elements.  The bridge is therefore stated as a named `Prop` below and nothing here assumes it. -/

/-- **The exact open bridge.**  Frozen residue transcendence (`M8.RVTrans`, the `iKAdd`-chain
vocabulary of the encoding) implies the Mathlib-level residue transcendence of
`QE/UnitTranscend.lean` over the subfield `KOfS S` generated by `VF(Ŝ)`.

With it, `ExpansionValBase` — and hence Claim (⋆), `GammaHullInitial` and `Standing` for `⟨Ŝ,e⟩` —
follows with no EP 3.4.3 (`standing_of_residueTranscendental` below). -/
def RVTransToResidueTranscendental (S : LRV.Substructure M) (e : M) (he : iVF e)
    (heu : iUnits (iRv e)) : Prop :=
  RVTrans S e heu →
    M7.ResidueTranscendental (VGBridge.vGammaValuation (M := M)) (KOfS S)
      (vGamma_eq_one_of_units he heu)

/-- **Lemma 3.6's `Γ`-step with no EP 3.4.3, at the paper's own hypotheses** (modulo the frozen↔
Mathlib residue bridge, which is the named `Prop` of this section and is *not* assumed here):
`e ∈ U(M)`, `rv(e)` transcendental over `K(Ŝ)`, `VF(⟨Ŝ,e⟩)` a quotient field of expansions of `e`
over `VF(Ŝ)`, and `S` inverse-closed on `VF`.  Conclusion: `Standing T` for the extension `T`. -/
theorem standing_of_residueTranscendental {S T : LRV.Substructure M} {e : M} (hST : S ≤ T)
    (hS : Assembly.Standing S) (he : iVF e) (heu : iUnits (iRv e))
    (hT : M7.ResidueTranscendental (VGBridge.vGammaValuation (M := M)) (KOfS S)
      (vGamma_eq_one_of_units he heu))
    (hquot : M5L.QuotExpansions S T e) (hfinv : M5L.VFInvClosedOn S)
    (hVFGen : Assembly.IsVFGen T) : Assembly.Standing T :=
  standing_of_unit_expansion hST hS (ExpansionValMin_of_residueTranscendental he heu hT) heu
    hquot hfinv he hVFGen

/-- The same from the frozen `RVTrans` and the named bridge `Prop`. -/
theorem standing_of_RVTrans {S T : LRV.Substructure M} {e : M} (hST : S ≤ T)
    (hS : Assembly.Standing S) (he : iVF e) (heu : iUnits (iRv e))
    (hbridge : RVTransToResidueTranscendental (M := M) S e he heu) (htrans : RVTrans S e heu)
    (hquot : M5L.QuotExpansions S T e) (hfinv : M5L.VFInvClosedOn S)
    (hVFGen : Assembly.IsVFGen T) : Assembly.Standing T :=
  standing_of_residueTranscendental hST hS he heu (hbridge htrans) hquot hfinv hVFGen

/-- **`ExpansionValMin` is the common form of the paper's two value computations.**  This is the
case split the paper makes between Lemma 3.7 (`e:transc`, separated) and Lemma 3.6
(`lift:transcendental`, unit + residue transcendence), in one statement: `ExpansionValMin` holds in
whichever regime the new element falls into. -/
theorem ExpansionValMin_of_regimes {S : LRV.Substructure M} {e : M} (he : iVF e)
    (heu : iUnits (iRv e))
    (hT : M7.ResidueTranscendental (VGBridge.vGammaValuation (M := M)) (KOfS S)
      (vGamma_eq_one_of_units he heu)) :
    ExpansionValMin (M := M) S e :=
  ExpansionValMin_of_residueTranscendental he heu hT

end

end SpecialTransformations.Milestone0.M8

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M8.not_separated_of_units
#print axioms SpecialTransformations.Milestone0.M8.not_units_of_separated
#print axioms SpecialTransformations.Milestone0.M8.gammaHullInitial_of_ResidualClasses
#print axioms SpecialTransformations.Milestone0.M8.standing_of_ResidualClasses
#print axioms SpecialTransformations.Milestone0.M8.vfPartClasses_of_expansion
#print axioms SpecialTransformations.Milestone0.M8.ResidualClasses_of_VFGen_unit
#print axioms SpecialTransformations.Milestone0.M8.gammaHullInitial_of_unit_expansion
#print axioms SpecialTransformations.Milestone0.M8.standing_of_unit_expansion
#print axioms SpecialTransformations.Milestone0.M8.vGamma_eq_one_of_units
#print axioms SpecialTransformations.Milestone0.M8.vfSum_val
#print axioms SpecialTransformations.Milestone0.M8.exists_coeff_val
#print axioms SpecialTransformations.Milestone0.M8.ExpansionValBase_of_residueTranscendental
#print axioms SpecialTransformations.Milestone0.M8.ExpansionValMin_of_residueTranscendental
#print axioms SpecialTransformations.Milestone0.M8.standing_of_residueTranscendental
#print axioms SpecialTransformations.Milestone0.M8.standing_of_RVTrans
#print axioms SpecialTransformations.Milestone0.M8.ExpansionValMin_of_regimes
