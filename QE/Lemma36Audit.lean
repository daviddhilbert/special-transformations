/-
# Audit of Lemma 3.6's hypothesis bundle at the tree's case split (`M5L.Separated`)

Member `m4`, swarm `smw2ngn1z`, direction d2.  Companion file `GroupCore.lean` does the `Γ`-side
(pure ordered-abelian-group) part; this file does the `L_RV`/`ACVF`-level part.

## Question

`QE/OneStepCases.lean` splits the frozen one-step at a fixed pair by the predicate
`M5L.Separated S m` (`QE/M5L34_36.lean:296`): for every `k > 0` and all nonzero `x, y ∈ VF(S)`,
`¬ (vv(m^k · x) = vv(y))`, i.e. `vv(m)^k ∉ Γ(Ŝ)` for every `k > 0`.  Its docstring assigns

* `CaseSeparated` = Lemmas 3.4 / 3.6 (`lift:all:root`, `lift:transcendental`),
* `CaseNotSeparated` = Lemma 3.5 (`lift:divisible:hull`).

**Both paper lemmas in the first line assume `e ∈ U(M)`** (`qe.tex:614,733`), i.e. `vv(e) = 0`,
which in the frozen encoding is `iUnits (iRv e)` (`memUnits` is the paper's `Kˣ`, `QE/RVAdd.lean`
`iUnits_iff_isInt_and_not_isMax`).  The audit below shows that `Separated` and `U(M)` are
**incompatible**, so the labels are wrong: Lemmas 3.4 and 3.6 live in the `¬ Separated` slot.  So
does Lemma 3.5: there `e^n = a ∈ VF(Ŝ)` gives `n • vv(e) = vv(a) ∈ Γ(Ŝ)`, so separation fails at
`k = n`.  `CaseSeparated` selects exactly Lemma 3.7's / 3.8's regime — `vv(e)` of *infinite* order
modulo `Γ(Ŝ)`, which implies separation for every `k > 0`.

## Contents

§0 `units_cls_one` — the missing vocabulary link `iUnits u ↔ Cls u 1` in `Cls` form.
§1 `separated_not_units`: `Separated S m → ¬ iUnits (iRv m)`.  The proof is the paper's own
arithmetic: `vv(m) = 0 ∈ Γ(Ŝ)` because `vv(1) = 0`, so separation fails already at `k = 1` with
`x = y = 1`.  (No transcendence, no divisibility, no `iRv m ∈ S` is used — the exclusion is
by `iUnits` alone.)
§2 `not_separated_of_mem`, `separated_top_forces_zero`: the slot only ever fires at an element
that is *new* and *nonzero*; at `S = ⊤` its hypothesis bundle forces `m = 0`.
§3 `not_separated_of_vfgen`: at a `VF`-generated `S` (the paper's `RV(S) = rv(VF(S))`, which is the
form of `Ŝ` and of every substructure at the end of the proof of Proposition 3.9) the slot is
empty — so `CaseSeparated` can only be applied to substructures whose `RV`-sort is strictly larger
than the values of their `VF`-sort.
§4 the ledger: `Lemma36UnitsHyp` (the case-split-relevant hypotheses of Lemma 3.6) implies
`¬ Separated`, and `CaseSeparatedHyp ∧ iUnits (iRv m)` is inconsistent.

Not in this file (and not claimed): the formalisation of "`rv(e)` transcendental over `K(Ŝ)`" and
the algebraic-descent step of Lemma 3.6 — those are the subject of direction d1; nothing in the
audit above depends on them.
-/
import M5L34_36
import RVAdd
import GammaGroup

set_option autoImplicit false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.GammaGroup

namespace Lemma36AuditACVF

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ## 0. `Kˣ` is the class of `1`, in `Cls` form -/

/-- **`iUnits u ↔ Cls u 1`**: `Axioms.leClassOne` read off (`QE/RVCalc.lean`'s
`units_iff_le_one`) in the tree's class notation `Transc.Cls`.  Every consumer of "`e ∈ U(M)`"
below goes through this lemma. -/
theorem units_cls_one {u : M} (hu : iUnits u) : Transc.Cls u iRVOne := by
  have h := (RVCalc.units_iff_le_one hM (RVAdd.iRV_of_iUnits hu) (units_ne_zero hu)).mp hu
  exact ⟨h.2, h.1⟩

/-- The converse orientation, for symmetry. -/
theorem cls_one_units {u : M} (hu : iRV u) (hu0 : u ≠ iRVZero) (h : Transc.Cls u iRVOne) :
    iUnits u :=
  (RVCalc.units_iff_le_one hM hu hu0).mpr ⟨h.2, h.1⟩

/-- The VF-one is in every substructure (it is the constant `Fn.vfOne`). -/
theorem vfOne_mem (S : LRV.Substructure M) : (Transfer.iVFOne : M) ∈ S :=
  S.fun_mem Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)

/-- The VF-one is nonzero. -/
theorem vfOne_ne_zero : (Transfer.iVFOne : M) ≠ Transfer.iVFZero :=
  fun h => RVCalc.vf_zero_ne_one hM h.symm

/-! ## 1. `Separated` excludes the units — Lemmas 3.4 / 3.6 are *not* in this slot

The paper's proof of Lemma 3.6 needs `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`, so in particular `vv(e) ∈ Γ(Ŝ)`; but
`e ∈ U(M)` gives `vv(e) = 0` outright.  Separation (`vv(e)^k ∉ Γ(Ŝ)` for all `k > 0`) is the
*opposite* hypothesis, and it is what Lemma 3.5 (`e ∉ U(M)`) and Lemma 3.7 (`vv(e)` of infinite
order modulo `Γ(Ŝ)`) assume. -/

/-- **`Separated S m` implies `rv(m) ∉ Kˣ`**, i.e. `m ∉ U(M)`.

Witness for the separation failure: `k = 1`, `x = y = 1` (both in `S`, nonzero), so separation
would require `¬ Cls (rv(m) · rv 1) (rv 1)`, while `rv 1 = 1` and `iUnits (rv m)` gives
`Cls (rv m) 1`. -/
theorem separated_not_units {S : LRV.Substructure M} {m : M} (hsep : M5L.Separated S m) :
    ¬ iUnits (iRv m) := by
  intro hu
  have h1vf : iVF (Transfer.iVFOne : M) := Transfer.vf_one_mem hM
  have hnot := hsep 1 (by norm_num) (Transfer.iVFOne) (Transfer.iVFOne)
    h1vf h1vf (vfOne_mem S) (vfOne_mem S) vfOne_ne_zero vfOne_ne_zero
  apply hnot
  rw [RVCalc.rv_one hM]
  have ht : iRV (iRv m) := RVAdd.iRV_of_iUnits hu
  rw [Transfer.rv_mul_one_any_right hM (Transc.iRV_rvpow hM ht 1)]
  show Transc.Cls (iRVMul iRVOne (iRv m)) iRVOne
  rw [Transfer.rv_mul_one_any hM ht]
  exact units_cls_one hu

/-- Contrapositive form: a unit never satisfies the separation hypothesis. -/
theorem not_separated_of_units {S : LRV.Substructure M} {m : M} (hu : iUnits (iRv m)) :
    ¬ M5L.Separated S m :=
  fun hsep => separated_not_units hsep hu

/-! ## 2. The slot only fires at new, nonzero elements -/

/-- **Separation fails at any nonzero element already in `S`** (take `k = 1`, `x = 1`, `y = m`). -/
theorem not_separated_of_mem {S : LRV.Substructure M} {m : M} (hmS : m ∈ S) (hm : iVF m)
    (hm0 : m ≠ Transfer.iVFZero) : ¬ M5L.Separated S m := by
  intro hsep
  have h1vf : iVF (Transfer.iVFOne : M) := Transfer.vf_one_mem hM
  have hnot := hsep 1 (by norm_num) (Transfer.iVFOne) m h1vf hm (vfOne_mem S) hmS
    vfOne_ne_zero hm0
  apply hnot
  rw [RVCalc.rv_one hM]
  have ht : iRV (iRv m) := Transfer.rv_mem hM hm
  rw [Transfer.rv_mul_one_any_right hM (Transc.iRV_rvpow hM ht 1)]
  show Transc.Cls (iRVMul iRVOne (iRv m)) (iRv m)
  rw [Transfer.rv_mul_one_any hM ht]
  exact Transc.cls_refl hM ht

/-- **`⊤`-witness**: at `S = ⊤` the hypothesis bundle of `CaseSeparated` forces `m = 0`.  So the
slot's content at the top substructure is the degenerate one (where `T = ⊤`, `g` any extension, is
the trivial conclusion), which is the `⊤`-stress test of `QE/OneStepCases.lean`. -/
theorem separated_top_forces_zero {m : M} (hm : iVF m) (hsep : M5L.Separated (⊤ : LRV.Substructure M) m) :
    m = Transfer.iVFZero := by
  by_contra hne
  exact not_separated_of_mem (S := ⊤) trivial hm hne hsep

/-! ## 3. The slot is empty at `VF`-generated substructures

`Assembly.IsVFGen S` is the paper's `RV(S) = rv(VF(S))` — the property `Ŝ = ⟨VF(S)⟩` has by
construction, and the property the last step of Proposition 3.9 establishes for the substructure it
applies Weispfenning's theorem to.  There, `iRv m ∈ S` gives a `VF`-witness `y ∈ S` with
`rv(y) = rv(m)`, and separation fails at `k = 1`, `x = 1`, `y = y`. -/

/-- **A `VF`-generated `S` has no separated elements**: if `rv(m)` is already the class of an
element of `S`, separation is impossible.  Hence `CaseSeparated` can only fire at substructures
whose `RV`-sort is strictly larger than `rv(VF(S))`. -/
theorem not_separated_of_vfgen {S : LRV.Substructure M} {m : M} (hm : iVF m)
    (hm0 : m ≠ Transfer.iVFZero) (hmS : iRv m ∈ S) (hgen : Assembly.IsVFGen S) :
    ¬ M5L.Separated S m := by
  intro hsep
  have h1vf : iVF (Transfer.iVFOne : M) := Transfer.vf_one_mem hM
  have htr : iRV (iRv m) := Transfer.rv_mem hM hm
  rcases hgen (iRv m) hmS htr with ⟨y, hyS, hyvf, hyeq⟩ | hzero
  · have hy0 : y ≠ Transfer.iVFZero := by
      intro h
      exact hm0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hm (by rw [← hyeq, h, RVCalc.rv_zero_eq hM]))
    have hnot := hsep 1 (by norm_num) (Transfer.iVFOne) y h1vf hyvf (vfOne_mem S) hyS
      vfOne_ne_zero hy0
    apply hnot
    rw [RVCalc.rv_one hM]
    rw [hyeq]
    rw [Transfer.rv_mul_one_any_right hM (Transc.iRV_rvpow hM htr 1)]
    show Transc.Cls (iRVMul iRVOne (iRv m)) (iRv m)
    rw [Transfer.rv_mul_one_any hM htr]
    exact Transc.cls_refl hM htr
  · exact hm0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hm hzero)

/-! ## 4. The ledger: where Lemma 3.6's hypotheses sit in the case split -/

/-- The case-split-relevant hypotheses of Lemmas 3.4 and 3.6: the standing assumptions plus the
paper's `e ∈ U(M)`.  (The remaining hypothesis of Lemma 3.6 — "`rv(e)` transcendental over `K(Ŝ)`"
— is not needed for anything in this file; the exclusion of §1 uses `iUnits` alone.) -/
def Lemma36UnitsHyp (S : LRV.Substructure M) (e : M) : Prop :=
  Assembly.Standing S ∧ iVF e ∧ iUnits (iRv e)

/-- The hypothesis bundle of `QE/OneStepCases.lean`'s `CaseSeparated`. -/
def CaseSeparatedHyp (S : LRV.Substructure M) (m : M) : Prop :=
  Assembly.Standing S ∧ iVF m ∧ iRv m ∈ S ∧ M5L.Separated S m

/-- **Lemma 3.6's hypotheses put `e` in the `¬ Separated` slot.**  This is the ledger statement:
whatever else is assumed (transcendence of `rv(e)`, divisibility of `Γ(Ŝ)`), an `e ∈ U(M)` is
never separated, so `CaseSeparated` cannot be the slot that discharges Lemma 3.6 (or Lemma 3.4);
the `CaseNotSeparated` slot is. -/
theorem lemma36UnitsHyp_not_separated {S : LRV.Substructure M} {e : M}
    (h : Lemma36UnitsHyp S e) : ¬ M5L.Separated S e :=
  not_separated_of_units h.2.2

/-- **The inconsistency, stated against the slot**: `CaseSeparated`'s hypothesis bundle is
incompatible with `e ∈ U(M)`.  Contrapositive reading: the separated slot is the paper's
`e ∉ U(M)` regime (Lemma 3.5), and the `¬ Separated` slot is the `e ∈ U(M)` regime
(Lemmas 3.4 and 3.6). -/
theorem caseSeparatedHyp_units_false {S : LRV.Substructure M} {m : M}
    (h : CaseSeparatedHyp S m) (hu : iUnits (iRv m)) : False :=
  separated_not_units h.2.2.2 hu

/-- The same inconsistency in the form "no element whatsoever satisfies both": the separated slot
and the `U(M)` regime are disjoint, at every substructure. -/
theorem separated_units_disjoint (S : LRV.Substructure M) :
    ∀ m : M, ¬ (M5L.Separated S m ∧ iUnits (iRv m)) :=
  fun _ h => separated_not_units h.1 h.2

/-! ## 5. Non-vacuity of the `¬ Separated` slot (the `⊤`-witness the audit owes)

The slot `CaseNotSeparated` is *inhabited*: at `S = ⊤` the standing assumptions hold
(`StandingTree.standing_top`), `m = 1` is a nonzero `VF`-element with `rv(m) ∈ Kˣ` (the paper's
`e ∈ U(M)`), and it satisfies the slot's hypothesis `¬ Separated`.  So the correction of §4 is not
an artefact of an empty slot: units are precisely what lives in that slot. -/

/-- `1 ∈ Kˣ`. -/
theorem iUnits_one : iUnits (iRVOne (M := M)) :=
  (RVCalc.units_iff_le_one hM (Transfer.rv_one_mem hM) (RVCalc.rv_one_ne_zero hM)).mpr
    ⟨RVCalc.le_refl_rv hM (Transfer.rv_one_mem hM), RVCalc.le_refl_rv hM (Transfer.rv_one_mem hM)⟩

/-- `rv 1 ∈ Kˣ`, i.e. the paper's `1 ∈ U(M)`. -/
theorem iUnits_rv_vfOne : iUnits (iRv (Transfer.iVFOne : M)) := by
  rw [RVCalc.rv_one hM]
  exact iUnits_one

/-- **Non-vacuity**: the hypothesis bundle of Lemmas 3.4 / 3.6 (the case-split-relevant part) is
satisfiable, and it lies in the `¬ Separated` slot. -/
theorem lemma36UnitsHyp_satisfiable :
    ∃ (S : LRV.Substructure M) (e : M), Lemma36UnitsHyp S e ∧ ¬ M5L.Separated S e :=
  ⟨⊤, Transfer.iVFOne,
    ⟨StandingTree.standing_top, Transfer.vf_one_mem hM, iUnits_rv_vfOne⟩,
    not_separated_of_units iUnits_rv_vfOne⟩

/-- The `¬ Separated` slot is non-vacuous as a slot of `QE/OneStepCases.lean`'s case split (same
witness, stated without the `Lemma36UnitsHyp` packaging). -/
theorem caseNotSeparated_hyp_satisfiable :
    ∃ (S : LRV.Substructure M) (m : M), Assembly.Standing S ∧ iVF m ∧ ¬ M5L.Separated S m :=
  ⟨⊤, Transfer.iVFOne, StandingTree.standing_top, Transfer.vf_one_mem hM,
    not_separated_of_units iUnits_rv_vfOne⟩

/-! ## 6. The audit, in one statement -/

/-- **Every instance of the `CaseSeparated` slot is a nonzero, non-unit element outside `S`.**

This is the punchline of the audit: `CaseSeparated`'s hypothesis bundle
(`Standing S`, `iVF m`, `iRv m ∈ S`, `Separated S m`) at a nonzero `m` forces `m ∉ S` and
`rv(m) ∉ Kˣ`, i.e. the paper's `e ∉ U(M)` regime — Lemmas 3.5 and 3.7, never 3.4 or 3.6. -/
theorem caseSeparated_instance_properties {S : LRV.Substructure M} {m : M}
    (h : CaseSeparatedHyp S m) (hm0 : m ≠ Transfer.iVFZero) :
    m ∉ S ∧ ¬ iUnits (iRv m) :=
  ⟨fun hmS => not_separated_of_mem hmS h.2.1 hm0 h.2.2.2, separated_not_units h.2.2.2⟩

/-- At a `VF`-generated `S` (in particular at `Ŝ = ⟨VF(S)⟩`) the slot has no nonzero instance at
all. -/
theorem caseSeparated_empty_of_vfgen {S : LRV.Substructure M} {m : M}
    (h : CaseSeparatedHyp S m) (hm0 : m ≠ Transfer.iVFZero) (hgen : Assembly.IsVFGen S) : False :=
  not_separated_of_vfgen h.2.1 hm0 h.2.2.1 hgen h.2.2.2

/-! ### 1′. The same exclusion for Lemma 3.5's `e` (`e^n = a ∈ VF(Ŝ)`)

Lemma 3.5 does not assume `e ∈ U(M)`; its hypothesis is that `e` is a root of `X^n - a` with
`a ∈ VF(Ŝ)` (and `vv(e^i) ∉ Γ(Ŝ)` for `0 < i < n`, which says `vv(e)` has order exactly `n` modulo
`Γ(Ŝ)`).  Separation fails at `k = n` with `x = 1`, `y = a`: `rv(e)^n = rv(e^n) = rv(a)` and
`rv(a) · 1 = rv(a)`.  So the `Separated` slot excludes Lemma 3.5's elements too, and
`QE/OneStepCases.lean`'s `CaseSeparated` is Lemma 3.7's regime only. -/

/-- **`Separated` excludes roots of `X^n - a` over `S`.**  If `0 < n`, `vpow e n = a` with
`a ∈ S` a nonzero `VF`-element, then `e` is not separated. -/
theorem not_separated_of_vpow_mem {S : LRV.Substructure M} {e a : M} {n : ℕ} (hn : 0 < n)
    (he : iVF e) (ha : iVF a) (haS : a ∈ S) (ha0 : a ≠ Transfer.iVFZero)
    (hpow : Transc.vpow e n = a) : ¬ M5L.Separated S e := by
  intro hsep
  have h1vf : iVF (Transfer.iVFOne : M) := Transfer.vf_one_mem hM
  have hnot := hsep n hn (Transfer.iVFOne) a h1vf ha (vfOne_mem S) haS vfOne_ne_zero ha0
  apply hnot
  rw [RVCalc.rv_one hM]
  have hrev : iRV (Transc.rvpow (iRv e) n) :=
    Transc.iRV_rvpow hM (Transfer.rv_mem hM he) n
  rw [Transfer.rv_mul_one_any_right hM hrev]
  rw [← Transc.rv_vpow hM he n, hpow]
  exact Transc.cls_refl hM (Transfer.rv_mem hM ha)

end Lemma36AuditACVF

/-! ## Axiom audit -/

#print axioms Lemma36AuditACVF.units_cls_one
#print axioms Lemma36AuditACVF.vfOne_mem
#print axioms Lemma36AuditACVF.separated_not_units
#print axioms Lemma36AuditACVF.not_separated_of_units
#print axioms Lemma36AuditACVF.not_separated_of_mem
#print axioms Lemma36AuditACVF.separated_top_forces_zero
#print axioms Lemma36AuditACVF.not_separated_of_vfgen
#print axioms Lemma36AuditACVF.lemma36UnitsHyp_not_separated
#print axioms Lemma36AuditACVF.caseSeparatedHyp_units_false
#print axioms Lemma36AuditACVF.separated_units_disjoint

#print axioms Lemma36AuditACVF.iUnits_one
#print axioms Lemma36AuditACVF.iUnits_rv_vfOne
#print axioms Lemma36AuditACVF.lemma36UnitsHyp_satisfiable
#print axioms Lemma36AuditACVF.caseNotSeparated_hyp_satisfiable

#print axioms Lemma36AuditACVF.caseSeparated_instance_properties
#print axioms Lemma36AuditACVF.caseSeparated_empty_of_vfgen

#print axioms Lemma36AuditACVF.not_separated_of_vpow_mem
