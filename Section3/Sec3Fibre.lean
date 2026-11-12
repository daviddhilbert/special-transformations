module

/-
**The `rv`-fibres are infinite** — the geometric input of `alg:ind:imag` (paper `paper.tex`:702),
over the frozen `L_RV` encoding of `Milestone0/Encoding.lean`.

`QE/AlgIndImag.lean` proves `alg:ind:imag` (`M5.alg_ind_imag`), and `QE/AclZero.lean` covers the
case `t = rv 0` (`M5.alg_ind_imag_all`).  The one input still missing there is the *geometric* one,
stated in the tree as the hypothesis

  `hfib : ∀ t, iRV t → t ≠ rv 0 → ¬ 𝕄.Small ↥{x | iVF x ∧ iRv x = t}`

i.e. *the `rv`-fibre of every `t ≠ ∞` is not small in the monster model*.  This file proves it, so
that `alg:ind:imag` (paper.tex:702) follows from **qe.tex Lemma 4.3 (`exchange`) alone**, with no
geometric hypothesis left.

The argument has two halves, and both are in the paper's own spirit (`rv⁻¹(t)` is a coset of the
unit ball `1 + m`, and a definable subset of a `κ`-saturated model of cardinality `Small` must be
finite):

* *infinite*: the axiom `Axioms.axNontrivialRV` of `Milestone0/Encoding.lean` gives `w ≠ 0` with
  `rv w` strictly above `rv 1`, i.e. `w` in the maximal ideal.  Then for every `n ≥ 1` the element
  `1 + wⁿ` has `rv = rv 1` (axiom `rvEqLink`, through `RVCalc.rv_eq_of_close`), and the `1 + wⁿ`
  are pairwise distinct: `1 + wⁿ = 1 + wᵐ` would give `w^(m-n) = 1`, hence
  `(rv w)^(m-n) = rv 1`, which is impossible because `rv w > 1` implies all its positive powers are
  `> 1` (the order axiom `leMulCompatFull`, i.e. `RVCalc.le_mul_iff`, makes `≤` scale-invariant).
  Multiplication by a fixed `x` with `rv x = t` (axiom `rvSurj`) then carries this infinite subset
  of `rv⁻¹(rv 1)` into `rv⁻¹(t)` injectively, so every fibre is infinite.
* *not small*: in a `κ`-saturated model, a definable set of cardinality `< κ` is finite: the type
  `{x ∈ S} ∪ {x ≠ s : s ∈ S}` over the `< κ` parameters `S` is finitely satisfiable (an infinite
  set has an element outside any prescribed finite subset), so it is realized, giving `x ∈ S`
  with `x ≠ x`.

Nothing here is a hypothesis in disguise: every ingredient is either an axiom of the frozen
`ACVF` (read off through the tree's own realisation lemmas) or the saturation data of
`Sat.MonsterACVF`.
-/
public import AclZero
public import MulNormalForm
public import RVCalc
public import VFField
public import Sat

@[expose] public section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M6Fibre

variable {M : Type} [LRV.Structure M]

/-! ## 1. The `rv`-fibre, and powers at the two sorts -/

/-- **`rv⁻¹(t) ∩ VF`** — the `rv`-fibre of `t`, the paper's `rv⁻¹(t)` (at the `VF` sort). -/
def fibre (t : M) : Set M := {x | iVF x ∧ iRv x = t}

/-- `xⁿ` at the `VF` sort (the encoding has no `^` symbol; this is the fold of `×`). -/
def vfPow (x : M) : ℕ → M
  | 0 => Transfer.iVFOne
  | n + 1 => iVFMul (vfPow x n) x

@[simp] theorem vfPow_zero (x : M) : vfPow x 0 = Transfer.iVFOne := rfl

@[simp] theorem vfPow_succ (x : M) (n : ℕ) : vfPow x (n + 1) = iVFMul (vfPow x n) x := rfl

theorem vfPow_mem (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) : ∀ n, iVF (vfPow x n)
  | 0 => Transfer.vf_one_mem hM
  | n + 1 => Transfer.vf_mul_mem hM (vfPow_mem hM hx n) hx

/-- `rv` of a power is the power of `rv` (axiom `rvMulHom`, read as multiplicativity of `rv`). -/
theorem rv_vfPow (hM : M ⊨ Axioms.ACVF) {w : M} (hw : iVF w) :
    ∀ n, iRv (vfPow w n) = MulNormalForm.rvPow (iRv w) n
  | 0 => by rw [vfPow_zero, MulNormalForm.rvPow_zero, RVCalc.rv_one hM]
  | n + 1 => by
    rw [vfPow_succ, MulNormalForm.rvPow_succ,
      Transfer.rv_mul_hom_of_model hM (vfPow_mem hM hw n) hw, rv_vfPow hM hw n]

/-! ## 2. Nontriviality: an element of the maximal ideal -/

/-- **`Axioms.axNontrivialRV`**: some nonzero `w` of the `VF` sort has value strictly below the
value of `1`, i.e. lies in the maximal ideal.  (This is the encoding's nontriviality axiom; without
it `alg:ind:imag` is false, since a trivially valued field has `rv` injective.) -/
theorem exists_maximal_ideal (hM : M ⊨ Axioms.ACVF) :
    ∃ w : M, iVF w ∧ w ≠ Transfer.iVFZero ∧ ¬ iLe (iRv w) iRVOne := by
  have h := hM.realize_of_mem Axioms.axNontrivialRV RVCalc.mem_ACVF_axNontrivialRV
  rw [Axioms.axNontrivialRV, Sentence.Realize] at h
  have h' := (MulNormalForm.exSorted_realize SortTag.vf
    (∼(pEq (tv 0 Nat.zero_lt_one) tVFZero) ⊓
      ∼(pLe (tRv (tv 0 Nat.zero_lt_one)) (tRv tVFOne)))
    (default : Empty → M) (fun i : Fin 0 => i.elim0)).mp h
  obtain ⟨w, hw, hw2⟩ := h'
  have hw3 : (∼(pEq (tv 0 Nat.zero_lt_one) tVFZero) ⊓
      ∼(pLe (tRv (tv 0 Nat.zero_lt_one)) (tRv tVFOne))).Realize (default : Empty → M)
        (Fin.snoc (fun i : Fin 0 => i.elim0) w) := hw2
  rw [BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_not] at hw3
  refine ⟨w, hw, ?_, ?_⟩
  · simp only [pEq, BoundedFormula.realize_bdEqual, MulNormalForm.realize_tv_last_apply,
      Transfer.realize_tVFZero] at hw3
    exact hw3.1
  · simp only [Transfer.realize_pLe, Transfer.realize_tRv, MulNormalForm.realize_tv_last_apply,
      Transfer.realize_tVFOne, RVCalc.rv_one hM] at hw3
    exact hw3.2

/-! ## 3. Powers of an element strictly above `1` -/

theorem rvPow_ne_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iRV x) (hx0 : x ≠ iRVZero) :
    ∀ n, MulNormalForm.rvPow x n ≠ iRVZero
  | 0 => by
    rw [MulNormalForm.rvPow_zero]
    exact MulNormalForm.rv_one_ne_zero hM
  | n + 1 => by
    rw [MulNormalForm.rvPow_succ]
    exact MulNormalForm.rv_mul_ne_zero hM (MulNormalForm.rvPow_mem hM hx n) hx
      (rvPow_ne_zero hM hx hx0 n) hx0

/-- **`1 ≤ x` gives `x ≤ xⁿ`** for `n ≥ 1`, in the preordered group `RV^×`.
(The proof is the standard one: `1 ≤ x` multiplied by `xᵏ` gives `xᵏ ≤ xᵏ⁺¹`, and order scaling is
the axiom `leMulCompatFull`, read as `RVCalc.le_mul_iff`.) -/
theorem le_rvPow_self (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iRV x) (hx0 : x ≠ iRVZero)
    (h1 : iLe iRVOne x) : ∀ k : ℕ, iLe x (MulNormalForm.rvPow x (k + 1)) := by
  intro k
  induction k with
  | zero =>
    rw [MulNormalForm.rvPow_succ, MulNormalForm.rvPow_zero,
      MulNormalForm.rv_mul_one_all hM hx]
    exact RVCalc.le_refl_rv hM hx
  | succ k ih =>
    have hc : iRV (MulNormalForm.rvPow x (k + 1)) :=
      MulNormalForm.rvPow_mem hM hx (k + 1)
    have hc0 : MulNormalForm.rvPow x (k + 1) ≠ iRVZero := rvPow_ne_zero hM hx hx0 (k + 1)
    have hm := (RVCalc.le_mul_iff hM (MulNormalForm.rv_one_mem hM) hx hc hc0).mp h1
    have hstep : iLe (MulNormalForm.rvPow x (k + 1)) (MulNormalForm.rvPow x (k + 1 + 1)) := by
      rw [MulNormalForm.rv_mul_one_all hM hc, MulNormalForm.rv_mul_comm hM hx hc,
        ← MulNormalForm.rvPow_succ] at hm
      exact hm
    exact RVCalc.le_trans_rv hM hx (MulNormalForm.rvPow_mem hM hx (k + 1))
      (MulNormalForm.rvPow_mem hM hx (k + 1 + 1)) ih hstep

/-- **No positive power of an element strictly above `1` is `≤ 1`.** -/
theorem not_le_rvPow_one (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iRV x) (hx0 : x ≠ iRVZero)
    (h1 : iLe iRVOne x) (h2 : ¬ iLe x iRVOne) :
    ∀ k : ℕ, ¬ iLe (MulNormalForm.rvPow x (k + 1)) iRVOne := by
  intro k h
  exact h2 (RVCalc.le_trans_rv hM hx (MulNormalForm.rvPow_mem hM hx (k + 1))
    (MulNormalForm.rv_one_mem hM) (le_rvPow_self hM hx hx0 h1 k) h)

/-- **`x^(a+b) = x^a · x^b`** in `RV^×` (the multiplicative group axioms). -/
theorem rvPow_add (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iRV x) (a b : ℕ) :
    MulNormalForm.rvPow x (a + b)
      = iRVMul (MulNormalForm.rvPow x a) (MulNormalForm.rvPow x b) := by
  induction b with
  | zero =>
    rw [Nat.add_zero, MulNormalForm.rvPow_zero,
      MulNormalForm.rv_mul_one_right hM (MulNormalForm.rvPow_mem hM hx a)]
  | succ b ih =>
    rw [Nat.add_succ, MulNormalForm.rvPow_succ, ih, MulNormalForm.rvPow_succ,
      MulNormalForm.rv_mul_assoc hM (MulNormalForm.rvPow_mem hM hx a)
        (MulNormalForm.rvPow_mem hM hx b) hx]

/-! ## 4. `1 + wⁿ` lies in the fibre of `rv 1` -/

/-- `(1 + a) - 1 = a` at the `VF` sort. -/
theorem one_add_sub_one (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iVF a) :
    iVFAdd (iVFAdd Transfer.iVFOne a) (iVFNeg Transfer.iVFOne) = a := by
  have h1 : iVF (Transfer.iVFOne (M := M)) := Transfer.vf_one_mem hM
  have hneg : iVF (iVFNeg (Transfer.iVFOne (M := M))) := Transfer.vf_neg_mem hM h1
  rw [RVCalc.vf_add_assoc hM h1 ha hneg, RVCalc.vf_add_comm hM ha hneg,
    ← RVCalc.vf_add_assoc hM h1 hneg ha, RVCalc.vf_add_neg hM h1, RVCalc.vf_zero_add hM ha]

/-- The hypotheses on `w`, collected: `iRv w` is a nonzero `RV`-element strictly above `1`. -/
theorem rv_gt_one (hM : M ⊨ Axioms.ACVF) {w : M} (hw : iVF w) (hw0 : w ≠ Transfer.iVFZero)
    (hgt : ¬ iLe (iRv w) iRVOne) :
    iRV (iRv w) ∧ iRv w ≠ iRVZero ∧ iLe iRVOne (iRv w) := by
  have hwrv : iRV (iRv w) := Transfer.rv_mem hM hw
  have hx0 : iRv w ≠ iRVZero := by
    intro h
    exact hw0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hw h)
  refine ⟨hwrv, hx0, ?_⟩
  rcases RVCalc.le_total_rv hM hwrv (MulNormalForm.rv_one_mem hM) with h | h
  · exact absurd h hgt
  · exact h

/-- **`rv (1 + wⁿ) = rv 1`** for `w` in the maximal ideal and `n ≥ 1`: the axiom `rvEqLink` in the
form `RVCalc.rv_eq_of_close`, since `(1 + wⁿ) - 1 = wⁿ` has value strictly above `rv 1`. -/
theorem rv_one_add_pow (hM : M ⊨ Axioms.ACVF) {w : M} (hw : iVF w) (hw0 : w ≠ Transfer.iVFZero)
    (hgt : ¬ iLe (iRv w) iRVOne) (n : ℕ) :
    iRv (iVFAdd Transfer.iVFOne (vfPow w (n + 1))) = iRVOne := by
  obtain ⟨hwrv, hx0, h1⟩ := rv_gt_one hM hw hw0 hgt
  have hp : ¬ iLe (iRv (vfPow w (n + 1))) iRVOne := by
    rw [rv_vfPow hM hw]
    exact not_le_rvPow_one hM hwrv hx0 h1 hgt n
  have hone : iVF (Transfer.iVFOne (M := M)) := Transfer.vf_one_mem hM
  have hsub : iVF (iVFAdd Transfer.iVFOne (vfPow w (n + 1))) :=
    Transfer.vf_add_mem hM hone (vfPow_mem hM hw (n + 1))
  have hmain := RVCalc.rv_eq_of_close hM hsub hone
    (fun h => Transfer.vf_zero_ne_one hM h.symm) ?_
  · rw [hmain, RVCalc.rv_one hM]
  · rw [one_add_sub_one hM (vfPow_mem hM hw (n + 1)), RVCalc.rv_one hM]
    exact hp

/-! ## 5. Cancellation in the field `VF`, and distinctness of the `1 + wⁿ` -/

/-- **Cancellation of a nonzero factor in `VF`** (the field axioms plus the existence of inverses). -/
theorem vf_mul_left_cancel (hM : M ⊨ Axioms.ACVF) {x u v : M} (hx : iVF x) (hu : iVF u)
    (hv : iVF v) (hx0 : x ≠ Transfer.iVFZero) (h : iVFMul x u = iVFMul x v) : u = v := by
  have hone : iVF (Transfer.iVFOne (M := M)) := Transfer.vf_one_mem hM
  obtain ⟨y, hy, hxy⟩ := (Transfer.vf_mul_inv_or_zero hM hx).resolve_left hx0
  have hyx : iVFMul y x = Transfer.iVFOne := by
    rw [Transfer.vf_mul_comm hM hy hx]; exact hxy
  calc u = iVFMul Transfer.iVFOne u := by
        rw [Transfer.vf_mul_comm hM hone hu, Transfer.vf_mul_one hM hu]
    _ = iVFMul (iVFMul y x) u := by rw [hyx]
    _ = iVFMul y (iVFMul x u) := Transfer.vf_mul_assoc hM hy hx hu
    _ = iVFMul y (iVFMul x v) := by rw [h]
    _ = iVFMul (iVFMul y x) v := (Transfer.vf_mul_assoc hM hy hx hv).symm
    _ = iVFMul Transfer.iVFOne v := by rw [hyx]
    _ = v := by rw [Transfer.vf_mul_comm hM hone hv]; exact Transfer.vf_mul_one hM hv

/-- **`n < m` gives `1 + wⁿ ≠ 1 + wᵐ`**, for `w` in the maximal ideal: cancelling `1` leaves
`wⁿ = wᵐ`, hence `(rv w)ⁿ = (rv w)ᵐ`, hence `(rv w)^(m-n) = 1` by cancellation inside the group
`RV^×` — contradicting `not_le_rvPow_one` (`rv w > 1` implies all its positive powers are `> 1`). -/
theorem one_add_pow_ne_of_lt (hM : M ⊨ Axioms.ACVF) {w : M} (hw : iVF w)
    (hw0 : w ≠ Transfer.iVFZero) (hgt : ¬ iLe (iRv w) iRVOne) {n m : ℕ} (hnm : n < m) :
    iVFAdd Transfer.iVFOne (vfPow w n) ≠ iVFAdd Transfer.iVFOne (vfPow w m) := by
  intro h
  obtain ⟨hwrv, hx0, h1⟩ := rv_gt_one hM hw hw0 hgt
  have hone : iVF (Transfer.iVFOne (M := M)) := Transfer.vf_one_mem hM
  have hpow : vfPow w n = vfPow w m :=
    RVCalc.vf_add_left_cancel hM hone (vfPow_mem hM hw n) (vfPow_mem hM hw m) h
  have hrv : MulNormalForm.rvPow (iRv w) n = MulNormalForm.rvPow (iRv w) m := by
    rw [← rv_vfPow hM hw, ← rv_vfPow hM hw]; exact congrArg iRv hpow
  have hxn : MulNormalForm.rvPow (iRv w) n ≠ iRVZero := rvPow_ne_zero hM hwrv hx0 n
  have hsum : n + (m - n) = m := by omega
  have hkey : iRVMul (MulNormalForm.rvPow (iRv w) n) (MulNormalForm.rvPow (iRv w) (m - n))
      = iRVMul (MulNormalForm.rvPow (iRv w) n) iRVOne := by
    rw [← rvPow_add hM hwrv n (m - n), hsum, ← hrv,
      MulNormalForm.rv_mul_one_right hM (MulNormalForm.rvPow_mem hM hwrv n)]
  have hmn : MulNormalForm.rvPow (iRv w) (m - n) = iRVOne :=
    MulNormalForm.rv_mul_left_cancel hM (MulNormalForm.rvPow_mem hM hwrv n)
      (MulNormalForm.rvPow_mem hM hwrv (m - n)) (MulNormalForm.rv_one_mem hM) hxn hkey
  have hle : iLe (MulNormalForm.rvPow (iRv w) (m - n)) iRVOne := by
    rw [hmn]; exact RVCalc.le_refl_rv hM (MulNormalForm.rv_one_mem hM)
  obtain ⟨k, hk⟩ : ∃ k, m - n = k + 1 := ⟨m - n - 1, by omega⟩
  rw [hk] at hle
  exact absurd hle (not_le_rvPow_one hM hwrv hx0 h1 hgt k)

/-- **`1 + wⁿ = 1 + wᵐ` forces `n = m`** for `w` in the maximal ideal. -/
theorem one_add_pow_inj (hM : M ⊨ Axioms.ACVF) {w : M} (hw : iVF w) (hw0 : w ≠ Transfer.iVFZero)
    (hgt : ¬ iLe (iRv w) iRVOne) {n m : ℕ}
    (h : iVFAdd Transfer.iVFOne (vfPow w n) = iVFAdd Transfer.iVFOne (vfPow w m)) : n = m := by
  rcases lt_trichotomy n m with hlt | heq | hgt'
  · exact absurd h (one_add_pow_ne_of_lt hM hw hw0 hgt hlt)
  · exact heq
  · exact absurd h.symm (one_add_pow_ne_of_lt hM hw hw0 hgt hgt')

/-! ## 6. The fibre of `rv 1` is infinite -/

/-- **`rv⁻¹(rv 1) ∩ VF` is infinite**: it contains `1 + wⁿ` for every `n`, and those are pairwise
distinct (part 5). -/
theorem fibre_one_infinite (hM : M ⊨ Axioms.ACVF) :
    (fibre (iRVOne : M)).Infinite := by
  obtain ⟨w, hw, hw0, hgt⟩ := exists_maximal_ideal hM
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => iVFAdd Transfer.iVFOne (vfPow w (n + 1))) ?_ ?_
  · intro n m hnm
    have h' := one_add_pow_inj hM hw hw0 hgt hnm
    omega
  · intro n
    exact ⟨Transfer.vf_add_mem hM (Transfer.vf_one_mem hM) (vfPow_mem hM hw (n + 1)),
      rv_one_add_pow hM hw hw0 hgt n⟩

/-! ## 7. Every `rv`-fibre of a nonzero `t` is infinite -/

/-- **`Axioms.rvSurj`**: every `RV`-element other than `rv 0 = ∞` is `rv x` for some `x ∈ VF`. -/
theorem exists_rv_eq (hM : M ⊨ Axioms.ACVF) {t : M} (ht : iRV t) (ht0 : t ≠ iRVZero) :
    ∃ x : M, iVF x ∧ iRv x = t := by
  have hmem : Axioms.rvSurj ∈ Axioms.ACVF :=
    RVCalc.mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])
  let θ : LRV.BoundedFormula Empty 2 :=
    pEq (tRv (tv 1 (by omega))) (tv 0 (by omega))
  have h := Transfer.allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (∼(pEq (tv 0 Nat.zero_lt_one) tRVZero) ⟹ LRV.exSorted SortTag.vf θ))
    hmem ![t] (by intro i; fin_cases i; simpa using ht)
  have h2 : t ≠ iRVZero → (LRV.exSorted SortTag.vf θ).Realize (default : Empty → M) ![t] := by
    simpa [pEq, BoundedFormula.realize_bdEqual, Transfer.realize_tv, Transfer.realize_tRVZero,
      Matrix.cons_val_zero, tRVInfty] using h
  have h4 := (MulNormalForm.exSorted_realize SortTag.vf θ (default : Empty → M) ![t]).mp (h2 ht0)
  obtain ⟨x, hx, hx2⟩ := h4
  refine ⟨x, hx, ?_⟩
  simpa [θ, pEq, BoundedFormula.realize_bdEqual, Transfer.realize_tv, Transfer.realize_tRv,
    MulNormalForm.realize_tv_last_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using hx2

/-- **Every `rv`-fibre of a nonzero `t` is infinite.**  Multiplication by a fixed `x` with `rv x = t`
maps the infinite set `rv⁻¹(rv 1)` (part 6) injectively into `rv⁻¹(t)`, because
`rv (x·u) = rv x · rv u` and `rv u = rv 1` is the identity of the multiplicative group `RV^×`. -/
theorem fibre_infinite (hM : M ⊨ Axioms.ACVF) {t : M} (ht : iRV t) (ht0 : t ≠ iRVZero) :
    (fibre t).Infinite := by
  obtain ⟨x, hx, hxt⟩ := exists_rv_eq hM ht ht0
  have hx0 : x ≠ Transfer.iVFZero := by
    intro h
    exact ht0 (by rw [← hxt, h, RVCalc.rv_zero_eq hM])
  haveI : Infinite ↥(fibre (iRVOne : M)) := Set.infinite_coe_iff.mpr (fibre_one_infinite hM)
  refine Set.infinite_of_injective_forall_mem
    (f := fun u : ↥(fibre (iRVOne : M)) => iVFMul x u.1) ?_ ?_
  · intro u v huv
    have h1 : u.1 = v.1 :=
      vf_mul_left_cancel hM hx u.2.1 v.2.1 hx0 huv
    exact Subtype.ext h1
  · intro u
    refine ⟨Transfer.vf_mul_mem hM hx u.2.1, ?_⟩
    rw [Transfer.rv_mul_hom_of_model hM hx u.2.1, hxt, u.2.2,
      MulNormalForm.rv_mul_one_right hM ht]


/-! ## 8. Realisation of the formula shapes at an arbitrary parameter type -/

/-- The free variable of a one-variable formula with parameters `α`. -/
def var0 {α : Type} : LRV.Term (α ⊕ Fin 1) := Term.var (Sum.inr (0 : Fin 1))

/-- A parameter of type `α` as a term. -/
def varParam {α : Type} (a : α) : LRV.Term (α ⊕ Fin 1) := Term.var (Sum.inl a)

/-- `rv` applied to a term of a one-variable formula. -/
def rvTm {α : Type} (t : LRV.Term (α ⊕ Fin 1)) : LRV.Term (α ⊕ Fin 1) :=
  Term.func Fn.rvMap ![t]

/-- `t ∈ VF` realised at an arbitrary parameter type. -/
theorem pVFG_realize {α : Type} {n : ℕ} (t : LRV.Term (α ⊕ Fin n)) (v : α → M)
    (xs : Fin n → M) :
    (pVFG t : LRV.BoundedFormula α n).Realize v xs ↔ iVF (Term.realize (Sum.elim v xs) t) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF
      (fun i => Term.realize (L := LRV) (Sum.elim v xs) (![t] i))
      ↔ iVF (Term.realize (Sum.elim v xs) t)
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v xs) (![t] i))
      = ![Term.realize (Sum.elim v xs) t] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem realize_var0 {α : Type} (v : α → M) (xs : Fin 1 → M) :
    Term.realize (Sum.elim v xs) (var0 (α := α)) = xs 0 := rfl

theorem realize_varParam {α : Type} (v : α → M) (xs : Fin 1 → M) (a : α) :
    Term.realize (Sum.elim v xs) (varParam a) = v a := rfl

theorem realize_rvTm_var0 {α : Type} (v : α → M) (xs : Fin 1 → M) :
    Term.realize (Sum.elim v xs) (rvTm (var0 (α := α))) = iRv (xs 0) := by
  let z : LRV.Term (α ⊕ Fin 1) := var0 (α := α)
  have h1 : Term.realize (Sum.elim v xs) (rvTm z)
      = Structure.funMap (L := LRV) Fn.rvMap
          (fun i : Fin 1 => Term.realize (L := LRV) (Sum.elim v xs) (![z] i)) :=
    Term.realize_func _ _ _
  have h2 : (fun i : Fin 1 => Term.realize (Sum.elim v xs) (![z] i)) = ![xs 0] := by
    funext i
    fin_cases i
    simp [z, var0]
  rw [show rvTm (var0 (α := α)) = rvTm z from rfl, h1, h2]
  rfl

theorem realize_rvTm_param {α : Type} (v : α → M) (xs : Fin 1 → M) (a : α) :
    Term.realize (Sum.elim v xs) (rvTm (varParam a)) = iRv (v a) := by
  let z : LRV.Term (α ⊕ Fin 1) := varParam a
  have h1 : Term.realize (Sum.elim v xs) (rvTm z)
      = Structure.funMap (L := LRV) Fn.rvMap
          (fun i : Fin 1 => Term.realize (L := LRV) (Sum.elim v xs) (![z] i)) :=
    Term.realize_func _ _ _
  have h2 : (fun i : Fin 1 => Term.realize (Sum.elim v xs) (![z] i)) = ![v a] := by
    funext i
    fin_cases i
    simp [z, varParam]
  rw [show rvTm (varParam a) = rvTm z from rfl, h1, h2]
  rfl

/-! ## 9. A definable set of cardinality `< κ` in a monster model is finite -/

/-- **The counting step of `alg:ind:imag`**: in a `κ`-saturated model, a *definable* set of
cardinality `< κ` is finite.  Contrapositive of the standard saturation argument: if `S` is infinite
and `|S| < κ`, the type `{x ∈ rv⁻¹(t)} ∪ {x ≠ s : s ∈ S}` over the `< κ` parameters `S` is finitely
satisfiable — an infinite set has an element outside any prescribed finite subset — so it is
realized, giving `x ∈ S` with `x ≠ x`.

The fibre is definable by the single formula `rv x = t`, and every point of the fibre is taken as a
parameter, which is what makes the disequalities available; that parameter set is `Small` by
hypothesis. -/
theorem not_small_of_infinite_fibre (𝕄 : Sat.MonsterACVF) {t : 𝕄.M} (ht : iRV t) :
    (fibre t).Infinite → ¬ 𝕄.Small ↥(fibre t) := by
  intro hinf hsmall
  classical
  obtain ⟨s₀, hs₀⟩ := hinf.nonempty
  let A := ↥(fibre t)
  let a₀ : A := ⟨s₀, hs₀⟩
  let v : A → 𝕄.M := fun a => a.1
  let θ : LRV.BoundedFormula A 1 :=
    pVFG (var0 (α := A)) ⊓ pEqG (rvTm (var0 (α := A))) (rvTm (varParam a₀))
  let δ : A → LRV.BoundedFormula A 1 := fun s => ∼(pEqG (var0 (α := A)) (varParam s))
  let p : Set (LRV.BoundedFormula A 1) := {θ} ∪ Set.range δ
  have hθiff : ∀ y : 𝕄.M, θ.Realize v ![y] ↔ (iVF y ∧ iRv y = iRv (v a₀)) := by
    intro y
    show (pVFG (var0 (α := A)) ⊓ pEqG (rvTm (var0 (α := A))) (rvTm (varParam a₀))).Realize v ![y]
      ↔ (iVF y ∧ iRv y = iRv (v a₀))
    rw [BoundedFormula.realize_inf, pVFG_realize, pEqG, BoundedFormula.realize_bdEqual,
      realize_var0, realize_rvTm_var0, realize_rvTm_param]
    exact Iff.rfl
  have hδiff : ∀ (s : A) (y : 𝕄.M), (δ s).Realize v ![y] ↔ y ≠ v s := by
    intro s y
    show (∼(pEqG (var0 (α := A)) (varParam s))).Realize v ![y] ↔ y ≠ v s
    rw [BoundedFormula.realize_not, pEqG, BoundedFormula.realize_bdEqual, realize_var0,
      realize_varParam]
    exact Iff.rfl
  have hsatisfiable : Sat.FinitelySatisfiable v p := by
    intro l hl
    let avoid : LRV.BoundedFormula A 1 → A := fun φ =>
      if h : ∃ s, δ s = φ then Classical.choose h else a₀
    let avoidM : LRV.BoundedFormula A 1 → 𝕄.M := fun φ => (avoid φ).1
    have havoid : ∀ (φ : LRV.BoundedFormula A 1) (h : ∃ s : A, δ s = φ), δ (avoid φ) = φ := by
      intro φ h
      simp only [avoid, dif_pos h]
      exact Classical.choose_spec h
    have hfin : (avoidM '' {φ : LRV.BoundedFormula A 1 | φ ∈ l}).Finite :=
      l.finite_toSet.image avoidM
    have hnotsub : ¬ (fibre t) ⊆ (avoidM '' {φ : LRV.BoundedFormula A 1 | φ ∈ l}) := by
      intro hsub
      exact hinf (hfin.subset hsub)
    obtain ⟨y, hyfib, hyavoid⟩ := Set.not_subset.mp hnotsub
    have hyavoid' : ∀ (φ : LRV.BoundedFormula A 1), φ ∈ l → avoidM φ ≠ y := by
      intro φ hφl hcon
      exact hyavoid ⟨φ, hφl, hcon⟩
    refine ⟨![y], ?_⟩
    intro φ hφ
    rcases hl φ hφ with hθ | hδ
    · subst hθ
      rw [hθiff]
      exact ⟨hyfib.1, by rw [hyfib.2, hs₀.2]⟩
    · obtain ⟨s, rfl⟩ := hδ
      have hspec : δ (avoid (δ s)) = δ s := havoid (δ s) ⟨s, rfl⟩
      have hyne : y ≠ v (avoid (δ s)) := fun hcon =>
        hyavoid' (δ s) hφ (hcon ▸ rfl)
      have hreal : (δ (avoid (δ s))).Realize v ![y] := (hδiff (avoid (δ s)) y).mpr hyne
      rwa [hspec] at hreal
  obtain ⟨xs, hxs⟩ := 𝕄.realizes v hsmall (p := p) hsatisfiable
  have hxs0 : xs = ![xs 0] := by
    funext i
    fin_cases i
    rfl
  have hθ := hxs θ (Set.mem_union_left _ rfl)
  rw [hxs0, hθiff] at hθ
  obtain ⟨hVF, hrv⟩ := hθ
  have hmem : xs 0 ∈ fibre t := ⟨hVF, by rw [hrv]; exact hs₀.2⟩
  have hne := hxs (δ ⟨xs 0, hmem⟩) (Set.mem_union_right _ ⟨⟨xs 0, hmem⟩, rfl⟩)
  have hne0 : (δ ⟨xs 0, hmem⟩).Realize v ![xs 0] := hxs0 ▸ hne
  rw [hδiff] at hne0
  exact hne0 rfl

/-- **The `rv`-fibre of every `t ≠ ∞` is not small.**  This is the geometric input `hfib` of
`M5.alg_ind_imag` (`QE/AlgIndImag.lean`) and `M5.alg_ind_imag_all` (`QE/AclZero.lean`). -/
theorem fibre_not_small (𝕄 : Sat.MonsterACVF) {t : 𝕄.M} (ht : iRV t) (ht0 : t ≠ iRVZero) :
    ¬ 𝕄.Small ↥(fibre t) :=
  not_small_of_infinite_fibre 𝕄 ht (fibre_infinite 𝕄.isModel ht ht0)

/-! ## 10. `alg:ind:imag` (paper.tex:702) with no geometric hypothesis -/

/-- **`alg:ind:imag`**, paper §3 (`paper.tex`:702), in the shape of the frozen target
`SP.swl_alg_ind_image` of `QE/Sec3_sat.lean`: *"If `a ∈ VF` is such that `a ∉ acl(0)`, then for any
`t ∈ RV` we have `a ∉ acl(t)`."*

The only model-theoretic input left is **Yin, `QE:ACVF:min`, Lemma 4.3** (`exchange`, the paper's
own citation for this corollary), carried as the named hypothesis `hex`; `hκ` and `hcnt` are the
metamathematical finiteness of the syntax that `M5.acl_small_of_countable` isolates (`κ > ℵ₀` and
countably many formulas).  The geometric input `hfib` that `QE/AlgIndImag.lean` had to assume is
*proved* here (`fibre_not_small`). -/
theorem alg_ind_imag (𝕄 : Sat.MonsterACVF.{0, 0}) (hex : M5.ExchangeVF 𝕄) (a t : 𝕄.M)
    (ha : iVF a)
    (ht : iRV t) (hκ : Cardinal.aleph0 < 𝕄.κ)
    (hcnt : Countable (LRV.BoundedFormula (Fin 1 ⊕ Fin 0) 1))
    (h : ¬ SP.acl (SP.base (M := 𝕄.M)) a) : ¬ SP.acl (SP.singleRV t ht) a :=
  M5.alg_ind_imag_all hex a ha (M5.acl_small_of_countable hκ hcnt a ha) h
    (fun t ht ht0 => fibre_not_small 𝕄 ht ht0) t ht

end SpecialTransformations.Milestone0.M6Fibre

/-! ## 11. Verification of the axioms used -/

#print axioms SpecialTransformations.Milestone0.M6Fibre.fibre_infinite
#print axioms SpecialTransformations.Milestone0.M6Fibre.fibre_one_infinite
#print axioms SpecialTransformations.Milestone0.M6Fibre.not_small_of_infinite_fibre
#print axioms SpecialTransformations.Milestone0.M6Fibre.fibre_not_small
#print axioms SpecialTransformations.Milestone0.M6Fibre.alg_ind_imag
