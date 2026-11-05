/-
**`Standing` at the top substructure: every model of the frozen `ACVF` is `Standing` at `⊤`.**

`QE/Assembly_frozen.lean`'s `Assembly.prop39P` builds the extension `∃ g : M ↪[LRV] R` through
substructures `S` that are `Standing` (`K(S) = K(M)` and `Γ(S)` divisible).  The two conditions
are *free* at the top substructure of a model:

* `KEqTop ⊤` is vacuous — `⊤` contains every element, in particular every unit;
* `GammaDivisible ⊤` is algebraic closedness plus surjectivity + multiplicativity of `rv`:
  for `t ≠ ∞` in `RV`, choose `x` with `rv x = t` and `w` with `rv w = 1`; an `n`-th root `y` of
  `x` (which exists because `VF` is algebraically closed) gives `u = rv y` with
  `u^n = rv(y^n) = rv x = t`, i.e. `u^n = t · 1`.

The divisibility statement is what `OneStepVFP`'s exhaustion never has to produce at `T = ⊤`;
Lemma 3.3's content is getting proper `S` to the same state.

Everything is proved from `Axioms.ACVF` over the frozen encoding; nothing is assumed.
-/
import RVCalc
import VFField
import VFValued
import VFAlgClosed
import Assembly_frozen

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

set_option linter.style.haveILetI false

namespace SpecialTransformations.Milestone0
namespace StandingTree

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Membership of the `Kˣ`-group axioms in `ACVF`. -/
theorem mem_ACVF_rvGroup {s : LRV.Sentence} (h : s ∈ Axioms.rvGroup) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

/-- **`1 ∈ Kˣ`** — the `rvGroup` axiom `rvOneMem`, realised. -/
theorem rv_one_units : iUnits (iRVOne (M := M)) := by
  have hmem : Axioms.rvOneMem ∈ Axioms.ACVF :=
    mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])
  have h := Transfer.sentence_realize (T := Axioms.ACVF) (M := M) hM hmem
  rw [Axioms.rvOneMem, Sentence.Realize, Formula.Realize] at h
  rw [Transfer.pUnits_realize] at h
  simpa [Transfer.realize_tRVOne_T] using h

/-- `x ^ n` on the `VF` sort, at the level of `M`. -/
def vfPow (x : M) : ℕ → M
  | 0 => Transfer.iVFOne
  | (n + 1) => iVFMul (vfPow x n) x

/-- Powers of a `VF`-element stay in the `VF` sort. -/
theorem vf_pow_mem {x : M} (hx : iVF x) (n : ℕ) : iVF (vfPow x n) := by
  induction n with
  | zero => exact Transfer.vf_one_mem (M := M) hM
  | succ k ih => exact Transfer.vf_mul_mem (M := M) hM ih hx

/-- `x ^ n` in `Transfer.VFType` is `vfPow` at the level of `M`. -/
theorem vfTypePow_val (y : Transfer.VFType (M := M)) (n : ℕ) :
    ((y ^ n : Transfer.VFType (M := M))).1 = vfPow y.1 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hmul : ((y ^ (k + 1) : Transfer.VFType (M := M))).1
        = iVFMul ((y ^ k : Transfer.VFType (M := M))).1 y.1 := by
      rw [pow_succ]; rfl
    rw [hmul, ih]
    rfl

/-- Zero has a trivial power: `vfPow 0 (k+1) = 0`. -/
theorem vfPow_zero_succ (k : ℕ) : vfPow (Transfer.iVFZero (M := M)) (k + 1) = Transfer.iVFZero := by
  have hz : iVF (Transfer.iVFZero (M := M)) := Transfer.vf_zero_mem (M := M) hM
  show iVFMul (vfPow (Transfer.iVFZero (M := M)) k) (Transfer.iVFZero (M := M)) = Transfer.iVFZero
  exact RVCalc.vf_mul_zero hM (vf_pow_mem hz k)

/-- **Every `VF`-element has an `n`-th root** (`n ≥ 1`): the `VF` sort is algebraically closed
(`QF/VFAlgClosed.lean`) and `IsAlgClosed.exists_pow_nat_eq` is the polynomial `X^n - c`. -/
theorem vfType_root (x : Transfer.VFType (M := M)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ y : Transfer.VFType (M := M), y ^ n = x := by
  letI : IsAlgClosed (Transfer.VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType (M := M) (hM := hM)
  exact IsAlgClosed.exists_pow_nat_eq x (by omega)

/-- The same at the level of `M`. -/
theorem vf_root {c : M} (hc : iVF c) {n : ℕ} (hn : 1 ≤ n) :
    ∃ y : M, iVF y ∧ vfPow y n = c := by
  obtain ⟨Y, hY⟩ := vfType_root ⟨c, hc⟩ hn
  exact ⟨Y.1, Y.2, by rw [← vfTypePow_val Y n, hY]⟩

/-- **`Γ(M)` is divisible**: for every nonzero `RV`-element `t` and every `n ≥ 1` there are
`u` (nonzero, in `RV`) and a unit `c` with `u ^ n = t · c` — namely `u = rv y` for an `n`-th
root `y` of any `x` with `rv x = t`, and `c = 1`. -/
theorem gammaDivisible_top : Assembly.GammaDivisible (⊤ : LRV.Substructure M) := by
  intro t _ hrv ht0 n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨x, hxVF, hxr⟩ : ∃ x : M, iVF x ∧ iRv x = t := by
    rcases Assembly.RVeqRvVF_of_model (M := M) t hrv with ⟨x, hx, hxr⟩ | hz
    · exact ⟨x, hx, hxr⟩
    · exact absurd hz ht0
  have hx0 : x ≠ Transfer.iVFZero := by
    intro h
    exact ht0 (by rw [← hxr, h, RVCalc.rv_zero_eq hM])
  obtain ⟨w, hwVF, hwr⟩ : ∃ w : M, iVF w ∧ iRv w = iRVOne := by
    rcases Assembly.RVeqRvVF_of_model (M := M) iRVOne
      (Transfer.rv_one_mem (M := M) hM) with ⟨w, hw, hwr⟩ | hz
    · exact ⟨w, hw, hwr⟩
    · exact absurd hz (RVCalc.rv_one_ne_zero (M := M) hM)
  obtain ⟨y, hy, hypow⟩ := vf_root hxVF (n := k + 1) (by omega)
  have hy0 : y ≠ Transfer.iVFZero := by
    intro h
    have h1 : vfPow y (k + 1) = Transfer.iVFZero := by rw [h]; exact vfPow_zero_succ k
    rw [hypow] at h1
    exact hx0 h1
  have hpow : ∀ k : ℕ, Assembly.rvPow (iRv y) (k + 1) = iRv (iVFMul w (vfPow y (k + 1))) := by
    intro k
    induction k with
    | zero =>
      have h1 : vfPow y (0 + 1) = y := by
        rw [show vfPow y (0 + 1) = iVFMul (vfPow y 0) y from rfl, vfPow]
        rw [Transfer.vf_mul_comm hM (Transfer.vf_one_mem (M := M) hM) hy]
        exact Transfer.vf_mul_one hM hy
      rw [show Assembly.rvPow (iRv y) (0 + 1)
          = iRVMul (Assembly.rvPow (iRv y) 0) (iRv y) from rfl, Assembly.rvPow, h1,
        Transfer.rv_mul_hom_of_model hM hwVF hy, hwr]
    | succ k ih =>
      rw [show Assembly.rvPow (iRv y) (k + 1 + 1)
          = iRVMul (Assembly.rvPow (iRv y) (k + 1)) (iRv y) from rfl, ih,
        ← Transfer.rv_mul_hom_of_model hM
          (Transfer.vf_mul_mem (M := M) hM hwVF (vf_pow_mem hy (k + 1))) hy]
      rw [show iVFMul (iVFMul w (vfPow y (k + 1))) y
          = iVFMul w (iVFMul (vfPow y (k + 1)) y) from
        Transfer.vf_mul_assoc hM hwVF (vf_pow_mem hy (k + 1)) hy]
      rfl
  refine ⟨iRv y, iRVOne, trivial, Transfer.rv_mem hM hy,
    VFValued.rv_ne_zero_of_ne_zero hy hy0, trivial, rv_one_units, ?_⟩
  rw [hpow k, hypow, Transfer.rv_mul_hom_of_model hM hwVF hxVF, hwr, hxr,
    Transfer.rv_mul_comm_of_model hM (Transfer.rv_one_mem (M := M) hM) hrv]

/-- **Every model of `ACVF` is `Standing` at `⊤`.** -/
theorem standing_top : Assembly.Standing (⊤ : LRV.Substructure M) :=
  ⟨fun _ _ => trivial, gammaDivisible_top⟩

end StandingTree
end SpecialTransformations.Milestone0
