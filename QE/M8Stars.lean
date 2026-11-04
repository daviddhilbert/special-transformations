/-
# Claim (⋆) in the frozen `LRV` encoding: the RV half, the divisibility half, and a defect in the
# `hdist` hypothesis that the previous swarm's `exists_rv_vfSum` used

Member `m8`, swarm `smw1ukwfb`.  Direction `d3`: shared infrastructure for the case lemmas
(paper's Lemmas 3.4-3.8), rather than the wiring of any one case.

## Contents

* §1 closure of an `LRV`-substructure under the `RV`-operations (`iRVMul`, `iRVOne`, `iRV*` powers).
* §2 **A defect in `M8.exists_rv_vfSum`** (and hence in `exists_rv_vfSum_pow`,
  `vfSum_ne_zero_of_distinct`, and in `qe.tex`'s line "so `rv (∑ b_i e^i) = rv (b_j e^j)` for some
  `j`" as the previous swarm transcribed it).  Its hypothesis is
  `¬ iLe a b ∧ ¬ iLe b a`, "neither class dominates the other".  In this encoding `iLe` on `RV` is
  *total* (`RVCalc.le_total_rv`, the axiom `leTotal` with `0` absorbing), so **that conjunction is
  never true**: no two `RV`-elements have incomparable classes.  `hdist_false` proves it, and
  `hdist_unsat` concludes that `exists_rv_vfSum` is vacuous for every length `≥ 2`.
* §3 the repair: the correct hypothesis is `¬ (iLe a b ∧ iLe b a)`, **"the classes differ"** (which
  under totality means exactly one direction holds).  `exists_rv_vfSum'` and
  `exists_rv_vfSum_pow'` are the previous lemma with that hypothesis, and they are *not* vacuous:
  `hne_of_cls` shows two different classes satisfy it.
* §4 the separation hypothesis of Lemma 3.5 implies `hne` (`hne_of_sep`), which is the paper's
  `vv(e^k) ∉ Γ(Ŝ) ⟹ vv(b_i e^i) ≠ vv(b_j e^j)`, and `hne_of_sep'` removes the order on `i, j`.
* §5 **the `RV`-control for an expansion**: if the coefficients' `rv` and `rv(e)` lie in `S`, then
  so does `rv (∑_{i<n} b_i e^i)`.  This is `RV(⟨Ŝ,e⟩) ⊆ RV(S)` restricted to polynomials, i.e. the
  first half of the paper's Claim (⋆) on the part of `VF(⟨Ŝ,e⟩)` a case lemma can reach without
  field inverses.
* §6 the paper's device for the whole claim: `RV`-control for the closure is what the case lemmas
  owe (`RVcontrol`), it is equivalent to a term-level statement (`RVcontrol_iff_term`), and it
  follows from exhibiting any substructure with the `RV`-property (`RVcontrol_of_le`) — the
  `Substructure.closure_le` induction replaces a term induction.  §7 composes it with the tree's
  generic embedding step to get the frozen `OneStepRVOld`.

Only `RVCalc` (through the repaired `M8RVAlg`) is used in §1-§5; §6-§7 also use
`Assembly_frozen` and `M5OneStep`.  No `sorry`, no `axiom`, no `native_decide`.
-/
import M8RVAlg
import Assembly_frozen
import M5OneStep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations.Milestone0
namespace M8Stars

open LRV
open RVCalc
open Transfer
open SpecialTransformations.Milestone0.M8

variable {M : Type} [LRV.Structure M]

/-! ## 1. An `LRV`-substructure is closed under the `RV`-operations -/

theorem rvMul_mem_sub (S : LRV.Substructure M) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    iRVMul x y ∈ S := by
  unfold iRVMul
  exact S.fun_mem Fn.rvMul ![x, y] (by intro i; fin_cases i <;> simpa)

theorem rvOne_mem_sub (S : LRV.Substructure M) : iRVOne (M := M) ∈ S := by
  unfold iRVOne
  exact S.fun_mem Fn.rvOne (fun i => i.elim0) (by intro i; exact i.elim0)

theorem rv_mem_sub (S : LRV.Substructure M) {x : M} (hx : x ∈ S) (hxVF : iVF x) :
    iRv x ∈ S := by
  unfold iRv
  exact S.fun_mem Fn.rvMap ![x] (by intro i; fin_cases i; simpa using hx)

theorem rvPowM_mem_sub (S : LRV.Substructure M) {r : M} (hr : r ∈ S) :
    ∀ n : ℕ, rvPowM r n ∈ S
  | 0 => rvOne_mem_sub S
  | (n + 1) => rvMul_mem_sub S (rvPowM_mem_sub S hr n) hr

/-! ## 2. The `hdist` hypothesis of `M8.exists_rv_vfSum` is unsatisfiable

`RVCalc.le_total_rv` is the encoding's `leTotal`, with `0` (the top, `∞`) absorbing: for *every*
pair of `RV`-elements, `a ≤ b` or `b ≤ a`.  So "neither dominates the other" — the hypothesis under
which `M8.exists_rv_vfSum` computes the leading term — can never hold, and the lemma is vacuous.
Note this is a statement about the *hypothesis*, not about the encoding: the paper's "the values are
different" is `¬ (a ≤ b ∧ b ≤ a)` (the classes differ), which is satisfiable and is what §3 uses. -/

theorem hdist_false (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b) :
    ¬ (¬ iLe a b ∧ ¬ iLe b a) := by
  rintro ⟨h1, h2⟩
  rcases le_total_rv hM ha hb with h | h
  · exact h1 h
  · exact h2 h

/-- **`M8.exists_rv_vfSum`'s hypothesis is unsatisfiable for every length `≥ 2`**, hence the lemma
(and `exists_rv_vfSum_pow`, `vfSum_ne_zero_of_distinct`, which use it) says nothing about any pair
of terms.  The previous swarm's `M8L35.lean` was built on it. -/
theorem hdist_unsat (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} (hb : ∀ i : ℕ, iVF (b i)) {n : ℕ}
    (hn : 2 ≤ n)
    (hdist : ∀ i : ℕ, i < n → ∀ j : ℕ, j < n → i ≠ j →
      ¬ iLe (iRv (b i)) (iRv (b j)) ∧ ¬ iLe (iRv (b j)) (iRv (b i))) : False := by
  have h0 : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
  have h1 : (1 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
  exact hdist_false hM (rv_mem hM (hb 0)) (rv_mem hM (hb 1))
    (hdist 0 h0 1 h1 (by norm_num))

/-- Two elements of `RV` with the *same* class do not satisfy the corrected hypothesis. -/
theorem not_hne_of_cls {a b : M} (h : iLe a b ∧ iLe b a) :
    ¬ ¬ (iLe a b ∧ iLe b a) := fun h' => h' h

/-- **The corrected hypothesis is satisfiable**: two nonzero elements of different `Γ`-classes
satisfy it.  (Only the total-preorder reading of `iLe` is needed; this exhibits the hypothesis as
non-vacuous, in contrast with `hdist_false`.) -/
theorem hne_of_lt {hM : M ⊨ Axioms.ACVF} {a b : M} (ha : iRV a) (hb : iRV b)
    (h : ¬ iLe b a) : ¬ (iLe a b ∧ iLe b a) := fun h' => h h'.2

/-! ## 3. The leading term, with the correct hypothesis: the classes differ pairwise

Same induction as `M8.exists_rv_vfSum` — the last term against the leading term of the prefix — but
in the branch where the two classes are mutually `≤` we now derive a contradiction from the
hypothesis itself instead of from an unsatisfiable pair of non-`≤` facts. -/

theorem exists_rv_vfSum' (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} (hb : ∀ i : ℕ, iVF (b i))
    (hnz : ∀ i : ℕ, b i ≠ iVFZero) :
    ∀ n : ℕ, 0 < n →
      (∀ i : ℕ, i < n → ∀ j : ℕ, j < n → i ≠ j →
        ¬ (iLe (iRv (b i)) (iRv (b j)) ∧ iLe (iRv (b j)) (iRv (b i)))) →
      ∃ j : ℕ, j < n ∧ iRv (vfSum b n) = iRv (b j) := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    intro _ hne
    rcases n with _ | m
    · -- length `1`
      refine ⟨0, Nat.one_pos, ?_⟩
      have hone : vfSum b 1 = b 0 := by
        rw [vfSum_succ, vfSum_zero, vf_zero_add hM (hb 0)]
      rw [hone]
    · -- length `m + 2`
      have hm1 : 0 < m + 1 := Nat.succ_pos m
      have hne' : ∀ i : ℕ, i < m + 1 → ∀ j : ℕ, j < m + 1 → i ≠ j →
          ¬ (iLe (iRv (b i)) (iRv (b j)) ∧ iLe (iRv (b j)) (iRv (b i))) :=
        fun i hi j hj hij => hne i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj) hij
      obtain ⟨j, hj, hrv⟩ := ih hm1 hne'
      set A : M := vfSum b (m + 1) with hA
      set B : M := b (m + 1) with hB
      have hAvf : iVF A := vfSum_mem hM hb (m + 1)
      have hBvf : iVF B := hb (m + 1)
      have hABvf : iVF (iVFAdd A B) := vf_add_mem hM hAvf hBvf
      have hjm : j ≠ m + 1 := Nat.ne_of_lt hj
      have hdj := hne j (Nat.lt_succ_of_lt hj) (m + 1) (Nat.lt_succ_self (m + 1)) hjm
      -- the prefix sum is nonzero, hence so is its value
      have hAnz : A ≠ iVFZero := by
        intro h0
        have hz : iRv A = iRVZero := by rw [h0]; exact rv_zero_eq (M := M) hM
        rw [hrv] at hz
        exact hnz j (vf_eq_zero_of_rv_eq_zero hM (hb j) hz)
      by_cases hdom : iLe (iRv A) (iRv B)
      · by_cases hstrict : ¬ iLe (iRv B) (iRv A)
        · -- `A` strictly dominates `B`: `rv (A + B) = rv A`
          refine ⟨j, Nat.lt_succ_of_lt hj, ?_⟩
          show iRv (iVFAdd A B) = iRv (b j)
          have hclose : iRv (iVFAdd A B) = iRv A := by
            refine rv_eq_of_close hM hABvf hAvf hAnz ?_
            have hswap : iVFAdd (iVFAdd A B) (iVFNeg A) = B := by
              rw [RVCalc.vf_add_comm hM hAvf hBvf, RVCalc.vf_add_add_neg hM hBvf hAvf]
            rw [hswap]
            exact hstrict
          rw [hclose, hrv]
        · -- the classes are mutually `≤`, which the hypothesis forbids
          exact absurd ⟨by rw [← hrv]; exact hdom, by rw [← hrv]; exact not_not.mp hstrict⟩ hdj
      · -- `B` strictly dominates `A`: `rv (A + B) = rv B`
        refine ⟨m + 1, Nat.lt_succ_self (m + 1), ?_⟩
        show iRv (iVFAdd A B) = iRv B
        refine rv_eq_of_close hM hABvf hBvf (hnz (m + 1)) ?_
        have hswap : iVFAdd (iVFAdd A B) (iVFNeg B) = A := by
          rw [RVCalc.vf_add_add_neg hM hAvf hBvf]
        rw [hswap]
        exact hdom

/-- §3 for the expansion `∑_{i<n} b_i e^i` (the form `lift:divisible:hull` uses). -/
theorem exists_rv_vfSum_pow' (hM : M ⊨ Axioms.ACVF) {β : ℕ → M} {e : M}
    (hβ : ∀ i : ℕ, iVF (β i)) (he : iVF e) (he0 : e ≠ iVFZero)
    (hnz : ∀ i : ℕ, β i ≠ iVFZero) {n : ℕ} (hn : 0 < n)
    (hne : ∀ i : ℕ, i < n → ∀ j : ℕ, j < n → i ≠ j →
      ¬ (iLe (iRv (iVFMul (β i) (vfPow e i))) (iRv (iVFMul (β j) (vfPow e j))) ∧
        iLe (iRv (iVFMul (β j) (vfPow e j))) (iRv (iVFMul (β i) (vfPow e i))))) :
    ∃ j : ℕ, j < n ∧
      iRv (vfSum (fun i => iVFMul (β i) (vfPow e i)) n) = iRv (iVFMul (β j) (vfPow e j)) := by
  have hb : ∀ i : ℕ, iVF ((fun i => iVFMul (β i) (vfPow e i)) i) :=
    fun i => vf_mul_mem (M := M) hM (hβ i) (vfPow_mem hM he i)
  have hnz' : ∀ i : ℕ, (fun i => iVFMul (β i) (vfPow e i)) i ≠ iVFZero :=
    fun i => vf_mul_ne_zero_of hM (hβ i) (vfPow_mem hM he i) (hnz i)
      (vfPow_ne_zero_of hM he he0 i)
  exact exists_rv_vfSum' hM hb hnz' n hn hne

/-- **Non-cancellation, with the correct hypothesis**: if every term is nonzero and the classes are
pairwise *different*, the sum is nonzero.  (The previous swarm's `vfSum_ne_zero_of_distinct` states
this with the unsatisfiable `hdist`, so it does not apply to any actual expansion.) -/
theorem vfSum_ne_zero_of_hne (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} (hb : ∀ i : ℕ, iVF (b i))
    (hnz : ∀ i : ℕ, b i ≠ iVFZero) {n : ℕ} (hn : 0 < n)
    (hne : ∀ i : ℕ, i < n → ∀ j : ℕ, j < n → i ≠ j →
      ¬ (iLe (iRv (b i)) (iRv (b j)) ∧ iLe (iRv (b j)) (iRv (b i)))) :
    vfSum b n ≠ iVFZero := by
  obtain ⟨j, _hj, hrv⟩ := exists_rv_vfSum' hM hb hnz n hn hne
  intro h0
  have hz : iRv (vfSum b n) = iRVZero := by rw [h0]; exact rv_zero_eq (M := M) hM
  rw [hrv] at hz
  exact hnz j (vf_eq_zero_of_rv_eq_zero hM (hb j) hz)

/-! ## 4. The separation hypothesis of Lemma 3.5 gives the corrected hypothesis

`M8.rv_pow_quot_unit_of_mutual_le` says: mutually `≤` term values force `rv (e^(j-i))` to be
`rv (b_i)/rv (b_j)` up to a unit.  A hypothesis forbidding exactly that (the tagged form of
`vv (e^k) ∉ Γ(Ŝ)`, `0 < k < n`) therefore contradicts mutual `≤`, which is `hne`. -/

theorem hne_of_sep (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} {e : M}
    (hb : ∀ i : ℕ, iVF (b i)) (he : iVF e) (he0 : e ≠ iVFZero)
    (hnz : ∀ i : ℕ, b i ≠ iVFZero)
    (hsep : ∀ i j : ℕ, i < j →
      ¬ iUnits (iRVMul (iRVMul (iRv (b i)) (iRVInv hM (iRv (b j))))
        (iRVInv hM (iRv (vfPow e (j - i))))))
    {i j : ℕ} (hij : i < j) :
    ¬ (iLe (iRv (iVFMul (b i) (vfPow e i))) (iRv (iVFMul (b j) (vfPow e j))) ∧
      iLe (iRv (iVFMul (b j) (vfPow e j))) (iRv (iVFMul (b i) (vfPow e i)))) := by
  rintro ⟨h1, h2⟩
  exact hsep i j hij (rv_pow_quot_unit_of_mutual_le hM hb he he0 hnz hij h1 h2)

/-- `hne_of_sep` without the order on the indices. -/
theorem hne_of_sep' (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} {e : M}
    (hb : ∀ i : ℕ, iVF (b i)) (he : iVF e) (he0 : e ≠ iVFZero)
    (hnz : ∀ i : ℕ, b i ≠ iVFZero)
    (hsep : ∀ i j : ℕ, i < j →
      ¬ iUnits (iRVMul (iRVMul (iRv (b i)) (iRVInv hM (iRv (b j))))
        (iRVInv hM (iRv (vfPow e (j - i))))))
    {i j : ℕ} (hij : i ≠ j) :
    ¬ (iLe (iRv (iVFMul (b i) (vfPow e i))) (iRv (iVFMul (b j) (vfPow e j))) ∧
      iLe (iRv (iVFMul (b j) (vfPow e j))) (iRv (iVFMul (b i) (vfPow e i)))) := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hne_of_sep hM hb he he0 hnz hsep h
  · intro ⟨h1, h2⟩
    exact hne_of_sep hM hb he he0 hnz hsep h ⟨h2, h1⟩

/-! ## 5. `RV`-control for an expansion: `rv (∑_{i<n} b_i e^i) ∈ S`

The leading term's class is `rv (b_j) · rv(e)^j`, a product of two elements of `S`. -/

theorem rv_term_mem_sub (S : LRV.Substructure M) (hM : M ⊨ Axioms.ACVF) {β : ℕ → M} {e : M}
    (hβ : ∀ i : ℕ, iVF (β i)) (he : iVF e) (hSβ : ∀ i : ℕ, iRv (β i) ∈ S)
    (hSe : iRv e ∈ S) (j : ℕ) :
    iRv (iVFMul (β j) (vfPow e j)) ∈ S := by
  rw [rv_mul_hom_of_model hM (hβ j) (vfPow_mem hM he j), rv_vfPow hM he j]
  exact rvMul_mem_sub S (hSβ j) (rvPowM_mem_sub S hSe j)

/-- **The `RV`-control for an expansion.**  If the `rv` of every coefficient and of `e` lies in the
substructure `S`, and the coefficient classes are pairwise different (§3's `hne`, which §4 derives
from Lemma 3.5's separation hypothesis), then `rv (∑_{i<n} b_i e^i) ∈ S`.  This is the first half of
the paper's Claim (⋆) on the polynomials in `e`: `RV(⟨Ŝ,e⟩) ⊆ ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`. -/
theorem rv_vfSum_pow_mem_sub (S : LRV.Substructure M) (hM : M ⊨ Axioms.ACVF) {β : ℕ → M} {e : M}
    (hβ : ∀ i : ℕ, iVF (β i)) (he : iVF e) (he0 : e ≠ iVFZero)
    (hnz : ∀ i : ℕ, β i ≠ iVFZero) {n : ℕ} (hn : 0 < n)
    (hne : ∀ i : ℕ, i < n → ∀ j : ℕ, j < n → i ≠ j →
      ¬ (iLe (iRv (iVFMul (β i) (vfPow e i))) (iRv (iVFMul (β j) (vfPow e j))) ∧
        iLe (iRv (iVFMul (β j) (vfPow e j))) (iRv (iVFMul (β i) (vfPow e i)))))
    (hSβ : ∀ i : ℕ, iRv (β i) ∈ S) (hSe : iRv e ∈ S) :
    iRv (vfSum (fun i => iVFMul (β i) (vfPow e i)) n) ∈ S := by
  obtain ⟨j, _hj, heq⟩ := exists_rv_vfSum_pow' hM hβ he he0 hnz hn hne
  rw [heq]
  exact rv_term_mem_sub S hM hβ he hSβ hSe j


/-- **A class-level conclusion is a membership conclusion.**  This removes the trap recorded in the
previous swarm's `RESULTS.md`: `RVCalc.rv_add_of_lt` and `rv_ultrametric` return *mutual* `iLe`
("same class"), not the equation `iRv x = iRv y`, so a leading-term argument cannot produce the
element `iRv (∑ …)` itself.  But if two nonzero `RV`-elements are in the same class, the first is
the second times a *unit*, and `Standing S` carries `KEqTop S`: every unit of `M` lies in `S`.  So
membership transfers, and `Cls`-shaped hypotheses are enough after all. -/
theorem mem_of_cls (S : LRV.Substructure M) (hM : M ⊨ Axioms.ACVF) (hK : Assembly.KEqTop S)
    {x y : M} (hx : iRV x) (hy : iRV y) (hy0 : y ≠ iRVZero)
    (hcls : iLe x y ∧ iLe y x) (hyS : y ∈ S) : x ∈ S := by
  set u : M := iRVMul x (iRVInv hM y) with hu
  have huRV : iRV u := rv_mul_mem hM hx (iRVInv_mem hM hy)
  have huS : u ∈ S := hK u (iUnits_of_mutual_le hM hx hy hy0 hcls.1 hcls.2)
  have hxuy : x = iRVMul u y := by
    rw [hu]
    exact (rv_mul_inv_mul_cancel hM hx hy hy0).symm
  rw [hxuy]
  exact rvMul_mem_sub S huS hyS

/-- **The additive step of Claim (⋆), at the level of `S`.**  If `x`'s class is in `S` and `x`
strictly dominates `y`, then `rv (x + y)` is still in `S`.  This is the paper's use of the strict
triangle (`rv_add_of_lt` gives mutual `iLe`, i.e. `Cls`, not the equation) followed by
`mem_of_cls`.  With `rv_mul_hom_of_model` it is what makes the `RV`-control survive addition, and it
is why `mem_of_cls` — rather than any equation-producing lemma — is the right interface. -/
theorem rv_add_mem_sub (S : LRV.Substructure M) (hM : M ⊨ Axioms.ACVF) (hK : Assembly.KEqTop S)
    {x y : M} (hx : iVF x) (hy : iVF y) (hxy : iLe (iRv x) (iRv y)) (hlt : ¬ iLe (iRv y) (iRv x))
    (hxS : iRv x ∈ S) : iRv (iVFAdd x y) ∈ S := by
  have hcls := rv_add_of_lt hM hx hy hxy hlt
  have hx0 : iRv x ≠ iRVZero := by
    intro h0
    exact hlt (h0 ▸ le_top_rv hM (rv_mem hM hy))
  exact mem_of_cls S hM hK (rv_mem hM (vf_add_mem hM hx hy)) (rv_mem hM hx) hx0
    ⟨hcls.1, hcls.2⟩ hxS

/-! ## 6. Claim (⋆)'s `RV` half as one residual: `RVcontrol`

The paper states Claim (⋆) as `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`.  At one element, in the frozen
encoding, the half a case lemma owes is: *every `RV`-element of the substructure generated by `S` and
`m` already lies in `S`*.  §6 shows it is equivalent to the term-level statement (what a syntactic
case lemma produces) and that it follows from exhibiting any substructure with the `RV`-property —
`Substructure.closure_le` supplies the term induction the paper does by hand. -/

/-- **Claim (⋆)'s first half at one element**: `RV(closure (↑S ∪ {m})) ⊆ S`. -/
def RVcontrol (S : LRV.Substructure M) (m : M) : Prop :=
  ∀ y : M, y ∈ Substructure.closure LRV ((S : Set M) ∪ {m}) → iRV y → y ∈ S

/-- **The paper's device.**  To prove the control for the *generated* substructure it suffices to
exhibit any substructure `U ⊇ S` that contains `m` and whose `RV`-part already lies in `S`; the
closure is the least substructure containing `S ∪ {m}`, so it is inside `U`.  This is the shape in
which a case lemma should be proved: describe `U` (by the paper's case analysis on `e`) instead of
inducting on terms. -/
theorem RVcontrol_of_le {S U : LRV.Substructure M} {m : M} (hSU : S ≤ U) (hm : m ∈ U)
    (hRV : ∀ y : M, y ∈ U → iRV y → y ∈ S) : RVcontrol S m := by
  intro y hy hrv
  have hle : Substructure.closure LRV ((S : Set M) ∪ {m}) ≤ U := by
    refine Substructure.closure_le.2 ?_
    intro x hx
    rcases hx with hx | hx
    · exact hSU hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hm
  exact hRV y (hle hy) hrv

/-- The control holds when `m` is already in `S` (the trivial step of every exhaustion). -/
theorem RVcontrol_of_mem {S : LRV.Substructure M} {m : M} (hm : m ∈ S) : RVcontrol S m :=
  RVcontrol_of_le le_rfl hm (fun _ hy _ => hy)

/-- The control holds outright when `S` already contains every `RV`-element of `M` (the last phase
of the paper's exhaustion, where the substructure is `VF`-generated). -/
theorem RVcontrol_of_rv_top {S : LRV.Substructure M} (h : ∀ y : M, iRV y → y ∈ S) (m : M) :
    RVcontrol S m :=
  RVcontrol_of_le le_top trivial (fun y _ hy => h y hy)

/-- **The term form of `RVcontrol`** — the statement a syntactic case lemma proves (an induction on
`LRV`-terms with parameters in `S` and the new element).  By `Substructure.closure_le` above, the
term form is *not* what a case lemma has to produce. -/
theorem RVcontrol_iff_term (S : LRV.Substructure M) (m : M) :
    RVcontrol S m ↔ ∀ t : LRV.Term ↥((S : Set M) ∪ {m}),
      iRV (t.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M)) →
        t.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) ∈ S := by
  constructor
  · intro h t ht
    exact h _ (Term.realize_mem t Subtype.val (fun a => Substructure.subset_closure a.2)) ht
  · intro h y hy hrv
    obtain ⟨t, ht⟩ := Substructure.mem_closure_iff_exists_term.1 hy
    rw [← ht] at hrv ⊢
    exact h t hrv

/-! ## 7. The frozen `OneStepRVOld` from `RVcontrol` and atomic-type realisation

`Assembly_frozen.lean` already contains the *embedding* half of a one-element step in full
generality: `Realize.exists_oneStep` extends `f` to `T = closure LRV (↑S ∪ {m})` from a realisation
`b` of the atomic type of `m` over `S`, for any first-order language.  What is left for the paper's
Lemmas 3.4/3.6 is therefore exactly `RVcontrol`; `M5.standing_of_RV_le` then gives `Standing T`, so
no case lemma ever has to prove `Standing` itself. -/

variable {N : Type} [LRV.Structure N]

/-- `Realize.exists_oneStep` with the generated substructure named, so that `RVcontrol` applies to
it without unfolding the existential. -/
theorem exists_oneStep_closure (hM : M ⊨ Axioms.ACVF) (S : LRV.Substructure M) (f : S ↪[LRV] N)
    {m : M} {b : N} (hb : Realize.RealizesAtomic S f m b) (hm : m ∉ S) :
    ∃ g : ↥(Substructure.closure LRV ((S : Set M) ∪ {m})) ↪[LRV] N,
      (∀ x : S, g ⟨(x : M), Substructure.subset_closure (Set.mem_union_left {m} x.2)⟩ = f x) ∧
        m ∈ Substructure.closure LRV ((S : Set M) ∪ {m}) := by
  refine ⟨Realize.gEmb hb hm, ?_,
    Substructure.subset_closure (Set.mem_union_right _ (Set.mem_singleton m))⟩
  intro x
  have hxT : (x : M) ∈ Substructure.closure LRV ((S : Set M) ∪ {m}) :=
    Substructure.subset_closure (Set.mem_union_left {m} x.2)
  have hk : Realize.kappa S m hm (⟨(x : M), Set.mem_union_left {m} x.2⟩ : ↥((S : Set M) ∪ {m}))
      = Sum.inl (⟨(x : M), x.2⟩ : S) := by
    simp only [Realize.kappa]
    exact (dif_pos x.2).trans (congrArg Sum.inl (Subtype.ext rfl))
  show Realize.gfun f b hm (x : M) hxT = f x
  rw [Realize.gfun_eq hb hm
    (Term.var (⟨(x : M), Set.mem_union_left {m} x.2⟩ : ↥((S : Set M) ∪ {m}))) (x : M) hxT rfl]
  show Realize.toN S f b m hm ⟨(x : M), Set.mem_union_left {m} x.2⟩ = f x
  show Realize.wv f b (Realize.kappa S m hm ⟨(x : M), Set.mem_union_left {m} x.2⟩) = f x
  rw [hk]
  rfl

/-- **`M5.RVStepP` — the paper's Claim (⋆) in the frozen encoding — from exactly two residuals**:
realisation of the atomic type, and `RVcontrol`.  (`RVStepP` is the form `M5OneStep.lean` isolated;
`M5.oneStepVFP_restricted_of_RVstep` turns it into a one-step with `Standing` preserved.) -/
theorem RVStepP_of_atomic_RVcontrol [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
    (hatomic : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), m ∉ S →
      ∃ b : N, Realize.RealizesAtomic S f m b)
    (hrv : ∀ (S : LRV.Substructure M) (m : M), iVF m → iRv m ∈ S → RVcontrol S m) :
    M5.RVStepP (M := M) (N := N) := by
  intro S f _hS m hmVF hmrv
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, fun _ => rfl, hm, fun _ hy _ => hy⟩
  · obtain ⟨b, hb⟩ := hatomic S f m hm
    obtain ⟨g, hagree, hmT⟩ := exists_oneStep_closure (M := M) (N := N) ‹M ⊨ Axioms.ACVF› S f hb hm
    exact ⟨Substructure.closure LRV ((S : Set M) ∪ {m}), g,
      fun x hx => Substructure.subset_closure (Set.mem_union_left _ hx), hagree, hmT,
      hrv S m hmVF hmrv⟩

/-- **The one-step that adds an element whose `rv` is already in `S` (the paper's Lemmas 3.4, 3.6,
3.8), modulo exactly two residuals**: realisation of the atomic type (present in the tree from
saturation, `Assembly_frozen.realizesAtomic_of_saturated`) and `RVcontrol` (Claim (⋆)'s first half).
`Standing T` is not a residual: it is `M5.standing_of_RV_le`. -/
theorem oneStepRVOld_of_RVcontrol [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
    (hatomic : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), m ∉ S →
      ∃ b : N, Realize.RealizesAtomic S f m b)
    (hrv : ∀ (S : LRV.Substructure M) (m : M), Assembly.Standing S → iVF m → iRv m ∈ S →
      RVcontrol S m) :
    M5.OneStepRVOld (M := M) (N := N) := by
  intro S f hS m hmVF hmrv
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩
  · obtain ⟨b, hb⟩ := hatomic S f m hm
    obtain ⟨g, hagree, hmT⟩ := exists_oneStep_closure (M := M) (N := N) ‹M ⊨ Axioms.ACVF› S f hb hm
    exact ⟨Substructure.closure LRV ((S : Set M) ∪ {m}), g,
      fun x hx => Substructure.subset_closure (Set.mem_union_left _ hx), hagree, hmT,
      M5.standing_of_RV_le (fun x hx => Substructure.subset_closure (Set.mem_union_left _ hx))
        hS (hrv S m hS hmVF hmrv)⟩

end M8Stars
end SpecialTransformations.Milestone0

#print axioms SpecialTransformations.Milestone0.M8Stars.rvMul_mem_sub
#print axioms SpecialTransformations.Milestone0.M8Stars.rvPowM_mem_sub
#print axioms SpecialTransformations.Milestone0.M8Stars.hdist_false
#print axioms SpecialTransformations.Milestone0.M8Stars.hdist_unsat
#print axioms SpecialTransformations.Milestone0.M8Stars.hne_of_lt
#print axioms SpecialTransformations.Milestone0.M8Stars.exists_rv_vfSum'
#print axioms SpecialTransformations.Milestone0.M8Stars.exists_rv_vfSum_pow'
#print axioms SpecialTransformations.Milestone0.M8Stars.hne_of_sep
#print axioms SpecialTransformations.Milestone0.M8Stars.hne_of_sep'
#print axioms SpecialTransformations.Milestone0.M8Stars.rv_term_mem_sub
#print axioms SpecialTransformations.Milestone0.M8Stars.rv_vfSum_pow_mem_sub
#print axioms SpecialTransformations.Milestone0.M8Stars.vfSum_ne_zero_of_hne
#print axioms SpecialTransformations.Milestone0.M8Stars.mem_of_cls
#print axioms SpecialTransformations.Milestone0.M8Stars.rv_add_mem_sub
#print axioms SpecialTransformations.Milestone0.M8Stars.RVcontrol_of_le
#print axioms SpecialTransformations.Milestone0.M8Stars.RVcontrol_of_mem
#print axioms SpecialTransformations.Milestone0.M8Stars.RVcontrol_of_rv_top
#print axioms SpecialTransformations.Milestone0.M8Stars.RVcontrol_iff_term
#print axioms SpecialTransformations.Milestone0.M8Stars.exists_oneStep_closure
#print axioms SpecialTransformations.Milestone0.M8Stars.oneStepRVOld_of_RVcontrol
#print axioms SpecialTransformations.Milestone0.M8Stars.RVStepP_of_atomic_RVcontrol

