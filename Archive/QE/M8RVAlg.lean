/-
# Lemma 3.5 (`lift:divisible:hull`, `qe.tex:633-685`) in the frozen tagged encoding:
the value-theoretic core, ported from `QE/Lemma35_divisible_hull.lean`

Direction 4 of swarm `smw1rx5g2`.  The paper's Lemma 3.5 concludes Claim (⋆) for `⟨Ŝ, e⟩`, given
`e^n = a ∈ VF(Ŝ)`, `vv(e^i) ∉ Γ(Ŝ)` for `0 < i < n`, and henselianity of `(VF(Ŝ), O(Ŝ))`.  Its
proof has two halves, and this file is the **first half in the frozen vocabulary** — the half that
the Mathlib-level file `QE/Lemma35_divisible_hull.lean` calls `exists_leading_term` +
`same_rv_class` + `sum_ne_zero`:

> every element of `VF(⟨Ŝ,e⟩)` is a quotient of expansions `∑_{i<n} b_i e^i` (`b_i ∈ VF(Ŝ)`),
> the terms of an expansion have pairwise distinct values (`vv(e^{j-i}) ∉ Γ(Ŝ)`), hence the sum
> has the value *of one of its terms*, so `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩`.

What is proved here, over `M ⊨ Axioms.ACVF` and using only the encoding's axioms
(`RVCalc`: `iLe` preorder, `rvUltrametric`, `rvEqLink`; `QF2Fragment`: `rvMulHom` and the group
structure on `RV ∖ {0}`):

| # | name | statement |
| --- | --- | --- |
| 1 | `vfSum_dominated` | the ultrametric step: `c` strictly dominating every term dominates the partial sum |
| 2 | `rv_add_sum_of_dominated` | `rv (∑ b + c) = rv c` — the display at `qe.tex:651-654` for a named dominant term |
| 3 | `add_sum_ne_zero_of_dominated` | a sum with a dominant term is nonzero |
| 4 | `exists_rv_vfSum` | **`∃ j < n, rv (∑_{i<n} b i) = rv (b j)`** when no two terms have the same value — the paper's "for some `j`", with `j` arbitrary, not just the last index |
| 5 | `vfSum_ne_zero_of_distinct` | `sum_ne_zero`: such a sum does not cancel |
| 6 | `exists_rv_vfSum_pow` | the same for the expansion `∑_{i<n} b_i e^i` of `K⟮e⟯` |
| 7 | `rv_pow_sub_of_eq_terms` | the quotient line at `qe.tex:650`: equal term values force `rv (e^(j-i)) = rv(b_i)·rv(b_j)⁻¹` |
| 8 | `iUnits_of_mutual_le` | **the `Γ`-dictionary, forward**: mutually `iLe` (same `Γ`-class) ⟹ the quotient is a unit `Kˣ` |
| 9 | `mutual_le_of_iUnits` | **the `Γ`-dictionary, backward**: a unit multiple has mutually `iLe` values |
| 10 | `iUnits_inv` | the inverse of a unit is a unit |

Two findings about the *encoding* that the port turns on, both machine-checked here:

* `iLe` on `RV` is only a **preorder**, so mutual `iLe` does *not* give equality of `iRv` values.
  `rv_add_of_lt` therefore cannot be used to conclude `rv (∑) = rv c`; the encoding's device for
  `rv`-equality is `rvEqLink` (`rv_eq_of_close`), i.e. one has to exhibit the *error term* as
  strictly dominated.  `rv_add_sum_of_dominated` does exactly that.
* the partial sum `∑_{i<n} b_i` need not be nonzero under "`c` dominates all terms" — `1 + (-1)`
  with `c` of large value — so the paper's nonzero-ness claim is about the full sum, not the
  prefix.  `add_sum_ne_zero_of_dominated` is stated for the full sum for that reason.

What is **not** here (the honest boundary, i.e. what is still owed to Lemma 3.5):

* assembling the translation of `vv(e^k) ∉ Γ(Ŝ)` into the tagged hypothesis `hdist` of §3.  The
  dictionary itself is now proved (§6): "same class in `Γ`" is mutual `iLe`, which is equivalent to
  "differ by a unit `Kˣ`".  What is still missing is the exponent bookkeeping: in the mutual-`iLe`
  case (not the equality case of §5) one has to normalise the unit `rv(b_i e^i)·rv(b_j e^j)⁻¹` into
  the form `(rv b_i·rv b_j⁻¹)·(rv e^(j-i))⁻¹`, i.e. prove `u = d·v⁻¹` with `v := rv(e^(j-i))` a unit
  multiple, using `rv_pow_sub_of_eq_terms`'s algebra with `iUnits_inv` in place of an equation.
  The paper then contradicts the separation hypothesis `vv(e^k) ∉ Γ(Ŝ)`, transcribed as
  "`rv(e^k) ≠ rv x · rv y⁻¹ · z` for `x, y ∈ S ∩ VF`, `y ≠ 0`, `z` a unit".  That transcription is
  the interface a Lemma 3.5 statement has to use; it is named here, not proved.
* "every element of `VF(⟨Ŝ,e⟩)` is a quotient of expansions" — polynomial division by `X^n - a`,
  proved at Mathlib level (`exists_reduce`, `exists_expansion_div` in
  `QE/Lemma35_divisible_hull.lean`) and reachable from the encoding only through a polynomial ring,
  i.e. through `Transfer.VFType M` plus `Polynomial`, not through the tagged syntax.
* the construction of the `L_RV`-monomorphism `⟨Ŝ,e⟩ → N` (Lemma 3.2 gives the root `d`; the
  transport to `↪[LRV]` is the other direction's problem).

Build (olean for `Enc`, `RVCalc`, `QF2Fragment` are in `.scratch2/sec3/`):

    cp .ultramath/smw1rx5g2/m8/M8L35.lean .scratch2/sec3/ && cd .scratch2/sec3 \
      && LEAN_PATH=$PWD:$LEAN_PATH lean M8L35.lean
-/
import RVCalc

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0

namespace M8

open LRV
open RVCalc
open Transfer

variable {M : Type} [LRV.Structure M]

/-- `x ^ n` on the `VF` sort of a model (the encoding has no exponentiation). -/
def vfPow (x : M) : ℕ → M
  | 0 => iVFOne
  | (n + 1) => iVFMul (vfPow x n) x

/-- `∑_{i<n} b i` on the `VF` sort (partial sums of a sequence). -/
def vfSum (b : ℕ → M) : ℕ → M
  | 0 => iVFZero
  | (n + 1) => iVFAdd (vfSum b n) (b n)

@[simp] theorem vfSum_zero (b : ℕ → M) : vfSum b 0 = iVFZero := rfl

@[simp] theorem vfSum_succ (b : ℕ → M) (n : ℕ) :
    vfSum b (n + 1) = iVFAdd (vfSum b n) (b n) := rfl

@[simp] theorem vfPow_zero (x : M) : vfPow x 0 = iVFOne := rfl

@[simp] theorem vfPow_succ (x : M) (n : ℕ) : vfPow x (n + 1) = iVFMul (vfPow x n) x := rfl

theorem vfPow_mem (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    ∀ n : ℕ, iVF (vfPow x n)
  | 0 => vf_one_mem (M := M) hM
  | (n + 1) => vf_mul_mem (M := M) hM (vfPow_mem hM hx n) hx

theorem vfSum_mem (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} (hb : ∀ i : ℕ, iVF (b i)) :
    ∀ n : ℕ, iVF (vfSum b n)
  | 0 => vf_zero_mem (M := M) hM
  | (n + 1) => vf_add_mem (M := M) hM (vfSum_mem hM hb n) (hb n)

open LRV
open RVCalc
open Transfer

variable {M : Type} [LRV.Structure M]

/-! ## The order dictionary used below

`iLe (iRv x) (iRv y)` holds iff `x` is *at least as large as* `y` in absolute value: under the
dictionary `iLe (iRv y) (iRv x) ↔ w x ≤ w y` of `QE/ValBridge.lean` it says `w y ≤ w x`, i.e.
`v y ≥ v x` for the paper's value `v`.  So `¬ iLe (iRv a) (iRv b)` says that `b` dominates `a`
strictly, `v a < v b`.  Everything below is phrased on the `VF`/`RV` sorts only, so no value group
is ever needed. -/

/-! ## 1. A finite sum is strictly dominated by any element dominating all its terms

This is the inequality at the start of the proof of `lift:divisible:hull` (`qe.tex:650`): if `c`
dominates every `b i` (`i < n`) strictly, then it dominates the partial sum `∑_{i<n} b i`
strictly.  The proof is the ultrametric inequality `rv_ultrametric` plus transitivity of `iLe`. -/

theorem vfSum_dominated (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} {c : M}
    (hb : ∀ i : ℕ, iVF (b i)) (hc : iVF c) (hc0 : c ≠ iVFZero) (n : ℕ)
    (hdom : ∀ i : ℕ, i < n → ¬ iLe (iRv (b i)) (iRv c)) :
    iLe (iRv c) (iRv (vfSum b n)) ∧ ¬ iLe (iRv (vfSum b n)) (iRv c) := by
  induction n with
  | zero =>
    have hz : iRv (vfSum b 0) = iRVZero := rv_zero_eq (M := M) hM
    refine ⟨?_, ?_⟩
    · rw [hz]; exact le_top_rv hM (rv_mem hM hc)
    · rw [hz]; intro h
      exact hc0 (vf_eq_zero_of_rv_eq_zero hM hc (le_infty_eq hM (rv_mem hM hc) h))
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hdom i (Nat.lt_succ_of_lt hi)
    have hbn : ¬ iLe (iRv (b n)) (iRv c) := hdom n (Nat.lt_succ_self n)
    have hpsum : iVF (vfSum b n) := vfSum_mem hM hb n
    have hbnVF : iVF (b n) := hb n
    have hsVF : iVF (vfSum b (n + 1)) := vfSum_mem hM hb (n + 1)
    have hsum' : iRV (iRv (vfSum b (n + 1))) := rv_mem hM hsVF
    have hc' : iRV (iRv c) := rv_mem hM hc
    have hult := rv_ultrametric hM hpsum hbnVF
    refine ⟨?_, ?_⟩
    · rcases hult with hu | hu
      · exact le_trans_rv hM hc' (rv_mem hM hpsum) hsum' h1 hu
      · have hcb : iLe (iRv c) (iRv (b n)) := by
          rcases le_total_rv hM (rv_mem hM hc) (rv_mem hM hbnVF) with h | h
          · exact h
          · exact absurd h hbn
        exact le_trans_rv hM hc' (rv_mem hM hbnVF) hsum' hcb hu
    · intro hbad
      rcases hult with hu | hu
      · exact h2 (le_trans_rv hM (rv_mem hM hpsum) hsum' hc' hu hbad)
      · exact hbn (le_trans_rv hM (rv_mem hM hbnVF) hsum' hc' hu hbad)
/-! ## 2. The leading term: the value of the sum is the value of the dominant term

This is the displayed conclusion of `lift:divisible:hull` (`qe.tex:651-654`):
`rv (∑_{i ≤ m} b_i e^i) = rv (b_j e^j)`, stated with the dominant term `c` pulled out of the
sum (that is the general case: `c` is `b_j e^j` and `b` is the rest of the expansion). -/

/-- The sum has the *same* `rv` as its dominant term.  Note the route: `rv_add_of_lt` gives mutual
`iLe` of the two `RV`-elements, but `iLe` is only a **preorder** in the frozen encoding, so mutual
`iLe` does not give equality of `iRv`-values.  The equality is recovered from `rv_eq_link`
(`rv_eq_of_close`), which is exactly the encoding's device for `rv`-equality: it suffices that the
*error term* `(∑ b) + c - c = ∑ b` be strictly dominated by `c`, which is `vfSum_dominated`. -/
theorem rv_add_sum_of_dominated (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} {c : M}
    (hb : ∀ i : ℕ, iVF (b i)) (hc : iVF c) (hc0 : c ≠ iVFZero) (n : ℕ)
    (hdom : ∀ i : ℕ, i < n → ¬ iLe (iRv (b i)) (iRv c)) :
    iRv (iVFAdd (vfSum b n) c) = iRv c := by
  have hpsum : iVF (vfSum b n) := vfSum_mem hM hb n
  have hxVF : iVF (iVFAdd (vfSum b n) c) := vf_add_mem hM hpsum hc
  obtain ⟨-, h2⟩ := vfSum_dominated hM hb hc hc0 n hdom
  refine rv_eq_of_close hM hxVF hc hc0 ?_
  rw [vf_add_add_neg hM hpsum hc]
  exact h2

/-- The full sum is nonzero when its dominant term is.

Note (a trap worth recording): the *partial* sum `∑_{i<n} b i` alone need not be nonzero under the
same hypothesis — `b 0 = 1`, `b 1 = -1` with `c = e` of large value is a counterexample, and the
paper never claims it.  Nonzero-ness of the sum needs the dominant term back in, and then it
follows from `rv (∑) = rv c ≠ 0`. -/
theorem add_sum_ne_zero_of_dominated (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} {c : M}
    (hb : ∀ i : ℕ, iVF (b i)) (hc : iVF c) (hc0 : c ≠ iVFZero) (n : ℕ)
    (hdom : ∀ i : ℕ, i < n → ¬ iLe (iRv (b i)) (iRv c)) :
    iVFAdd (vfSum b n) c ≠ iVFZero := by
  have hxVF : iVF (iVFAdd (vfSum b n) c) := vf_add_mem hM (vfSum_mem hM hb n) hc
  have h := rv_add_sum_of_dominated hM hb hc hc0 n hdom
  intro h0
  have hz : iRv (iVFAdd (vfSum b n) c) = iRVZero := by
    rw [h0]; exact rv_zero_eq (M := M) hM
  rw [h] at hz
  exact hc0 (vf_eq_zero_of_rv_eq_zero hM hc hz)

/-! ## 3. The leading term of a finite expansion, with a *general* dominant index

`qe.tex:650-654`: "For any `i < j`, if `b_i` and `b_j` are nonzero then
`vv(b_i e^i) ≠ vv(b_j e^j)` … So `rv (∑_{0 ≤ i ≤ m} b_i e^i) = rv(b_j e^j)` for some `j`."

No reindexing is needed for this: run the induction on the length and compare the *last* term with
the already-computed leading term of the prefix.  In a preorder, two `RV`-elements are *distinct*
when neither dominates the other (`hdist` below), and then exactly one of the last term and the
prefix sum strictly dominates the other, so `rv_eq_of_close` applies in one of its two orientations.
-/

theorem exists_rv_vfSum (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} (hb : ∀ i : ℕ, iVF (b i))
    (hnz : ∀ i : ℕ, b i ≠ iVFZero) :
    ∀ n : ℕ, 0 < n →
      (∀ i : ℕ, i < n → ∀ j : ℕ, j < n → i ≠ j →
        ¬ iLe (iRv (b i)) (iRv (b j)) ∧ ¬ iLe (iRv (b j)) (iRv (b i))) →
      ∃ j : ℕ, j < n ∧ iRv (vfSum b n) = iRv (b j) := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    intro _ hdist
    rcases n with _ | m
    · -- length `1`
      refine ⟨0, Nat.one_pos, ?_⟩
      have hone : vfSum b 1 = b 0 := by
        rw [vfSum_succ, vfSum_zero, vf_zero_add hM (hb 0)]
      rw [hone]
    · -- length `m + 2`
      have hm1 : 0 < m + 1 := Nat.succ_pos m
      have hdist' : ∀ i : ℕ, i < m + 1 → ∀ j : ℕ, j < m + 1 → i ≠ j →
          ¬ iLe (iRv (b i)) (iRv (b j)) ∧ ¬ iLe (iRv (b j)) (iRv (b i)) :=
        fun i hi j hj hij => hdist i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj) hij
      obtain ⟨j, hj, hrv⟩ := ih hm1 hdist'
      set A : M := vfSum b (m + 1) with hA
      set B : M := b (m + 1) with hB
      have hAvf : iVF A := vfSum_mem hM hb (m + 1)
      have hBvf : iVF B := hb (m + 1)
      have hABvf : iVF (iVFAdd A B) := vf_add_mem hM hAvf hBvf
      have hjm : j ≠ m + 1 := Nat.ne_of_lt hj
      have hdj := hdist j (Nat.lt_succ_of_lt hj) (m + 1) (Nat.lt_succ_self (m + 1)) hjm
      -- the prefix sum is nonzero, hence so is its value
      have hAnz : A ≠ iVFZero := by
        intro h0
        have hz : iRv A = iRVZero := by rw [h0]; exact rv_zero_eq (M := M) hM
        rw [hrv] at hz
        exact hnz j (vf_eq_zero_of_rv_eq_zero hM (hb j) hz)
      have hAnz' : iRv A ≠ iRVZero := fun h => hAnz (vf_eq_zero_of_rv_eq_zero hM hAvf h)
      by_cases hdom : iLe (iRv A) (iRv B)
      · by_cases hstrict : ¬ iLe (iRv B) (iRv A)
        · -- `A` strictly dominates `B`: `rv (A + B) = rv A`
          refine ⟨j, Nat.lt_succ_of_lt hj, ?_⟩
          show iRv (iVFAdd A B) = iRv (b j)
          have hclose : iRv (iVFAdd A B) = iRv A := by
            refine rv_eq_of_close hM hABvf hAvf hAnz ?_
            have hswap : iVFAdd (iVFAdd A B) (iVFNeg A) = B := by
              rw [vf_add_comm hM hAvf hBvf, vf_add_add_neg hM hBvf hAvf]
            rw [hswap]
            exact hstrict
          rw [hclose, hrv]
        · -- mutual domination: excluded by distinctness of the values
          exact absurd hdj.2 (by rw [← hrv]; exact hstrict)
      · -- `B` strictly dominates `A`: `rv (A + B) = rv B`
        refine ⟨m + 1, Nat.lt_succ_self (m + 1), ?_⟩
        show iRv (iVFAdd A B) = iRv B
        refine rv_eq_of_close hM hABvf hBvf (hnz (m + 1)) ?_
        have hswap : iVFAdd (iVFAdd A B) (iVFNeg B) = A := by
          rw [vf_add_add_neg hM hAvf hBvf]
        rw [hswap]
        exact hdom

/-- The value of the sum is one of the values of its terms, and in particular the sum is nonzero:
if every term is nonzero and no two terms have the same value, the sum does not cancel.  (This is the
`sum_ne_zero` half of the Mathlib-level `QE/Lemma35_divisible_hull.lean`, `:242`, in the frozen
encoding.) -/
theorem vfSum_ne_zero_of_distinct (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} (hb : ∀ i : ℕ, iVF (b i))
    (hnz : ∀ i : ℕ, b i ≠ iVFZero) {n : ℕ} (hn : 0 < n)
    (hdist : ∀ i : ℕ, i < n → ∀ j : ℕ, j < n → i ≠ j →
      ¬ iLe (iRv (b i)) (iRv (b j)) ∧ ¬ iLe (iRv (b j)) (iRv (b i))) :
    vfSum b n ≠ iVFZero := by
  obtain ⟨j, hj, hrv⟩ := exists_rv_vfSum hM hb hnz n hn hdist
  intro h0
  have hz : iRv (vfSum b n) = iRVZero := by rw [h0]; exact rv_zero_eq (M := M) hM
  rw [hrv] at hz
  exact hnz j (vf_eq_zero_of_rv_eq_zero hM (hb j) hz)

/-! ## 4. The expansion `∑_{i<n} b_i e^i`, in the paper's shape

`lift:divisible:hull` applies §3 to the terms `b_i e^i` of an expansion of an element of
`K⟮e⟯`.  The following is that corollary verbatim: **the `rv`-class of an expansion is the class of
one of its terms**, which is the content of `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩` for an expansion. -/

/-- The `rv`-class of a `VF`-product is nonzero when both factors are. -/
theorem vf_mul_ne_zero_of (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y)
    (hx0 : x ≠ iVFZero) (hy0 : y ≠ iVFZero) : iVFMul x y ≠ iVFZero := by
  intro h
  have hrv : iRv (iVFMul x y) = iRVZero := by rw [h]; exact rv_zero_eq (M := M) hM
  rw [rv_mul_hom_of_model hM hx hy] at hrv
  rcases (rv_mul_eq_zero_of_model hM (rv_mem hM hx) (rv_mem hM hy)).1 hrv with h1 | h1
  · exact hx0 (vf_eq_zero_of_rv_eq_zero hM hx h1)
  · exact hy0 (vf_eq_zero_of_rv_eq_zero hM hy h1)

/-- Powers of a nonzero `VF`-element are nonzero. -/
theorem vfPow_ne_zero_of (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) (he0 : e ≠ iVFZero) :
    ∀ n : ℕ, vfPow e n ≠ iVFZero
  | 0 => fun h => vf_zero_ne_one hM h.symm
  | (n + 1) =>
    vf_mul_ne_zero_of hM (vfPow_mem hM he n) he (vfPow_ne_zero_of hM he he0 n) he0

theorem exists_rv_vfSum_pow (hM : M ⊨ Axioms.ACVF) {β : ℕ → M} {e : M}
    (hβ : ∀ i : ℕ, iVF (β i)) (he : iVF e) (he0 : e ≠ iVFZero)
    (hnz : ∀ i : ℕ, β i ≠ iVFZero) {n : ℕ} (hn : 0 < n)
    (hdist : ∀ i : ℕ, i < n → ∀ j : ℕ, j < n → i ≠ j →
      ¬ iLe (iRv (iVFMul (β i) (vfPow e i))) (iRv (iVFMul (β j) (vfPow e j))) ∧
        ¬ iLe (iRv (iVFMul (β j) (vfPow e j))) (iRv (iVFMul (β i) (vfPow e i)))) :
    ∃ j : ℕ, j < n ∧ iRv (vfSum (fun i => iVFMul (β i) (vfPow e i)) n)
      = iRv (iVFMul (β j) (vfPow e j)) := by
  have hb : ∀ i : ℕ, iVF ((fun i => iVFMul (β i) (vfPow e i)) i) :=
    fun i => vf_mul_mem (M := M) hM (hβ i) (vfPow_mem hM he i)
  have hnz' : ∀ i : ℕ, (fun i => iVFMul (β i) (vfPow e i)) i ≠ iVFZero :=
    fun i => vf_mul_ne_zero_of hM (hβ i) (vfPow_mem hM he i) (hnz i)
      (vfPow_ne_zero_of hM he he0 i)
  exact exists_rv_vfSum hM hb hnz' n hn hdist

/-! ## 5. The quotient step: equal values of two terms determine `rv (e ^ (j - i))`

`lift:divisible:hull` uses, in one line (`qe.tex:650`), the implication

  `vv (b_i e^i) = vv (b_j e^j) ⟹ vv (e ^ (j - i)) = vv (b_i) - vv (b_j)`,

whose right-hand side the paper reads as "`vv (e ^ (j-i)) ∈ Γ(Ŝ)` because `b_i, b_j ∈ VF(Ŝ)`".
That inference is *not* available elementwise in `VF(Ŝ)` — `S ∩ VF` is a ring, not a field, so
`b_i / b_j` need not lie in it — but it **is** available at the level of `RV`: the encoding's
`repairRV` axioms make `RV ∖ {0}` a group, with `iRVInv` the inverse, so the quotient `rv (b_i)/rv (b_j)`
exists no matter what.  What the paper needs of `Γ(Ŝ)` can therefore be stated without Γ and
without field inverses: "`rv x` is not `rv y · rv z` for `y, z` in the domain".  This section proves
the equation; it is the piece a `hdis`-style hypothesis has to contradict. -/

/-- `r ^ n` on the `RV` sort. -/
def rvPowM (r : M) : ℕ → M
  | 0 => iRVOne
  | (n + 1) => iRVMul (rvPowM r n) r

@[simp] theorem rvPowM_zero (r : M) : rvPowM r 0 = iRVOne := rfl

@[simp] theorem rvPowM_succ (r : M) (n : ℕ) : rvPowM r (n + 1) = iRVMul (rvPowM r n) r := rfl

theorem rvPowM_mem (hM : M ⊨ Axioms.ACVF) {r : M} (hr : iRV r) : ∀ n : ℕ, iRV (rvPowM r n)
  | 0 => rv_one_mem (M := M) hM
  | (n + 1) => rv_mul_mem (M := M) hM (rvPowM_mem hM hr n) hr

theorem rvPowM_ne_zero (hM : M ⊨ Axioms.ACVF) {r : M} (hr : iRV r) (hr0 : r ≠ iRVZero) :
    ∀ n : ℕ, rvPowM r n ≠ iRVZero
  | 0 => rv_one_ne_zero hM
  | (n + 1) => by
    refine fun h => ?_
    rcases (rv_mul_eq_zero_of_model hM (rvPowM_mem hM hr n) hr).1 h with h1 | h1
    · exact rvPowM_ne_zero hM hr hr0 n h1
    · exact hr0 h1

/-- `rv (e ^ n) = (rv e) ^ n`. -/
theorem rv_vfPow (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) :
    ∀ n : ℕ, iRv (vfPow e n) = rvPowM (iRv e) n
  | 0 => rv_one hM
  | (n + 1) => by
    rw [vfPow_succ, rv_mul_hom_of_model hM (vfPow_mem hM he n) he, rv_vfPow hM he n]
    rfl

theorem rvPowM_add (hM : M ⊨ Axioms.ACVF) {r : M} (hr : iRV r) (a : ℕ) :
    ∀ b : ℕ, rvPowM r (a + b) = iRVMul (rvPowM r a) (rvPowM r b)
  | 0 => by
    rw [Nat.add_zero, rvPowM_zero, rv_mul_one_any_right hM (rvPowM_mem hM hr a)]
  | (b + 1) => by
    have hmem := rvPowM_mem hM hr a
    have hmem' := rvPowM_mem hM hr b
    rw [Nat.add_succ, rvPowM_succ, rvPowM_succ, rvPowM_add hM hr a b,
      rv_mul_assoc_of_model hM hmem hmem' hr, rv_mul_comm_of_model hM hmem' hr,
      ← rv_mul_assoc_of_model hM hmem hr hmem', ← rvPowM_succ]

/-- **The quotient form of `qe.tex:650`.**  If two nonzero terms of an expansion have the same
`rv`-class, then `rv (e ^ (j - i))` is the `RV`-quotient `rv (b i) · rv (b j)⁻¹`. -/
theorem rv_pow_sub_of_eq_terms (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} {e : M}
    (hb : ∀ i : ℕ, iVF (b i)) (he : iVF e) (he0 : e ≠ iVFZero)
    (hnz : ∀ i : ℕ, b i ≠ iVFZero) {i j : ℕ} (hij : i < j)
    (h : iRv (iVFMul (b i) (vfPow e i)) = iRv (iVFMul (b j) (vfPow e j))) :
    iRv (vfPow e (j - i)) = iRVMul (iRv (b i)) (iRVInv hM (iRv (b j))) := by
  set r : M := iRv e with hrdef
  have hr : iRV r := rv_mem hM he
  have hr0 : r ≠ iRVZero := fun h0 => he0 (vf_eq_zero_of_rv_eq_zero hM he h0)
  have hi : iRV (iRv (b i)) := rv_mem hM (hb i)
  have hj : iRV (iRv (b j)) := rv_mem hM (hb j)
  have hbjn : iRv (b j) ≠ iRVZero :=
    fun h0 => hnz j (vf_eq_zero_of_rv_eq_zero hM (hb j) h0)
  have hp_i : iRV (rvPowM r i) := rvPowM_mem hM hr i
  have hp_d : iRV (rvPowM r (j - i)) := rvPowM_mem hM hr (j - i)
  have hp_i0 : rvPowM r i ≠ iRVZero := rvPowM_ne_zero hM hr hr0 i
  have hp_d0 : rvPowM r (j - i) ≠ iRVZero := rvPowM_ne_zero hM hr hr0 (j - i)
  have hvfp : ∀ k : ℕ, iRv (vfPow e k) = rvPowM r k := by
    intro k
    rw [rv_vfPow hM he k, ← hrdef]
  -- the hypothesis, in `rvPowM` form
  have h1 : iRVMul (iRv (b i)) (rvPowM r i)
      = iRVMul (iRv (b j)) (rvPowM r j) := by
    have hh := h
    rw [rv_mul_hom_of_model hM (hb i) (vfPow_mem hM he i),
      rv_mul_hom_of_model hM (hb j) (vfPow_mem hM he j)] at hh
    rw [hvfp i, hvfp j] at hh
    exact hh
  -- split `j = (j - i) + i`
  have hsplit : rvPowM r j = iRVMul (rvPowM r (j - i)) (rvPowM r i) := by
    rw [← rvPowM_add hM hr (j - i) i, Nat.sub_add_cancel hij.le]
  rw [hsplit] at h1
  -- cancel `rvPowM r i` on the right
  have hmul : iRV (iRVMul (iRv (b j)) (rvPowM r (j - i))) := rv_mul_mem hM hj hp_d
  have hmul0 : iRVMul (iRv (b j)) (rvPowM r (j - i)) ≠ iRVZero := by
    intro h0
    rcases (rv_mul_eq_zero_of_model hM hj hp_d).1 h0 with h1' | h1'
    · exact hbjn h1'
    · exact hp_d0 h1'
  have h2 : iRv (b i) = iRVMul (iRv (b j)) (rvPowM r (j - i)) := by
    refine rv_mul_left_cancel_of_model (hM := hM) (a := iRv (b i)) (b := rvPowM r i)
      (c := iRVMul (iRv (b j)) (rvPowM r (j - i))) hi hp_i hp_i0 hmul ?_
    rw [h1, rv_mul_assoc_of_model hM hj hp_d hp_i]
  -- multiply on the left by `rv (b j)⁻¹`
  have hinv : iRV (iRVInv hM (iRv (b j))) := iRVInv_mem hM hj
  have hcancel : iRVMul (iRVInv hM (iRv (b j))) (iRv (b j)) = iRVOne :=
    iRVInv_mul_cancel hM hj hbjn
  calc iRv (vfPow e (j - i)) = rvPowM r (j - i) := hvfp (j - i)
    _ = iRVMul iRVOne (rvPowM r (j - i)) := (rv_mul_one_any hM hp_d).symm
    _ = iRVMul (iRVMul (iRVInv hM (iRv (b j))) (iRv (b j))) (rvPowM r (j - i)) := by
        rw [hcancel]
    _ = iRVMul (iRVInv hM (iRv (b j))) (iRVMul (iRv (b j)) (rvPowM r (j - i))) :=
        rv_mul_assoc_of_model hM hinv hj hp_d
    _ = iRVMul (iRVInv hM (iRv (b j))) (iRv (b i)) := by rw [← h2]
    _ = iRVMul (iRv (b i)) (iRVInv hM (iRv (b j))) := rv_mul_comm_of_model hM hinv hi

/-! ## 6. The `Γ`-dictionary: equivalent `iLe` classes are exactly unit multiples

`Γ = RV / Kˣ` in the paper, but the frozen language has no `Γ`-sort, so every statement about `Γ(S)`
has to be transcribed.  The dictionary is: two nonzero `RV`-elements have the *same class in `Γ`*
iff they are *mutually `iLe`* (the encoding's total preorder on `RV`), iff they differ by a unit
`Kˣ` (`iUnits`).  Both directions are proved here.  They are what a `vv(e^k) ∉ Γ(Ŝ)` hypothesis has
to be translated into, and what the unit factor `c` in `GammaDivisible` is.

The side condition `c ≠ iRVZero` is a hypothesis rather than a theorem on purpose: the frozen
`leClassOne` axioms are *guarded* by `pRV` (`= ≠ 0`), so `iUnits c → c ≠ 0` is not among them;
it needs `rvMulInv` (`QE/QF2Fragment.lean:1062`) together with `t × 0 = 0`. -/

/-- `d = a / b` (as an `RV`-quotient) satisfies `d · b = a`. -/
theorem rv_mul_inv_mul_cancel (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b)
    (hb0 : b ≠ iRVZero) : iRVMul (iRVMul a (iRVInv hM b)) b = a := by
  have hinv : iRV (iRVInv hM b) := iRVInv_mem hM hb
  rw [rv_mul_assoc_of_model hM ha hinv hb, iRVInv_mul_cancel hM hb hb0,
    rv_mul_one_any_right hM ha]

/-- **Same `Γ`-class ⟹ unit multiple.**  If `a` and `b` are mutually `iLe` (the encoding's
"same class in `Γ`"), the quotient `a / b` lies in `Kˣ`. -/
theorem iUnits_of_mutual_le (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b)
    (hb0 : b ≠ iRVZero) (hab : iLe a b) (hba : iLe b a) :
    iUnits (iRVMul a (iRVInv hM b)) := by
  have hinv : iRV (iRVInv hM b) := iRVInv_mem hM hb
  have hd : iRV (iRVMul a (iRVInv hM b)) := rv_mul_mem hM ha hinv
  have hdb : iRVMul (iRVMul a (iRVInv hM b)) b = a := rv_mul_inv_mul_cancel hM ha hb hb0
  have ha0 : a ≠ iRVZero := by
    intro h
    rw [h] at hab
    exact hb0 (le_infty_eq hM hb hab)
  have hd0 : iRVMul a (iRVInv hM b) ≠ iRVZero := by
    intro h
    have h' : iRVMul (iRVMul a (iRVInv hM b)) b = iRVZero := by
      rw [h]; exact rv_mul_zero_left_of_model hM hb
    rw [hdb] at h'
    exact ha0 h'
  have hone : iLe iRVOne (iRVMul a (iRVInv hM b)) := by
    refine (le_mul_iff hM (rv_one_mem hM) hd hb hb0).2 ?_
    rw [hdb, rv_mul_one_any hM hb]
    exact hba
  have hone' : iLe (iRVMul a (iRVInv hM b)) iRVOne := by
    refine (le_mul_iff hM hd (rv_one_mem hM) hb hb0).2 ?_
    rw [hdb, rv_mul_one_any hM hb]
    exact hab
  exact (units_iff_le_one hM hd hd0).2 ⟨hone, hone'⟩

/-- **Unit multiple ⟹ same `Γ`-class**: `a = b · c` with `c` in `Kˣ` gives mutual `iLe`. -/
theorem mutual_le_of_iUnits (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b)
    (hc : iRV c) (hc0 : c ≠ iRVZero) (hu : iUnits c) (h : a = iRVMul b c) :
    iLe a b ∧ iLe b a := by
  obtain ⟨hu1, hu2⟩ := (units_iff_le_one hM hc hc0).1 hu
  rcases eq_or_ne b iRVZero with hb0 | hb0
  · subst hb0
    have haz : a = iRVZero := by rw [h, rv_mul_zero_left_of_model hM hc]
    subst haz
    exact ⟨le_refl_rv hM (rv_zero_mem hM), le_refl_rv hM (rv_zero_mem hM)⟩
  · have hcb : iRVMul c b = a := by
      rw [rv_mul_comm_of_model hM hc hb]
      exact h.symm
    constructor
    · have hstep : iLe (iRVMul c b) (iRVMul iRVOne b) :=
        (le_mul_iff hM hc (rv_one_mem hM) hb hb0).1 hu2
      rwa [hcb, rv_mul_one_any hM hb] at hstep
    · have hstep : iLe (iRVMul iRVOne b) (iRVMul c b) :=
        (le_mul_iff hM (rv_one_mem hM) hc hb hb0).1 hu1
      rwa [hcb, rv_mul_one_any hM hb] at hstep

/-- A unit's inverse is a unit. -/
theorem iUnits_inv (hM : M ⊨ Axioms.ACVF) {c : M} (hc : iRV c) (hc0 : c ≠ iRVZero)
    (hu : iUnits c) : iUnits (iRVInv hM c) := by
  obtain ⟨hu1, hu2⟩ := (units_iff_le_one hM hc hc0).1 hu
  -- `c⁻¹ = 1 / c`
  have := iUnits_of_mutual_le hM (rv_one_mem hM) hc hc0 hu1 hu2
  rwa [rv_mul_one_any hM (iRVInv_mem hM hc)] at this

/-! ## 7. Axiom audit -/

#print axioms vfSum_dominated
#print axioms rv_add_sum_of_dominated
#print axioms add_sum_ne_zero_of_dominated
#print axioms exists_rv_vfSum
#print axioms vfSum_ne_zero_of_distinct
#print axioms exists_rv_vfSum_pow
#print axioms rv_pow_sub_of_eq_terms
#print axioms iUnits_of_mutual_le
#print axioms mutual_le_of_iUnits
#print axioms iUnits_inv

/-! ## 8. Assembly: the separation hypothesis delivers §3's `hdist`

This is the step that converts Lemma 3.5's hypothesis on `Γ(Ŝ)` into the hypothesis of
`exists_rv_vfSum_pow`.  The trick that avoids *any* quotient algebra: write the two term values with
a **common factor**.  With `P_k := rv (e^k)`, `v := P_{j-i}`, `d := rv (b i) / rv (b j)`,

  `rv (b_i e^i) = d · w`  and  `rv (b_j e^j) = v · w`,  where `w := rv (b j) · P_i`,

because `P_j = v · P_i`.  So comparing the two term values (mutual `iLe`) is the same as comparing
`d` and `v` (`le_mul_iff`, scale invariance), and then §6 says `d / v` is a unit — i.e. `rv (e^(j-i))`
is `rv (b_i) / rv (b_j)` times a unit, which is precisely "`vv(e^(j-i)) ∈ Γ(Ŝ)`" for the paper's
`b_i, b_j ∈ VF(Ŝ)`.  A separation hypothesis forbidding that contradicts it, giving `hdist`. -/

/-- `(a / b) · (b · c) = a · c`. -/
theorem rv_div_mul_cancel_left (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b)
    (hc : iRV c) (hb0 : b ≠ iRVZero) :
    iRVMul (iRVMul a (iRVInv hM b)) (iRVMul b c) = iRVMul a c := by
  have hinv : iRV (iRVInv hM b) := iRVInv_mem hM hb
  calc iRVMul (iRVMul a (iRVInv hM b)) (iRVMul b c)
      = iRVMul a (iRVMul (iRVInv hM b) (iRVMul b c)) :=
        rv_mul_assoc_of_model hM ha hinv (rv_mul_mem hM hb hc)
    _ = iRVMul a (iRVMul (iRVMul (iRVInv hM b) b) c) := by
        rw [rv_mul_assoc_of_model hM hinv hb hc]
    _ = iRVMul a (iRVMul iRVOne c) := by rw [iRVInv_mul_cancel hM hb hb0]
    _ = iRVMul a c := by rw [rv_mul_one_any hM hc]

/-- `(a / b) · (c · b) = a · c`. -/
theorem rv_div_mul_cancel_right (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b)
    (hc : iRV c) (hb0 : b ≠ iRVZero) :
    iRVMul (iRVMul a (iRVInv hM b)) (iRVMul c b) = iRVMul a c := by
  rw [rv_mul_comm_of_model hM hc hb, rv_div_mul_cancel_left hM ha hb hc hb0]

/-- **The paper's `Γ(Ŝ)` step, tagged.**  If the two term values `rv (b_i e^i)`, `rv (b_j e^j)`
(`i < j`, coefficients and `e` nonzero) have the *same* `Γ`-class — i.e. are mutually `iLe` — then
`rv (e^(j-i))` is `rv (b_i) / rv (b_j)` modulo a unit `Kˣ`.  A hypothesis saying that this never
happens (`vv (e^k) ∉ Γ(Ŝ)` for `0 < k < n`) therefore contradicts it, which is how Lemma 3.5 turns
its separation hypothesis into `hdist`. -/
theorem rv_pow_quot_unit_of_mutual_le (hM : M ⊨ Axioms.ACVF) {b : ℕ → M} {e : M}
    (hb : ∀ i : ℕ, iVF (b i)) (he : iVF e) (he0 : e ≠ iVFZero)
    (hnz : ∀ i : ℕ, b i ≠ iVFZero) {i j : ℕ} (hij : i < j)
    (h1 : iLe (iRv (iVFMul (b i) (vfPow e i))) (iRv (iVFMul (b j) (vfPow e j))))
    (h2 : iLe (iRv (iVFMul (b j) (vfPow e j))) (iRv (iVFMul (b i) (vfPow e i)))) :
    iUnits (iRVMul (iRVMul (iRv (b i)) (iRVInv hM (iRv (b j))))
      (iRVInv hM (iRv (vfPow e (j - i))))) := by
  set r : M := iRv e with hrdef
  have hr : iRV r := rv_mem hM he
  have hr0 : r ≠ iRVZero := fun h0 => he0 (vf_eq_zero_of_rv_eq_zero hM he h0)
  have hi : iRV (iRv (b i)) := rv_mem hM (hb i)
  have hj : iRV (iRv (b j)) := rv_mem hM (hb j)
  have hbj0 : iRv (b j) ≠ iRVZero :=
    fun h0 => hnz j (vf_eq_zero_of_rv_eq_zero hM (hb j) h0)
  have hPi : iRV (rvPowM r i) := rvPowM_mem hM hr i
  have hPd : iRV (rvPowM r (j - i)) := rvPowM_mem hM hr (j - i)
  have hPi0 : rvPowM r i ≠ iRVZero := rvPowM_ne_zero hM hr hr0 i
  have hPd0 : rvPowM r (j - i) ≠ iRVZero := rvPowM_ne_zero hM hr hr0 (j - i)
  have hinvj : iRV (iRVInv hM (iRv (b j))) := iRVInv_mem hM hj
  have hinvd : iRV (iRVInv hM (rvPowM r (j - i))) := iRVInv_mem hM hPd
  -- the three named `RV`-elements
  set d : M := iRVMul (iRv (b i)) (iRVInv hM (iRv (b j))) with hddef
  set w : M := iRVMul (iRv (b j)) (rvPowM r i) with hwdef
  have hd : iRV d := rv_mul_mem hM hi hinvj
  have hw : iRV w := rv_mul_mem hM hj hPi
  have hw0 : w ≠ iRVZero := by
    intro h0
    rcases (rv_mul_eq_zero_of_model hM hj hPi).1 h0 with h' | h'
    · exact hbj0 h'
    · exact hPi0 h'
  -- `rv (e^k) = P_k`
  have hvfp : ∀ k : ℕ, iRv (vfPow e k) = rvPowM r k := by
    intro k
    rw [rv_vfPow hM he k, ← hrdef]
  have hv : iRV (iRv (vfPow e (j - i))) := rv_mem hM (vfPow_mem hM he (j - i))
  have hv0 : iRv (vfPow e (j - i)) ≠ iRVZero := by
    rw [hvfp (j - i)]
    exact hPd0
  -- `P_j = P_{j-i} · P_i`
  have hsplit : rvPowM r j = iRVMul (rvPowM r (j - i)) (rvPowM r i) := by
    rw [← rvPowM_add hM hr (j - i) i, Nat.sub_add_cancel hij.le]
  -- the two common-factor identities
  have hA : iRv (iVFMul (b i) (vfPow e i)) = iRVMul d w := by
    rw [rv_mul_hom_of_model hM (hb i) (vfPow_mem hM he i), hvfp i, hddef, hwdef]
    exact (rv_div_mul_cancel_right hM hi hj hPi hbj0).symm.trans
      (congrArg (fun z => iRVMul d z) (rv_mul_comm_of_model hM hPi hj))
  have hB : iRv (iVFMul (b j) (vfPow e j)) = iRVMul (iRv (vfPow e (j - i))) w := by
    rw [rv_mul_hom_of_model hM (hb j) (vfPow_mem hM he j), hvfp j, hsplit, hvfp (j - i), hwdef]
    rw [← rv_mul_assoc_of_model hM hj hPd hPi, rv_mul_comm_of_model hM hj hPd,
      rv_mul_assoc_of_model hM hPd hj hPi]
  -- compare `d` and `v` by cancelling the common factor `w`
  have hdw : iRV (iRVMul d w) := rv_mul_mem hM hd hw
  have hvw : iRV (iRVMul (iRv (vfPow e (j - i))) w) := rv_mul_mem hM hv hw
  have hdv : iLe d (iRv (vfPow e (j - i))) := by
    refine (le_mul_iff hM hd hv hw hw0).mpr ?_
    rw [← hA, ← hB]
    exact h1
  have hvd : iLe (iRv (vfPow e (j - i))) d := by
    refine (le_mul_iff hM hv hd hw hw0).mpr ?_
    rw [← hA, ← hB]
    exact h2
  exact iUnits_of_mutual_le hM hd hv hv0 hdv hvd

end M8

end SpecialTransformations.Milestone0
