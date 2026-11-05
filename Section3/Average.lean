/-
# Lemma 3.8: the zero-average lemma

Adapted from the local legacy `Sec3Average.lean`, whose mathematical proof is
retained below. The legacy header incorrectly called the paper's RV
nonconstancy conclusion a slip. Same valuation does not mean same RV class.
The exported result includes both conclusions and derives the integer
unit condition from ACVF(0,0). Source: arXiv:1006.2467v1, Lemma 3.8.
-/
import VFValued
import CanonicalRV

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section3.Average

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 0. The value of a `VF`-element, and the elementary calculus -/

/-- RV representative of the value of x. Equal values mean mutual `iLe`,
not equality of these representatives; `vrv` is a quotient map. -/
noncomputable def val (x : VFType (M := M)) : M := iRv x.1

theorem val_mem (x : VFType (M := M)) : iRV (val x) := rv_mem hM x.2

theorem val_zero : val (0 : VFType (M := M)) = iRVZero := RVCalc.rv_zero_eq hM

theorem val_add (x y : VFType (M := M)) :
    val (x + y) = iRv (iVFAdd x.1 y.1) := rfl

theorem val_neg_val (x : VFType (M := M)) :
    val (-x) = iRv (iVFNeg x.1) := rfl

/-- The ultrametric inequality, at the `VF` sort: `vv(x + y) ≥ min(vv x, vv y)`. -/
theorem le_val_add (x y : VFType (M := M)) :
    iLe (val x) (val (x + y)) ∨ iLe (val y) (val (x + y)) :=
  RVCalc.rv_ultrametric hM x.2 y.2

/-- `x` and `-x` have the same value (both `iLe` directions). -/
theorem val_neg_le (x : VFType (M := M)) :
    iLe (val (-x)) (val x) ∧ iLe (val x) (val (-x)) :=
  RVCalc.rv_neg_class hM x.2

/-- Transitivity of the value order, at the `VF` sort. -/
theorem val_trans {a : M} (ha : iRV a) (x y : VFType (M := M))
    (h1 : iLe a (val x)) (h2 : iLe (val x) (val y)) : iLe a (val y) :=
  RVCalc.le_trans_rv hM ha (val_mem x) (val_mem y) h1 h2

/-! ## 1. Strict inequalities are preserved by finite sums

`vv(x) > α` is `¬ iLe (val x) α`: in the encoding's preorder (which is the value order *reversed*
relative to the containment order of balls, `iLe a b ↔ vv(a) ≤ vv(b)` by `Axioms.leTop`/`leRefl`)
"`¬ b ≤ a`" is "`a < b`" — but expressed without mentioning the strict order, which the encoding
does not have as a symbol. -/

/-- **`vv(x + y) > α` when `vv(x) > α` and `vv(y) > α`**: the two-term strict triangle.  This is
the ultrametric axiom read contrapositively, and it is what makes the paper's
`vv(∑_{i} (c_i - c₁)) > α` work. -/
theorem add_strict {a : M} (ha : iRV a) {x y : VFType (M := M)}
    (hx : ¬ iLe (val x) a) (hy : ¬ iLe (val y) a) : ¬ iLe (val (x + y)) a := by
  intro h
  rcases le_val_add x y with h1 | h1
  · exact hx (RVCalc.le_trans_rv hM (val_mem x) (val_mem (x + y)) ha h1 h)
  · exact hy (RVCalc.le_trans_rv hM (val_mem y) (val_mem (x + y)) ha h1 h)

/-- **Strict inequalities are preserved by arbitrary finite sums**: if every term of the finite
sum `∑ i ∈ s, f i` has value `> α`, then so does the sum.  (The empty sum is `0`, of value `∞`,
which is `> α` precisely because `α ≠ ∞`; hence the hypothesis `ha0`.) -/
theorem sum_strict {ι : Type*} (s : Finset ι) (f : ι → VFType (M := M)) {a : M}
    (ha : iRV a) (ha0 : a ≠ iRVZero)
    (h : ∀ i ∈ s, ¬ iLe (val (f i)) a) : ¬ iLe (val (∑ i ∈ s, f i)) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      show ¬ iLe (iRv (iVFZero : M)) a
      rw [RVCalc.rv_zero_eq hM]
      intro hz
      exact ha0 (RVCalc.le_infty_eq hM ha hz)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact add_strict ha (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end SpecialTransformations.Section3.Average

namespace SpecialTransformations.Section3.Average

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 2. `val x = ∞` is `x = 0` -/

/-- A `VF`-element has value `∞` exactly when it is `0` (`Axioms.rvEqInfty`). -/
theorem val_eq_infty_iff {x : VFType (M := M)} : val x = iRVZero ↔ x = 0 := by
  constructor
  · intro h
    have h' : x.1 = iVFZero := RVCalc.vf_eq_zero_of_rv_eq_zero hM x.2 h
    refine Subtype.ext ?_
    rw [h']
    rfl
  · intro h
    subst h
    exact RVCalc.rv_zero_eq hM

/-- **`average:0:rv:not:constant`** (paper §3, `paper.tex:709`, = `qe.tex` Lemma 4.9),
**sharp form**: the paper's computation proves more than stated, and the extra is exactly what its
standing hypothesis ("`𝒞` pure characteristic `0`", `qe.tex:1046`) is used for.

Let `c_1, …, c_k` (`k ≥ 2`) be distinct `VF`-elements of the same value `α = val (c i₀)` with
average `0`.  Then **either** two of them have `vv(c_i - c_j) = α` (both `iLe` directions, the
encoding's order being a preorder), **or** `k·1` lies in the maximal ideal, i.e. `vv(k·1) > 1`.

The second alternative is not an artefact: `average_zero_counterexample` below exhibits, in a model
with `v(2) > 0`, a `k = 2` instance whose conclusion fails.  Under `cha K = res.char = 0` — the
paper's standing hypothesis — the second alternative is impossible (`k·1` is a unit), and the
lemma is the paper's. -/
theorem average_zero_no_pair_forces_maxIdeal {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k)
    (c : Fin k → VFType (M := M)) (hinj : Function.Injective c)
    (hsame : ∀ i, iLe (val (c i)) (val (c i₀)) ∧ iLe (val (c i₀)) (val (c i)))
    (hsum : (∑ i, c i) = 0) :
    (∃ i j : Fin k, i ≠ j ∧ iLe (val (c i - c j)) (val (c i₀)) ∧
        iLe (val (c i₀)) (val (c i - c j)))
      ∨ ¬ iLe (iRv ((k : VFType (M := M)).1)) iRVOne := by
  classical
  by_cases hex : ∃ i j : Fin k, i ≠ j ∧ iLe (val (c i - c j)) (val (c i₀)) ∧
      iLe (val (c i₀)) (val (c i - c j))
  · exact Or.inl hex
  · right
    have ha_mem : iRV (val (c i₀)) := val_mem (c i₀)
    -- a second index
    have hne : ∃ i₁ : Fin k, i₁ ≠ i₀ := by
      by_cases h : i₀.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro hh
        have h1 : (1 : ℕ) = i₀.val := congrArg Fin.val hh
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro hh
        exact h (by have h1 : (0 : ℕ) = i₀.val := congrArg Fin.val hh; omega)
    -- `α ≠ ∞`, because `α = ∞` would force all the `c i` to be `0`
    have ha0 : val (c i₀) ≠ iRVZero := by
      intro h
      obtain ⟨i₁, hi₁ne⟩ := hne
      have h0 : c i₀ = 0 := val_eq_infty_iff.1 h
      have h1 : c i₁ = 0 := val_eq_infty_iff.1 (RVCalc.le_infty_eq hM (val_mem (c i₁))
        (h ▸ (hsame i₁).2))
      exact hi₁ne (hinj (h1.trans h0.symm))
    -- **Step A**: `α ≤ vv(c_i - c_j)` for *every* pair, by the ultrametric inequality
    have hle : ∀ i j : Fin k, iLe (val (c i₀)) (val (c i - c j)) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        have hz : c i - c i = (0 : VFType (M := M)) := sub_self (c i)
        rw [hz]
        show iLe (val (c i₀)) (iRv (iVFZero : M))
        rw [RVCalc.rv_zero_eq hM]
        exact RVCalc.le_top_rv hM ha_mem
      · have hs : c i - c j = c i + (-(c j)) := sub_eq_add_neg (c i) (c j)
        rw [hs]
        rcases le_val_add (c i) (-(c j)) with h1 | h1
        · exact RVCalc.le_trans_rv hM ha_mem (val_mem (c i)) (val_mem _) (hsame i).2 h1
        · exact RVCalc.le_trans_rv hM ha_mem (val_mem (-(c j))) (val_mem _)
            (RVCalc.le_trans_rv hM ha_mem (val_mem (c j)) (val_mem (-(c j)))
              (hsame j).2 (val_neg_le (c j)).2) h1
    -- **Step B**: no pair means `vv(c_i - c_j) > α` for every `i ≠ j`
    have hstrict : ∀ i j : Fin k, i ≠ j → ¬ iLe (val (c i - c j)) (val (c i₀)) := by
      intro i j hij h
      exact hex ⟨i, j, hij, h, hle i j⟩
    -- **Step C**: `∑_{i ≠ i₀} (c_i - c_i₀) = -k·c_i₀`
    have hkey : (∑ i ∈ (Finset.univ.erase i₀), (c i - c i₀))
        = -((k : VFType (M := M)) * c i₀) := by
      have h0mem : i₀ ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
      have hers := Finset.add_sum_erase (Finset.univ : Finset (Fin k))
        (fun i => c i - c i₀) h0mem
      have hcnt : (∑ i ∈ (Finset.univ : Finset (Fin k)), (c i - c i₀))
          = -((k : VFType (M := M)) * c i₀) := by
        rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        exact zero_sub _
      rw [hcnt] at hers
      simpa using hers
    -- **Step D**: all the terms are `> α`, so their sum is
    have hD : ¬ iLe (val (∑ i ∈ (Finset.univ.erase i₀), (c i - c i₀)))
        (val (c i₀)) :=
      sum_strict (Finset.univ.erase i₀) (fun i => c i - c i₀) ha_mem ha0
        (fun i hi => hstrict i i₀ (Finset.ne_of_mem_erase hi))
    rw [hkey] at hD
    -- **Step E**: `-k·c_i₀` has the size of `k·c_i₀`
    have hE : ¬ iLe (val ((k : VFType (M := M)) * c i₀)) (val (c i₀)) := by
      intro h
      exact hD (RVCalc.le_trans_rv hM (val_mem _) (val_mem _) ha_mem
        (val_neg_le ((k : VFType (M := M)) * c i₀)).1 h)
    -- **Step F**: `vv(k·c_i₀) = vv(k)·α`, and scaling by `α` is order reflecting
    have hprod : val ((k : VFType (M := M)) * c i₀)
        = iRVMul (iRv ((k : VFType (M := M)).1)) (val (c i₀)) :=
      rv_mul_hom_of_model hM (k : VFType (M := M)).2 (c i₀).2
    intro hk1le
    have h1 : iLe (iRVMul (iRv ((k : VFType (M := M)).1)) (val (c i₀)))
        (iRVMul iRVOne (val (c i₀))) :=
      (RVCalc.le_mul_iff hM (rv_mem hM (k : VFType (M := M)).2) (rv_one_mem (M := M) hM)
        ha_mem ha0).1 hk1le
    rw [rv_mul_one_any hM ha_mem] at h1
    exact hE (by rwa [hprod])

end SpecialTransformations.Section3.Average


namespace SpecialTransformations.Section3.Average

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 3. The paper's lemma, with the standing hypothesis made explicit -/

theorem val_one : val (1 : VFType (M := M)) = iRVOne := RVCalc.rv_one hM

/-- **`vv(k·1) ≥ 1`** for every `k`: a natural number is integral, `k·1 ∈ O`.  This is the half of
"`k·1` is a unit" that needs no hypothesis (it holds in every model of `Axioms.ACVF`, including
residual characteristic `p`), and it is the reason `average_zero_rv_not_constant`'s hypothesis
`vv(k·1) ≤ 1` is *only* the residue-characteristic-zero half of the paper's `cha K = res.char = 0`.
-/
theorem le_one_natCast : ∀ n : ℕ, iLe iRVOne (val ((n : VFType (M := M))))
  | 0 => by
      rw [Nat.cast_zero]
      show iLe iRVOne (iRv (iVFZero : M))
      rw [RVCalc.rv_zero_eq hM]
      exact RVCalc.le_top_rv hM (rv_one_mem (M := M) hM)
  | n + 1 => by
      have hcast : ((n + 1 : ℕ) : VFType (M := M)) = (n : VFType (M := M)) + 1 :=
        Nat.cast_succ n
      rw [hcast]
      rcases le_val_add (n : VFType (M := M)) 1 with h1 | h1
      · exact RVCalc.le_trans_rv hM (rv_one_mem (M := M) hM) (val_mem _) (val_mem _)
          (le_one_natCast n) h1
      · rwa [show val (1 : VFType (M := M)) = iRVOne from RVCalc.rv_one hM] at h1

/-- **`average:0:rv:not:constant`** (paper §3, `paper.tex:709`; Yin, *QE:ACVF:min*, Lemma 4.9),
in the form the paper states it, with the standing hypothesis of `qe.tex` §4 ("`𝒞` pure
characteristic `0`") made explicit as `vv(k·1) ≤ 1`, i.e. `k·1` is not in the maximal ideal;
`le_one_natCast` supplies the other inequality, so together they say `k·1` is a unit — which is
exactly what `cha K = 0, res.char K = 0` gives for a natural number `k`.

(Without that hypothesis the statement is false; `average_zero_counterexample` below is the
machine-checked counterexample, in every model of residual characteristic `2`.) -/
theorem average_zero_rv_not_constant {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k)
    (c : Fin k → VFType (M := M)) (hinj : Function.Injective c)
    (hsame : ∀ i, iLe (val (c i)) (val (c i₀)) ∧ iLe (val (c i₀)) (val (c i)))
    (hsum : (∑ i, c i) = 0)
    (hunit : iLe (iRv ((k : VFType (M := M)).1)) iRVOne) :
    ∃ i j : Fin k, i ≠ j ∧ iLe (val (c i - c j)) (val (c i₀)) ∧
      iLe (val (c i₀)) (val (c i - c j)) := by
  rcases average_zero_no_pair_forces_maxIdeal hk i₀ c hinj hsame hsum with h | h
  · exact h
  · exact absurd hunit h


end SpecialTransformations.Section3.Average

namespace SpecialTransformations.Section3.Average
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem numeral_realize (k : ℕ) {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFNumeral k : Tm n).realize v = ((k : VFType (M := M)).1) := by
  induction k with
  | zero => exact realize_tVFZero v
  | succ k ih =>
    rw [tVFNumeral, realize_tVFAdd, ih, realize_tVFOne, Nat.cast_succ]
    rfl

theorem prime_unit (h00 : M ⊨ Axioms.ACVF00) (p : ℕ) (hp : p.Prime) :
    iLe (val (p : VFType (M := M))) iRVOne := by
  haveI := h00
  have h := Axioms.ACVF00.realize_sentence_of_mem (M := M)
    (show Axioms.residueCharZero p ∈ Axioms.ACVF00 from
      Or.inr ⟨p, hp, rfl⟩)
  have h' : ¬ (iLe iRVOne (val (p : VFType (M := M))) ∧
      ¬ iLe (val (p : VFType (M := M))) iRVOne) := by
    simpa [Sentence.Realize, Formula.Realize, Axioms.residueCharZero,
      pGtOne, realize_pLe, realize_tRv, numeral_realize, val,
      realize_tRVOne_T] using h
  exact Classical.byContradiction (fun hn => h' ⟨le_one_natCast p, hn⟩)

theorem nat_unit (h00 : M ⊨ Axioms.ACVF00) (k : ℕ) (hk : k ≠ 0) :
    iLe (val (k : VFType (M := M))) iRVOne := by
  have all : ∀ k : ℕ, k ≠ 0 → iLe (val (k : VFType (M := M))) iRVOne := by
    apply Nat.recOnMul
    · intro hz; exact (hz rfl).elim
    · intro _; rw [Nat.cast_one, val_one]; exact RVCalc.le_refl_rv hM (rv_one_mem hM)
    · intro p hp _; exact prime_unit h00 p hp
    · intro a b ha hb hab
      have ha0 : a ≠ 0 := fun h => hab (by simp [h])
      have hb0 : b ≠ 0 := fun h => hab (by simp [h])
      have hrb0 : val (b : VFType (M := M)) ≠ iRVZero := by
        intro hz
        exact (RVCalc.rv_one_ne_zero hM)
          (RVCalc.le_infty_eq hM (rv_one_mem hM) (hz ▸ hb hb0))
      have hmul := (RVCalc.le_mul_iff hM (val_mem (a : VFType (M := M)))
        (rv_one_mem hM) (val_mem (b : VFType (M := M))) hrb0).mp (ha ha0)
      rw [rv_mul_one_any hM (val_mem (b : VFType (M := M)))] at hmul
      have hprod : val ((a * b : ℕ) : VFType (M := M)) =
          iRVMul (val (a : VFType (M := M))) (val (b : VFType (M := M))) := by
        rw [Nat.cast_mul]
        exact rv_mul_hom_of_model hM (a : VFType (M := M)).2 (b : VFType (M := M)).2
      rw [hprod]
      exact RVCalc.le_trans_rv hM
        (rv_mul_mem hM (val_mem _) (val_mem _)) (val_mem _) (rv_one_mem hM)
        hmul (hb hb0)
  exact all k hk

theorem lemma_3_8 (h00 : M ⊨ Axioms.ACVF00) {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k)
    (c : Fin k → VFType (M := M)) (hinj : Function.Injective c)
    (hsame : ∀ i, iLe (val (c i)) (val (c i₀)) ∧ iLe (val (c i₀)) (val (c i)))
    (hsum : (∑ i, c i) = 0) :
    ∃ i j : Fin k, i ≠ j ∧ iLe (val (c i - c j)) (val (c i₀)) ∧
      iLe (val (c i₀)) (val (c i - c j)) ∧ iRv (c i).1 ≠ iRv (c j).1 := by
  obtain ⟨i, j, hij, hle, hge⟩ := average_zero_rv_not_constant hk i₀ c hinj hsame hsum
    (nat_unit h00 k (by omega))
  refine ⟨i, j, hij, hle, hge, ?_⟩
  intro heq
  have hj0 : c j ≠ 0 := by
    intro hz
    have hbase : val (c i₀) = iRVZero :=
      RVCalc.le_infty_eq hM (val_mem (c i₀))
        (by simpa [hz, val_zero] using (hsame j).1)
    have hiv : val (c i) = iRVZero :=
      RVCalc.le_infty_eq hM (val_mem (c i)) (hbase ▸ (hsame i).2)
    have hi0 := val_eq_infty_iff.mp hiv
    exact hij (hinj (hi0.trans hz.symm))
  have hclose := (CanonicalRV.encoded_eq_iff_close (c i).2 (c j).2
    (fun hh => hj0 (Subtype.ext hh))).mp heq
  apply hclose
  change iLe (val (c i - c j)) (val (c j))
  exact RVCalc.le_trans_rv hM (val_mem _) (val_mem _) (val_mem _) hle (hsame j).2
end SpecialTransformations.Section3.Average
