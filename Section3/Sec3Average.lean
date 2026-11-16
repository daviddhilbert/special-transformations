module

/-
Section 3 of Yin, *Special transformations in algebraically closed valued fields*
(arXiv:1006.2467), Lemma `average:0:rv:not:constant` (`paper.tex:709`), quoted there from
`\cite[Lemma~4.9]{Yin:QE:ACVF:min}` = `qe.tex` line 1052.

The paper's sentence:

> **Lemma** (`average:0:rv:not:constant`).  Let `c₁, …, c_k ∈ VF` be distinct elements of the same
> value `α` such that their average is `0`.  Then for some `c_i ≠ c_j` we have `vv(c_i - c_j) = α`
> and hence `rv` is not constant on the set `{c₁, …, c_k}`.

The proof (`qe.tex` 1052-1066) is

> Suppose for contradiction that `vv(c_i - c_j) > α` for all `i ≠ j`.  Since `cha K = 0` and
> `c₁ = -(c₂ + … + c_k)`, we have `α = vv(kc₁) = vv((k-1)c₁ - (c₂ + … + c_k))
> = vv(∑_{i=2}^k (c_i - c₁)) > α`, contradiction.

and it is preceded in `qe.tex` (line 1046) by the standing hypothesis of the whole subsection:
*"For the rest of this section we shall assume that `𝒞` is of pure characteristic `0`"*, and
`qe.tex` line 1049 says of this very lemma: *"It fails when `cha K > 0`."*

Two things are therefore wrong with the frozen form of the statement in the tree
(`QE/Sec3_sat.lean:118`, `SP.swl_average_zero_rv_not_constant`), both of them about the
hypotheses rather than the conclusion:

1. `Axioms.ACVF` of `Milestone0/Encoding.lean` is not the paper's `ACVF(0,0)`: it carries no
   characteristic at all (`Axioms.ACVF00` adds `charZeroVF`/`residueCharZero`), so a model of it
   may have residual characteristic `p`, and then the conclusion fails: the subsection's standing
   hypothesis is load-bearing, not decorative.  `average_zero_counterexample` below is the
   machine-checked refutation: in a model with `v(2) > 0` the pair `c = (1, -1)` satisfies every
   hypothesis of the frozen statement and has no pair with `vv(c_i - c_j) = α`.
2. The legacy `Sec3_sat` transcription assumed the same RV class, whereas the
   paper assumes only the same valuation. The paper's RV nonconstancy conclusion
   is correct. The new `Section3/Average.lean` proves both conclusions and derives
   the integer-unit premise from ACVF(0,0); this legacy file alone still exposes
   that premise and proves only the valuation conclusion.

What this file delivers, in the frozen `L_RV` encoding, on the `VF` sort as the field
`Transfer.VFType` (`QE/VFField.lean`), with the valuation-order calculus of `QE/RVCalc.lean`:

* `average_zero_no_pair_forces_maxIdeal` — the **sharp** form of the lemma, valid in *every*
  model of `Axioms.ACVF` and with no characteristic hypothesis: if no pair of the `c_i` has
  `vv(c_i - c_j) ≤ α`, then `k·1` lies in the maximal ideal, i.e. `v(k) > 0`.  This is exactly
  the residue of the paper's computation `α = vv(kc₁) = vv(∑(c_i - c₁))`, with the equality
  `vv(kc₁) = α` weakened to `vv(kc₁) = vv(k) + α`: the paper's argument proves this stronger
  statement and then discards the `v(k)` term using "pure characteristic 0".
* `average_zero_rv_not_constant` — the paper's lemma, with the standing hypothesis made explicit
  as `v(k·1) ≤ 0` (the half of "`k·1` is a unit" that the paper's `cha K = 0, res.char = 0` is
  used for; the other half, `v(k·1) ≥ 0`, is a theorem, `le_one_natCast`, so nothing is
  smuggled in).
* `average_zero_counterexample` — the refutation of the frozen form, showing the hypothesis is
  necessary, together with the verification that `c = (1, -1)` satisfies the frozen hypotheses
  (distinct, same value, average `0`) in such a model.
* `swl_average_zero_rv_not_constant_corrected` and `swl_average_zero_refuted` — the same two
  statements in the frozen statement's own shape: `c : Fin k → M` with `sumVF (List.ofFn c) =
  iVFZero` and the conclusion written with `iRv (iVFAdd (c i) (iVFNeg (c j)))`, bridged by
  `sumVF_eq_zero_iff` (the frozen `sumVF` left fold is the field sum, `sum_map_val`).

No `sorry`, no `axiom`, no `native_decide`.  The encoding's order `iLe` on `RV` is a **preorder**,
not a partial order, so all equalities of values below are stated as the two `iLe` directions,
which is what the ball predicates of the encoding consume.
-/
public import VFValued

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Transfer

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 0. The value of a `VF`-element, and the elementary calculus -/

/-- **The paper's `vv(x)`**, read on the `VF` sort: `vv(x) = vrv(rv x)`. Here `val` retains the RV representative,
while equality of valuations is expressed by mutual `iLe`, not RV equality.  This is the paper's `α` in `average:0:rv:not:constant`. -/
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

end SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Milestone0.Transfer

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

end SpecialTransformations.Milestone0.Transfer


namespace SpecialTransformations.Milestone0.Transfer

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

/-! ## 4. The frozen form is false: the counterexample `k = 2`, `c = (1, -1)`

The frozen statement `SP.swl_average_zero_rv_not_constant` (`QE/Sec3_sat.lean:118`) quantifies over
instances of `Axioms.ACVF`, which carries **no** characteristic hypothesis (`Axioms.ACVF00` is the
char-`(0,0)` theory: `Milestone0/Encoding.lean`).  In a model of residual characteristic `2`, the
family `c = (1, -1)` is distinct, its average is `0`, both elements have value `1`, and
`vv(c₀ - c₁) = vv(2) > 1`: the paper's conclusion fails.  `qe.tex` says so too, next to the lemma:
*"It fails when `cha K > 0`"*. -/

/-- The family `(1, -1)` of `average_zero_counterexample`. -/
def cTwo : Fin 2 → VFType (M := M) := ![1, -1]

theorem cTwo_injective (h2n : (2 : VFType (M := M)) ≠ 0) :
    Function.Injective (cTwo (M := M)) := by
  have hne : (1 : VFType (M := M)) ≠ -1 := by
    intro hh
    apply h2n
    have h2 : (1 : VFType (M := M)) + 1 = 1 + (-1) :=
      congrArg (fun x => (1 : VFType (M := M)) + x) hh
    calc (2 : VFType (M := M)) = 1 + 1 := by norm_num
      _ = 1 + (-1) := h2
      _ = 0 := add_neg_cancel 1
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cTwo]

/-- Both members of `(1, -1)` have value `1` (`vv(-1) = vv(1)`). -/
theorem cTwo_same : ∀ i : Fin 2,
    iLe (val (cTwo (M := M) i)) (val (cTwo (M := M) 0)) ∧
      iLe (val (cTwo (M := M) 0)) (val (cTwo (M := M) i)) := by
  intro i
  fin_cases i
  · exact ⟨RVCalc.le_refl_rv hM (val_mem _), RVCalc.le_refl_rv hM (val_mem _)⟩
  · show iLe (val (-(1 : VFType (M := M)))) (val 1) ∧ iLe (val 1) (val (-(1 : VFType (M := M))))
    exact val_neg_le 1

/-- The average of `(1, -1)` is `0`. -/
theorem cTwo_sum : (∑ i : Fin 2, cTwo (M := M) i) = 0 := by
  rw [Fin.sum_univ_two]
  simp only [cTwo, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact add_neg_cancel 1

/-- **The conclusion fails for `(1, -1)` when `vv(2) > 1`.** -/
theorem cTwo_no_pair (h2 : ¬ iLe (iRv ((2 : VFType (M := M)).1)) iRVOne) :
    ¬ ∃ i j : Fin 2, i ≠ j ∧ iLe (val (cTwo (M := M) i - cTwo (M := M) j))
      (val (cTwo (M := M) 0)) ∧
      iLe (val (cTwo (M := M) 0)) (val (cTwo (M := M) i - cTwo (M := M) j)) := by
  have hα : val (cTwo (M := M) 0) = iRVOne := RVCalc.rv_one hM
  have h2v : val ((2 : VFType (M := M))) = iRv ((2 : VFType (M := M)).1) := rfl
  rintro ⟨i, j, hij, h1, -⟩
  rw [hα] at h1
  have hsub1 : (1 : VFType (M := M)) - (-1) = 2 := by ring
  have hsub2 : (-1 : VFType (M := M)) - 1 = -(2 : VFType (M := M)) := by ring
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · have h1' : iLe (val ((1 : VFType (M := M)) - (-1))) iRVOne := h1
    rw [hsub1, h2v] at h1'
    exact h2 h1'
  · have h1' : iLe (val ((-1 : VFType (M := M)) - 1)) iRVOne := h1
    rw [hsub2] at h1'
    have h1'' : iLe (iRv ((2 : VFType (M := M)).1)) iRVOne := by
      refine RVCalc.le_trans_rv hM (a := val (2 : VFType (M := M)))
        (b := val (-(2 : VFType (M := M)))) (c := iRVOne) ?_ ?_ ?_ ?_ ?_
      · exact val_mem _
      · exact val_mem _
      · exact rv_one_mem (M := M) hM
      · exact (val_neg_le (2 : VFType (M := M))).2
      · exact h1'
    exact h2 h1''
  · exact absurd rfl hij

/-- **The frozen `average:0:rv:not:constant` is false without a characteristic hypothesis.**
In a model with `(2 : VF) ≠ 0` and `vv(2) > 1` — i.e. residual characteristic `2`, `char K ≠ 2` —
the family `c = (1, -1)` satisfies every hypothesis of the frozen statement (distinct elements,
same value, average `0` at `k = 2`) and the conclusion fails. -/
theorem average_zero_counterexample (h2n : (2 : VFType (M := M)) ≠ 0)
    (h2 : ¬ iLe (iRv ((2 : VFType (M := M)).1)) iRVOne) :
    Function.Injective (cTwo (M := M)) ∧
      (∀ i : Fin 2, iLe (val (cTwo (M := M) i)) (val (cTwo (M := M) 0)) ∧
        iLe (val (cTwo (M := M) 0)) (val (cTwo (M := M) i))) ∧
      (∑ i : Fin 2, cTwo (M := M) i) = 0 ∧
      ¬ ∃ i j : Fin 2, i ≠ j ∧ iLe (val (cTwo (M := M) i - cTwo (M := M) j))
        (val (cTwo (M := M) 0)) ∧
        iLe (val (cTwo (M := M) 0)) (val (cTwo (M := M) i - cTwo (M := M) j)) :=
  ⟨cTwo_injective h2n, cTwo_same, cTwo_sum, cTwo_no_pair h2⟩


/-! ## 5. The frozen shape: `sumVF` and the M-level statement

`SP.swl_average_zero_rv_not_constant` (`QE/Sec3_sat.lean:118`) is stated for a family
`c : Fin k → M` of `M`-elements with the hypothesis `sumVF (List.ofFn c) = iVFZero`, `SP.sumVF`
being the left fold of `iVFAdd`.  This section bridges that shape to the `VFType`-valued statements
above, and restates both the corrected lemma and the counterexample in the frozen shape. -/

/-- The sum of a list of `VF`-elements — the same definition as `SP.sumVF` of
`QE/Sec3_sat.lean:65` (`[] ↦ 0`, `a :: l ↦ a + sumVF l`), repeated here so that this file does not
depend on the file that carries the frozen (unproved) statement. -/
def sumVF : List M → M
  | [] => iVFZero
  | a :: l => iVFAdd a (sumVF l)

theorem iVF_sumVF : ∀ l : List M, (∀ x ∈ l, iVF x) → iVF (sumVF l)
  | [], _ => vf_zero_mem (M := M) hM
  | a :: l, h =>
      vf_add_mem (M := M) hM (h a List.mem_cons_self)
        (iVF_sumVF l (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- **The `M`-valued family attached to a list of `VF`-elements.** -/
def vfMk {ι : Type*} (c : ι → M) (hVF : ∀ i, iVF (c i)) : ι → VFType (M := M) :=
  fun i => ⟨c i, hVF i⟩

/-- **`sumVF` computes the field sum**: the underlying `M`-element of a finite field sum is the
`sumVF` of the underlying list. -/
theorem sum_map_val {ι : Type*} (l : List ι) (c' : ι → VFType (M := M)) :
    ((l.map c').sum).1 = sumVF (l.map (fun i => (c' i).1)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      show iVFAdd (c' a).1 ((l.map c').sum).1 = iVFAdd (c' a).1 (sumVF (l.map (fun i => (c' i).1)))
      rw [ih]

/-- **The bridge between the frozen hypothesis `sumVF (List.ofFn c) = iVFZero` and the field sum
`∑ i, c i = 0`.** -/
theorem sumVF_eq_zero_iff {k : ℕ} (c : Fin k → M) (hVF : ∀ i, iVF (c i)) :
    sumVF (List.ofFn c) = iVFZero ↔ (∑ i : Fin k, vfMk c hVF i) = 0 := by
  have key : ((∑ i : Fin k, vfMk c hVF i)).1 = sumVF (List.ofFn c) := by
    rw [← List.sum_ofFn, List.ofFn_eq_map, List.ofFn_eq_map]
    exact sum_map_val (List.finRange k) (vfMk c hVF)
  constructor
  · intro h
    refine Subtype.ext ?_
    show ((∑ i : Fin k, vfMk c hVF i)).1 = iVFZero
    rw [key, h]
  · intro h
    rw [← key]
    exact congrArg Subtype.val h

/-- **`average:0:rv:not:constant` in the frozen shape of `SP.swl_average_zero_rv_not_constant`**
(`QE/Sec3_sat.lean:118`), with the correction: the standing hypothesis of `qe.tex` §4 (pure
characteristic `0`, `qe.tex:1046`) is an explicit hypothesis `vv(k·1) ≤ 1`, and the conclusion is
the paper's `vv(c_i - c_j) = α` written as the two `iLe` directions, since the encoding's `RV`-order
is a preorder.  (The `rv`-constancy clause of the paper's sentence is a slip, refuted by
`SP.swl_average_conclusion_unsat`; it is not part of this statement.) -/
theorem swl_average_zero_rv_not_constant_corrected {k : ℕ} (hk : 2 ≤ k) (i₀ : Fin k)
    (c : Fin k → M) (hVF : ∀ i, iVF (c i)) (hinj : Function.Injective c)
    (hsame : ∀ i, iLe (iRv (c i)) (iRv (c i₀)) ∧ iLe (iRv (c i₀)) (iRv (c i)))
    (havg : sumVF (List.ofFn c) = iVFZero)
    (hunit : iLe (iRv ((k : VFType (M := M)).1)) iRVOne) :
    ∃ i j : Fin k, i ≠ j ∧
      iLe (iRv (iVFAdd (c i) (iVFNeg (c j)))) (iRv (c i₀)) ∧
      iLe (iRv (c i₀)) (iRv (iVFAdd (c i) (iVFNeg (c j)))) := by
  have hzero := (sumVF_eq_zero_iff c hVF).1 havg
  have hinj' : Function.Injective (vfMk c hVF) := fun i j hij => hinj (congrArg Subtype.val hij)
  obtain ⟨i, j, hij, h1, h2⟩ :=
    average_zero_rv_not_constant hk i₀ (vfMk c hVF) hinj' hsame hzero hunit
  exact ⟨i, j, hij, h1, h2⟩

/-- The frozen family `(1, -1)` at the `M` sort. -/
def cTwoM : Fin 2 → M := fun i => (cTwo (M := M) i).1

theorem cTwoM_vf : ∀ i, iVF (cTwoM (M := M) i) := fun i => (cTwo (M := M) i).2

theorem cTwoM_eq : vfMk (cTwoM (M := M)) (cTwoM_vf (M := M)) = cTwo (M := M) := by
  funext i
  exact Subtype.ext rfl

/-- **The frozen `SP.swl_average_zero_rv_not_constant` is FALSE in a model of residual
characteristic `2`.**  With `c = (1, -1)` (as an `M`-valued family), every hypothesis of the frozen
statement holds — the elements are distinct, `rv` agrees on them, and `sumVF (List.ofFn c) = 0` —
while the conclusion fails, because `vv(1 - (-1)) = vv(2) > 1`. -/
theorem swl_average_zero_refuted (h2n : (2 : VFType (M := M)) ≠ 0)
    (h2 : ¬ iLe (iRv ((2 : VFType (M := M)).1)) iRVOne) :
    Function.Injective (cTwoM (M := M)) ∧
      (∀ i : Fin 2, iLe (iRv (cTwoM (M := M) i)) (iRv (cTwoM (M := M) 0)) ∧
        iLe (iRv (cTwoM (M := M) 0)) (iRv (cTwoM (M := M) i))) ∧
      sumVF (List.ofFn (cTwoM (M := M))) = iVFZero ∧
      ¬ ∃ i j : Fin 2, i ≠ j ∧
        iLe (iRv (iVFAdd (cTwoM (M := M) i) (iVFNeg (cTwoM (M := M) j))))
          (iRv (cTwoM (M := M) 0)) ∧
        iLe (iRv (cTwoM (M := M) 0))
          (iRv (iVFAdd (cTwoM (M := M) i) (iVFNeg (cTwoM (M := M) j)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact cTwo_injective h2n (Subtype.ext hij)
  · exact cTwo_same
  · rw [sumVF_eq_zero_iff (cTwoM (M := M)) (cTwoM_vf (M := M)), cTwoM_eq]
    exact cTwo_sum
  · exact cTwo_no_pair h2

end SpecialTransformations.Milestone0.Transfer
