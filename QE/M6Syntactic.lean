/-
**Lemma 3.2 (`rv:root:lift:vf`) in the vocabulary of the frozen `L_RV`.**

`QE/Lemma32_at_model.lean` instantiates Yin's Lemma 3.2 (`YinRV.rv_root_lift_rv`, proved
unconditionally in `QE/Lemma32_root_lifting.lean`) at `Transfer.VFType M` for `M ⊨ Axioms.ACVF`.
Its hypotheses and conclusion are stated with a *Mathlib* valuation `w`, which no formula of `L_RV`
can mention:

    huniv : ∀ i ∈ F.support, w (F.coeff i * b ^ i) = 1
    hred  : w (Σ i ∈ F.support, F.coeff i * b ^ i) < 1
    ⊢ ∃ b', YinRV.rv w b' = YinRV.rv w b ∧ F.IsRoot b'

A port of the paper's Section 3 needs the same lemma where every hypothesis and the conclusion are
readable in `L_RV`, so that it applies to the image of an `RV`-polynomial under an embedding
`S ↪[LRV] N`.  That is what this file supplies.  No `w` survives in the statements below.

## The dictionary

`QE/VFValued.lean` provides, for every model `M ⊨ Axioms.ACVF`, a Mathlib valuation
`w : Valuation (VFType M) Γ` whose order is the encoding's relation read backwards:

    predV x y = iLe (iRv y.1) (iRv x.1)   and   predV x y ↔ w x ≤ w y.

Since `w 1 = 1` this gives the whole translation, and it is an **iff** at every point:

* `one_le_iff`       : `iLe iRVOne (iRv c) ↔ w c ≤ 1`      (`c ∈ O`)
* `le_one_iff`       : `iLe (iRv c) iRVOne ↔ 1 ≤ w c`      (`c ∉ M`)
* `value_lt_one_iff` : `w c < 1 ↔ ¬ iLe (iRv c) iRVOne`    (`c ∈ M`)
* `value_eq_one_of_units` / `units_of_value_eq_one`:
  `c ≠ 0 → (iUnits (iRv c) ↔ w c = 1)`.

The last line is the translation the paper's `huniv` needs: the paper's `Kˣ` is the encoding's
`iUnits`, and `huniv` says every term `b_i b ^ i` is a unit of the valuation ring.  Note that it is
**strictly weaker** than "`iRv (b_i b ^ i) = iRVOne`" (`rv_unit_value`'s hypothesis, i.e.
`b_i b ^ i ≡ 1 mod M`), which is *not* what the paper's `F̄(t) = 0` yields: all one gets is that
each `rv(b_i b ^ i)` lies in `Kˣ`.  `hred` says the sum lies in the maximal ideal, which reads
`¬ iLe (iRv s.1) iRVOne`.

## Results

* `rv_root_lift_encoding` — Lemma 3.2, hypotheses and conclusion in `L_RV`.
* `rv_root_lift_encoding_I` — the same in the paper's bookkeeping: only a subset `I` of the support
  need consist of units (the coefficients with `t_i ≠ 0`), the remaining coefficients of the
  support only have to lie in the maximal ideal (the paper's `vrv(rv(b_i) t^i) > 0` for `t_i = 0`),
  and `2 ≤ I.card` says the reduced polynomial is not a monomial.  This is the form
  `lift:all:root` (3.4) and `lift:divisible:hull` (3.5) consume.
* `hred_of_residue_sum_zero` — where `hred` comes from: two unit terms whose residue sum (the
  encoding's `iKAdd`) vanishes add up inside the maximal ideal.  This is the step that turns the
  paper's hypothesis "`F̄(t) = 0` in the residue field" into the `hred` hypothesis above.
* `rv_root_lift_encoding_reduction_LRV` — Lemma 3.2 with hypotheses on the *coefficients* only:
  all coefficients integral, `b` a unit, `I` the support of the reduction, `F̄` not a monomial, and
  `hred`.  `huniv`/`hsmall` are *derived*, not assumed.  This is the form a port of 3.4/3.5
  consumes.
* §6, the closure laws of the valuation ring `O` and its maximal ideal `M` in `L_RV`:
  `one_le_add`, `lt_one_add`, `one_le_mul`, `lt_one_mul`, `one_le_neg`, `lt_one_neg`, and the
  `Kˣ`-closure facts `units_mul`, `units_pow`, `units_neg`.

Statements are term-mode on purpose: `rw` does not match lemmas stated for `Mul (VFType M)` /
`One (VFType M)` against terms here, because those instances arrive through the
`noncomputable Field (VFType M)` structure and are not reducibly transparent.
-/
import Lemma32_at_model

open FirstOrder FirstOrder.Language
open Polynomial
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

-- the `IsAlgClosed` instance is used as an instance, not as a `let`
set_option linter.style.haveILetI false

namespace SpecialTransformations.Milestone0.M6Syntactic

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `Transfer.VFType M` is a field, so it has no zero divisors.  (Not an instance in this
Mathlib's `Field` hierarchy, and the ports need `mul_ne_zero`.) -/
noncomputable instance instNoZeroDivisorsVFType : NoZeroDivisors (Transfer.VFType (M := M)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    by_cases ha : a = 0
    · exact Or.inl ha
    · refine Or.inr ?_
      have h2 : a⁻¹ * a = (1 : Transfer.VFType (M := M)) := inv_mul_cancel₀ ha
      have s1 : a⁻¹ * (a * b) = (a⁻¹ * a) * b := (mul_assoc a⁻¹ a b).symm
      have s2 : (a⁻¹ * a) * b = (1 : Transfer.VFType (M := M)) * b :=
        congrArg (fun t => t * b) h2
      have s3 : (1 : Transfer.VFType (M := M)) * b = b := one_mul b
      have e1 : a⁻¹ * (a * b) = a⁻¹ * (0 : Transfer.VFType (M := M)) :=
        congrArg (fun t => a⁻¹ * t) h
      have e2 : a⁻¹ * (0 : Transfer.VFType (M := M)) = 0 := mul_zero a⁻¹
      have e3 : a⁻¹ * (a * b) = b := (s1.trans s2).trans s3
      exact e3.symm.trans (e1.trans e2)

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
variable {w : Valuation (Transfer.VFType (M := M)) Γ}

/-! ## 1. The order dictionary: `iLe` on `RV`-classes is the valuation order, reversed -/

/-- `iLe iRVOne (rv c)` is `c ∈ O`. -/
theorem one_le_iff (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    (c : Transfer.VFType (M := M)) :
    iLe iRVOne (iRv c.1) ↔ w c ≤ 1 := by
  have hone : w (1 : Transfer.VFType (M := M)) = 1 := Valuation.map_one w
  have hp : VFValued.predV c 1 ↔ iLe iRVOne (iRv c.1) := by
    show iLe (iRv ((1 : Transfer.VFType (M := M))).1) (iRv c.1) ↔ iLe iRVOne (iRv c.1)
    rw [show ((1 : Transfer.VFType (M := M))).1 = Transfer.iVFOne from rfl, RVCalc.rv_one hM]
  refine (hp.symm.trans (hw c 1)).trans ?_
  show w c ≤ w (1 : Transfer.VFType (M := M)) ↔ w c ≤ 1
  exact iff_of_eq (congrArg (fun t : Γ => w c ≤ t) hone)

/-- `iLe (rv c) iRVOne` is `c ∉ M`. -/
theorem le_one_iff (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    (c : Transfer.VFType (M := M)) :
    iLe (iRv c.1) iRVOne ↔ 1 ≤ w c := by
  have hone : w (1 : Transfer.VFType (M := M)) = 1 := Valuation.map_one w
  have hp : VFValued.predV 1 c ↔ iLe (iRv c.1) iRVOne := by
    show iLe (iRv c.1) (iRv ((1 : Transfer.VFType (M := M))).1) ↔ iLe (iRv c.1) iRVOne
    rw [show ((1 : Transfer.VFType (M := M))).1 = Transfer.iVFOne from rfl, RVCalc.rv_one hM]
  refine (hp.symm.trans (hw 1 c)).trans ?_
  show w (1 : Transfer.VFType (M := M)) ≤ w c ↔ 1 ≤ w c
  exact iff_of_eq (congrArg (fun t : Γ => t ≤ w c) hone)

/-- `iLe (rv c) iRVOne` fails exactly when `c` lies in the maximal ideal: this is `hred` of
Lemma 3.2 in the encoding's vocabulary. -/
theorem value_lt_one_iff (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    (c : Transfer.VFType (M := M)) :
    w c < 1 ↔ ¬ iLe (iRv c.1) iRVOne :=
  not_le.symm.trans ((le_one_iff hw c).not).symm

/-! ## 2. `huniv`: the paper's `Kˣ` is the encoding's `iUnits` -/

/-- **A unit of the valuation ring has value `1`.**  In particular the paper's hypothesis that all
the terms `b_i b ^ i` of the reduced polynomial are units is a statement about `iUnits`. -/
theorem value_eq_one_of_units (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {c : Transfer.VFType (M := M)} (hc0 : c ≠ 0) (h : iUnits (iRv c.1)) : w c = 1 := by
  have hr : iRV (iRv c.1) := Transfer.rv_mem hM c.2
  have hz : c.1 ≠ Transfer.iVFZero := fun hh => hc0 (Subtype.ext hh)
  have hr0 : iRv c.1 ≠ iRVZero := VFValued.rv_ne_zero_of_ne_zero c.2 hz
  obtain ⟨h1, h2⟩ := (RVCalc.units_iff_le_one hM hr hr0).mp h
  exact le_antisymm ((one_le_iff hw c).mp h1) ((le_one_iff hw c).mp h2)

/-- Conversely, value `1` is a unit of the valuation ring — `huniv` and the `iUnits`-form are the
same hypothesis, not merely one implying the other. -/
theorem units_of_value_eq_one (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {c : Transfer.VFType (M := M)} (h : w c = 1) : iUnits (iRv c.1) := by
  have hzero : w (0 : Transfer.VFType (M := M)) = 0 := Valuation.map_zero w
  have hc0 : c ≠ 0 := by
    intro hh
    have h' : w (0 : Transfer.VFType (M := M)) = 1 := hh ▸ h
    exact zero_ne_one (hzero.symm.trans h')
  have hz : c.1 ≠ Transfer.iVFZero := fun hh => hc0 (Subtype.ext hh)
  have hr0 : iRv c.1 ≠ iRVZero := VFValued.rv_ne_zero_of_ne_zero c.2 hz
  refine (RVCalc.units_iff_le_one hM (Transfer.rv_mem hM c.2) hr0).mpr ⟨?_, ?_⟩
  · exact (one_le_iff hw c).mpr (le_of_eq h)
  · exact (le_one_iff hw c).mpr (le_of_eq h.symm)

/-- `huniv` in the encoding's vocabulary: every term `b_i b ^ i` of the support is a unit. -/
theorem huniv_of_units (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)} (hb0 : b ≠ 0)
    (h : ∀ i ∈ F.support, iUnits (iRv ((F.coeff i * b ^ i)).1)) :
    ∀ i ∈ F.support, w (F.coeff i * b ^ i) = 1 := by
  intro i hi
  exact value_eq_one_of_units hw
    (mul_ne_zero (Polynomial.mem_support_iff.mp hi) (pow_ne_zero i hb0)) (h i hi)

/-! ## 3. Lemma 3.2 in the encoding's vocabulary -/

/-- **Lemma 3.2 (`rv:root:lift:vf`), encoding form, over a fixed valuation.**  `F` has a root in
the `rv`-class of `b`. -/
theorem rv_root_lift_encoding_valuation
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0)
    (hunit : ∀ i ∈ F.support, iUnits (iRv ((F.coeff i * b ^ i)).1))
    (hred : ¬ iLe (iRv (∑ i ∈ F.support, F.coeff i * b ^ i).1) iRVOne) :
    ∃ b' : Transfer.VFType (M := M), iRv b'.1 = iRv b.1 ∧ F.IsRoot b' := by
  have hbase : YinRV.rv w b ≠ YinRV.rvZero w := fun h => hb0 ((YinRV.rv_eq_none_iff (v := w)).mp h)
  have hred' : w (∑ i ∈ F.support, F.coeff i * b ^ i) < 1 :=
    (value_lt_one_iff hw _).mpr hred
  obtain ⟨b', hb', hroot⟩ :=
    M5AtModel.rv_root_lift_at_model (M := M) w hF hbase rfl
      (huniv_of_units hw hb0 hunit) hred'
  exact ⟨b', (RVDict.rv_class_iff hw b' b hb0).mpr hb', hroot⟩

/-- **Lemma 3.2 (`rv:root:lift:vf`) in `L_RV`.**  Everything in the statement is one of the
encoding's own primitives — `iRv`, `iLe`, `iRVOne`, `iUnits` — so this applies to the image of an
`RV`-polynomial under an `L_RV`-embedding.  The valuation is produced inside the proof. -/
theorem rv_root_lift_encoding
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0)
    (hunit : ∀ i ∈ F.support, iUnits (iRv ((F.coeff i * b ^ i)).1))
    (hred : ¬ iLe (iRv (∑ i ∈ F.support, F.coeff i * b ^ i).1) iRVOne) :
    ∃ b' : Transfer.VFType (M := M), iRv b'.1 = iRv b.1 ∧ F.IsRoot b' := by
  obtain ⟨Γ, hΓ, w, hw⟩ := VFValued.exists_valuation_predV (M := M) (hM := hM)
  letI : LinearOrderedCommGroupWithZero Γ := hΓ
  exact rv_root_lift_encoding_valuation (w := w) hw hF hb0 hunit hred

/-- **Lemma 3.2 in the paper's bookkeeping**, over a fixed valuation. -/
theorem rv_root_lift_encoding_I_valuation
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0) (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hunit : ∀ i ∈ I, iUnits (iRv ((F.coeff i * b ^ i)).1))
    (hsmall : ∀ i ∈ F.support, i ∉ I → ¬ iLe (iRv ((F.coeff i * b ^ i)).1) iRVOne)
    (hI : 2 ≤ I.card)
    (hred : ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne) :
    ∃ b' : Transfer.VFType (M := M), iRv b'.1 = iRv b.1 ∧ F.IsRoot b' := by
  letI : IsAlgClosed (Transfer.VFType (M := M)) :=
    VFAlgClosed.isAlgClosed_vfType (M := M) (hM := hM)
  have huniv : ∀ i ∈ I, w (F.coeff i * b ^ i) = 1 := by
    intro i hi
    exact value_eq_one_of_units hw
      (mul_ne_zero (Polynomial.mem_support_iff.mp (hIsub i hi)) (pow_ne_zero i hb0)) (hunit i hi)
  have hsmall' : ∀ i ∈ F.support, i ∉ I → w (F.coeff i * b ^ i) < 1 := by
    intro i hi hiI
    exact (value_lt_one_iff hw _).mpr (hsmall i hi hiI)
  have hred' : w (∑ i ∈ I, F.coeff i * b ^ i) < 1 :=
    (value_lt_one_iff hw _).mpr hred
  obtain ⟨b', hb', hroot⟩ := YinRV.rv_root_lift w hF hb0 I hIsub huniv hsmall' hI hred'
  exact ⟨b', (RVDict.rv_class_iff hw b' b hb0).mpr hb', hroot⟩

/-- **Lemma 3.2 in the paper's bookkeeping, in `L_RV`.**  Only the coefficients `i ∈ I` are
required to be units (those with `t_i ≠ 0`); the remaining coefficients of the support only have to
lie in the maximal ideal (the paper's `vrv(rv(b_i) t^i) > 0` for `t_i = 0`), and `2 ≤ I.card` says
the reduced polynomial is not a monomial.  This is the form `lift:all:root` (3.4) and
`lift:divisible:hull` (3.5) consume. -/
theorem rv_root_lift_encoding_I
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0) (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hunit : ∀ i ∈ I, iUnits (iRv ((F.coeff i * b ^ i)).1))
    (hsmall : ∀ i ∈ F.support, i ∉ I → ¬ iLe (iRv ((F.coeff i * b ^ i)).1) iRVOne)
    (hI : 2 ≤ I.card)
    (hred : ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne) :
    ∃ b' : Transfer.VFType (M := M), iRv b'.1 = iRv b.1 ∧ F.IsRoot b' := by
  obtain ⟨Γ, hΓ, w, hw⟩ := VFValued.exists_valuation_predV (M := M) (hM := hM)
  letI : LinearOrderedCommGroupWithZero Γ := hΓ
  exact rv_root_lift_encoding_I_valuation (w := w) hw hF hb0 I hIsub hunit hsmall hI hred

/-! ## 4. Where `hred` comes from: a vanishing residue sum

The paper applies Lemma 3.2 to the *reduction* `F̄` of `F`, so the hypothesis is
`F̄(t) = Σ_i t_i t^i = 0` in the residue field, where `t_i = rv(b_i)`.  `L_RV` has no addition on
`RV`; the residue-field sum is the encoding's `iKAdd`, which is defined on units.  The lemma below is
that translation step: two unit terms whose residue sum is `0` add up inside the maximal ideal, i.e.
`hred` holds.  (The general finite sum is the `Finset` fold of this, which additionally needs each
partial sum to be a unit.) -/

/-- `Axioms.kAddLink` is an axiom of the frozen `ACVF`. -/
theorem mem_ACVF_kAddLink : Axioms.kAddLink ∈ Axioms.ACVF :=
  Transfer.mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

/-- `¬ iLe iRVZero iRVOne`: `rv 0` is alone in its class, and `rv 1 ≠ rv 0`. -/
theorem not_le_zero_one : ¬ iLe (iRVZero (M := M)) iRVOne := by
  intro h
  exact RVCalc.rv_one_ne_zero hM (RVCalc.le_infty_eq hM (Transfer.rv_one_mem hM) h)

/-- **A vanishing residue sum is a sum in the maximal ideal.** -/
theorem hred_of_residue_sum_zero_valuation
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {u v : Transfer.VFType (M := M)} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : iUnits (iRv u.1)) (hv : iUnits (iRv v.1))
    (hsum : iKAdd (iRv u.1) (iRv v.1) = iRVZero) :
    ¬ iLe (iRv (u + v).1) iRVOne := by
  have hlink := Transfer.allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero)))))
    mem_ACVF_kAddLink ![u.1, v.1] (by intro i; fin_cases i <;> simp [u.2, v.2])
  have h2 : iUnits (iRv u.1) → iUnits (iRv v.1) →
      ((iUnits (iRv (iVFAdd u.1 v.1)) → iKAdd (iRv u.1) (iRv v.1) = iRv (iVFAdd u.1 v.1)) ∧
       (¬ iUnits (iRv (iVFAdd u.1 v.1)) → iKAdd (iRv u.1) (iRv v.1) = iRVZero)) := by
    simpa [BoundedFormula.realize_imp, BoundedFormula.realize_inf, Transfer.pUnits_realize,
      pEq, BoundedFormula.realize_bdEqual, Transfer.realize_tRv, TrivCase.realize_tKAdd,
      Transfer.realize_tVFAdd, Transfer.realize_tRVZero, RVCalc.realize_var_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hlink
  obtain ⟨hA, hB⟩ := h2 hu hv
  have hzeroMemo : w (0 : Transfer.VFType (M := M)) = 0 := Valuation.map_zero w
  by_cases hU : iUnits (iRv (iVFAdd u.1 v.1))
  · have hzero : iRv (iVFAdd u.1 v.1) = iRVZero := (hA hU).symm.trans hsum
    have hvz : iVFAdd u.1 v.1 = Transfer.iVFZero :=
      RVCalc.vf_eq_zero_of_rv_eq_zero hM (Transfer.vf_add_mem hM u.2 v.2) hzero
    have hsub : (u + v) = (0 : Transfer.VFType (M := M)) := Subtype.ext hvz
    have hw0 : w (u + v) = 0 := (congrArg w hsub).trans hzeroMemo
    exact (value_lt_one_iff hw _).mp (hw0 ▸ zero_lt_one)
  · by_cases hz : (u + v) = (0 : Transfer.VFType (M := M))
    · have hw0 : w (u + v) = 0 := (congrArg w hz).trans hzeroMemo
      exact (value_lt_one_iff hw _).mp (hw0 ▸ zero_lt_one)
    · have hne : iVFAdd u.1 v.1 ≠ Transfer.iVFZero := fun hh => hz (Subtype.ext hh)
      have hr0 : iRv (iVFAdd u.1 v.1) ≠ iRVZero :=
        VFValued.rv_ne_zero_of_ne_zero (Transfer.vf_add_mem hM u.2 v.2) hne
      have huw : w u = 1 := value_eq_one_of_units hw hu0 hu
      have hvw : w v = 1 := value_eq_one_of_units hw hv0 hv
      have hle : w (u + v) ≤ 1 := by
        rcases RVCalc.rv_ultrametric hM u.2 v.2 with h' | h'
        · exact huw ▸ ((hw (u + v) u).mp h')
        · exact hvw ▸ ((hw (u + v) v).mp h')
      intro hcon
      exact hU ((RVCalc.units_iff_le_one hM
        (Transfer.rv_mem hM (Transfer.vf_add_mem hM u.2 v.2)) hr0).mpr
        ⟨(one_le_iff hw (u + v)).mpr hle, hcon⟩)

/-- **A vanishing residue sum is a sum in the maximal ideal**, in `L_RV`. -/
theorem hred_of_residue_sum_zero
    {u v : Transfer.VFType (M := M)} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : iUnits (iRv u.1)) (hv : iUnits (iRv v.1))
    (hsum : iKAdd (iRv u.1) (iRv v.1) = iRVZero) :
    ¬ iLe (iRv (u + v).1) iRVOne := by
  obtain ⟨Γ, hΓ, w, hw⟩ := VFValued.exists_valuation_predV (M := M) (hM := hM)
  letI : LinearOrderedCommGroupWithZero Γ := hΓ
  exact hred_of_residue_sum_zero_valuation (w := w) hw hu0 hv0 hu hv hsum

/-- The same as a value inequality, the form in which the paper states it (`vrv(Σ) > 0`). -/
theorem value_lt_one_of_residue_sum_zero
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {u v : Transfer.VFType (M := M)} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : iUnits (iRv u.1)) (hv : iUnits (iRv v.1))
    (hsum : iKAdd (iRv u.1) (iRv v.1) = iRVZero) :
    w (u + v) < 1 :=
  (value_lt_one_iff hw _).mpr (hred_of_residue_sum_zero_valuation hw hu0 hv0 hu hv hsum)


/-! ## 5. Lemma 3.2 with hypotheses on the *coefficients* only

In `lift:all:root` (3.4) and `lift:divisible:hull` (3.5) Lemma 3.2 is applied to a polynomial
`F` whose reduction `F̄` is given; the data available is about the coefficients, not about the terms
`b_i b ^ i`:

* every coefficient `a_i` of `F` is **integral** (`a_i ∈ O`), which is the hypothesis
  `F ∈ O(Ŝ)[X]`;
* `b` is a **unit** (`b ∈ O^×`, from `e ∈ U(M)`);
* `I` is exactly the set of indices at which the reduced coefficient does not vanish, i.e.
  `i ∈ I ↔ rv(a_i) ∈ K^×` (`t_i = rv(b_i)` whenever `t_i ≠ 0`);
* `F̄` is not a monomial (`2 ≤ I.card`) and `F̄(t) = 0` (`hred`).

The two lemmas below derive `hunit` and `hsmall` from that data, and
`rv_root_lift_encoding_reduction` is Lemma 3.2 with those coefficient hypotheses.  This is the
form a port of Lemmas 3.4/3.5 consumes: the `RV`-polynomial hypothesis is read once, here, and the
saturation/embedding arguments never see `w`. -/

/-- **Unit coefficients give unit terms.**  If `b` is a unit and every `a_i` (`i ∈ I`) is a unit,
then every `a_i b ^ i` (`i ∈ I`) is a unit. -/
theorem huniv_of_coeff_units
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)} (hb0 : b ≠ 0)
    (hb : iUnits (iRv b.1)) {I : Finset ℕ} (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hIc : ∀ i ∈ I, iUnits (iRv (F.coeff i).1)) :
    ∀ i ∈ I, iUnits (iRv ((F.coeff i * b ^ i)).1) := by
  intro i hi
  have hbw : w b = 1 := value_eq_one_of_units hw hb0 hb
  have hcw : w (F.coeff i) = 1 :=
    value_eq_one_of_units hw (Polynomial.mem_support_iff.mp (hIsub i hi)) (hIc i hi)
  have h2 : w (b ^ i) = w b ^ i := Valuation.map_pow w b i
  have hval : w (F.coeff i * b ^ i) = 1 := by
    refine (((Valuation.map_mul w _ _).trans (congrArg (fun t : Γ => w (F.coeff i) * t) h2)).trans ?_)
    rw [hcw, hbw, one_pow, mul_one]
  exact units_of_value_eq_one hw hval

/-- **Non-unit coefficients give terms in the maximal ideal.**  If `b` is a unit, every coefficient
of `F` is integral, and `a_i` (`i ∉ I`) is *not* a unit, then `a_i b ^ i` lies in the maximal
ideal — the paper's `vrv(rv(b_i) t^i) > 0` for `t_i = 0`. -/
theorem hsmall_of_coeff_not_units
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)} (hb0 : b ≠ 0)
    (hb : iUnits (iRv b.1)) {I : Finset ℕ}
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (hInot : ∀ i ∈ F.support, i ∉ I → ¬ iUnits (iRv (F.coeff i).1)) :
    ∀ i ∈ F.support, i ∉ I → ¬ iLe (iRv ((F.coeff i * b ^ i)).1) iRVOne := by
  intro i hi hiI
  have hbw : w b = 1 := value_eq_one_of_units hw hb0 hb
  have hle : w (F.coeff i) ≤ 1 := (one_le_iff hw (F.coeff i)).mp (hint i hi)
  have hne : w (F.coeff i) ≠ 1 := fun h => hInot i hi hiI (units_of_value_eq_one hw h)
  have hlt : w (F.coeff i) < 1 := lt_of_le_of_ne hle hne
  have h2 : w (b ^ i) = w b ^ i := Valuation.map_pow w b i
  have hval : w (F.coeff i * b ^ i) = w (F.coeff i) := by
    refine ((Valuation.map_mul w _ _).trans (congrArg (fun t : Γ => w (F.coeff i) * t) h2)).trans ?_
    rw [hbw, one_pow, mul_one]
  exact (value_lt_one_iff hw (F.coeff i * b ^ i)).mp (hval.symm ▸ hlt)

/-- **Lemma 3.2 (`rv:root:lift:vf`) with the paper's coefficient hypotheses**, in `L_RV`.  `I` is
the support of the reduction `F̄` (the indices at which the coefficient is a unit), `F̄` is not a
monomial, every coefficient is integral, `b` is a unit, and the reduction vanishes at `t = rv b`. -/
theorem rv_root_lift_encoding_reduction
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0) (hb : iUnits (iRv b.1)) (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hIc : ∀ i ∈ I, iUnits (iRv (F.coeff i).1))
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (hInot : ∀ i ∈ F.support, i ∉ I → ¬ iUnits (iRv (F.coeff i).1))
    (hI : 2 ≤ I.card)
    (hred : ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne) :
    ∃ b' : Transfer.VFType (M := M), iRv b'.1 = iRv b.1 ∧ F.IsRoot b' :=
  rv_root_lift_encoding_I_valuation (w := w) hw hF hb0 I hIsub
    (huniv_of_coeff_units hw hb0 hb hIsub hIc)
    (hsmall_of_coeff_not_units hw hb0 hb hint hInot) hI hred

/-- **Lemma 3.2 with the paper's coefficient hypotheses, in `L_RV`** — no valuation in the
statement. -/
theorem rv_root_lift_encoding_reduction_LRV
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0) (hb : iUnits (iRv b.1)) (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hIc : ∀ i ∈ I, iUnits (iRv (F.coeff i).1))
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (hInot : ∀ i ∈ F.support, i ∉ I → ¬ iUnits (iRv (F.coeff i).1))
    (hI : 2 ≤ I.card)
    (hred : ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne) :
    ∃ b' : Transfer.VFType (M := M), iRv b'.1 = iRv b.1 ∧ F.IsRoot b' := by
  obtain ⟨Γ, hΓ, w, hw⟩ := VFValued.exists_valuation_predV (M := M) (hM := hM)
  letI : LinearOrderedCommGroupWithZero Γ := hΓ
  exact rv_root_lift_encoding_reduction (w := w) hw hF hb0 hb I hIsub hIc hint hInot hI hred


/-! ## 6. The valuation ring `O` and its maximal ideal `M`, in `L_RV`

`O = {c : v c ≤ 1}` and `M = {c : v c < 1}` are `iLe`-definable: `c ∈ O` is
`iLe iRVOne (iRv c)` and `c ∈ M` is `¬ iLe (iRv c) iRVOne`.  Every port of Lemmas 3.4/3.5/3.7
manipulates these two sets (`F ∈ O(Ŝ)[X]`, `e ∈ O^×`, `e^n ∈ M`, …), so the closure laws are
collected here in the encoding's vocabulary.  The proofs go through `w` because that is where the
content is (the ultrametric inequality and multiplicativity), and come back out by `one_le_iff` /
`value_lt_one_iff`; no `w` appears in the statements. -/

/-- **`O` is closed under addition** (the ultrametric inequality `rv_ultrametric`). -/
theorem one_le_add (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a b : Transfer.VFType (M := M)}
    (ha : iLe iRVOne (iRv a.1)) (hb : iLe iRVOne (iRv b.1)) :
    iLe iRVOne (iRv (a + b).1) := by
  refine (one_le_iff hw (a + b)).mpr ?_
  exact (Valuation.map_add w a b).trans (max_le ((one_le_iff hw a).mp ha) ((one_le_iff hw b).mp hb))

/-- **`M` is closed under addition.** -/
theorem lt_one_add (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a b : Transfer.VFType (M := M)}
    (ha : ¬ iLe (iRv a.1) iRVOne) (hb : ¬ iLe (iRv b.1) iRVOne) :
    ¬ iLe (iRv (a + b).1) iRVOne := by
  refine (value_lt_one_iff hw (a + b)).mp ?_
  exact lt_of_le_of_lt (Valuation.map_add w a b)
    (max_lt ((value_lt_one_iff hw a).mpr ha) ((value_lt_one_iff hw b).mpr hb))

/-- **`O` is closed under multiplication.** -/
theorem one_le_mul (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a b : Transfer.VFType (M := M)}
    (ha : iLe iRVOne (iRv a.1)) (hb : iLe iRVOne (iRv b.1)) :
    iLe iRVOne (iRv (a * b).1) := by
  refine (one_le_iff hw (a * b)).mpr ?_
  calc w (a * b) = w a * w b := Valuation.map_mul w a b
    _ ≤ 1 * 1 := mul_le_mul' ((one_le_iff hw a).mp ha) ((one_le_iff hw b).mp hb)
    _ = 1 := one_mul 1

/-- **`M · O ⊆ M`** — the maximal ideal is an ideal. -/
theorem lt_one_mul (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a b : Transfer.VFType (M := M)}
    (ha : ¬ iLe (iRv a.1) iRVOne) (hb : iLe iRVOne (iRv b.1)) :
    ¬ iLe (iRv (a * b).1) iRVOne := by
  refine (value_lt_one_iff hw (a * b)).mp ?_
  have hle : w a * w b ≤ w a :=
    (mul_le_mul' (le_refl (w a)) ((one_le_iff hw b).mp hb)).trans (le_of_eq (mul_one (w a)))
  exact lt_of_le_of_lt ((Valuation.map_mul w a b).le.trans hle) ((value_lt_one_iff hw a).mpr ha)

/-- `O` is closed under negation. -/
theorem one_le_neg (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a : Transfer.VFType (M := M)} (ha : iLe iRVOne (iRv a.1)) :
    iLe iRVOne (iRv (-a).1) := by
  refine (one_le_iff hw (-a)).mpr ?_
  exact (Valuation.map_neg w a).le.trans ((one_le_iff hw a).mp ha)

/-- `M` is closed under negation. -/
theorem lt_one_neg (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a : Transfer.VFType (M := M)} (ha : ¬ iLe (iRv a.1) iRVOne) :
    ¬ iLe (iRv (-a).1) iRVOne := by
  refine (value_lt_one_iff hw (-a)).mp ?_
  exact (Valuation.map_neg w a).symm ▸ ((value_lt_one_iff hw a).mpr ha)

/-! ### Finite sums

The paper constantly sums a finite family whose terms are all integral (a polynomial with
coefficients in `O` evaluated at an integral element) or all in `M`.  `iLe` is only meaningful on
nonzero elements, so the empty sum is handled by `le_top_rv` (`iLe iRVOne iRVZero` does hold) and
`not_le_zero_one` (`iRVZero` is not `≥ 1`). -/

/-- A finite sum of elements of `O` lies in `O`. -/
theorem one_le_sum (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {ι : Type*} (s : Finset ι) (f : ι → Transfer.VFType (M := M))
    (h : ∀ i ∈ s, iLe iRVOne (iRv (f i).1)) :
    iLe iRVOne (iRv (∑ i ∈ s, f i).1) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have e : (∑ i ∈ (∅ : Finset ι), f i) = (0 : Transfer.VFType (M := M)) := Finset.sum_empty
      have hz : iRv ((∑ i ∈ (∅ : Finset ι), f i)).1 = iRVZero :=
        (congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) e).trans (RVCalc.rv_zero_eq hM)
      exact hz.symm ▸ (RVCalc.le_top_rv hM (Transfer.rv_one_mem hM))
  | insert a s ha ih =>
      have hsum : (∑ i ∈ insert a s, f i) = f a + ∑ i ∈ s, f i := Finset.sum_insert ha
      have ha' : iLe iRVOne (iRv (f a).1) := h a (Finset.mem_insert_self a s)
      have hs' : iLe iRVOne (iRv (∑ i ∈ s, f i).1) :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hz : iRv ((∑ i ∈ insert a s, f i)).1 = iRv ((f a + ∑ i ∈ s, f i)).1 :=
        congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) hsum
      exact hz.symm ▸ (one_le_add hw ha' hs')

/-- A finite sum of elements of the maximal ideal lies in the maximal ideal. -/
theorem lt_one_sum (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {ι : Type*} (s : Finset ι) (f : ι → Transfer.VFType (M := M))
    (h : ∀ i ∈ s, ¬ iLe (iRv (f i).1) iRVOne) :
    ¬ iLe (iRv (∑ i ∈ s, f i).1) iRVOne := by
  classical
  induction s using Finset.induction with
  | empty =>
      have e : (∑ i ∈ (∅ : Finset ι), f i) = (0 : Transfer.VFType (M := M)) := Finset.sum_empty
      have hz : iRv ((∑ i ∈ (∅ : Finset ι), f i)).1 = iRVZero :=
        (congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) e).trans (RVCalc.rv_zero_eq hM)
      exact hz.symm ▸ not_le_zero_one
  | insert a s ha ih =>
      have hsum : (∑ i ∈ insert a s, f i) = f a + ∑ i ∈ s, f i := Finset.sum_insert ha
      have ha' : ¬ iLe (iRv (f a).1) iRVOne := h a (Finset.mem_insert_self a s)
      have hs' : ¬ iLe (iRv (∑ i ∈ s, f i).1) iRVOne :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hz : iRv ((∑ i ∈ insert a s, f i)).1 = iRv ((f a + ∑ i ∈ s, f i)).1 :=
        congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) hsum
      exact hz.symm ▸ (lt_one_add hw ha' hs')

/-- **A unit plus a sum of elements of `M` is a unit** — the standard "the term of least value
dominates": if `f i₀` is a unit and every other term of the finite sum lies in the maximal ideal,
then the whole sum has the value of `f i₀`, hence is a unit.  This is the step that reads
`e ∈ O^×` off a `Ŝ`-expansion of `e` whose non-leading terms are all in `M`. -/
theorem le_one_and_one_le_sum (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {ι : Type*} (s : Finset ι) (f : ι → Transfer.VFType (M := M)) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (hunit : iLe iRVOne (iRv (f i₀).1) ∧ iLe (iRv (f i₀).1) iRVOne)
    (hsmall : ∀ i ∈ s, i ≠ i₀ → ¬ iLe (iRv (f i).1) iRVOne) :
    iLe iRVOne (iRv (∑ i ∈ s, f i).1) ∧ iLe (iRv (∑ i ∈ s, f i).1) iRVOne := by
  classical
  have hw0 : w (f i₀) = 1 :=
    le_antisymm ((one_le_iff hw _).mp hunit.1) ((le_one_iff hw _).mp hunit.2)
  have hO : iLe iRVOne (iRv (∑ i ∈ s, f i).1) := by
    refine one_le_sum hw s f (fun i hi => ?_)
    by_cases h : i = i₀
    · subst h; exact hunit.1
    · exact (one_le_iff hw _).mpr ((value_lt_one_iff hw _).mpr (hsmall i hi h)).le
  refine ⟨hO, ?_⟩
  have hrest : w (∑ i ∈ s.erase i₀, f i) < 1 :=
    (value_lt_one_iff hw _).mpr (lt_one_sum hw (s.erase i₀) f
      (fun i hi => hsmall i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)))
  have hlt : w (∑ i ∈ s.erase i₀, f i) < w (f i₀) := by rw [hw0]; exact hrest
  have e : (∑ i ∈ s, f i) = (∑ i ∈ s.erase i₀, f i) + f i₀ :=
    (Finset.sum_erase_add s f hi₀).symm
  have hval : w (∑ i ∈ s, f i) = 1 :=
    ((congrArg w e).trans
      ((Valuation.map_add_eq_of_lt_right (v := w) hlt).trans hw0))
  exact (le_one_iff hw _).mpr (le_of_eq hval.symm)

/-! ### `Kˣ` is closed under multiplication, powers and negation -/

/-- `Kˣ` is closed under negation. -/
theorem units_neg (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a : Transfer.VFType (M := M)} (ha0 : a ≠ 0) (h : iUnits (iRv a.1)) :
    iUnits (iRv (-a).1) := by
  have haw : w a = 1 := value_eq_one_of_units hw ha0 h
  exact units_of_value_eq_one hw ((Valuation.map_neg w a).trans haw)

/-- `Kˣ` is closed under multiplication. -/
theorem units_mul (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a b : Transfer.VFType (M := M)} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : iUnits (iRv a.1)) (hb : iUnits (iRv b.1)) : iUnits (iRv (a * b).1) := by
  have haw : w a = 1 := value_eq_one_of_units hw ha0 ha
  have hbw : w b = 1 := value_eq_one_of_units hw hb0 hb
  refine units_of_value_eq_one hw ?_
  calc w (a * b) = w a * w b := Valuation.map_mul w a b
    _ = 1 := by rw [haw, hbw, mul_one]

/-- `Kˣ` is closed under powers. -/
theorem units_pow (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a : Transfer.VFType (M := M)} (ha0 : a ≠ 0) (h : iUnits (iRv a.1)) (n : ℕ) :
    iUnits (iRv (a ^ n).1) := by
  have haw : w a = 1 := value_eq_one_of_units hw ha0 h
  refine units_of_value_eq_one hw ?_
  calc w (a ^ n) = w a ^ n := Valuation.map_pow w a n
    _ = 1 := by rw [haw, one_pow]

end SpecialTransformations.Milestone0.M6Syntactic

#print axioms SpecialTransformations.Milestone0.M6Syntactic.rv_root_lift_encoding
#print axioms SpecialTransformations.Milestone0.M6Syntactic.rv_root_lift_encoding_I
#print axioms SpecialTransformations.Milestone0.M6Syntactic.hred_of_residue_sum_zero
#print axioms SpecialTransformations.Milestone0.M6Syntactic.rv_root_lift_encoding_reduction_LRV
#print axioms SpecialTransformations.Milestone0.M6Syntactic.lt_one_mul
