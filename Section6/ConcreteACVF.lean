import Section6.ConcreteRVAxioms
import Section6.ConcreteCharacteristic
import VFAlgClosed
import JohnsonGeometry

/-! Realization of the ACVF axioms by the ordinary algebraically closed
valued field used as an algebraic envelope. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Polynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer TrivCase RVElim
open SpecialTransformations.Section6.ConcreteRV

namespace SpecialTransformations.Section6.ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)
local instance closedStructure : LRV.Structure (Carrier v) := nativeStructure v

private theorem monic_root {R : Type} [Field R] [IsAlgClosed R] {m : ℕ}
    (c : Fin (m + 1) → R) :
    ∃ x : R, x ^ (m + 1) + (HenselianTheory.coefficientPolynomial c).eval x = 0 := by
  let f : R[X] := X ^ (m + 1) + HenselianTheory.coefficientPolynomial c
  have hcoeff : f.coeff (m + 1) = 1 := by
    simp only [f, coeff_add, coeff_X_pow, if_pos rfl, HenselianTheory.coefficientPolynomial, finsetSum_coeff]
    rw [Finset.sum_eq_zero]
    · exact add_zero _
    · intro i _
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
  have hf : f.degree ≠ 0 := by
    intro he
    have hle := le_degree_of_ne_zero (p := f) (show f.coeff (m + 1) ≠ 0 by rw [hcoeff]; exact one_ne_zero)
    rw [he] at hle
    exact Nat.not_succ_le_zero m (by exact_mod_cast hle)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root f hf
  exact ⟨x, by simpa [IsRoot, f] using hx⟩

private theorem horner_realize {R : Type} [CommRing R] {m : ℕ}
    (pack : R → Carrier v) (add mul : {n : ℕ} → Tm n → Tm n → Tm n)
    (ha : ∀ {n : ℕ} (t u : Tm n) (z : Empty ⊕ Fin n → Carrier v) (r s : R),
      t.realize z = pack r → u.realize z = pack s →
      (add t u).realize z = pack (r + s))
    (hm : ∀ {n : ℕ} (t u : Tm n) (z : Empty ⊕ Fin n → Carrier v) (r s : R),
      t.realize z = pack r → u.realize z = pack s →
      (mul t u).realize z = pack (r * s))
    (c : Fin (m + 1) → R) (x : R) (e : Empty → Carrier v) :
    (hornerPoly (k := m + 1) add mul).realize
        (Sum.elim e (Fin.snoc (pack ∘ c) (pack x))) =
      pack (x ^ (m + 1) + (HenselianTheory.coefficientPolynomial c).eval x) := by
  let z := Sum.elim e (Fin.snoc (pack ∘ c) (pack x))
  let X : Tm (m + 1 + 1) := tv (m + 1) (by omega)
  let A (i : Fin (m + 1)) : Tm (m + 1 + 1) := tv i.val (by omega)
  have hx : X.realize z = pack x := by
    exact VFAlgClosed.snoc_last_apply (pack ∘ c) (pack x)
  have hc (i : Fin (m + 1)) : (A i).realize z = pack (c i) := by
    change Fin.snoc (α := fun _ : Fin (m + 2) => Carrier v) (pack ∘ c) (pack x) i.castSucc = pack (c i)
    exact Fin.snoc_castSucc (α := fun _ : Fin (m + 2) => Carrier v) (pack x) (pack ∘ c) i
  have hfold (l : List (Fin m)) (t : Tm (m + 1 + 1)) (r : R) (ht : t.realize z = pack r) :
      (l.foldl (fun acc i => add (mul acc X) (A i.castSucc)) t).realize z =
        pack (l.foldl (fun acc i => acc * x + c i.castSucc) r) := by
    induction l generalizing t r with
    | nil => exact ht
    | cons i l ih =>
      exact ih _ _ (ha _ _ _ _ _ (hm _ _ _ _ _ ht hx) (hc i.castSucc))
  change ((List.finRange m).reverse.foldl (fun acc i => add (mul acc X) (A i.castSucc))
    (add X (A (Fin.last m)))).realize z = _
  rw [hfold _ _ _ (ha _ _ _ _ _ hx (hc (Fin.last m)))]
  let d (i : ℕ) := if h : i < m + 1 then c ⟨i, h⟩ else 0
  have h := VFAlgClosed.horner_fold_eq d x m
  have hd (i : Fin (m + 1)) : d i.val = c i := dif_pos i.isLt
  have hfoldStep (acc : R) (i : Fin m) : acc * x + d i.val = acc * x + c i.castSucc := by
    rw [← hd i.castSucc]
    rfl
  rw [HenselianTheory.coefficientPolynomial_eval]
  have hlast : d m = c (Fin.last m) := dif_pos (by omega)
  simpa only [hfoldStep, hlast, hd] using congrArg pack h

private theorem model_vfAlgClosed [IsAlgClosed K] : Carrier v ⊨ Axioms.vfAlgClosed := by
  constructor
  rintro σ ⟨k, hk, rfl⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Axioms.acfScheme, allVF v _ (fun _ => rfl)]
  intro c
  rw [exVF v]
  obtain ⟨x, hx⟩ := monic_root c
  refine ⟨x, ?_⟩
  rw [pEq, BoundedFormula.realize_bdEqual, realize_tVFZero, vfZero_eq]
  change (hornerPoly (k := m + 1) tVFAdd tVFMul).realize
    (Sum.elim _ (Fin.snoc (Sum.inl ∘ c) (.inl x))) = Sum.inl 0
  rw [horner_realize v Sum.inl tVFAdd tVFMul
    (fun t u z r s ht hu => by rw [realize_tVFAdd, ht, hu, vfAdd_eq])
    (fun t u z r s ht hu => by rw [realize_tVFMul, ht, hu, vfMul_eq]) c x _, hx]

private theorem model_kAlgClosed [IsAlgClosed (ConcreteRV.Residue v)] :
    Carrier v ⊨ Axioms.kAlgClosed := by
  constructor
  rintro σ ⟨k, hk, rfl⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Axioms.acfSchemeK, allResidue v _ (fun _ => rfl)]
  intro c
  rw [exResidue v]
  obtain ⟨x, hx⟩ := monic_root c
  refine ⟨x, ?_⟩
  rw [pEq, BoundedFormula.realize_bdEqual, realize_tRVZero, rvZero_eq]
  change (hornerPoly (k := m + 1) tKAdd tRVMul).realize
    (Sum.elim _ (Fin.snoc ((fun r => Sum.inr (residueCode v r)) ∘ c) (.inr (residueCode v x)))) =
    Sum.inr none
  rw [horner_realize v (fun r => Sum.inr (residueCode v r)) tKAdd tRVMul
    (fun t u z r s ht hu => by rw [realize_tKAdd, ht, hu, kAdd_eq, addResidue_code])
    (fun t u z r s ht hu => by rw [realize_tRVMul, ht, hu, rvMul_eq, ← residueCode_mul]) c x _,
    hx, residueCode_zero]

private theorem rvPower_realize {n : ℕ} (t : Tm n) (z : Empty ⊕ Fin n → Carrier v)
    (r : ConcreteRV.Residue v) (hr : t.realize z = .inr (residueCode v r)) (k : ℕ) :
    (tRVPow t k).realize z = .inr (residueCode v (r ^ k)) := by
  induction k with
  | zero => rw [tRVPow, realize_tRVOne_T, rvOne_eq, pow_zero, residueCode_one]
  | succ k ih => rw [tRVPow, realize_tRVMul, ih, hr, rvMul_eq, ← residueCode_mul, pow_succ]

private theorem rvDivisible_realize [IsAlgClosed (ConcreteRV.Residue v)] {k : ℕ}
    (hk : 1 ≤ k) : Carrier v ⊨ Axioms.rvDivisible k := by
  rw [Axioms.rvDivisible, allRV v _ (fun i => by fin_cases i; rfl)]
  intro z
  simp only [BoundedFormula.realize_imp, pUnits_realize, RVCalc.realize_var_inr, units_inr]
  intro hz
  obtain ⟨r, hr⟩ := show z 0 ∈ Set.range (residueCode v) by
    rw [residueCode_range]
    exact Or.inr hz
  have hr0 : r ≠ 0 := by
    intro he
    rw [← hr, he, residueCode_zero, RVCalc.vrv_none] at hz
    exact zero_ne_one hz
  have hk0 : k ≠ 0 := by omega
  let f : (ConcreteRV.Residue v)[X] := X ^ k - C r
  have hdeg : f.degree ≠ 0 := by
    rw [show f.degree = (k : WithBot ℕ) by
      exact degree_X_pow_sub_C (by omega) r]
    exact_mod_cast hk0
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root f hdeg
  have hsr : s ^ k = r := by
    change f.eval s = 0 at hs
    exact sub_eq_zero.mp (by simpa [f] using hs)
  have hs0 : s ≠ 0 := by
    intro he
    apply hr0
    rw [← hsr, he, zero_pow hk0]
  rw [exRV v]
  refine ⟨residueCode v s, ?_⟩
  let zs : Fin 2 → Carrier v := Fin.snoc (fun i => Sum.inr (z i)) (Sum.inr (residueCode v s))
  let e : Empty → Carrier v := @default _ Unique.instInhabited
  have hlast : (&1 : Tm 2).realize (Sum.elim e zs) = Sum.inr (residueCode v s) := by
    rw [RVCalc.realize_var_inr]
    change zs (Fin.last 1) = _
    exact Fin.snoc_last (α := fun _ : Fin 2 => Carrier v) _ _
  have hfirst : (&0 : Tm 2).realize (Sum.elim e zs) = Sum.inr (z 0) := by
    rw [RVCalc.realize_var_inr]
    exact Fin.snoc_castSucc (α := fun _ : Fin 2 => Carrier v) _ _ (0 : Fin 1)
  simp only [BoundedFormula.realize_inf, pUnits_realize, pEq, BoundedFormula.realize_bdEqual]
  change iUnits ((&1 : Tm 2).realize (Sum.elim e zs)) ∧
    (tRVPow &1 k).realize (Sum.elim e zs) = (&0 : Tm 2).realize (Sum.elim e zs)
  rw [rvPower_realize v _ _ s hlast, hsr, hr, hfirst, hlast, units_inr]
  exact ⟨value_residueCode v hs0, rfl⟩

theorem model_ACVF00 [IsAlgClosed K] [CharZero K] [CharZero (ConcreteRV.Residue v)]
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) : Carrier v ⊨ Axioms.ACVF00 := by
  letI : IsAlgClosed (ConcreteRV.Residue v) := ValOneEC.Johnson.isAlgClosed_residueField v
  have h := model_valuedField v hnt
  constructor
  intro σ hσ
  rcases hσ with ((hσ | ⟨k, rfl⟩) | ⟨p, hp, rfl⟩)
  · rcases hσ with (hs | (((((((hv | hvac) | (hg | ⟨k, hk, rfl⟩)) | hres) |
        hac) | hle) | hrv) | hrepair) | hrepair)
    · exact sentence_realize h (by simp [HenselianTheory.valuedField, hs])
    · exact sentence_realize h (by simp [HenselianTheory.valuedField, hv])
    · exact sentence_realize (model_vfAlgClosed v) hvac
    · exact sentence_realize h (by simp [HenselianTheory.valuedField, HenselianTheory.rvGroupBase, hg])
    · exact rvDivisible_realize v hk
    · exact sentence_realize h (by simp [HenselianTheory.valuedField, hres])
    · exact sentence_realize (model_kAlgClosed v) hac
    · exact sentence_realize h (by simp [HenselianTheory.valuedField, hle])
    · exact sentence_realize h (by simp [HenselianTheory.valuedField, hrv])
    · exact sentence_realize h (by simp [HenselianTheory.valuedField, hrepair])
    · exact sentence_realize h (by simp [HenselianTheory.valuedField, hrepair])
  · exact charZeroVF_realize v k
  · exact residueCharZero_realize v hp

end SpecialTransformations.Section6.ConcreteValued
