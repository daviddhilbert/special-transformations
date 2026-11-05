import VFValued
import RVClassEquality
import ResidueTranscendentalTransport

set_option backward.isDefEq.respectTransparency false

/-! Identification of the frozen RV sort with the actual leading-term quotient.
The valuation has the reversed order specified by `VFValued.predV`.
The only inputs are the frozen ACVF axioms and a valuation realizing that predicate.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace CanonicalRV

noncomputable def equivOfSameFibers {A B C : Type*} (f : A → B) (g : A → C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a b, f a = f b ↔ g a = g b) : B ≃ C where
  toFun b := g (Classical.choose (hf b))
  invFun c := f (Classical.choose (hg c))
  left_inv b := by
    have he := Classical.choose_spec (hg (g (Classical.choose (hf b))))
    exact ((h _ _).mpr he).trans (Classical.choose_spec (hf b))
  right_inv c := by
    have he := Classical.choose_spec (hf (f (Classical.choose (hg c))))
    exact ((h _ _).mp he).trans (Classical.choose_spec (hg c))

theorem equivOfSameFibers_apply {A B C : Type*} (f : A → B) (g : A → C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    equivOfSameFibers f g hf hg h (f a) = g a :=
  (h _ _).mp (Classical.choose_spec (hf (f a)))

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev RVSort (M : Type) [LRV.Structure M] := {x : M // iRV x}

def encodedRv (a : VFType (M := M)) : RVSort M := ⟨iRv a.1, rv_mem hM a.2⟩

theorem encodedRv_zero_iff (a : VFType (M := M)) :
    iRv a.1 = iRVZero ↔ a = 0 := by
  constructor
  · exact fun h => Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM a.2 h)
  · rintro rfl
    exact RVCalc.rv_zero_eq hM

/-- The rvEqLink axiom, with both directions retained. -/
theorem encoded_eq_iff_close {x y : M} (hx : iVF x) (hy : iVF y)
    (hy0 : y ≠ iVFZero) :
    iRv x = iRv y ↔ ¬ iLe (iRv (iVFAdd x (iVFNeg y))) (iRv y) := by
  have h' := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (∼(pEq &1 tVFZero) ⟹ (pEq (tRv &0) (tRv &1) ⇔
      ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1)))))
    RVCalc.mem_ACVF_rvEqLink ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  have h3 : y ≠ iVFZero → (iRv x = iRv y ↔
      ¬ (pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1)).Realize default ![x, y]) := by
    simpa [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_not,
      BoundedFormula.realize_iff, realize_tVFZero, realize_tRv,
      RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using h'
  have hh := h3 hy0
  rw [realize_pLe] at hh
  simpa [realize_tRv, realize_tVFAdd, realize_tVFNeg, RVCalc.realize_var_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hh

theorem encodedRv_surjective : Function.Surjective (encodedRv (M := M)) := by
  rintro ⟨y, hy⟩
  by_cases hy0 : y = iRVZero
  · exact ⟨0, Subtype.ext ((RVCalc.rv_zero_eq hM).trans hy0.symm)⟩
  have hmem : Axioms.rvSurj ∈ Axioms.ACVF :=
    RVCalc.mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))) hmem ![y]
    (by intro i; fin_cases i; simpa using hy)
  simp only [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, exSorted, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, sortPred, realize_tRVZero, realize_tRv, pVF_realize,
    realize_tv] at h
  obtain ⟨x, hx, he⟩ := h hy0
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem rv_surjective {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ) : Function.Surjective (_root_.RVCalc.rv v) := by
  intro t
  cases t with
  | none => exact ⟨0, _root_.RVCalc.rv_zero⟩
  | some t =>
      obtain ⟨x, _, hx⟩ := _root_.RVCalc.rv_surjective v t
      exact ⟨x, hx⟩

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

include hv

theorem same_fibers (a b : VFType (M := M)) :
    _root_.RVCalc.rv v a = _root_.RVCalc.rv v b ↔ encodedRv a = encodedRv b := by
  rw [Subtype.ext_iff]
  change _ ↔ iRv a.1 = iRv b.1
  by_cases ha : a = 0
  · subst a
    rw [_root_.RVCalc.rv_zero,
      show iRv (0 : VFType (M := M)).1 = iRVZero from RVCalc.rv_zero_eq hM]
    simpa only [eq_comm] using
      ((_root_.RVCalc.rv_eq_none_iff (v := v) (x := b)).trans (encodedRv_zero_iff b).symm)
  by_cases hb : b = 0
  · subst b
    rw [_root_.RVCalc.rv_zero,
      show iRv (0 : VFType (M := M)).1 = iRVZero from RVCalc.rv_zero_eq hM]
    exact (_root_.RVCalc.rv_eq_none_iff (v := v)).trans (encodedRv_zero_iff a).symm
  have hsource : _root_.RVCalc.rv v a = _root_.RVCalc.rv v b ↔ v (a - b) < v b := by
    rw [eq_comm, _root_.RVCalc.rv_eq_iff hb ha, ← neg_sub a b, Valuation.map_neg]
  rw [hsource, encoded_eq_iff_close a.2 b.2 (fun he => hb (Subtype.ext he))]
  change v (a - b) < v b ↔ ¬ VFValued.predV b (a - b)
  rw [hv, not_le]

/-- Actual equivalence, including the absorbing element, between the canonical
quotient RV and the RV sort of the frozen model. -/
noncomputable def equiv : _root_.RVCalc.RV v ≃ RVSort M :=
  equivOfSameFibers (_root_.RVCalc.rv v) encodedRv (rv_surjective v)
    encodedRv_surjective (same_fibers v hv)

@[simp] theorem equiv_rv (a : VFType (M := M)) :
    equiv v hv (_root_.RVCalc.rv v a) = encodedRv a :=
  equivOfSameFibers_apply _ _ _ _ _ a

theorem equiv_mul (a b : _root_.RVCalc.RV v) :
    (equiv v hv (_root_.RVCalc.rvMul v a b)).1 =
      iRVMul (equiv v hv a).1 (equiv v hv b).1 := by
  obtain ⟨x, rfl⟩ := rv_surjective v a
  obtain ⟨y, rfl⟩ := rv_surjective v b
  rw [← ResidueTranscendentalTransport.rv_mul_all, equiv_rv, equiv_rv, equiv_rv]
  exact rv_mul_hom_of_model hM x.2 y.2

end CanonicalRV

#print axioms CanonicalRV.same_fibers
#print axioms CanonicalRV.equiv
#print axioms CanonicalRV.equiv_rv
#print axioms CanonicalRV.equiv_mul
