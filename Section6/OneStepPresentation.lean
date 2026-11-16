module

public import Section6.ExpandedOpenBounds
public import Section6.FiniteSortContext

@[expose] public section

/-! The original outer variables become finite coefficient variables;
the one VF witness remains distinguished. This is an actual reindexing
of Mathlib syntax, with no preparation or elimination hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.OneStepPresentation
open RVTermSupport FiniteSortContext

variable {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} {n : ℕ}

def exchange (A B C : Type) : (A ⊕ B) ⊕ C ≃ (A ⊕ C) ⊕ B where
  toFun := fun j => match j with
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr b
    | .inr c => .inl (.inr c)
  invFun := fun j => match j with
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr c) => .inr c
    | .inr b => .inl (.inr b)
  left_inv j := by rcases j with (j | j) | j <;> rfl
  right_inv j := by rcases j with (j | j) | j <;> rfl

def splitEquiv (I : Type) (n : ℕ) : I ⊕ Fin (n + 1) ≃ (I ⊕ Fin n) ⊕ Fin 1 :=
  ((Equiv.refl I).sumCongr finSumFinEquiv.symm).trans (Equiv.sumAssoc _ _ _).symm

def indices (s : I → SortTag) (sn : Fin n → SortTag) :
    I ⊕ Fin (n + 1) ≃ (VFPart (Sum.elim s sn) ⊕ Fin 1) ⊕ RVPart (Sum.elim s sn) :=
  (splitEquiv I n).trans
    (((partition (Sum.elim s sn)).sumCongr (Equiv.refl _)).trans (exchange _ _ _))

def old : I ⊕ Fin n → I ⊕ Fin (n + 1) := Sum.map id Fin.castSucc

theorem inverse_vf (s : I → SortTag) (sn : Fin n → SortTag) (i : VFPart (Sum.elim s sn)) :
    (indices s sn).symm (.inl (.inl i)) = old i.val := by
  rcases i with ⟨i | i, hi⟩ <;> rfl

theorem inverse_rv (s : I → SortTag) (sn : Fin n → SortTag) (i : RVPart (Sum.elim s sn)) :
    (indices s sn).symm (.inr i) = old i.val := by
  rcases i with ⟨i | i, hi⟩ <;> rfl

theorem inverse_new (s : I → SortTag) (sn : Fin n → SortTag) (i : Fin 1) :
    (indices s sn).symm (.inl (.inr i)) = .inr (Fin.natAdd n i) := rfl

theorem old_sort (s : I → SortTag) (sn : Fin n → SortTag) (j : I ⊕ Fin n) :
    Sum.elim s (Fin.snoc sn .vf) (old j) = Sum.elim s sn j := by
  cases j <;> simp only [old, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc, id_eq]

theorem inverse_sort (s : I → SortTag) (sn : Fin n → SortTag)
    (j : (VFPart (Sum.elim s sn) ⊕ Fin 1) ⊕ RVPart (Sum.elim s sn)) :
    Sum.elim s (Fin.snoc sn .vf) ((indices s sn).symm j) =
      Sum.elim (fun _ => SortTag.vf) (fun _ => .rv) j := by
  rcases j with (j | j) | j
  · rw [inverse_vf, old_sort]
    exact j.property
  · rw [inverse_new]
    fin_cases j
    change (Fin.snoc (α := fun _ : Fin (n + 1) => SortTag) sn SortTag.vf) (Fin.last n) = SortTag.vf
    simp only [Fin.snoc_last]
  · rw [inverse_rv, old_sort]
    exact j.property

def body (s : I → SortTag) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I (n + 1)) :
    (Expanded E).Formula ((VFPart (Sum.elim s sn) ⊕ Fin 1) ⊕ RVPart (Sum.elim s sn)) :=
  (BoundedFormula.relabelEquiv (indices s sn)) φ.toFormula

theorem body_isVFQF (s : I → SortTag) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I (n + 1)) (hφ : ExpandedLogic.IsVFQF φ) :
    ExpandedLogic.IsVFQF (body s sn φ) :=
  ExpandedRenaming.isVFQF _ _ (ExpandedOpenBounds.isVFQF φ hφ)

theorem body_wellSorted (s : I → SortTag) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I (n + 1))
    (hφ : ExpandedLogic.WellSorted s (Fin.snoc sn .vf) φ) :
    ExpandedLogic.WellSorted (Sum.elim (fun _ => .vf) (fun _ => .rv)) (fun _ => .rv) (body s sn φ) := by
  apply ExpandedRenaming.wellSorted (indices s sn) (Sum.elim s (Fin.snoc sn .vf))
    (Sum.elim (fun _ => .vf) (fun _ => .rv)) _ _ φ.toFormula
    (ExpandedOpenBounds.wellSorted s (Fin.snoc sn .vf) φ hφ)
  intro j
  have h := inverse_sort s sn (indices s sn j)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem old_value {M : Type} (v : I → M) (x : Fin n → M) (a : M) (j : I ⊕ Fin n) :
    Sum.elim v (Fin.snoc x a) (old j) = Sum.elim v x j := by
  cases j <;> simp only [old, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc, id_eq]

theorem body_realize {M : Type} [(Expanded E).Structure M]
    (s : I → SortTag) (sn : Fin n → SortTag) (φ : (Expanded E).BoundedFormula I (n + 1))
    (v : I → M) (x : Fin n → M) (a : Fin 1 → M) :
    (body s sn φ).Realize (Sum.elim
      (Sum.elim (fun i : VFPart (Sum.elim s sn) => Sum.elim v x i.val) a)
      (fun i : RVPart (Sum.elim s sn) => Sum.elim v x i.val)) ↔
      φ.Realize v (Fin.snoc x (a 0)) := by
  let z := Sum.elim v (Fin.snoc x (a 0))
  let w := Sum.elim
    (Sum.elim (fun i : VFPart (Sum.elim s sn) => Sum.elim v x i.val) a)
    (fun i : RVPart (Sum.elim s sn) => Sum.elim v x i.val)
  have hi : z ∘ (indices s sn).symm = w := by
    funext j
    rcases j with (j | j) | j
    · rw [Function.comp_apply, inverse_vf]
      exact old_value v x (a 0) j.val
    · rw [Function.comp_apply, inverse_new]
      fin_cases j
      change (Fin.snoc (α := fun _ : Fin (n + 1) => M) x (a 0)) (Fin.last n) = a 0
      simp only [Fin.snoc_last]
    · rw [Function.comp_apply, inverse_rv]
      exact old_value v x (a 0) j.val
  have hj : w ∘ indices s sn = z := by
    rw [← hi, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  change Formula.Realize ((BoundedFormula.relabelEquiv (indices s sn)) φ.toFormula) w ↔ _
  rw [Formula.Realize, BoundedFormula.realize_relabelEquiv, hj]
  change Formula.Realize φ.toFormula z ↔ _
  rw [BoundedFormula.realize_toFormula]
  rfl

end SpecialTransformations.Section6.OneStepPresentation
