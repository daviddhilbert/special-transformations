module

public import Section6.ExpandedLogic

@[expose] public section

/-! Bijective free-variable renaming preserves the exact guarded syntax
and its VF-free fragment. Bound variables are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.ExpandedRenaming
open RVTermSupport

variable {E : _root_.FirstOrder.Language.{0, 0}} {I J : Type}

theorem guard (e : I ≃ J) {n : ℕ} (s : SortTag) (i : Fin n) :
    (BoundedFormula.relabelEquiv e) (ExpandedLogic.guardAtom (E := E) (α := I) s i) =
      ExpandedLogic.guardAtom (E := E) (α := J) s i := by
  change BoundedFormula.rel (ExpandedLogic.sortRelation s)
    (fun j => ((![Term.var (.inr i)] : Fin 1 → (Expanded E).Term (I ⊕ Fin n)) j).relabel
      (Sum.map e id)) = _
  congr 1
  funext j
  fin_cases j
  rfl

theorem allSorted (e : I ≃ J) {n : ℕ} (s : SortTag)
    (φ : (Expanded E).BoundedFormula I (n + 1)) :
    (BoundedFormula.relabelEquiv e) (ExpandedLogic.allSorted s φ) =
      ExpandedLogic.allSorted s ((BoundedFormula.relabelEquiv e) φ) := by
  change ((BoundedFormula.relabelEquiv e) (ExpandedLogic.guardAtom s (Fin.last n)) ⟹
    (BoundedFormula.relabelEquiv e) φ).all = _
  rw [guard]
  rfl

theorem isVFQF (e : I ≃ J) {n : ℕ} (φ : (Expanded E).BoundedFormula I n)
    (hφ : ExpandedLogic.IsVFQF φ) :
    ExpandedLogic.IsVFQF ((BoundedFormula.relabelEquiv e) φ) := by
  induction hφ with
  | falsum => exact .falsum
  | atomic h => cases h with
    | equal t u => exact .atomic (.equal _ _)
    | rel r ts => exact .atomic (.rel _ _)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | all_rv hφ ih => rw [allSorted]; exact .all_rv ih

theorem term_sort (e : I ≃ J) (sI : I → SortTag) (sJ : J → SortTag)
    (he : ∀ i, sJ (e i) = sI i) {n : ℕ} (sn : Fin n → SortTag)
    (t : (Expanded E).Term (I ⊕ Fin n)) :
    termSort (Sum.elim sJ sn) (t.relabel (Sum.map e id)) = termSort (Sum.elim sI sn) t := by
  apply GuardedLift.termSort_relabel
  intro j
  cases j with
  | inl i => exact he i
  | inr i => rfl

theorem wellSorted (e : I ≃ J) (sI : I → SortTag) (sJ : J → SortTag)
    (he : ∀ i, sJ (e i) = sI i) {n : ℕ} (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I n) (hφ : ExpandedLogic.WellSorted sI sn φ) :
    ExpandedLogic.WellSorted sJ sn ((BoundedFormula.relabelEquiv e) φ) := by
  induction hφ with
  | falsum sn => exact .falsum _
  | equal ht hu =>
    exact .equal ((term_sort e sI sJ he _ _).trans ht) ((term_sort e sI sJ he _ _).trans hu)
  | rel r ts hts =>
    apply ExpandedLogic.WellSorted.rel
    intro i
    exact (term_sort e sI sJ he _ _).trans (hts i)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | all hφ ih => rw [allSorted]; exact .all ih

end SpecialTransformations.Section6.ExpandedRenaming
