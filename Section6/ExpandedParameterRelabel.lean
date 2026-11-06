import Section6.ExpandedRestriction
import ParamBridgeRelabel

/-! Parameter promotion in arbitrary RV expansions. The index arithmetic
and sort assembly are reused from the retained Shared/ParamBridgeRelabel
helper; only the expanded formula constructors are handled here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.ExpandedParameterRelabel
open RVTermSupport

variable {E : _root_.FirstOrder.Language.{0, 0}} {I J : Type} {m n : ℕ}

theorem term_sort (g : I → J ⊕ Fin m) (sI : I → SortTag) (sJ : J → SortTag)
    (sG : Fin m → SortTag) (sn : Fin n → SortTag)
    (hg : ∀ i, Sum.elim sJ sG (g i) = sI i) (t : (Expanded E).Term (I ⊕ Fin n)) :
    termSort (Sum.elim sJ (ParamBridge.sortAssem sG sn))
        (t.relabel (BoundedFormula.relabelAux g n)) = termSort (Sum.elim sI sn) t := by
  apply GuardedLift.termSort_relabel
  intro i
  cases i with
  | inl i =>
    rw [ParamBridge.relabelAux_inl]
    have hi := hg i
    cases he : g i with
    | inl j => simpa only [he, Sum.map_inl, Sum.elim_inl, id_eq] using hi
    | inr j =>
      simpa only [he, Sum.map_inr, Sum.elim_inr, Sum.elim_inl, ParamBridge.sortAssem_castAdd] using hi
  | inr i => simp only [ParamBridge.relabelAux_inr, Sum.elim_inr, ParamBridge.sortAssem_natAdd]

theorem guard (g : I → J ⊕ Fin m) (s : SortTag) (i : Fin n) :
    (ExpandedLogic.guardAtom (E := E) (α := I) s i).relabel g =
      ExpandedLogic.guardAtom (E := E) (α := J) s (Fin.natAdd m i) := by
  change BoundedFormula.rel (ExpandedLogic.sortRelation s) _ = _
  congr 1
  funext j
  fin_cases j
  change Term.relabel (BoundedFormula.relabelAux g n) (Term.var (.inr i)) =
    Term.var (.inr (Fin.natAdd m i))
  simp only [Term.relabel, ParamBridge.relabelAux_inr]

theorem allSorted (g : I → J ⊕ Fin m) (s : SortTag)
    (φ : (Expanded E).BoundedFormula I (n + 1)) :
    (ExpandedLogic.allSorted s φ).relabel g = ExpandedLogic.allSorted s (φ.relabel g) := by
  unfold ExpandedLogic.allSorted
  rw [BoundedFormula.relabel_all]
  change ((ExpandedLogic.guardAtom s (Fin.last n)).relabel g ⟹ φ.relabel g).all = _
  rw [guard]
  have hi : Fin.natAdd m (Fin.last n) = Fin.last (m + n) := Fin.ext rfl
  rw [hi]
  rfl

theorem isVFQF (g : I → J ⊕ Fin m) (φ : (Expanded E).BoundedFormula I n)
    (hφ : ExpandedLogic.IsVFQF φ) : ExpandedLogic.IsVFQF (φ.relabel g) := by
  induction hφ with
  | falsum => exact .falsum
  | atomic h => exact .atomic (h.relabel g)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | all_rv hφ ih => rw [allSorted]; exact .all_rv ih

theorem wellSorted (g : I → J ⊕ Fin m) (sI : I → SortTag) (sJ : J → SortTag)
    (sG : Fin m → SortTag) (sn : Fin n → SortTag)
    (hg : ∀ i, Sum.elim sJ sG (g i) = sI i)
    (φ : (Expanded E).BoundedFormula I n) (hφ : ExpandedLogic.WellSorted sI sn φ) :
    ExpandedLogic.WellSorted sJ (ParamBridge.sortAssem sG sn) (φ.relabel g) := by
  induction hφ with
  | falsum sn => exact .falsum _
  | equal ht hu =>
    exact .equal ((term_sort g sI sJ sG _ hg _).trans ht)
      ((term_sort g sI sJ sG _ hg _).trans hu)
  | rel r ts hs =>
    apply ExpandedLogic.WellSorted.rel
    intro i
    exact (term_sort g sI sJ sG _ hg _).trans (hs i)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | all hφ ih =>
    rw [allSorted]
    apply ExpandedLogic.WellSorted.all
    rw [← ParamBridge.sortAssem_snoc]
    exact ih

end SpecialTransformations.Section6.ExpandedParameterRelabel
