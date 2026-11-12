module

public import Section6.ExpandedParameterRelabel

@[expose] public section

/-! Opening the existing bound context as free variables preserves the
sorted syntax and its VF-free fragment. The actual formula construction
and realization theorem are Mathlib's BoundedFormula.toFormula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.ExpandedOpenBounds
open RVTermSupport

variable {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}

def splitLast (n : ℕ) : I ⊕ Fin (n + 1) → (I ⊕ Fin n) ⊕ Fin 1 :=
  Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm)

theorem splitLast_free (n : ℕ) (i : I) : splitLast n (.inl i) = .inl (.inl i) := rfl

theorem splitLast_cast (n : ℕ) (i : Fin n) :
    splitLast (I := I) n (.inr i.castSucc) = .inl (.inr i) := by
  change Sum.map Sum.inr id (finSumFinEquiv.symm i.castSucc) = _
  have h : i.castSucc = finSumFinEquiv (.inl i : Fin n ⊕ Fin 1) := rfl
  rw [h, Equiv.symm_apply_apply]
  rfl

theorem splitLast_last (n : ℕ) :
    splitLast (I := I) n (.inr (Fin.last n)) = .inr (Fin.last 0) := by
  change Sum.map Sum.inr id (finSumFinEquiv.symm (Fin.last n)) = _
  have h : Fin.last n = finSumFinEquiv (.inr (Fin.last 0) : Fin n ⊕ Fin 1) := rfl
  rw [h, Equiv.symm_apply_apply]
  rfl

theorem guard (n : ℕ) (s : SortTag) :
    BoundedFormula.relabel (splitLast (I := I) n)
        (ExpandedLogic.guardAtom (E := E) (α := I) s (Fin.last n)).toFormula =
      ExpandedLogic.guardAtom (E := E) (α := I ⊕ Fin n) s (Fin.last 0) := by
  change BoundedFormula.rel (ExpandedLogic.sortRelation s) _ = _
  congr 1
  funext j
  fin_cases j
  change Term.relabel (BoundedFormula.relabelAux (splitLast (I := I) n) 0)
      (Term.relabel Sum.inl (Term.var (.inr (Fin.last n)))) = Term.var (.inr (Fin.last 0))
  simp only [Term.relabel, ParamBridge.relabelAux_inl, splitLast_last, Sum.map_inr]
  rfl

theorem isVFQF {n : ℕ} (φ : (Expanded E).BoundedFormula I n)
    (hφ : ExpandedLogic.IsVFQF φ) : ExpandedLogic.IsVFQF φ.toFormula := by
  induction hφ with
  | falsum => exact .falsum
  | atomic h => cases h with
    | equal t u => exact .atomic (.equal _ _)
    | rel r ts => exact .atomic (.rel _ _)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | @all_rv n φ hφ ih =>
    change ExpandedLogic.IsVFQF
      ((BoundedFormula.relabel (splitLast n) (ExpandedLogic.guardAtom .rv (Fin.last n)).toFormula ⟹
        BoundedFormula.relabel (splitLast n) φ.toFormula).all)
    rw [guard]
    exact .all_rv (ExpandedParameterRelabel.isVFQF (splitLast n) φ.toFormula ih)

theorem term_sort {n : ℕ} (sI : I → SortTag) (sn : Fin n → SortTag)
    (t : (Expanded E).Term (I ⊕ Fin n)) :
    termSort (Sum.elim (Sum.elim sI sn) (fun _ : Fin 0 => .rv)) (t.relabel Sum.inl) =
      termSort (Sum.elim sI sn) t := by
  apply GuardedLift.termSort_relabel
  intro i
  rfl

theorem sortAssem_empty {m : ℕ} (sG : Fin m → SortTag) (sn : Fin 0 → SortTag) :
    ParamBridge.sortAssem sG sn = sG := by
  funext i
  have hi : i.val < m := i.isLt
  rw [ParamBridge.sortAssem, dif_pos hi]
  congr 1 <;> exact Fin.ext rfl

theorem wellSorted {n : ℕ} (sI : I → SortTag) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I n) (hφ : ExpandedLogic.WellSorted sI sn φ) :
    ExpandedLogic.WellSorted (Sum.elim sI sn) (fun _ => .rv) φ.toFormula := by
  induction hφ with
  | falsum sn => exact .falsum _
  | equal ht hu =>
    exact .equal ((term_sort sI _ _).trans ht) ((term_sort sI _ _).trans hu)
  | rel r ts hs =>
    apply ExpandedLogic.WellSorted.rel
    intro i
    exact (term_sort sI _ _).trans (hs i)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | @all n sn s φ hφ ih =>
    have hg : ∀ i : I ⊕ Fin (n + 1),
        Sum.elim (Sum.elim sI sn) (fun _ : Fin 1 => s) (splitLast n i) =
          Sum.elim sI (Fin.snoc sn s) i := by
      intro i
      cases i with
      | inl i => rfl
      | inr i =>
        cases i using Fin.lastCases with
        | last => rw [splitLast_last]; simp only [Sum.elim_inr, Fin.snoc_last]
        | cast i => rw [splitLast_cast]; simp only [Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc]
    have hs := ExpandedParameterRelabel.wellSorted (splitLast n)
      (Sum.elim sI (Fin.snoc sn s)) (Sum.elim sI sn) (fun _ => s) (fun _ => .rv) hg φ.toFormula ih
    rw [sortAssem_empty] at hs
    have he : (fun _ : Fin 1 => s) = Fin.snoc (fun _ : Fin 0 => SortTag.rv) s := by
      funext i
      fin_cases i
      rfl
    rw [he] at hs
    change ExpandedLogic.WellSorted (Sum.elim sI sn) (fun _ => .rv)
      ((BoundedFormula.relabel (splitLast n) (ExpandedLogic.guardAtom s (Fin.last n)).toFormula ⟹
        BoundedFormula.relabel (splitLast n) φ.toFormula).all)
    rw [guard]
    exact .all hs

end SpecialTransformations.Section6.ExpandedOpenBounds
