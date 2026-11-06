import Section6.RVAbstraction
import Section6.ExpandedRenaming

/-! Reindex the VF and RV free contexts of a normalized formula without
altering any of its inner RV binders or ordinary polynomial leaves. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.RVFragmentRenaming
open RVTermSupport RVAbstraction

variable {E : _root_.FirstOrder.Language.{0, 0}} {V R V' R' : Type}

theorem term_sort (eV : V ≃ V') (eR : R ≃ R') {n : ℕ}
    (t : (Expanded E).Term ((V ⊕ R) ⊕ Fin n)) :
    termSort sourceSort (t.relabel (Sum.map (eV.sumCongr eR) id)) = termSort sourceSort t := by
  apply ExpandedRenaming.term_sort (eV.sumCongr eR)
    (Sum.elim (fun _ => .vf) (fun _ => .rv)) (Sum.elim (fun _ => .vf) (fun _ => .rv))
  intro i
  cases i <;> rfl

theorem fragment (eV : V ≃ V') (eR : R ≃ R') {n : ℕ}
    (φ : (Expanded E).BoundedFormula (V ⊕ R) n) (hφ : Fragment φ) :
    Fragment ((BoundedFormula.relabelEquiv (eV.sumCongr eR)) φ) := by
  induction hφ with
  | falsum => exact .falsum
  | equal t u ht hu =>
    exact .equal _ _ ((term_sort eV eR t).trans ht) ((term_sort eV eR u).trans hu)
  | rel r ts hs =>
    apply Fragment.rel r
    intro i
    exact (term_sort eV eR (ts i)).trans (hs i)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | @all n φ hφ ih =>
    change Fragment ((BoundedFormula.relabelEquiv (eV.sumCongr eR))
      (ExpandedLogic.allSorted .rv φ))
    rw [ExpandedRenaming.allSorted]
    exact .all ih

end SpecialTransformations.Section6.RVFragmentRenaming
