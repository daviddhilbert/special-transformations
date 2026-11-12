module

public import Section6.HenselianTheory
public import Section6.ExpandedLogic

@[expose] public section

/-! The added-symbol typing and off-sort conventions are consequences
of the actual first-order axiom scheme. These laws only describe the
RV-only language expansion; they assert no closure or elimination fact.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.ExtraSortSemantics
open RVTermSupport ExpandedLogic HenselianTheory

variable {E : _root_.FirstOrder.Language.{0, 0}} {M : Type} [(Expanded E).Structure M]

def zero : M := Structure.funMap (L := Expanded E) (.inl Fn.rvZero) Fin.elim0

structure Laws : Prop where
  functions : ∀ {k} (f : E.Functions k) (z : Fin k → M),
    (∀ i, tagEval (E := E) .rv (z i)) →
      tagEval (E := E) .rv (Structure.funMap (L := Expanded E) (.inr f) z)
  junk : ∀ {k} (f : E.Functions k) (z : Fin k → M),
    ¬ (∀ i, tagEval (E := E) .rv (z i)) →
      Structure.funMap (L := Expanded E) (.inr f) z = zero (E := E)
  relations : ∀ {k} (r : E.Relations k) (z : Fin k → M),
    Structure.RelMap (L := Expanded E) (.inr r) z →
      ∀ i, tagEval (E := E) .rv (z i)

private theorem arguments_list {n : ℕ} (l : List (Fin n)) (u : Empty → M) (z : Fin n → M) :
    ((l.map (guardAtom (E := E) (α := Empty) .rv)).foldr (· ⊓ ·) ⊤).Realize
      u z ↔ ∀ i ∈ l, tagEval (E := E) .rv (z i) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simpa only [List.map_cons, List.foldr_cons, BoundedFormula.realize_inf,
      guardAtom_realize, List.mem_cons, forall_eq_or_imp] using and_congr Iff.rfl ih

theorem arguments_realize {n : ℕ} (u : Empty → M) (z : Fin n → M) :
    (rvArguments E n).Realize u z ↔ ∀ i, tagEval (E := E) .rv (z i) := by
  change (((List.finRange n).map (ExpandedLogic.guardAtom (E := E) (α := Empty) .rv)).foldr
    (· ⊓ ·) ⊤).Realize u z ↔ _
  simpa only [List.mem_finRange, forall_const] using
    arguments_list (E := E) (List.finRange n) u z

theorem functionSort_realize {k : ℕ} (f : E.Functions k) :
    (M ⊨ extraFunctionSort E f) ↔
      ∀ z : Fin k → M, (∀ i, tagEval (E := E) .rv (z i)) →
        tagEval (E := E) .rv (Structure.funMap (L := Expanded E) (.inr f) z) := by
  rw [extraFunctionSort, Sentence.Realize, BoundedFormula.realize_alls]
  apply forall_congr'
  intro z
  rw [BoundedFormula.realize_imp, arguments_realize]
  apply imp_congr Iff.rfl
  change Structure.RelMap (L := Expanded E) (.inl Rel.memRV) _ ↔ _
  have he : (fun i : Fin 1 =>
      ((![Term.func (.inr f) (fun j => Term.var (.inr j))] :
        Fin 1 → (Expanded E).Term (Empty ⊕ Fin k)) i).realize
          (Sum.elim (default : Empty → M) z)) =
      ![Structure.funMap (L := Expanded E) (.inr f) z] := by
    funext i
    fin_cases i
    rfl
  rw [he]
  rfl

theorem functionJunk_realize {k : ℕ} (f : E.Functions k) :
    (M ⊨ extraFunctionJunk E f) ↔
      ∀ z : Fin k → M, ¬ (∀ i, tagEval (E := E) .rv (z i)) →
        Structure.funMap (L := Expanded E) (.inr f) z = zero (E := E) := by
  rw [extraFunctionJunk, Sentence.Realize, BoundedFormula.realize_alls]
  apply forall_congr'
  intro z
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_not, arguments_realize]
  apply imp_congr Iff.rfl
  have hzero : ((Term.func (L := Expanded E) (.inl Fn.rvZero) Fin.elim0) :
      (Expanded E).Term (Empty ⊕ Fin k)).realize (Sum.elim (default : Empty → M) z) =
      zero (E := E) := by
    change Structure.funMap (L := Expanded E) (.inl Fn.rvZero) _ =
      Structure.funMap (L := Expanded E) (.inl Fn.rvZero) _
    congr 1
    funext i
    exact i.elim0
  change (Structure.funMap (L := Expanded E) (.inr f) z =
    ((Term.func (L := Expanded E) (.inl Fn.rvZero) Fin.elim0) :
      (Expanded E).Term (Empty ⊕ Fin k)).realize (Sum.elim (default : Empty → M) z)) ↔ _
  rw [hzero]

theorem relationSort_realize {k : ℕ} (r : E.Relations k) :
    (M ⊨ extraRelationSort E r) ↔
      ∀ z : Fin k → M, Structure.RelMap (L := Expanded E) (.inr r) z →
        ∀ i, tagEval (E := E) .rv (z i) := by
  rw [extraRelationSort, Sentence.Realize, BoundedFormula.realize_alls]
  apply forall_congr'
  intro z
  rw [BoundedFormula.realize_imp, arguments_realize]
  rfl

theorem laws_of_model (h : M ⊨ extraSortAxioms E) : Laws (E := E) (M := M) where
  functions := fun f z hz => (functionSort_realize f).mp
    (h.realize_of_mem _ (Or.inl (Or.inl ⟨_, f, rfl⟩))) z hz
  junk := fun f z hz => (functionJunk_realize f).mp
    (h.realize_of_mem _ (Or.inl (Or.inr ⟨_, f, rfl⟩))) z hz
  relations := fun r z hr => (relationSort_realize r).mp
    (h.realize_of_mem _ (Or.inr ⟨_, r, rfl⟩)) z hr

theorem laws_of_henselian_model (h : M ⊨ HenselianTheory.expanded E) : Laws (E := E) (M := M) :=
  laws_of_model (h.mono Set.subset_union_right)

end SpecialTransformations.Section6.ExtraSortSemantics
