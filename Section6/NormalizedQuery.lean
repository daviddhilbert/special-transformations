import Section6.NativeFormulaElimination
import Section6.SortedFragment

/-! An actual formula for the normalized existential query, with the
remaining VF parameters still free. Its named-parameter interpretation
is exactly the source formula of the prepared-map descent theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV
  SpecialTransformations.DefinableGeometry.Space.prod SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.NormalizedQuery
open RVTermSupport NamedLanguage

variable {E : _root_.FirstOrder.Language.{0, 0}} {R β : Type} {r n m : ℕ}

def guards : (Expanded E).Formula (Fin n ⊕ (Fin r ⊕ R)) :=
  Formula.iInf (fun i : Fin n => SortedFragment.guardOne (E := E) (fun _ => .vf) (.inl i))

def reindex : (Fin r ⊕ Fin n) ⊕ R → Fin n ⊕ (Fin r ⊕ R)
  | .inl (.inl j) => .inr (.inl j)
  | .inl (.inr i) => .inl i
  | .inr b => .inr (.inr b)

def formula (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ R)) :
    (Expanded E).Formula (Fin r ⊕ R) :=
  RVFormula.existsLeft (guards ⊓ φ.relabel reindex)

theorem realize {M : Type} [(Expanded E).Structure M]
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ R))
    (c : Fin r → M) (b : R → M) :
    (formula φ).Realize (Sum.elim c b) ↔
      ∃ x : Fin n → M, (∀ i, ExpandedLogic.tagEval (E := E) .vf (x i)) ∧
        φ.Realize (Sum.elim (Sum.elim c x) b) := by
  rw [formula, RVFormula.existsLeft_realize]
  apply exists_congr
  intro x
  rw [Formula.realize_inf, guards, Formula.realize_iInf, Formula.realize_relabel]
  have hg : (∀ i : Fin n, (SortedFragment.guardOne (E := E) (fun _ => .vf) (.inl i)).Realize
      (Sum.elim x (Sum.elim c b))) ↔ ∀ i, ExpandedLogic.tagEval (E := E) .vf (x i) := by
    apply forall_congr'
    intro i
    exact SortedFragment.guardOne_realize _ _ _
  have he : Sum.elim x (Sum.elim c b) ∘ reindex =
      Sum.elim (Sum.elim c x) b := by
    funext j
    rcases j with (j | i) | b
    · rfl
    · rfl
    · rfl
  rw [hg, he]

section Substructures
variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]

private theorem tag_vf (X : LRV.Substructure C) [E.Structure (SubRV (X : Set C))] (x : X) :
    letI := RVSubstructure.extraStructure (E := E) X
    ExpandedLogic.tagEval (E := E) .vf x ↔ iVF x.val := by
  letI := RVSubstructure.extraStructure (E := E) X
  change Structure.RelMap (L := LRV) Rel.memVF (fun i : Fin 1 => (![x] i).val) ↔ _
  have he : (fun i : Fin 1 => (![x] i).val) = ![x.val] := by funext i; fin_cases i; rfl
  rw [he]
  rfl

theorem named_realize (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))]
    (c : Fin r → VF (M := C)) (hc : ∀ i, (c i).val ∈ S)
    (d : Fin m → SubRV (S : Set C))
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ β)))
    (b : β → SubRV (X : Set C)) :
    letI := RVSubstructure.extraStructure (E := E) X
    ((formula φ).Realize (Sum.elim (fun i => (⟨(c i).val, hSX (hc i)⟩ : X))
      (RVSubstructure.inclusion X ∘ Sum.elim (FiniteNamedSyntax.rvTuple S X hSX d) b)) ↔
      @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
        (FVBinding.existsVF S (FiniteNamedSyntax.nameInput S c hc d φ))
        (RVSubstructure.inclusion X ∘ b)) := by
  letI := RVSubstructure.extraStructure (E := E) X
  rw [realize, FVBinding.existsVF_realize_points S X hSX]
  constructor
  · rintro ⟨x, hx, hφ⟩
    let xC : Fin n → VF (M := C) := fun i => ⟨(x i).val, (tag_vf X (x i)).mp (hx i)⟩
    let a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C) :=
      ⟨(xC, Fin.elim0), Set.mem_univ _⟩
    have ha : PointIn (X : Set C) a.val :=
      Sum.rec (fun i => (x i).property) (fun i => i.elim0)
    have he := FiniteNamedSyntax.nameInput_realize S X hSX c hc d φ xC
      (fun i => (x i).property) b
    refine ⟨a, ha, he.mpr ?_⟩
    convert hφ using 1
    · funext j
      rcases j with (j | i) | (i | b)
      · rfl
      · rfl
      · rfl
      · rfl
  · rintro ⟨a, ha, hφ⟩
    let x := vfAssignment X a ha
    have hx : ∀ i, ExpandedLogic.tagEval (E := E) .vf (x i) :=
      fun i => (tag_vf X (x i)).mpr (a.val.1 i).property
    have he := FiniteNamedSyntax.nameInput_realize S X hSX c hc d φ (vfAt a.val)
      (fun i => ha (.inl i)) b
    refine ⟨x, hx, ?_⟩
    have ht := he.mp hφ
    convert ht using 1
    · funext j
      rcases j with (j | i) | (i | b)
      · rfl
      · rfl
      · rfl
      · rfl

end Substructures
end SpecialTransformations.Section6.NormalizedQuery
