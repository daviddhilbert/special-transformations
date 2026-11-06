import Section6.FiniteNamedSyntax
import Section6.RVFormula

/-! Bind the FV tuple in the actual named language, with its native sort
guards. The semantics is exactly the substructure-point existential used
by the geometric descent, including the empty tuple.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.FVBinding
open RVTermSupport NamedLanguage

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}} {β : Type} {n : ℕ}

def guards (S : LRV.Substructure C) : (Source E S).Formula (Fin n ⊕ β) :=
  Formula.iInf (fun i : Fin n => BoundedFormula.rel (.inl (.inl Rel.memVF))
    ![Term.var (.inl (.inl i))])

def existsVF (S : LRV.Substructure C) (φ : (Source E S).Formula (Fin n ⊕ β)) :
    (Source E S).Formula β := RVFormula.existsLeft (guards S ⊓ φ)

theorem guards_realize (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))] (x : Fin n → X) (b : β → X) :
    @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ (guards S)
      (Sum.elim x b) ↔ ∀ i, iVF (x i).val := by
  letI := sourceStructure (E := E) S X hSX
  rw [guards, Formula.realize_iInf]
  apply forall_congr'
  intro i
  have he : (fun j : Fin 1 => (Term.realize (Sum.elim (Sum.elim x b) (default : Fin 0 → X))
      ((![.var (.inl (.inl i))] : Fin 1 → (Source E S).Term ((Fin n ⊕ β) ⊕ Fin 0)) j)).val) =
      ![(x i).val] := by
    funext j
    fin_cases j
    rfl
  change Structure.RelMap (L := LRV) Rel.memVF _ ↔ iVF (x i).val
  rw [he]
  rfl

theorem existsVF_realize_points (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))] (φ : (Source E S).Formula (Fin n ⊕ β)) (b : β → X) :
    @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ (existsVF S φ) b ↔
      ∃ a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C),
        ∃ ha : PointIn (X : Set C) a.val,
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ φ
            (Sum.elim (vfAssignment X a ha) b) := by
  letI := sourceStructure (E := E) S X hSX
  rw [existsVF, RVFormula.existsLeft_realize]
  simp only [Formula.realize_inf, guards_realize]
  constructor
  · rintro ⟨x, hx, hφ⟩
    let a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C) :=
      ⟨(fun i => ⟨(x i).val, hx i⟩, Fin.elim0), Set.mem_univ _⟩
    have ha : PointIn (X : Set C) a.val :=
      Sum.rec (fun i => (x i).property) (fun i => i.elim0)
    have he : vfAssignment X a ha = x := by
      funext i
      apply Subtype.ext
      rfl
    exact ⟨a, ha, by simpa only [he] using hφ⟩
  · rintro ⟨a, ha, hφ⟩
    refine ⟨vfAssignment X a ha, ?_, hφ⟩
    intro i
    exact (a.val.1 i).property

end SpecialTransformations.Section6.FVBinding
