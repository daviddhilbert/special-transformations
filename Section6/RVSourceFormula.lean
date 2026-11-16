module

public import Section6.ExpandedLogic
public import Section6.RVSubstructure

@[expose] public section

/-! Return an auxiliary RV formula to the actual expanded language. Every
binder is guarded by the native RV predicate. Semantic correctness uses
the substructure's own auxiliary interpretation, including all extra RV
structure, rather than evaluating auxiliary quantifiers in ACVF.
-/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.RVSourceFormula
open RVTermSupport RVAbstraction

variable {E : Language} {β : Type}

def lift (φ : (Auxiliary E).Formula β) : (Expanded E).Formula β :=
  GuardedLift.formula (fun b => .var b) φ

theorem lift_isVFQF (φ : (Auxiliary E).Formula β) : ExpandedLogic.IsVFQF (lift φ) :=
  GuardedLift.formula_isVFQF _ _

theorem lift_wellSorted (φ : (Auxiliary E).Formula β) :
    ExpandedLogic.WellSorted (fun _ => .rv) (fun _ => .rv) (lift φ) :=
  GuardedLift.formula_wellSorted _ _ (fun _ => rfl) φ

theorem lift_realize_substructure
    {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
    (X : LRV.Substructure C) [E.Structure (SubRV (X : Set C))]
    (φ : (Auxiliary E).Formula β) (b : β → SubRV (X : Set C)) :
    letI := RVSubstructure.auxiliaryStructure (E := E) X
    letI := RVSubstructure.extraStructure (E := E) X
    (lift φ).Realize (RVSubstructure.inclusion X ∘ b) ↔ φ.Realize b := by
  letI := RVSubstructure.auxiliaryStructure (E := E) X
  letI := RVSubstructure.extraStructure (E := E) X
  have he := GuardedLift.formula_realize (RVSubstructure.inclusion X)
    (RVSubstructure.inclusion_injective X) (RVSubstructure.functions_compatible X)
    (RVSubstructure.relations_compatible X) (RVSubstructure.guard_compatible X)
    (fun q => Term.var q) (RVSubstructure.inclusion X ∘ b) b (fun _ => rfl) φ
    (default : Fin 0 → SubRV (X : Set C))
  have hb : RVSubstructure.inclusion X ∘ (default : Fin 0 → SubRV (X : Set C)) =
      (default : Fin 0 → X) := Subsingleton.elim _ _
  simpa only [lift, Formula.Realize, hb] using he

end SpecialTransformations.Section6.RVSourceFormula
