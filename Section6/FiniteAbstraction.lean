module

public import Section6.RVSubstructure

@[expose] public section

/-! The finite syntactic replacement φ ↦ φ*. The occurrence list and body
are selected before the ambient model, substructure or assignment. The
body's RV quantifiers are evaluated on RV(X), with arbitrary extra RV
structure. Earlier native VF-literal normalization is used as given.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.FiniteAbstraction
open RVTermSupport RVAbstraction

variable {E : Language} {V R : Type}

def count (φ : (Expanded E).Formula (V ⊕ R)) : ℕ :=
  (RVFormula.leftSupport (formula φ)).card

def occurrence (φ : (Expanded E).Formula (V ⊕ R)) (i : Fin (count φ)) :
    (Expanded E).Term V := (RVFormula.enumeration (formula φ) i).val

def body (φ : (Expanded E).Formula (V ⊕ R)) :
    (Auxiliary E).Formula (Fin (count φ) ⊕ R) := RVFormula.abstractLeft (formula φ)

/-- Replacement under every inner guarded RV quantifier, with all
substructure compatibility hypotheses discharged. -/
theorem body_realize_substructure
    {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
    (X : LRV.Substructure C) [E.Structure (SubRV (X : Set C))]
    (v : V → X) (hv : ∀ i, iVF (v i).val) (r : R → SubRV (X : Set C))
    (φ : (Expanded E).Formula (V ⊕ R)) (hφ : Fragment φ) :
    letI := RVSubstructure.auxiliaryStructure (E := E) X
    letI := RVSubstructure.extraStructure (E := E) X
    (body φ).Realize (Sum.elim
      (fun i => RVSubstructure.coefficient X v hv (occurrence φ i)) r) ↔
      φ.Realize (Sum.elim v (RVSubstructure.inclusion X ∘ r)) := by
  letI := RVSubstructure.auxiliaryStructure (E := E) X
  letI := RVSubstructure.extraStructure (E := E) X
  have ha := RVFormula.abstractLeft_realize (formula φ)
    (RVSubstructure.coefficient X v hv) r
  have hb := RVSubstructure.formula_realize_substructure X v hv r
    (default : Fin 0 → SubRV (X : Set C)) φ hφ
  have h0 : RVSubstructure.inclusion X ∘ (default : Fin 0 → SubRV (X : Set C)) =
      (default : Fin 0 → X) := Subsingleton.elim _ _
  simpa only [body, occurrence, count, Formula.Realize, h0] using ha.trans hb

end SpecialTransformations.Section6.FiniteAbstraction
