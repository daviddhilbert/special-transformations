import Section6.RVGraphExpansion
import Section6.RVSourceFormula

/-! Name the original base in the source language. FV constants stay in
the native parameter expansion; only RV constants are introduced into the
auxiliary language. The final renaming adds no quantifiers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.NamedLanguage
open RVTermSupport RVAbstraction RVGraphExpansion

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}}

abbrev Source (E : _root_.FirstOrder.Language.{0, 0}) (S : LRV.Substructure C) :=
  (Expanded E)[[(S : Set C)]]

@[instance_reducible] def sourceStructure (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))] : (Source E S).Structure X := by
  letI := RVSubstructure.extraStructure (E := E) X
  letI : (constantsOn (S : Set C)).Structure X :=
    constantsOn.structure (fun s => ⟨s.val, hSX s.property⟩)
  exact inferInstance

def rvParameter (S : LRV.Substructure C) : SubRV (S : Set C) → S :=
  fun r => ⟨r.val.val, r.property⟩

def nameRV (E : _root_.FirstOrder.Language.{0, 0}) (S : LRV.Substructure C) :
    Expanded (NamedExtra E S) →ᴸ Source E S :=
  ((LHom.sumInl : Expanded E →ᴸ Source E S).comp LHom.sumInl).sumElim
    (((LHom.sumInl : Expanded E →ᴸ Source E S).comp LHom.sumInr).sumElim
      ((LHom.sumInr : constantsOn (S : Set C) →ᴸ Source E S).comp
        (LHom.constantsOnMap (rvParameter S))))

theorem names_expansion (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))] :
    letI := namedExtraStructure (E := E) S X hSX
    letI := RVSubstructure.extraStructure (E := NamedExtra E S) X
    letI := sourceStructure (E := E) S X hSX
    (nameRV E S).IsExpansionOn X := by
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.extraStructure (E := NamedExtra E S) X
  letI := sourceStructure (E := E) S X hSX
  constructor
  · intro n f z
    cases f with
    | inl f => rfl
    | inr f =>
      cases f with
      | inl f => rfl
      | inr c =>
        cases n with
        | succ n => exact isEmptyElim c
        | zero =>
          change (⟨c.val.val, hSX c.property⟩ : X) =
            (if _h : ∀ i : Fin 0, iRV (z i).val then
              RVSubstructure.inclusion X (⟨c.val, hSX c.property⟩ : SubRV (X : Set C))
            else RVSubstructure.inclusion X (RVSubstructure.zero X))
          rw [dif_pos (fun i => i.elim0)]
          rfl
  · intro n r z
    cases r with
    | inl r => rfl
    | inr r => cases r with
      | inl r => rfl
      | inr r => exact isEmptyElim r

def fromAuxiliary {β : Type} (S : LRV.Substructure C)
    (φ : (Auxiliary (NamedExtra E S)).Formula β) : (Source E S).Formula β :=
  (nameRV E S).onBoundedFormula (RVSourceFormula.lift φ)

/-- A syntactic witness in the actual RV reduct, retaining the original
RV parameter names. This stronger witness also permits their subsequent
replacement by native terms after adjoining free VF parameters. It has
no semantic-equivalence or elimination premise. -/
def RVQuantified {β : Type} (S : LRV.Substructure C) (φ : (Source E S).Formula β) : Prop :=
  ∃ χ : (Auxiliary (NamedExtra E S)).Formula β, fromAuxiliary S χ = φ

theorem fromAuxiliary_rvQuantified {β : Type} (S : LRV.Substructure C)
    (φ : (Auxiliary (NamedExtra E S)).Formula β) : RVQuantified S (fromAuxiliary S φ) :=
  ⟨φ, rfl⟩

theorem RVQuantified.guarded {β : Type} {S : LRV.Substructure C}
    {φ : (Source E S).Formula β} (h : RVQuantified S φ) :
    ∃ χ : (Expanded (NamedExtra E S)).Formula β,
      ExpandedLogic.IsVFQF χ ∧
      ExpandedLogic.WellSorted (fun _ => .rv) (fun _ => .rv) χ ∧
      (nameRV E S).onBoundedFormula χ = φ := by
  obtain ⟨χ, rfl⟩ := h
  exact ⟨_, RVSourceFormula.lift_isVFQF χ, RVSourceFormula.lift_wellSorted χ, rfl⟩

theorem fromAuxiliary_realize {β : Type} (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))]
    (φ : (Auxiliary (NamedExtra E S)).Formula β) (b : β → SubRV (X : Set C)) :
    letI := namedExtraStructure (E := E) S X hSX
    letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
    (φ.Realize b ↔ @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
      (fromAuxiliary S φ) (RVSubstructure.inclusion X ∘ b)) := by
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  letI := RVSubstructure.extraStructure (E := NamedExtra E S) X
  letI := sourceStructure (E := E) S X hSX
  letI := names_expansion (E := E) S X hSX
  have he := RVSourceFormula.lift_realize_substructure X φ b
  simpa only [fromAuxiliary, Formula.Realize, LHom.realize_onBoundedFormula] using he.symm

end SpecialTransformations.Section6.NamedLanguage
