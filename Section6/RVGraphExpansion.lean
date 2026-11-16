module

public import Section6.RVGraphLanguage

@[expose] public section

/-! A full contraction graph in an arbitrary RV-only expansion, retaining
only named RV parameters from the original base. The native graph is
renamed into the auxiliary expansion; its correctness is transferred by
an actual language map, not by RV elementarity in the ambient ACVF model.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.RVGraphExpansion
open RVAbstraction RVGraphLanguage

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : Language}

def NamedExtra (E : Language) (S : LRV.Substructure C) : Language :=
  E.sum (constantsOn (SubRV (S : Set C)))

def graphInclusion (E : Language) (S : LRV.Substructure C) :
    RVBase[[SubRV (S : Set C)]] →ᴸ Auxiliary (NamedExtra E S) where
  onFunction := fun {_} f => match f with
    | .inl f => .inl f
    | .inr c => .inr (.inr c)
  onRelation := fun {_} r => match r with
    | .inl r => .inl r
    | .inr r => isEmptyElim r

@[instance_reducible] def namedExtraStructure (S X : LRV.Substructure C)
    (hSX : S ≤ X) [E.Structure (SubRV (X : Set C))] :
    (NamedExtra E S).Structure (SubRV (X : Set C)) := by
  change (E.sum (constantsOn (SubRV (S : Set C)))).Structure (SubRV (X : Set C))
  letI : (constantsOn (SubRV (S : Set C))).Structure (SubRV (X : Set C)) :=
    constantsOn.structure (fun s => ⟨s.val, hSX s.property⟩)
  exact inferInstance

theorem graph_expansion (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))] :
    letI := sourceWithParameters S X hSX
    letI := namedExtraStructure (E := E) S X hSX
    letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
    (graphInclusion E S).IsExpansionOn (SubRV (X : Set C)) := by
  letI := sourceWithParameters S X hSX
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  constructor
  · intro n f z
    cases f with
    | inl f => rfl
    | inr c =>
      cases n with
      | zero => rfl
      | succ n => exact isEmptyElim c
  · intro n r z
    cases r with
    | inl r => rfl
    | inr r => exact isEmptyElim r

/-- A graph formula is chosen before X and before the extra RV structure. -/
theorem prepared_graph_formula (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {β : Type} {n m l k : ℕ} {A : DefSet (M := C) (S : Set C) n m}
    {B : DefSet (M := C) (S : Set C) n l} {D : DefSet (M := C) (S : Set C) 0 k}
    (f : Map A D) (T : SpecialBijection A B)
    (hf : Contractible (Map.comp f T.inverseMap)) :
    ∃ ψ : (Auxiliary (NamedExtra E S)).Formula (Fin (n + l) ⊕ Fin k ⊕ β),
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))],
        letI := namedExtraStructure (E := E) S X hSX
        letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
        ContractionGraphFormula (X := (X : Set C)) f T ψ := by
  obtain ⟨φ, hφ⟩ := RVGraphLanguage.prepared_graph_formula S hdefs f T hf (β := β)
  refine ⟨(graphInclusion E S).onBoundedFormula φ, ?_⟩
  intro X hSX _
  letI := sourceWithParameters S X hSX
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  letI := graph_expansion (E := E) S X hSX
  intro y z b
  simpa only [Formula.Realize, LHom.realize_onBoundedFormula] using hφ X hSX y z b

end SpecialTransformations.Section6.RVGraphExpansion
