module

public import Section6.NativeFormulaElimination
public import Section6.GeneratedDenaming

@[expose] public section

/-! The type comparison needed for Proposition 6.4 on two henselian
copies in a common native ACVF envelope. The VF-free comparison formula
is constructed by preparation and then denamed into the original free
context. Agreement on its type is used only after that construction.
The separate standard common-envelope existence bridge is not assumed
to follow from this theorem or from a definition of saturation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.CommonEnvelopeComparison
open RVTermSupport RVAbstraction RVGraphLanguage NamedLanguage

variable {C I β : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}}

@[instance_reducible] def expandedStructure (X : LRV.Substructure C)
    [E.Structure (SubRV (X : Set C))] : (Expanded E).Structure X := by
  letI := RVSubstructure.extraStructure (E := E) X
  exact inferInstance

def assignment (v : I → C) (X : LRV.Substructure C)
    (hBX : Substructure.closure LRV (Set.range v) ≤ X)
    (b : β → SubRV (X : Set C)) : I ⊕ β → X :=
  Sum.elim (fun i => ⟨v i, hBX (Substructure.subset_closure (Set.mem_range_self i))⟩)
    (RVSubstructure.inclusion X ∘ b)

theorem existential_type_invariant {r n : ℕ}
    (hcan : CanonicalStructure.IsCanonical (M := C))
    (s : I → SortTag) (z : I → C) (hz : ∀ i, sortEval (s i) (z i))
    (hdefs : RVQFDefinitions (Substructure.closure LRV (Set.range z)))
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v
      ((Substructure.closure LRV (Set.range z)) : Set C) N)
    (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ Substructure.closure LRV (Set.range z))
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin 0 ⊕ β))) (hφ : Fragment φ)
    (X Y : LRV.Substructure C)
    (hBX : Substructure.closure LRV (Set.range z) ≤ X)
    (hBY : Substructure.closure LRV (Set.range z) ≤ Y)
    [E.Structure (SubRV (X : Set C))] [E.Structure (SubRV (Y : Set C))]
    (hX : HenselianInputs X) (hY : HenselianInputs Y)
    (bX : β → SubRV (X : Set C)) (bY : β → SubRV (Y : Set C))
    (htype : ∀ χ : (Expanded E).Formula (I ⊕ β),
      ExpandedLogic.IsVFQF χ →
      ExpandedLogic.WellSorted (Sum.elim s (fun _ => .rv)) (fun _ => .rv) χ →
      (@Formula.Realize _ _ (expandedStructure (E := E) X) _ χ (assignment z X hBX bX) ↔
        @Formula.Realize _ _ (expandedStructure (E := E) Y) _ χ (assignment z Y hBY bY))) :
    (@Formula.Realize _ _ (sourceStructure (E := E)
        (Substructure.closure LRV (Set.range z)) X hBX) _
      (FVBinding.existsVF _ (FiniteNamedSyntax.nameInput _ c hc Fin.elim0 φ))
      (RVSubstructure.inclusion X ∘ bX) ↔
    @Formula.Realize _ _ (sourceStructure (E := E)
        (Substructure.closure LRV (Set.range z)) Y hBY) _
      (FVBinding.existsVF _ (FiniteNamedSyntax.nameInput _ c hc Fin.elim0 φ))
      (RVSubstructure.inclusion Y ∘ bY)) := by
  let B := Substructure.closure LRV (Set.range z)
  obtain ⟨ψ, ⟨θ, rfl⟩, he⟩ := native_formula_elimination B hdefs h00 v hv hObstacles
    c hc Fin.elim0 φ hφ
  obtain ⟨χ, hχ, hsχ, hχsem⟩ := GeneratedDenaming.dename_rv_formula hcan s z hz θ
  have hθX := hχsem X hBX bX
  have hθY := hχsem Y hBY bY
  have hsame := htype χ hχ hsχ
  have hXψ := fromAuxiliary_realize B X hBX θ bX
  have hYψ := fromAuxiliary_realize B Y hBY θ bY
  exact (he X hBX hX bX).trans
    (hXψ.symm.trans (hθX.symm.trans (hsame.trans (hθY.trans
      (hYψ.trans (he Y hBY hY bY).symm)))))

end SpecialTransformations.Section6.CommonEnvelopeComparison
