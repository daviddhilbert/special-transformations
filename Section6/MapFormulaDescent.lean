import Section6.NamedLanguage
import Section6.HenselianInputs
import Section5.GeneralExistence

/-! The generic syntactic descent engine, using the accepted general
definable-map preparation theorem. A complete graph formula is constructed,
its domain is retained, and the output lives in the original named source
language. The extra RV structure is chosen only on the substructure.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6
open RVAbstraction RVGraphLanguage RVGraphExpansion NamedLanguage

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}} {β : Type} {n m k : ℕ}

theorem map_formula_descent
    (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v (S : Set C) N)
    {A : DefSet (M := C) (S : Set C) n m} {D : DefSet (M := C) (S : Set C) 0 k}
    (f : Map A D) (body : (Auxiliary (NamedExtra E S)).Formula (Fin k ⊕ β)) :
    ∃ ψ : (Source E S).Formula β, RVQuantified S ψ ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))], HenselianInputs X →
        ∀ b : β → SubRV (X : Set C),
        letI := namedExtraStructure (E := E) S X hSX
        letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
        ((∃ a : A, PointIn (X : Set C) a.val ∧
          ∃ z : Fin k → SubRV (X : Set C),
            (f a).val.2 = (fun i => (z i).val) ∧ body.Realize (Sum.elim z b)) ↔
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ ψ
            (RVSubstructure.inclusion X ∘ b)) := by
  obtain ⟨l, B, T, _, hB, hf⟩ :=
    map_preparation h00 v hv hObstacles (SpecialBijection.refl A) f
  obtain ⟨graph, hgraph⟩ :=
    RVGraphExpansion.prepared_graph_formula (E := E) S hdefs f T hf (β := β)
  let ψ := RVFormula.assemble graph body
  refine ⟨fromAuxiliary S ψ, fromAuxiliary_rvQuantified S ψ, ?_⟩
  intro X hSX _ hH b
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  have hrv : ∀ a : VF (M := C), a.val ∈ X → (rv a).val ∈ X := by
    intro a ha
    exact X.fun_mem Fn.rvMap ![a.val] (by intro i; fin_cases i; exact ha)
  have hd := prepared_formula_elimination hH.dclClosed hSX hrv hH.rv_surjective T hB f hf
    graph (hgraph X hSX) body b
  exact hd.trans (fromAuxiliary_realize S X hSX ψ b)

end SpecialTransformations.Section6
