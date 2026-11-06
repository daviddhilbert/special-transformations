import Section6.PolynomialDescent
import Section6.RVGraphExpansion
import Section6.RVSourceFormula

/-! One actual RV formula for a finite polynomial tuple and an arbitrary
RV body. Preparation and the complete graph are selected before the
substructure, its extra RV structure and its free RV assignment. The
earlier RV normal form and Section 5 preparation are the only such inputs;
the graph-correctness premise of SyntacticDescent is discharged here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6
open RVAbstraction RVGraphLanguage RVGraphExpansion

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : Language} {β : Type} {n k : ℕ}

theorem polynomial_formula_descent
    (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v (S : Set C) N)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := C)))
    (hc : ∀ i d, ((p i).coeff d).val ∈ S)
    (body : (Auxiliary (NamedExtra E S)).Formula (Fin k ⊕ β)) :
    ∃ ψ : (Auxiliary (NamedExtra E S)).Formula β,
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))],
        NormalizedDclClosed (X : Set C) →
        (∀ t : RV (M := C), t.val ∈ X →
          ∃ a : VF (M := C), a.val ∈ X ∧ rv a = t) →
        ∀ b : β → SubRV (X : Set C),
        letI := namedExtraStructure (E := E) S X hSX
        letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
        ((∃ a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C),
          PointIn (X : Set C) a.val ∧
          ∃ z : Fin k → SubRV (X : Set C),
            (fun i => rv (MvPolynomial.eval (R := VF (M := C)) a.val.1 (p i))) =
              (fun i => (z i).val) ∧ body.Realize (Sum.elim z b)) ↔ ψ.Realize b) := by
  let A := PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C)
  let f := polynomialRVMap A p hc
  obtain ⟨l, B, T, _, hB, hf⟩ :=
    map_preparation h00 v hv hObstacles (SpecialBijection.refl A) f
  obtain ⟨graph, hgraph⟩ :=
    RVGraphExpansion.prepared_graph_formula (E := E) S hdefs f T hf (β := β)
  refine ⟨RVFormula.assemble graph body, ?_⟩
  intro X hSX _ hX hRV b
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  have hrv : ∀ a : VF (M := C), a.val ∈ X → (rv a).val ∈ X := by
    intro a ha
    exact X.fun_mem Fn.rvMap ![a.val] (by intro i; fin_cases i; exact ha)
  have he := prepared_formula_elimination hX hSX hrv hRV T hB f hf graph
    (hgraph X hSX) body b
  simpa only [f, polynomialRVMap_values] using he

/-- The descended expression is an actual VF-quantifier-free formula in
the expanded language, with a checked guarded-syntax witness. -/
theorem polynomial_source_formula_descent
    (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v (S : Set C) N)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := C)))
    (hc : ∀ i d, ((p i).coeff d).val ∈ S)
    (body : (Auxiliary (NamedExtra E S)).Formula (Fin k ⊕ β)) :
    ∃ ψ : (RVTermSupport.Expanded (NamedExtra E S)).Formula β,
      ExpandedLogic.IsVFQF ψ ∧
      ExpandedLogic.WellSorted (fun _ => .rv) (fun _ => .rv) ψ ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))],
        NormalizedDclClosed (X : Set C) →
        (∀ t : RV (M := C), t.val ∈ X →
          ∃ a : VF (M := C), a.val ∈ X ∧ rv a = t) →
        ∀ b : β → SubRV (X : Set C),
        letI := namedExtraStructure (E := E) S X hSX
        letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
        letI := RVSubstructure.extraStructure (E := NamedExtra E S) X
        ((∃ a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C),
          PointIn (X : Set C) a.val ∧
          ∃ z : Fin k → SubRV (X : Set C),
            (fun i => rv (MvPolynomial.eval (R := VF (M := C)) a.val.1 (p i))) =
              (fun i => (z i).val) ∧ body.Realize (Sum.elim z b)) ↔
            ψ.Realize (RVSubstructure.inclusion X ∘ b)) := by
  obtain ⟨ψ, he⟩ := polynomial_formula_descent S hdefs h00 v hv hObstacles p hc body
  refine ⟨RVSourceFormula.lift ψ, RVSourceFormula.lift_isVFQF ψ,
    RVSourceFormula.lift_wellSorted ψ, ?_⟩
  intro X hSX _ hX hRV b
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  letI := RVSubstructure.extraStructure (E := NamedExtra E S) X
  exact (he X hSX hX hRV b).trans (RVSourceFormula.lift_realize_substructure X ψ b).symm

end SpecialTransformations.Section6
