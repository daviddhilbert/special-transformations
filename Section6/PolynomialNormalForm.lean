import Section6.PolynomialFormulaDescent
import Section6.NamedLanguage
import Section6.HenselianInputs
import Section6.NativeOccurrence

/-! Apply prepared descent to an explicit earlier polynomial normal form.
The normal-form premise is pointwise replacement, not existential VF
elimination. Its polynomial tuple, body and coefficient scope are exposed.
The final formula is in the actual language with the original base named.
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
open RVAbstraction RVGraphLanguage RVGraphExpansion NamedLanguage

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}} {β : Type} {n : ℕ}

/-- The exact pointwise earlier normal-form input. The existential on the
right ranges only over the finite tuple of RV polynomial values; no VF
existential-elimination assertion is contained in this structure. -/
structure PolynomialNormalForm (S : LRV.Substructure C)
    (φ : (Source E S).Formula (Fin n ⊕ β)) where
  count : ℕ
  polynomials : Fin count → MvPolynomial (Fin n) (VF (M := C))
  coefficients : ∀ i d, ((polynomials i).coeff d).val ∈ S
  body : (Auxiliary (NamedExtra E S)).Formula (Fin count ⊕ β)
  correct : ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))]
    (a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C))
    (ha : PointIn (X : Set C) a.val) (b : β → SubRV (X : Set C)),
    letI := namedExtraStructure (E := E) S X hSX
    letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
    (@Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ φ
      (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b)) ↔
      ∃ z : Fin count → SubRV (X : Set C),
        (fun i => rv (MvPolynomial.eval (R := VF (M := C)) a.val.1 (polynomials i))) =
          (fun i => (z i).val) ∧ body.Realize (Sum.elim z b))

/-- One actual named-language RV formula works for every henselian
substructure and every interpretation of its extra RV signature. The
ordinary henselian/envelope data discharge closure through Lemma 6.2. -/
theorem normal_form_formula_descent
    (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v (S : Set C) N)
    (φ : (Source E S).Formula (Fin n ⊕ β)) (F : PolynomialNormalForm S φ) :
    ∃ ψ : (Source E S).Formula β, RVQuantified S ψ ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))], HenselianInputs X →
        ∀ b : β → SubRV (X : Set C),
        ((∃ a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C),
          ∃ ha : PointIn (X : Set C) a.val,
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ φ
            (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b))) ↔
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ ψ
            (RVSubstructure.inclusion X ∘ b)) := by
  obtain ⟨ψ, he⟩ := polynomial_formula_descent S hdefs h00 v hv hObstacles
    F.polynomials F.coefficients F.body
  refine ⟨fromAuxiliary S ψ, fromAuxiliary_rvQuantified S ψ, ?_⟩
  intro X hSX _ hH b
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  have hpoint :
      (∃ a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C),
        ∃ ha : PointIn (X : Set C) a.val,
        @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ φ
          (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b))) ↔
      ∃ a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C),
        PointIn (X : Set C) a.val ∧
        ∃ z : Fin F.count → SubRV (X : Set C),
          (fun i => rv (MvPolynomial.eval (R := VF (M := C)) a.val.1 (F.polynomials i))) =
            (fun i => (z i).val) ∧ F.body.Realize (Sum.elim z b) := by
    constructor
    · rintro ⟨a, ha, hφ⟩
      exact ⟨a, ha, (F.correct X hSX a ha b).mp hφ⟩
    · rintro ⟨a, ha, hz⟩
      exact ⟨a, ha, (F.correct X hSX a ha b).mpr hz⟩
  exact hpoint.trans ((he X hSX hH.dclClosed hH.rv_surjective b).trans
    (fromAuxiliary_realize S X hSX ψ b))

end SpecialTransformations.Section6
