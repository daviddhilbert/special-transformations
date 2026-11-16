module

public import Section6.FiniteNamedSyntax
public import Section6.ParameterNaming
public import Section6.MapFormulaDescent
public import Section6.FVBinding

@[expose] public section

/-! The syntactic prepared-map argument for an actual RV-fragment
formula with finite original parameter tuples. Earlier FV-literal removal
is taken as given. Finite replacement, native leaf-map values, original
RV names, complete graph interpretation and source-language reconstruction
are all proved here, with no assumed existential-elimination premise.
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

namespace SpecialTransformations.Section6
open RVTermSupport RVAbstraction RVGraphLanguage RVGraphExpansion NamedLanguage

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}} {β : Type} {r n m : ℕ}

theorem native_formula_elimination_points
    (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v (S : Set C) N)
    (c : Fin r → VF (M := C)) (hc : ∀ i, (c i).val ∈ S)
    (d : Fin m → SubRV (S : Set C))
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ β))) (hφ : Fragment φ) :
    ∃ ψ : (Source E S).Formula β, RVQuantified S ψ ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))], HenselianInputs X →
        ∀ b : β → SubRV (X : Set C),
        ((∃ a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C),
          ∃ ha : PointIn (X : Set C) a.val,
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
            (FiniteNamedSyntax.nameInput S c hc d φ)
            (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b))) ↔
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ ψ
            (RVSubstructure.inclusion X ∘ b)) := by
  let A := PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C)
  let f := NativeTermMap.tupleMap A c hc (NativeOccurrence.native φ) (NativeOccurrence.native_sorted φ)
  let body := ParameterNaming.nameFinite S d (FiniteAbstraction.body φ)
  obtain ⟨ψ, hψ, he⟩ := map_formula_descent S hdefs h00 v hv hObstacles f body
  refine ⟨ψ, hψ, ?_⟩
  intro X hSX _ hH b
  letI := RVSubstructure.extraStructure (E := E) X
  letI := RVSubstructure.auxiliaryStructure (E := E) X
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  have hpoint (a : A) (ha : PointIn (X : Set C) a.val) :
      @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
        (FiniteNamedSyntax.nameInput S c hc d φ)
        (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b)) ↔
      ∃ z : Fin (FiniteAbstraction.count φ) → SubRV (X : Set C),
        (f a).val.2 = (fun i => (z i).val) ∧ body.Realize (Sum.elim z b) := by
    let x := vfAt a.val
    have hx : ∀ i, (x i).val ∈ X := fun i => ha (.inl i)
    let v₀ := NativeOccurrence.fvTuple X c (fun i => hSX (hc i)) x hx
    have hv₀ := NativeOccurrence.fvTuple_sorted X c (fun i => hSX (hc i)) x hx
    let z₀ : Fin (FiniteAbstraction.count φ) → SubRV (X : Set C) :=
      fun i => RVSubstructure.coefficient X v₀ hv₀ (FiniteAbstraction.occurrence φ i)
    have hz₀ : (fun i => (z₀ i).val) = (f a).val.2 := by
      funext i
      exact NativeOccurrence.coefficient_native X c (fun i => hSX (hc i)) x hx φ i
    have h₁ := FiniteNamedSyntax.nameInput_realize S X hSX c hc d φ x hx b
    have h₂ := FiniteAbstraction.body_realize_substructure X v₀ hv₀
      (Sum.elim (FiniteNamedSyntax.rvTuple S X hSX d) b) φ hφ
    have h₃ := ParameterNaming.nameFinite_realize S X hSX d (FiniteAbstraction.body φ) z₀ b
    have hmain :
        @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
          (FiniteNamedSyntax.nameInput S c hc d φ)
          (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b)) ↔
          body.Realize (Sum.elim z₀ b) := h₁.trans (h₂.symm.trans h₃.symm)
    rw [hmain]
    constructor
    · intro hb
      exact ⟨z₀, hz₀.symm, hb⟩
    · rintro ⟨z, hz, hb⟩
      have hzz : z₀ = z := by
        funext i
        apply Subtype.ext
        exact (congrFun hz₀ i).trans (congrFun hz i)
      simpa only [hzz] using hb
  have hinputs :
      (∃ a : A, ∃ ha : PointIn (X : Set C) a.val,
        @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
          (FiniteNamedSyntax.nameInput S c hc d φ)
          (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b))) ↔
      ∃ a : A, PointIn (X : Set C) a.val ∧
        ∃ z : Fin (FiniteAbstraction.count φ) → SubRV (X : Set C),
          (f a).val.2 = (fun i => (z i).val) ∧ body.Realize (Sum.elim z b) := by
    constructor
    · rintro ⟨a, ha, hφa⟩
      exact ⟨a, ha, (hpoint a ha).mp hφa⟩
    · rintro ⟨a, ha, hz⟩
      exact ⟨a, ha, (hpoint a ha).mpr hz⟩
  exact hinputs.trans (he X hSX hH b)

/-- Both sides are actual formulas of the original named source language.
The output formula is selected before X and all its RV interpretations. -/
theorem native_formula_elimination
    (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v (S : Set C) N)
    (c : Fin r → VF (M := C)) (hc : ∀ i, (c i).val ∈ S)
    (d : Fin m → SubRV (S : Set C))
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ β))) (hφ : Fragment φ) :
    ∃ ψ : (Source E S).Formula β, RVQuantified S ψ ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))], HenselianInputs X →
        ∀ b : β → SubRV (X : Set C),
        (@Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
          (FVBinding.existsVF S (FiniteNamedSyntax.nameInput S c hc d φ))
          (RVSubstructure.inclusion X ∘ b) ↔
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ ψ
            (RVSubstructure.inclusion X ∘ b)) := by
  obtain ⟨ψ, hψ, he⟩ := native_formula_elimination_points S hdefs h00 v hv hObstacles c hc d φ hφ
  refine ⟨ψ, hψ, ?_⟩
  intro X hSX _ hH b
  exact (FVBinding.existsVF_realize_points S X hSX
    (FiniteNamedSyntax.nameInput S c hc d φ) (RVSubstructure.inclusion X ∘ b)).trans
      (he X hSX hH b)

end SpecialTransformations.Section6
