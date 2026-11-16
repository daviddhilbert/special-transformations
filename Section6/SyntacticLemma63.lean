module

public import Section6.NativeFormulaElimination
public import Section6.FiniteParameterSyntax

@[expose] public section

/-! The syntactic part of Lemma 6.3, with arbitrary original parameter
names rather than an assumed finite presentation. The input is the
RV-literal normal form supplied by the earlier sections. Its finite
parameter lists, finite occurrence map, replacement identity, complete
contraction graph and output formula are constructed in Section 6.
The output is chosen before X and its arbitrary RV expansion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6
open RVTermSupport RVAbstraction RVGraphLanguage NamedLanguage

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}} {β : Type} {n : ℕ}

abbrev SubVF (S : LRV.Substructure C) := {a : VF (M := C) // a.val ∈ S}

namespace OriginalParameterSyntax

def substitution (S : LRV.Substructure C) :
    (SubVF S ⊕ Fin n) ⊕ (SubRV (S : Set C) ⊕ β) → (Source E S).Term (Fin n ⊕ β)
  | .inl (.inl c) => .func (l := 0) (.inr ⟨c.val.val, c.property⟩) Fin.elim0
  | .inl (.inr i) => .var (.inl i)
  | .inr (.inl d) => .func (l := 0) (.inr ⟨d.val.val, d.property⟩) Fin.elim0
  | .inr (.inr b) => .var (.inr b)

def nameInput (S : LRV.Substructure C)
    (φ : (Expanded E).Formula ((SubVF S ⊕ Fin n) ⊕ (SubRV (S : Set C) ⊕ β))) :
    (Source E S).Formula (Fin n ⊕ β) :=
  ((LHom.sumInl : Expanded E →ᴸ Source E S).onBoundedFormula φ).subst (substitution S)

theorem nameInput_realize (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))]
    (φ : (Expanded E).Formula ((SubVF S ⊕ Fin n) ⊕ (SubRV (S : Set C) ⊕ β)))
    (x : Fin n → X) (b : β → SubRV (X : Set C)) :
    letI := RVSubstructure.extraStructure (E := E) X
    @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ (nameInput S φ)
      (Sum.elim x (RVSubstructure.inclusion X ∘ b)) ↔
      φ.Realize (Sum.elim (Sum.elim (fun c => (⟨c.val.val, hSX c.property⟩ : X)) x)
        (Sum.elim (fun d => (⟨d.val.val, hSX d.property⟩ : X))
          (RVSubstructure.inclusion X ∘ b))) := by
  letI := RVSubstructure.extraStructure (E := E) X
  letI := sourceStructure (E := E) S X hSX
  have he : (fun a => (substitution (E := E) (n := n) (β := β) S a).realize
      (Sum.elim x (RVSubstructure.inclusion X ∘ b))) =
      Sum.elim (Sum.elim (fun c : SubVF S => (⟨c.val.val, hSX c.property⟩ : X)) x)
        (Sum.elim (fun d : SubRV (S : Set C) => (⟨d.val.val, hSX d.property⟩ : X))
          (RVSubstructure.inclusion X ∘ b)) := by
    funext a
    rcases a with (c | i) | (d | b) <;> rfl
  simp only [nameInput, Formula.Realize, BoundedFormula.realize_subst, he,
    LHom.realize_onBoundedFormula]

end OriginalParameterSyntax

theorem syntactic_lemma_6_3
    (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v (S : Set C) N)
    (φ : (Expanded E).Formula ((SubVF S ⊕ Fin n) ⊕ (SubRV (S : Set C) ⊕ β)))
    (hφ : Fragment φ) :
    ∃ ψ : (Source E S).Formula β, RVQuantified S ψ ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))], HenselianInputs X →
        ∀ b : β → SubRV (X : Set C),
        (@Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
          (FVBinding.existsVF S (OriginalParameterSyntax.nameInput S φ))
          (RVSubstructure.inclusion X ∘ b) ↔
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ ψ
            (RVSubstructure.inclusion X ∘ b)) := by
  let c := fun i => (FiniteParameterSyntax.vfEnumeration φ i).val.val
  have hc : ∀ i, (c i).val ∈ S := fun i => (FiniteParameterSyntax.vfEnumeration φ i).val.property
  let d := fun i => (FiniteParameterSyntax.rvEnumeration φ i).val
  let θ := FiniteParameterSyntax.formula φ
  obtain ⟨ψ, hψ, he⟩ := native_formula_elimination S hdefs h00 v hv hObstacles c hc d θ
    (FiniteParameterSyntax.formula_fragment φ hφ)
  refine ⟨ψ, hψ, ?_⟩
  intro X hSX _ hH b
  letI := RVSubstructure.extraStructure (E := E) X
  have hpoint (a : PresentedSet.univ (pointSpace (M := C) n 0) (S : Set C))
      (ha : PointIn (X : Set C) a.val) :
      @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
        (OriginalParameterSyntax.nameInput S φ)
        (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b)) ↔
      @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
        (FiniteNamedSyntax.nameInput S c hc d θ)
        (Sum.elim (vfAssignment X a ha) (RVSubstructure.inclusion X ∘ b)) := by
    have h₁ := OriginalParameterSyntax.nameInput_realize S X hSX φ (vfAssignment X a ha) b
    have h₂ := FiniteParameterSyntax.formula_realize φ
      (fun c : SubVF S => (⟨c.val.val, hSX c.property⟩ : X)) (vfAssignment X a ha)
      (fun d : SubRV (S : Set C) => (⟨d.val.val, hSX d.property⟩ : X))
      (RVSubstructure.inclusion X ∘ b)
    have h₃ := FiniteNamedSyntax.nameInput_realize S X hSX c hc d θ (vfAt a.val)
      (fun i => ha (.inl i)) b
    have hargs :
        Sum.elim
          (Sum.elim (fun i => (⟨(FiniteParameterSyntax.vfEnumeration φ i).val.val.val,
            hSX (FiniteParameterSyntax.vfEnumeration φ i).val.property⟩ : X))
            (vfAssignment X a ha))
          (Sum.elim (fun i => (⟨(FiniteParameterSyntax.rvEnumeration φ i).val.val.val,
            hSX (FiniteParameterSyntax.rvEnumeration φ i).val.property⟩ : X))
            (RVSubstructure.inclusion X ∘ b)) =
        Sum.elim (NativeOccurrence.fvTuple X c (fun i => hSX (hc i)) (vfAt a.val)
          (fun i => ha (.inl i)))
          (RVSubstructure.inclusion X ∘ Sum.elim (FiniteNamedSyntax.rvTuple S X hSX d) b) := by
      funext j
      rcases j with (j | i) | (j | b) <;> rfl
    rw [hargs] at h₂
    exact h₁.trans (h₂.symm.trans h₃.symm)
  have hbind :
      @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
        (FVBinding.existsVF S (OriginalParameterSyntax.nameInput S φ))
        (RVSubstructure.inclusion X ∘ b) ↔
      @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
        (FVBinding.existsVF S (FiniteNamedSyntax.nameInput S c hc d θ))
        (RVSubstructure.inclusion X ∘ b) := by
    rw [FVBinding.existsVF_realize_points S X hSX,
      FVBinding.existsVF_realize_points S X hSX]
    exact exists_congr (fun a => exists_congr (fun ha => hpoint a ha))
  exact hbind.trans (he X hSX hH b)

end SpecialTransformations.Section6
