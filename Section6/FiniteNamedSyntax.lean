import Section6.NamedLanguage
import Section6.NativeOccurrence

/-! Finite parameter syntax in the actual named source language. FV
parameters remain native constants. RV parameters are also original base
constants. Mathlib substitution gives the semantics under every RV binder.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.FiniteNamedSyntax
open RVTermSupport NamedLanguage

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}} {β : Type} {r n m : ℕ}

def rvTuple (S X : LRV.Substructure C) (hSX : S ≤ X)
    (d : Fin m → SubRV (S : Set C)) : Fin m → SubRV (X : Set C) :=
  fun j => ⟨(d j).val, hSX (d j).property⟩

def substitution (S : LRV.Substructure C) (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ S) (d : Fin m → SubRV (S : Set C)) :
    (Fin r ⊕ Fin n) ⊕ (Fin m ⊕ β) → (Source E S).Term (Fin n ⊕ β)
  | .inl (.inl j) => Term.func (L := Source E S) (l := 0) (.inr ⟨(c j).val, hc j⟩) Fin.elim0
  | .inl (.inr i) => .var (.inl i)
  | .inr (.inl j) => Term.func (L := Source E S) (l := 0)
      (.inr ⟨(d j).val.val, (d j).property⟩) Fin.elim0
  | .inr (.inr b) => .var (.inr b)

def nameInput (S : LRV.Substructure C) (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ S) (d : Fin m → SubRV (S : Set C))
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ β))) :
    (Source E S).Formula (Fin n ⊕ β) :=
  ((LHom.sumInl : Expanded E →ᴸ Source E S).onBoundedFormula φ).subst (substitution S c hc d)

theorem nameInput_realize (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))] (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ S) (d : Fin m → SubRV (S : Set C))
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ β)))
    (x : Fin n → VF (M := C)) (hx : ∀ i, (x i).val ∈ X)
    (b : β → SubRV (X : Set C)) :
    letI := RVSubstructure.extraStructure (E := E) X
    ((@Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ (nameInput S c hc d φ)
      (Sum.elim (fun i => ⟨(x i).val, hx i⟩) (RVSubstructure.inclusion X ∘ b))) ↔
      φ.Realize (Sum.elim (NativeOccurrence.fvTuple X c (fun i => hSX (hc i)) x hx)
        (RVSubstructure.inclusion X ∘ Sum.elim (rvTuple S X hSX d) b))) := by
  letI := RVSubstructure.extraStructure (E := E) X
  letI := sourceStructure (E := E) S X hSX
  have he : (fun a => (substitution (E := E) S c hc d a).realize
      (Sum.elim (fun i => (⟨(x i).val, hx i⟩ : X)) (RVSubstructure.inclusion X ∘ b))) =
      Sum.elim (NativeOccurrence.fvTuple X c (fun i => hSX (hc i)) x hx)
        (RVSubstructure.inclusion X ∘ Sum.elim (rvTuple S X hSX d) b) := by
    funext a
    cases a with
    | inl a => cases a <;> rfl
    | inr a => cases a <;> rfl
  simp only [nameInput, Formula.Realize, BoundedFormula.realize_subst, he,
    LHom.realize_onBoundedFormula]

end SpecialTransformations.Section6.FiniteNamedSyntax
