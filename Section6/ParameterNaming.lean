import Section6.RVGraphExpansion

/-! Substitute the original finite RV parameter tuple back into the
auxiliary formula. Pinned Mathlib substitution proves correctness below
all auxiliary quantifiers; no new substitution recursion is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.ParameterNaming
open RVAbstraction RVGraphExpansion

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}}

def auxiliaryInclusion (E : _root_.FirstOrder.Language.{0, 0}) (S : LRV.Substructure C) :
    Auxiliary E →ᴸ Auxiliary (NamedExtra E S) where
  onFunction := fun {_} f => match f with
    | .inl f => .inl f
    | .inr f => .inr (.inl f)
  onRelation := fun {_} r => match r with
    | .inl r => .inl r
    | .inr r => .inr (.inl r)

theorem auxiliary_expansion (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))] :
    letI := RVSubstructure.auxiliaryStructure (E := E) X
    letI := namedExtraStructure (E := E) S X hSX
    letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
    (auxiliaryInclusion E S).IsExpansionOn (SubRV (X : Set C)) := by
  letI := RVSubstructure.auxiliaryStructure (E := E) X
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  constructor
  · intro n f z
    cases f <;> rfl
  · intro n r z
    cases r <;> rfl

def substitution {β : Type} {r k : ℕ} (S : LRV.Substructure C)
    (d : Fin r → SubRV (S : Set C)) :
    Fin k ⊕ (Fin r ⊕ β) → (Auxiliary (NamedExtra E S)).Term (Fin k ⊕ β)
  | .inl i => .var (.inl i)
  | .inr (.inl j) => Term.func (L := Auxiliary (NamedExtra E S)) (l := 0)
      (.inr (.inr (d j))) Fin.elim0
  | .inr (.inr b) => .var (.inr b)

def nameFinite {β : Type} {r k : ℕ} (S : LRV.Substructure C)
    (d : Fin r → SubRV (S : Set C))
    (φ : (Auxiliary E).Formula (Fin k ⊕ (Fin r ⊕ β))) :
    (Auxiliary (NamedExtra E S)).Formula (Fin k ⊕ β) :=
  ((auxiliaryInclusion E S).onBoundedFormula φ).subst (substitution S d)

theorem nameFinite_realize {β : Type} {r k : ℕ}
    (S X : LRV.Substructure C) (hSX : S ≤ X)
    [E.Structure (SubRV (X : Set C))] (d : Fin r → SubRV (S : Set C))
    (φ : (Auxiliary E).Formula (Fin k ⊕ (Fin r ⊕ β)))
    (z : Fin k → SubRV (X : Set C)) (b : β → SubRV (X : Set C)) :
    letI := RVSubstructure.auxiliaryStructure (E := E) X
    letI := namedExtraStructure (E := E) S X hSX
    letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
    ((nameFinite S d φ).Realize (Sum.elim z b) ↔
      φ.Realize (Sum.elim z (Sum.elim (fun j => ⟨(d j).val, hSX (d j).property⟩) b))) := by
  letI := RVSubstructure.auxiliaryStructure (E := E) X
  letI := namedExtraStructure (E := E) S X hSX
  letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E S) X
  letI := auxiliary_expansion (E := E) S X hSX
  have he : (fun a => (substitution (E := E) (β := β) (k := k) S d a).realize
      (Sum.elim z b)) =
      Sum.elim z (Sum.elim (fun j => (⟨(d j).val, hSX (d j).property⟩ : SubRV (X : Set C))) b) := by
    funext a
    cases a with
    | inl i => rfl
    | inr a => cases a <;> rfl
  simp only [nameFinite, Formula.Realize, BoundedFormula.realize_subst, he,
    LHom.realize_onBoundedFormula]

end SpecialTransformations.Section6.ParameterNaming
