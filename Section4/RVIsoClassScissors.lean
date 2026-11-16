module

public import Section4.RVIsomorphismClasses
public import Section4.RVUnionCoproduct
public import Section4.RVScissorPresentation
public import Mathlib.Tactic.Tauto

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem rvIsoClass_disjoint_union (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    (hd : Disjoint A.carrier B.carrier) :
    rvIsoClass (U.restrict (A.union B) (rvUnionSubset U A B hA hB)) =
      rvIsoClass (U.restrict A hA) + rvIsoClass (U.restrict B hB) := by
  rw [← rvIsoClass_iso (rvCoprodUnionIso U A B hA hB hd), rvIsoClass_coprod]

/-- Scissors already hold among actual isomorphism classes: split X into
X\Y and X∩Y, and split X∪Y into X\Y and Y. No cancellation is used. -/
theorem rvIsoClass_scissor {A B C D : RVObject (M := M) S k} (h : RVScissor A B C D) :
    rvIsoClass A + rvIsoClass B = rvIsoClass C + rvIsoClass D := by
  obtain ⟨U, X, Y, hX, hY, rfl, rfl, rfl, rfl⟩ := h
  let E := X.sdiff Y
  let I := X.inter Y
  have hE : E.carrier ⊆ U.domain.carrier := fun _ he => hX he.1
  have hI : I.carrier ⊆ U.domain.carrier := fun _ hi => hX hi.1
  have hdI : Disjoint E.carrier I.carrier := by
    apply Set.disjoint_left.mpr
    intro x he hi
    exact he.2 hi.2
  have hdY : Disjoint E.carrier Y.carrier := by
    apply Set.disjoint_left.mpr
    intro x he hy
    exact he.2 hy
  have heX : (E.union I).carrier = X.carrier := by
    ext x
    change (x ∈ X.carrier ∧ x ∉ Y.carrier) ∨
      (x ∈ X.carrier ∧ x ∈ Y.carrier) ↔ x ∈ X.carrier
    tauto
  have heU : (E.union Y).carrier = (X.union Y).carrier := by
    ext x
    change (x ∈ X.carrier ∧ x ∉ Y.carrier) ∨ x ∈ Y.carrier ↔
      x ∈ X.carrier ∨ x ∈ Y.carrier
    tauto
  have hsplitX := rvIsoClass_disjoint_union U E I hE hI hdI
  have hsplitU := rvIsoClass_disjoint_union U E Y hE hY hdY
  rw [U.restrict_eq_of_carrier_eq _ X _ hX heX] at hsplitX
  rw [U.restrict_eq_of_carrier_eq _ (X.union Y) _ (rvUnionSubset U X Y hX hY) heU] at hsplitU
  rw [hsplitX, hsplitU]
  ac_rfl

def rvIsoClassInvariant :
    PositiveAdditiveGrothendieck.Invariant (rvScissorPresentation (M := M) S k)
      (A := RVIsoClasses (M := M) S k) where
  toFun := rvIsoClass
  iso h := rvIsoClass_eq_iff.mpr h
  empty := rvIsoClass_empty
  scissor := rvIsoClass_scissor

def rvKPlusToIsoClasses : RVKPlus (M := M) S k →+ RVIsoClasses (M := M) S k :=
  PositiveAdditiveGrothendieck.lift (rvScissorPresentation S k) rvIsoClassInvariant

@[simp] theorem rvKPlusToIsoClasses_class (U : RVObject (M := M) S k) :
    rvKPlusToIsoClasses (rvClass U) = rvIsoClass U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

end SpecialTransformations.Section4

end
