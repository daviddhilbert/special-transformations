module

public import Section4.RVRestrictions
public import Section4.FiniteGluing
public import Section4.PositiveAdditivePresentation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

/-- The actual scissor relation for restrictions of a single RV object.
The inherited volume map is retained on all four definable subsets. -/
def RVScissor (A B C D : RVObject (M := M) S k) : Prop :=
  ∃ U : RVObject (M := M) S k,
    ∃ X Y : DefSet (rawRVSpace (M := M) U.arity) S,
    ∃ hX : X.carrier ⊆ U.domain.carrier, ∃ hY : Y.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧ B = U.restrict Y hY ∧
      C = U.restrict (X.union Y) (fun _ h => h.elim (fun hx => hX hx) (fun hy => hY hy)) ∧
      D = U.restrict (X.inter Y) (fun _ h => hX h.1)

def rvScissorPresentation (S : Set M) (k : ℕ) :
    PositiveAdditiveGrothendieck.Presentation (RVObject (M := M) S k) where
  iso U V := Nonempty (U ≅ V)
  empty := RVObject.empty S k
  scissor := RVScissor

/-- Section 4.3's positive additive quotient for the actual fixed-degree
RV category. The comparison with single isomorphism classes is separate. -/
abbrev RVKPlus (S : Set M) (k : ℕ) :=
  PositiveAdditiveGrothendieck.KPlus (rvScissorPresentation (M := M) S k)

def rvClass (U : RVObject (M := M) S k) : RVKPlus (M := M) S k :=
  PositiveAdditiveGrothendieck.of (rvScissorPresentation S k) U

theorem rvClass_iso {U V : RVObject (M := M) S k} (e : U ≅ V) : rvClass U = rvClass V :=
  PositiveAdditiveGrothendieck.of_iso (rvScissorPresentation S k) ⟨e⟩

@[simp] theorem rvClass_empty : rvClass (RVObject.empty (M := M) S k) = 0 :=
  PositiveAdditiveGrothendieck.of_empty (rvScissorPresentation S k)

theorem rvClass_scissor {A B C D : RVObject (M := M) S k} (h : RVScissor A B C D) :
    rvClass A + rvClass B = rvClass C + rvClass D :=
  PositiveAdditiveGrothendieck.of_scissor (rvScissorPresentation S k) h

def rvScissorUniversalEquiv {N : Type} [AddCommMonoid N] :
    PositiveAdditiveGrothendieck.Invariant (rvScissorPresentation (M := M) S k) (A := N) ≃
      (RVKPlus (M := M) S k →+ N) :=
  PositiveAdditiveGrothendieck.universalEquiv (rvScissorPresentation S k)

variable [hM : M ⊨ Axioms.ACVF]

theorem rvPadObject_empty : rvPadObject (RVObject.empty (M := M) S k) =
    RVObject.empty S (k + 1) := by
  change RVObject.mk 0 (DefSet.empty (rawRVSpace 0) S) _ = RVObject.mk 0 _ _
  congr 1
  apply Map.ext
  intro a
  exact False.elim a.property

theorem RVScissor.pad {A B C D : RVObject (M := M) S k} (h : RVScissor A B C D) :
    RVScissor (rvPadObject A) (rvPadObject B) (rvPadObject C) (rvPadObject D) := by
  obtain ⟨U, X, Y, hX, hY, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨rvPadObject U, X, Y, hX, hY, rvPadObject_restrict U X hX,
    rvPadObject_restrict U Y hY, rvPadObject_restrict U (X.union Y) _,
    rvPadObject_restrict U (X.inter Y) _⟩

def rvPaddingClassInvariant :
    PositiveAdditiveGrothendieck.Invariant (rvScissorPresentation (M := M) S k)
      (A := RVKPlus (M := M) S (k + 1)) where
  toFun U := rvClass (rvPadObject U)
  iso h := by
    obtain ⟨e⟩ := h
    exact rvClass_iso ((rvPaddingFunctor S k).mapIso e)
  empty := by
    change rvClass (rvPadObject (RVObject.empty S k)) = 0
    rw [rvPadObject_empty, rvClass_empty]
  scissor h := rvClass_scissor h.pad

/-- Padding preserves the actual scissor relations and hence induces the
positive semigroup homomorphism. Injectivity requires its own proof. -/
def rvPaddingKPlus : RVKPlus (M := M) S k →+ RVKPlus (M := M) S (k + 1) :=
  PositiveAdditiveGrothendieck.lift (rvScissorPresentation S k) rvPaddingClassInvariant

@[simp] theorem rvPaddingKPlus_class (U : RVObject (M := M) S k) :
    rvPaddingKPlus (rvClass U) = rvClass (rvPadObject U) :=
  PositiveAdditiveGrothendieck.lift_of (rvScissorPresentation S k) rvPaddingClassInvariant U

end SpecialTransformations.Section4

end
