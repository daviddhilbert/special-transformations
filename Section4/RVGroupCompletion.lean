module

public import Section4.RVRepresentatives
public import Section4.Imported.GrothendieckRing

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

/-- Groupification of the actual fixed-degree positive scissor monoid. -/
abbrev RVKGroup (S : Set M) (k : ℕ) :=
  Algebra.GrothendieckAddGroup (RVKPlus (M := M) S k)

def rvGroupCompletion : RVKPlus (M := M) S k →+ RVKGroup (M := M) S k :=
  Algebra.GrothendieckAddGroup.of

def rvGroupClass (U : RVObject (M := M) S k) : RVKGroup (M := M) S k :=
  rvGroupCompletion (rvClass U)

/-- Additive scissor invariants into any commutative group extend
uniquely across groupification; cancellation is not assumed. -/
def rvGroupUniversalEquiv {G : Type} [AddCommGroup G] :
    PositiveAdditiveGrothendieck.Invariant (rvScissorPresentation (M := M) S k) (A := G) ≃
      (RVKGroup (M := M) S k →+ G) :=
  rvScissorUniversalEquiv.trans Algebra.GrothendieckAddGroup.lift

theorem rvGroupUniversalEquiv_class {G : Type} [AddCommGroup G]
    (f : PositiveAdditiveGrothendieck.Invariant (rvScissorPresentation (M := M) S k)
      (A := G)) (U : RVObject (M := M) S k) :
    rvGroupUniversalEquiv f (rvGroupClass U) = f.toFun U := by
  change Algebra.GrothendieckAddGroup.lift
    (PositiveAdditiveGrothendieck.lift _ f)
    (Algebra.GrothendieckAddGroup.of (rvClass U)) = _
  rw [Algebra.GrothendieckAddGroup.lift_apply_of]
  exact PositiveAdditiveGrothendieck.lift_of (rvScissorPresentation S k) f U

variable [hM : M ⊨ Axioms.ACVF]

theorem rvGroupClass_difference_surjective (x : RVKGroup (M := M) S k) :
    ∃ U V : RVObject (M := M) S k, x = rvGroupClass U - rvGroupClass V := by
  obtain ⟨a, b, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  obtain ⟨V, rfl⟩ := rvClass_surjective b
  exact ⟨U, V, he⟩

end SpecialTransformations.Section4

end
