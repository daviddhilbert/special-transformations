module

public import Section4.RVFiniteGradedSemiring
public import Section4.RVGradedRing

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

abbrev RVFiniteGradedKRing (S : Set M) := Algebra.GrothendieckAddGroup (RVFiniteGradedKPlus (M := M) S)

def rvFiniteGradedRingCompletion : RVFiniteGradedKPlus (M := M) S →+* RVFiniteGradedKRing (M := M) S :=
  Algebra.GrothendieckAddGroup.ofRingHom

def rvFiniteGradedRingClass {k : ℕ} (U : RVFiniteObject (M := M) S k) :
    RVFiniteGradedKRing (M := M) S := rvFiniteGradedRingCompletion (rvFiniteGradedClass U)

theorem rvFiniteGradedRingClass_product {k l : ℕ} (U : RVFiniteObject (M := M) S k)
    (V : RVFiniteObject (M := M) S l) :
    rvFiniteGradedRingClass (rvFiniteProductObject U V) = rvFiniteGradedRingClass U * rvFiniteGradedRingClass V := by
  change rvFiniteGradedRingCompletion (rvFiniteGradedClass (rvFiniteProductObject U V)) = _
  rw [rvFiniteGradedClass_product, map_mul]
  rfl

def rvFiniteGradedRingUniversalEquiv {R : Type} [CommRing R] :
    (RVFiniteGradedKPlus (M := M) S →+* R) ≃ (RVFiniteGradedKRing (M := M) S →+* R) :=
  Algebra.GrothendieckAddGroup.liftRingHom

def rvFiniteGradedRingForget : RVFiniteGradedKRing (M := M) S →+* RVGradedKRing (M := M) S :=
  Algebra.GrothendieckAddGroup.liftRingHom (rvGradedRingCompletion.comp rvFiniteGradedForgetSemiring)

end SpecialTransformations.Section4

end
