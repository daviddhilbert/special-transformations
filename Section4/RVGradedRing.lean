module

public import Section4.RVGradedSemiring
public import Section4.Imported.GrothendieckRing

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

abbrev RVGradedKRing (S : Set M) := Algebra.GrothendieckAddGroup (RVGradedKPlus (M := M) S)

def rvGradedRingCompletion : RVGradedKPlus (M := M) S →+* RVGradedKRing (M := M) S :=
  Algebra.GrothendieckAddGroup.ofRingHom

def rvGradedRingClass {k : ℕ} (U : RVObject (M := M) S k) : RVGradedKRing (M := M) S :=
  rvGradedRingCompletion (rvGradedClass U)

theorem rvGradedRingClass_product {k l : ℕ} (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) :
    rvGradedRingClass (rvProductObject U V) = rvGradedRingClass U * rvGradedRingClass V := by
  change rvGradedRingCompletion (rvGradedClass (rvProductObject U V)) = _
  rw [rvGradedClass_product, map_mul]
  rfl

def rvGradedRingUniversalEquiv {R : Type} [CommRing R] :
    (RVGradedKPlus (M := M) S →+* R) ≃ (RVGradedKRing (M := M) S →+* R) :=
  Algebra.GrothendieckAddGroup.liftRingHom

end SpecialTransformations.Section4

end
