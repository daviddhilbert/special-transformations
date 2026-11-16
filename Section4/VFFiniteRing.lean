module

public import Section4.VFFiniteSemiring
public import Section4.Imported.GrothendieckRing

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

abbrev VFFiniteKRing (S : Set M) := Algebra.GrothendieckAddGroup (VFFiniteKPlus (M := M) S)

def vfFiniteRingCompletion : VFFiniteKPlus (M := M) S →+* VFFiniteKRing (M := M) S :=
  Algebra.GrothendieckAddGroup.ofRingHom

def vfFiniteRingClass (U : VFFiniteAllObject (M := M) S) : VFFiniteKRing (M := M) S :=
  vfFiniteRingCompletion (vfFiniteClass U)

theorem vfFiniteRingClass_product (U V : VFFiniteAllObject (M := M) S) :
    vfFiniteRingClass (vfFiniteAllProductObject U V) = vfFiniteRingClass U * vfFiniteRingClass V := by
  change vfFiniteRingCompletion (vfFiniteClass (vfFiniteAllProductObject U V)) = _
  rw [← vfFiniteClass_mul, map_mul]
  rfl

def vfFiniteRingUniversalEquiv {R : Type} [CommRing R] :
    (VFFiniteKPlus (M := M) S →+* R) ≃ (VFFiniteKRing (M := M) S →+* R) :=
  Algebra.GrothendieckAddGroup.liftRingHom

theorem vfFiniteRingClass_difference_surjective (x : VFFiniteKRing (M := M) S) :
    ∃ U V : VFFiniteAllObject (M := M) S, x = vfFiniteRingClass U - vfFiniteRingClass V := by
  obtain ⟨a, b, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := vfFiniteClass_surjective a
  obtain ⟨V, rfl⟩ := vfFiniteClass_surjective b
  exact ⟨U, V, he⟩

end SpecialTransformations.Section4

end
