module

public import Section4.VFAllSemiring
public import Section4.Imported.GrothendieckRing

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

abbrev VFAllKRing (S : Set M) := Algebra.GrothendieckAddGroup (VFAllKPlus (M := M) S)

def vfAllRingCompletion : VFAllKPlus (M := M) S →+* VFAllKRing (M := M) S :=
  Algebra.GrothendieckAddGroup.ofRingHom

def vfAllRingClass (U : VFAllObject (M := M) S) : VFAllKRing (M := M) S :=
  vfAllRingCompletion (vfAllClass U)

theorem vfAllRingClass_product (U V : VFAllObject (M := M) S) :
    vfAllRingClass (vfAllProductObject U V) = vfAllRingClass U * vfAllRingClass V := by
  change vfAllRingCompletion (vfAllClass (vfAllProductObject U V)) = _
  rw [← vfAllClass_mul, map_mul]
  rfl

def vfAllRingUniversalEquiv {R : Type} [CommRing R] :
    (VFAllKPlus (M := M) S →+* R) ≃ (VFAllKRing (M := M) S →+* R) :=
  Algebra.GrothendieckAddGroup.liftRingHom

theorem vfAllRingClass_difference_surjective (x : VFAllKRing (M := M) S) :
    ∃ U V : VFAllObject (M := M) S, x = vfAllRingClass U - vfAllRingClass V := by
  obtain ⟨a, b, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := vfAllClass_surjective a
  obtain ⟨V, rfl⟩ := vfAllClass_surjective b
  exact ⟨U, V, he⟩

end SpecialTransformations.Section4

end
