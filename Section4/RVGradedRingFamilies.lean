import Section4.RVGradedRing
import Section4.RVFiniteGradedRing
import Section4.RVFiniteGradedRepresentatives

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def rvGradedRingFamilyClass (U : RVGradedObject (M := M) S) : RVGradedKRing (M := M) S :=
  rvGradedRingCompletion (rvGradedFamilyClass U)

theorem rvGradedRingFamily_difference_surjective (x : RVGradedKRing (M := M) S) :
    ∃ U V : RVGradedObject (M := M) S, x = rvGradedRingFamilyClass U - rvGradedRingFamilyClass V := by
  obtain ⟨a, b, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := rvGradedFamilyClass_surjective a
  obtain ⟨V, rfl⟩ := rvGradedFamilyClass_surjective b
  exact ⟨U, V, he⟩

def rvFiniteGradedRingFamilyClass (U : RVFiniteGradedObject (M := M) S) : RVFiniteGradedKRing (M := M) S :=
  rvFiniteGradedRingCompletion (rvFiniteGradedFamilyClass U)

theorem rvFiniteGradedRingFamily_difference_surjective (x : RVFiniteGradedKRing (M := M) S) :
    ∃ U V : RVFiniteGradedObject (M := M) S,
      x = rvFiniteGradedRingFamilyClass U - rvFiniteGradedRingFamilyClass V := by
  obtain ⟨a, b, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := rvFiniteGradedFamilyClass_surjective a
  obtain ⟨V, rfl⟩ := rvFiniteGradedFamilyClass_surjective b
  exact ⟨U, V, he⟩

end SpecialTransformations.Section4

end
