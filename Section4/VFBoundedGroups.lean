import Section4.VFFinitePositiveFiltration
import Section4.Imported.GrothendieckRing

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hcan : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
variable (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)

abbrev VFBoundedKGroup (k : ℕ) :=
  Algebra.GrothendieckAddGroup (VFBoundedKPlus hcan hs hsmall Γ hΓ k)

def vfBoundedGroupCompletion {k : ℕ} :
    VFBoundedKPlus hcan hs hsmall Γ hΓ k →+ VFBoundedKGroup hcan hs hsmall Γ hΓ k :=
  Algebra.GrothendieckAddGroup.of

def vfBoundedGroupClass {k : ℕ} (U : VFObject Γ (M := M) S k) :
    VFBoundedKGroup hcan hs hsmall Γ hΓ k :=
  vfBoundedGroupCompletion hcan hs hsmall Γ hΓ (vfBoundedClass hcan hs hsmall Γ hΓ U)

def vfBoundedGroupUniversalEquiv {k : ℕ} {G : Type} [AddCommGroup G] :
    (VFBoundedKPlus hcan hs hsmall Γ hΓ k →+ G) ≃
      (VFBoundedKGroup hcan hs hsmall Γ hΓ k →+ G) := Algebra.GrothendieckAddGroup.lift

theorem vfBoundedGroupClass_difference_surjective {k : ℕ}
    (x : VFBoundedKGroup hcan hs hsmall Γ hΓ k) :
    ∃ U V : VFObject Γ (M := M) S k,
      x = vfBoundedGroupClass hcan hs hsmall Γ hΓ U - vfBoundedGroupClass hcan hs hsmall Γ hΓ V := by
  obtain ⟨a, b, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := vfBoundedClass_surjective hcan hs hsmall Γ hΓ a
  obtain ⟨V, rfl⟩ := vfBoundedClass_surjective hcan hs hsmall Γ hΓ b
  exact ⟨U, V, he⟩

abbrev VFFiniteBoundedKGroup (k : ℕ) :=
  Algebra.GrothendieckAddGroup (VFFiniteBoundedKPlus hcan hs hsmall Γ hΓ k)

def vfFiniteBoundedGroupCompletion {k : ℕ} :
    VFFiniteBoundedKPlus hcan hs hsmall Γ hΓ k →+ VFFiniteBoundedKGroup hcan hs hsmall Γ hΓ k :=
  Algebra.GrothendieckAddGroup.of

def vfFiniteBoundedGroupClass {k : ℕ} (U : VFFiniteObject Γ (M := M) S k) :
    VFFiniteBoundedKGroup hcan hs hsmall Γ hΓ k :=
  vfFiniteBoundedGroupCompletion hcan hs hsmall Γ hΓ (vfFiniteBoundedClass hcan hs hsmall Γ hΓ U)

def vfFiniteBoundedGroupUniversalEquiv {k : ℕ} {G : Type} [AddCommGroup G] :
    (VFFiniteBoundedKPlus hcan hs hsmall Γ hΓ k →+ G) ≃
      (VFFiniteBoundedKGroup hcan hs hsmall Γ hΓ k →+ G) := Algebra.GrothendieckAddGroup.lift

theorem vfFiniteBoundedGroupClass_difference_surjective {k : ℕ}
    (x : VFFiniteBoundedKGroup hcan hs hsmall Γ hΓ k) :
    ∃ U V : VFFiniteObject Γ (M := M) S k,
      x = vfFiniteBoundedGroupClass hcan hs hsmall Γ hΓ U -
        vfFiniteBoundedGroupClass hcan hs hsmall Γ hΓ V := by
  obtain ⟨a, b, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := vfFiniteBoundedClass_surjective hcan hs hsmall Γ hΓ a
  obtain ⟨V, rfl⟩ := vfFiniteBoundedClass_surjective hcan hs hsmall Γ hΓ b
  exact ⟨U, V, he⟩

end SpecialTransformations.Section4

end
