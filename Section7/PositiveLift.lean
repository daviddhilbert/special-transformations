import Section7.LiftedIsomorphism
import Section4.RVFiniteScissors
import Section4.VFFinitePositiveFiltration

/-!
# Lifting on the two actual positive scissors quotients

The inputs are the actual fixed-degree categories from Section 4.
Isomorphisms descend by Theorem 7.6 and empty and scissors relations
descend by the canonical lift construction. Surjectivity is reduced to
the checked Section 5 representation theorem in the next module.
-/

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]
variable (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded) (k : ℕ)

def positiveLiftInvariant :
    PositiveAdditiveGrothendieck.Invariant (rvScissorPresentation B.real k)
      (A := VFBoundedKPlus hcan hs hsmall Δ hΔ k) where
  toFun U := vfBoundedClass hcan hs hsmall Δ hΔ (rvLiftObject Δ U)
  iso := by
    rintro U V ⟨e⟩
    obtain ⟨f⟩ := rvLiftObject_iso_of_rvIso hcan hκ hs h00 B hsmall hB v hv Δ e
    exact Subtype.ext (vfAllClass_iso f)
  empty := by
    apply Subtype.ext
    change vfAllClass (rvLiftObject Δ (RVObject.empty B.real k)).obj = 0
    rw [vfAllClass_iso (rvLift_empty_iso Δ), vfAllClass_empty]
  scissor := by
    intro U V W X h
    apply Subtype.ext
    exact vfAllClass_scissor (rvLift_scissor Δ h)

def positiveLift : RVKPlus (M := M) B.real k →+
    VFBoundedKPlus hcan hs hsmall Δ hΔ k :=
  PositiveAdditiveGrothendieck.lift (rvScissorPresentation B.real k)
    (positiveLiftInvariant hcan hκ hs h00 B hsmall hB v hv Δ hΔ k)

@[simp] theorem positiveLift_class (U : RVObject (M := M) B.real k) :
    positiveLift hcan hκ hs h00 B hsmall hB v hv Δ hΔ k (rvClass U) =
      vfBoundedClass hcan hs hsmall Δ hΔ (rvLiftObject Δ U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def positiveFiniteLiftInvariant :
    PositiveAdditiveGrothendieck.Invariant (rvFiniteScissorPresentation B.real k)
      (A := VFFiniteBoundedKPlus hcan hs hsmall Δ hΔ k) where
  toFun U := vfFiniteBoundedClass hcan hs hsmall Δ hΔ (rvLiftFiniteObject Δ U)
  iso := by
    rintro U V ⟨e⟩
    obtain ⟨f⟩ := rvLiftObject_iso_of_rvIso hcan hκ hs h00 B hsmall hB v hv Δ
      ((finiteVolumeProperty B.real k).ι.mapIso e)
    exact (vfFiniteBoundedClass_eq_iff_iso hcan hs hsmall Δ hΔ _ _).mpr
      ⟨vfFiniteBoundedIsoOfAmbient Δ f⟩
  empty := by
    apply Subtype.ext
    change vfFiniteClass _ = 0
    have f : (rvLiftObject Δ (RVObject.empty (M := M) B.real k)).obj ≅ vfAllEmptyObject B.real :=
      rvLift_empty_iso Δ
    exact (vfFiniteClass_iso (vfFiniteAllIsoOfAmbient f)).trans vfFiniteClass_empty
  scissor := by
    intro U V W X h
    exact vfFiniteBoundedClass_scissor hcan hs hsmall Δ hΔ _ _ _ _ (rvLift_scissor Δ h)

def positiveFiniteLift : RVFiniteKPlus (M := M) B.real k →+
    VFFiniteBoundedKPlus hcan hs hsmall Δ hΔ k :=
  PositiveAdditiveGrothendieck.lift (rvFiniteScissorPresentation B.real k)
    (positiveFiniteLiftInvariant hcan hκ hs h00 B hsmall hB v hv Δ hΔ k)

@[simp] theorem positiveFiniteLift_class (U : RVFiniteObject (M := M) B.real k) :
    positiveFiniteLift hcan hκ hs h00 B hsmall hB v hv Δ hΔ k (rvFiniteClass U) =
      vfFiniteBoundedClass hcan hs hsmall Δ hΔ (rvLiftFiniteObject Δ U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem positiveLift_surjective_of_representation
    (hrep : ∀ X : VFObject Δ (M := M) B.real k,
      ∃ U : RVObject (M := M) B.real k, Nonempty (X ≅ rvLiftObject Δ U)) :
    Function.Surjective (positiveLift hcan hκ hs h00 B hsmall hB v hv Δ hΔ k) := by
  intro x
  obtain ⟨X, rfl⟩ := vfBoundedClass_surjective hcan hs hsmall Δ hΔ x
  obtain ⟨U, he⟩ := hrep X
  refine ⟨rvClass U, ?_⟩
  rw [positiveLift_class]
  exact ((vfBoundedClass_eq_iff_iso hcan hs hsmall Δ hΔ _ _).mpr he).symm

theorem positiveFiniteLift_surjective_of_representation
    (hrep : ∀ X : VFFiniteObject Δ (M := M) B.real k,
      ∃ U : RVFiniteObject (M := M) B.real k, Nonempty (X ≅ rvLiftFiniteObject Δ U)) :
    Function.Surjective (positiveFiniteLift hcan hκ hs h00 B hsmall hB v hv Δ hΔ k) := by
  intro x
  obtain ⟨X, rfl⟩ := vfFiniteBoundedClass_surjective hcan hs hsmall Δ hΔ x
  obtain ⟨U, he⟩ := hrep X
  refine ⟨rvFiniteClass U, ?_⟩
  rw [positiveFiniteLift_class]
  exact ((vfFiniteBoundedClass_eq_iff_iso hcan hs hsmall Δ hΔ _ _).mpr he).symm

end SpecialTransformations.Section7
