import Section4.VFFiniteScissors

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def vfFiniteForgetInvariant : PositiveAdditiveGrothendieck.Invariant
    (vfFiniteScissorPresentation (M := M) S) (A := VFAllKPlus (M := M) S) where
  toFun U := vfAllClass U.obj
  iso h := by
    obtain ⟨e⟩ := h
    exact vfAllClass_iso ((vfFiniteProperty S).ι.mapIso e)
  empty := vfAllClass_empty
  scissor h := vfAllClass_scissor h

def vfFiniteForgetKPlus : VFFiniteKPlus (M := M) S →+ VFAllKPlus (M := M) S :=
  PositiveAdditiveGrothendieck.lift (vfFiniteScissorPresentation S) vfFiniteForgetInvariant

@[simp] theorem vfFiniteForgetKPlus_class (U : VFFiniteAllObject (M := M) S) :
    vfFiniteForgetKPlus (vfFiniteClass U) = vfAllClass U.obj :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem vfFiniteClass_surjective : Function.Surjective (vfFiniteClass (M := M) (S := S)) :=
  PositiveAdditiveGrothendieck.of_surjective (vfFiniteScissorPresentation S)
    vfFiniteAllCoprodObject vfFiniteClass_coprod

theorem vfFiniteClass_eq_iff_iso {U V : VFFiniteAllObject (M := M) S} :
    vfFiniteClass U = vfFiniteClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    have he : vfAllClass U.obj = vfAllClass V.obj := by
      simpa only [vfFiniteForgetKPlus_class] using congrArg vfFiniteForgetKPlus h
    obtain ⟨e⟩ := vfAllClass_eq_iff_iso.mp he
    exact ⟨vfFiniteAllIsoOfAmbient e⟩
  · rintro ⟨e⟩
    exact vfFiniteClass_iso e

/-- Forgetting finite RV fibres adds no identifications to the actual
positive scissor quotient. No saturation or cancellation premise is used. -/
theorem vfFiniteForgetKPlus_injective :
    Function.Injective (vfFiniteForgetKPlus (M := M) (S := S)) := by
  intro a b h
  obtain ⟨U, rfl⟩ := vfFiniteClass_surjective a
  obtain ⟨V, rfl⟩ := vfFiniteClass_surjective b
  apply vfFiniteClass_eq_iff_iso.mpr
  have he : vfAllClass U.obj = vfAllClass V.obj := by
    simpa only [vfFiniteForgetKPlus_class] using h
  obtain ⟨e⟩ := vfAllClass_eq_iff_iso.mp he
  exact ⟨vfFiniteAllIsoOfAmbient e⟩

end SpecialTransformations.Section4

end
