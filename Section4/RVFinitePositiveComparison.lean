module

public import Section4.RVFiniteScissors

@[expose] public section

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def rvFiniteForgetInvariant :
    PositiveAdditiveGrothendieck.Invariant (rvFiniteScissorPresentation (M := M) S k)
      (A := RVKPlus (M := M) S k) where
  toFun U := rvClass U.obj
  iso h := by
    obtain ⟨e⟩ := h
    exact rvClass_iso ((finiteVolumeProperty S k).ι.mapIso e)
  empty := rvClass_empty
  scissor h := rvClass_scissor h

def rvFiniteForgetKPlus : RVFiniteKPlus (M := M) S k →+ RVKPlus (M := M) S k :=
  PositiveAdditiveGrothendieck.lift (rvFiniteScissorPresentation S k) rvFiniteForgetInvariant

@[simp] theorem rvFiniteForgetKPlus_class (U : RVFiniteObject (M := M) S k) :
    rvFiniteForgetKPlus (rvFiniteClass U) = rvClass U.obj :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

variable [hM : M ⊨ Axioms.ACVF]

theorem rvFiniteClass_surjective :
    Function.Surjective (rvFiniteClass (M := M) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (rvFiniteScissorPresentation S k)
    rvFiniteCoprodObject rvFiniteClass_coprod

theorem rvFiniteClass_eq_iff_iso {U V : RVFiniteObject (M := M) S k} :
    rvFiniteClass U = rvFiniteClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    have he : rvClass U.obj = rvClass V.obj := by
      simpa only [rvFiniteForgetKPlus_class] using congrArg rvFiniteForgetKPlus h
    obtain ⟨e⟩ := rvClass_eq_iff_iso.mp he
    exact ⟨rvFiniteIsoOfAmbient e⟩
  · rintro ⟨e⟩
    exact rvFiniteClass_iso e

/-- Forgetting finite volume creates no additional positive-class
identifications: ambient isomorphisms restrict to the full subcategory. -/
theorem rvFiniteForgetKPlus_injective :
    Function.Injective (rvFiniteForgetKPlus (M := M) (S := S) (k := k)) := by
  intro a b h
  obtain ⟨U, rfl⟩ := rvFiniteClass_surjective a
  obtain ⟨V, rfl⟩ := rvFiniteClass_surjective b
  apply rvFiniteClass_eq_iff_iso.mpr
  have he : rvClass U.obj = rvClass V.obj := by
    simpa only [rvFiniteForgetKPlus_class] using h
  obtain ⟨e⟩ := rvClass_eq_iff_iso.mp he
  exact ⟨rvFiniteIsoOfAmbient e⟩

end SpecialTransformations.Section4

end
