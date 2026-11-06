import Section4.RVGrading
import Section4.RVCoproduct

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def rvGradedCoprod (U V : RVGradedObject (M := M) S) : RVGradedObject (M := M) S := by
  refine ⟨fun k => rvCoprodObject (U.obj k) (V.obj k), ?_⟩
  apply (U.property.union V.property).subset
  intro k hk
  exact (rvCoprod_nonempty_iff (U.obj k) (V.obj k)).mp hk

def rvGradedCoprodInl (U V : RVGradedObject (M := M) S) : U ⟶ rvGradedCoprod U V :=
  ObjectProperty.homMk (fun k => rvCoprodInl (U.obj k) (V.obj k))

def rvGradedCoprodInr (U V : RVGradedObject (M := M) S) : V ⟶ rvGradedCoprod U V :=
  ObjectProperty.homMk (fun k => rvCoprodInr (U.obj k) (V.obj k))

def rvGradedCoprodDesc {U V W : RVGradedObject (M := M) S} (f : U ⟶ W) (g : V ⟶ W) :
    rvGradedCoprod U V ⟶ W :=
  ObjectProperty.homMk (fun k => rvCoprodDesc (f.hom k) (g.hom k))

theorem rvGradedCoprod_inl_desc {U V W : RVGradedObject (M := M) S} (f : U ⟶ W) (g : V ⟶ W) :
    rvGradedCoprodInl U V ≫ rvGradedCoprodDesc f g = f := by
  apply ObjectProperty.hom_ext
  funext k
  exact rvCoprodInl_desc (f.hom k) (g.hom k)

theorem rvGradedCoprod_inr_desc {U V W : RVGradedObject (M := M) S} (f : U ⟶ W) (g : V ⟶ W) :
    rvGradedCoprodInr U V ≫ rvGradedCoprodDesc f g = g := by
  apply ObjectProperty.hom_ext
  funext k
  exact rvCoprodInr_desc (f.hom k) (g.hom k)

theorem rvGradedCoprod_hom_ext {U V W : RVGradedObject (M := M) S}
    {f g : rvGradedCoprod U V ⟶ W}
    (hl : rvGradedCoprodInl U V ≫ f = rvGradedCoprodInl U V ≫ g)
    (hr : rvGradedCoprodInr U V ≫ f = rvGradedCoprodInr U V ≫ g) : f = g := by
  apply ObjectProperty.hom_ext
  funext k
  exact rvCoprod_hom_ext (congrArg (fun h => h.hom k) hl) (congrArg (fun h => h.hom k) hr)

def rvGradedCoprodIsColimit (U V : RVGradedObject (M := M) S) :
    IsColimit (BinaryCofan.mk (rvGradedCoprodInl U V) (rvGradedCoprodInr U V)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => rvGradedCoprodDesc f g)
    rvGradedCoprod_inl_desc rvGradedCoprod_inr_desc (fun f g m hl hr =>
      rvGradedCoprod_hom_ext (hl.trans (rvGradedCoprod_inl_desc f g).symm)
        (hr.trans (rvGradedCoprod_inr_desc f g).symm))

theorem rvGradedCoprod_finite_volume (U V : RVGradedObject (M := M) S)
    (hU : rvGradedFiniteVolumeProperty S U) (hV : rvGradedFiniteVolumeProperty S V) :
    rvGradedFiniteVolumeProperty S (rvGradedCoprod U V) :=
  fun k => rvCoprod_finite_volume (U.obj k) (V.obj k) (hU k) (hV k)

theorem rvGradedCoprod_bounded (U V : RVGradedObject (M := M) S) (b : ℕ)
    (hU : rvBoundedGradingProperty S b U) (hV : rvBoundedGradingProperty S b V) :
    rvBoundedGradingProperty S b (rvGradedCoprod U V) := by
  intro k hk
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  rcases (rvCoprod_nonempty_iff (U.obj k) (V.obj k)).mp hne with h | h
  · rw [hU k hk] at h
    exact Set.not_nonempty_empty h
  · rw [hV k hk] at h
    exact Set.not_nonempty_empty h

end SpecialTransformations.Section4

end
