module

public import Section4.VFPositiveFiltration
public import Section4.VFFiniteSemiring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hcan : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
variable (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)

def vfFiniteBoundedPositive (k : ℕ) : AddSubmonoid (VFFiniteKPlus (M := M) S) :=
  (vfBoundedPositive hcan hs hsmall Γ hΓ k).comap vfFiniteForgetKPlus

local notation "Bnd" => vfBoundedPositive hcan hs hsmall Γ hΓ
local notation "FBnd" => vfFiniteBoundedPositive hcan hs hsmall Γ hΓ

abbrev VFFiniteBoundedKPlus (k : ℕ) := ↥(FBnd k)

theorem vfFiniteClass_mem_bounded_iff (U : VFFiniteAllObject (M := M) S) (k : ℕ) :
    vfFiniteClass U ∈ FBnd k ↔ vfDim Γ U.obj.set ≤ k := by
  change vfFiniteForgetKPlus (vfFiniteClass U) ∈ Bnd k ↔ _
  rw [vfFiniteForgetKPlus_class]
  exact vfAllClass_mem_bounded_iff hcan hs hsmall Γ hΓ U.obj k

def vfFiniteBoundedClass {k : ℕ} (U : VFFiniteObject Γ (M := M) S k) :
    VFFiniteBoundedKPlus hcan hs hsmall Γ hΓ k :=
  ⟨vfFiniteClass ⟨U.obj.obj, U.property⟩,
    (vfFiniteClass_mem_bounded_iff hcan hs hsmall Γ hΓ _ k).mpr U.obj.property⟩

def vfFiniteBoundedIsoOfAmbient {k : ℕ} {U V : VFFiniteObject Γ (M := M) S k}
    (e : U.obj.obj ≅ V.obj.obj) : U ≅ V where
  hom := ObjectProperty.homMk (vfBoundedIsoOfAmbient Γ e).hom
  inv := ObjectProperty.homMk (vfBoundedIsoOfAmbient Γ e).inv
  hom_inv_id := by apply ObjectProperty.hom_ext; exact (vfBoundedIsoOfAmbient Γ e).hom_inv_id
  inv_hom_id := by apply ObjectProperty.hom_ext; exact (vfBoundedIsoOfAmbient Γ e).inv_hom_id

theorem vfFiniteBoundedClass_eq_iff_iso {k : ℕ} (U V : VFFiniteObject Γ (M := M) S k) :
    vfFiniteBoundedClass hcan hs hsmall Γ hΓ U =
      vfFiniteBoundedClass hcan hs hsmall Γ hΓ V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    obtain ⟨e⟩ := vfFiniteClass_eq_iff_iso.mp (congrArg Subtype.val h)
    exact ⟨vfFiniteBoundedIsoOfAmbient Γ ((vfFiniteProperty S).ι.mapIso e)⟩
  · rintro ⟨e⟩
    apply Subtype.ext
    exact vfFiniteClass_iso (vfFiniteAllIsoOfAmbient
      ((vfDimensionProperty Γ S k).ι.mapIso ((vfBoundedFiniteProperty Γ S k).ι.mapIso e)))

theorem vfFiniteBoundedClass_surjective {k : ℕ} :
    Function.Surjective (vfFiniteBoundedClass hcan hs hsmall Γ hΓ (k := k)) := by
  intro x
  obtain ⟨U, hU⟩ := vfFiniteClass_surjective x.val
  have hm : vfFiniteClass U ∈ FBnd k := hU.symm ▸ x.property
  have hd := (vfFiniteClass_mem_bounded_iff hcan hs hsmall Γ hΓ U k).mp hm
  exact ⟨⟨⟨U.obj, hd⟩, U.property⟩, Subtype.ext hU⟩

theorem vfFiniteBoundedClass_coprod {k : ℕ} (U V : VFFiniteObject Γ (M := M) S k) :
    vfFiniteBoundedClass hcan hs hsmall Γ hΓ (vfFiniteCoprodObject hcan hs hsmall Γ hΓ U V) =
      vfFiniteBoundedClass hcan hs hsmall Γ hΓ U + vfFiniteBoundedClass hcan hs hsmall Γ hΓ V := by
  apply Subtype.ext
  exact vfFiniteClass_coprod ⟨U.obj.obj, U.property⟩ ⟨V.obj.obj, V.property⟩

theorem vfFiniteBoundedClass_scissor {k : ℕ} (A B C D : VFFiniteObject Γ (M := M) S k)
    (h : VFAllScissor A.obj.obj B.obj.obj C.obj.obj D.obj.obj) :
    vfFiniteBoundedClass hcan hs hsmall Γ hΓ A + vfFiniteBoundedClass hcan hs hsmall Γ hΓ B =
      vfFiniteBoundedClass hcan hs hsmall Γ hΓ C + vfFiniteBoundedClass hcan hs hsmall Γ hΓ D := by
  apply Subtype.ext
  exact vfFiniteClass_scissor h

theorem vfFiniteBoundedPositive_mono {k l : ℕ} (hkl : k ≤ l) : FBnd k ≤ FBnd l :=
  fun _ hx => vfBoundedPositive_mono hcan hs hsmall Γ hΓ hkl hx

theorem vfFiniteBoundedPositive_mul {k l : ℕ} {x y : VFFiniteKPlus (M := M) S}
    (hx : x ∈ FBnd k) (hy : y ∈ FBnd l) : x * y ∈ FBnd (k + l) := by
  change vfFiniteForgetKPlus (x * y) ∈ Bnd (k + l)
  rw [vfFiniteForgetKPlus_mul]
  exact vfBoundedPositive_mul hcan hs hsmall Γ hΓ hx hy

theorem vfFiniteBoundedPositive_one : (1 : VFFiniteKPlus (M := M) S) ∈ FBnd 0 := by
  change vfFiniteForgetKPlus 1 ∈ Bnd 0
  rw [vfFiniteForgetKPlus_one]
  exact vfBoundedPositive_one hcan hs hsmall Γ hΓ

theorem vfFiniteBoundedPositive_exhaustive (x : VFFiniteKPlus (M := M) S) : ∃ k, x ∈ FBnd k :=
  vfBoundedPositive_exhaustive hcan hs hsmall Γ hΓ (vfFiniteForgetKPlus x)

end SpecialTransformations.Section4

end
