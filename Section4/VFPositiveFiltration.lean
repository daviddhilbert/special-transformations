module

public import Section4.VFAllSemiring
public import Section4.VFCoproductBounds
public import Section4.VFProducts

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

/-- The positive classes represented by actual objects of VF[k,·].
Ambient scissors introduce no extra identifications: equality is actual
definable isomorphism, proved below also in the full bounded category. -/
def vfBoundedPositive (k : ℕ) : AddSubmonoid (VFAllKPlus (M := M) S) where
  carrier := {x | ∃ U : VFObject Γ (M := M) S k, vfAllClass U.obj = x}
  zero_mem' := ⟨⟨vfAllEmptyObject S, (vfDim_le_arity Γ _).trans (Nat.zero_le k)⟩, vfAllClass_empty⟩
  add_mem' := by
    rintro x y ⟨U, rfl⟩ ⟨V, rfl⟩
    exact ⟨vfCoprodObject hcan hs hsmall Γ hΓ U V, vfAllClass_coprod U.obj V.obj⟩

local notation "Bnd" => vfBoundedPositive hcan hs hsmall Γ hΓ

abbrev VFBoundedKPlus (k : ℕ) := ↥(Bnd k)

def vfBoundedClass {k : ℕ} (U : VFObject Γ (M := M) S k) :
    VFBoundedKPlus hcan hs hsmall Γ hΓ k := ⟨vfAllClass U.obj, U, rfl⟩

def vfBoundedIsoOfAmbient {k : ℕ} {U V : VFObject Γ (M := M) S k} (e : U.obj ≅ V.obj) : U ≅ V where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := by apply ObjectProperty.hom_ext; exact e.hom_inv_id
  inv_hom_id := by apply ObjectProperty.hom_ext; exact e.inv_hom_id

theorem vfBoundedClass_eq_iff_iso {k : ℕ} (U V : VFObject Γ (M := M) S k) :
    vfBoundedClass hcan hs hsmall Γ hΓ U = vfBoundedClass hcan hs hsmall Γ hΓ V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    obtain ⟨e⟩ := vfAllClass_eq_iff_iso.mp (congrArg Subtype.val h)
    exact ⟨vfBoundedIsoOfAmbient Γ e⟩
  · rintro ⟨e⟩
    apply Subtype.ext
    exact vfAllClass_iso ((vfDimensionProperty Γ S k).ι.mapIso e)

theorem vfBoundedClass_surjective {k : ℕ} :
    Function.Surjective (vfBoundedClass hcan hs hsmall Γ hΓ (k := k)) := by
  intro x
  obtain ⟨U, hU⟩ := x.property
  exact ⟨U, Subtype.ext hU⟩

theorem vfBoundedClass_coprod {k : ℕ} (U V : VFObject Γ (M := M) S k) :
    vfBoundedClass hcan hs hsmall Γ hΓ (vfCoprodObject hcan hs hsmall Γ hΓ U V) =
      vfBoundedClass hcan hs hsmall Γ hΓ U + vfBoundedClass hcan hs hsmall Γ hΓ V := by
  apply Subtype.ext
  exact vfAllClass_coprod U.obj V.obj

theorem vfBoundedClass_scissor {k : ℕ} (A B C D : VFObject Γ (M := M) S k)
    (h : VFAllScissor A.obj B.obj C.obj D.obj) :
    vfBoundedClass hcan hs hsmall Γ hΓ A + vfBoundedClass hcan hs hsmall Γ hΓ B =
      vfBoundedClass hcan hs hsmall Γ hΓ C + vfBoundedClass hcan hs hsmall Γ hΓ D := by
  apply Subtype.ext
  exact vfAllClass_scissor h

theorem vfBoundedPositive_mono {k l : ℕ} (hkl : k ≤ l) : Bnd k ≤ Bnd l := by
  rintro x ⟨U, hU⟩
  exact ⟨⟨U.obj, U.property.trans hkl⟩, hU⟩

theorem vfBoundedPositive_mul {k l : ℕ} {x y : VFAllKPlus (M := M) S}
    (hx : x ∈ Bnd k) (hy : y ∈ Bnd l) : x * y ∈ Bnd (k + l) := by
  obtain ⟨U, rfl⟩ := hx
  obtain ⟨V, rfl⟩ := hy
  exact ⟨vfProductObject Γ U V, (vfAllClass_mul U.obj V.obj).symm⟩

theorem vfBoundedPositive_one : (1 : VFAllKPlus (M := M) S) ∈ Bnd 0 :=
  ⟨⟨vfAllUnitObject S, vfDim_le_arity Γ _⟩, rfl⟩

theorem vfBoundedPositive_exhaustive (x : VFAllKPlus (M := M) S) : ∃ k, x ∈ Bnd k := by
  obtain ⟨U, rfl⟩ := vfAllClass_surjective x
  exact ⟨U.index.1, ⟨U, vfDim_le_arity Γ U.set⟩, rfl⟩

/-- Every representative of a bounded positive class has the stated VF
dimension; this uses actual isomorphism invariance, not a chosen representative. -/
theorem vfAllClass_mem_bounded_iff (U : VFAllObject (M := M) S) (k : ℕ) :
    vfAllClass U ∈ Bnd k ↔ vfDim Γ U.set ≤ k := by
  constructor
  · rintro ⟨V, hV⟩
    obtain ⟨e⟩ := vfAllClass_eq_iff_iso.mp hV
    have hd := vfDim_eq_of_bijective Γ e.hom (DefinableSetCat.bijective_of_iso e)
    exact hd ▸ V.property
  · intro h
    exact ⟨⟨U, h⟩, rfl⟩

end SpecialTransformations.Section4

end
