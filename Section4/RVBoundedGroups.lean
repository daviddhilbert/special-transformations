module

public import Section4.RVGradedFiltration
public import Section4.Imported.GrothendieckRing

@[expose] public section

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

abbrev RVBoundedGradedKPlus (S : Set M) (b : ℕ) :=
  ↥(rvGradedBoundedPositive (M := M) S b)

def rvBoundedGradedClass {b : ℕ} (U : RVBoundedGradedObject (M := M) S b) :
    RVBoundedGradedKPlus S b :=
  ⟨rvGradedFamilyClass U.obj, (rvGradedFamilyClass_bounded_iff U.obj b).mpr U.property⟩

def rvBoundedGradedIsoOfAmbient {b : ℕ} {U V : RVBoundedGradedObject (M := M) S b}
    (e : U.obj ≅ V.obj) : U ≅ V where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := by apply ObjectProperty.hom_ext; exact e.hom_inv_id
  inv_hom_id := by apply ObjectProperty.hom_ext; exact e.inv_hom_id

theorem rvBoundedGradedClass_eq_iff_iso {b : ℕ} (U V : RVBoundedGradedObject (M := M) S b) :
    rvBoundedGradedClass U = rvBoundedGradedClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    obtain ⟨e⟩ := (rvGradedFamilyClass_eq_iff_iso U.obj V.obj).mp (congrArg Subtype.val h)
    exact ⟨rvBoundedGradedIsoOfAmbient e⟩
  · rintro ⟨e⟩
    apply Subtype.ext
    exact (rvGradedFamilyClass_eq_iff_iso U.obj V.obj).mpr
      ⟨(rvBoundedGradingProperty S b).ι.mapIso e⟩

theorem rvBoundedGradedClass_surjective {b : ℕ} :
    Function.Surjective (rvBoundedGradedClass (M := M) (S := S) (b := b)) := by
  intro x
  obtain ⟨U, hU⟩ := rvGradedFamilyClass_surjective x.val
  have hmem : rvGradedFamilyClass U ∈ rvGradedBoundedPositive S b := hU.symm ▸ x.property
  exact ⟨⟨U, (rvGradedFamilyClass_bounded_iff U b).mp hmem⟩, Subtype.ext hU⟩

abbrev RVBoundedGradedKGroup (S : Set M) (b : ℕ) :=
  Algebra.GrothendieckAddGroup (RVBoundedGradedKPlus (M := M) S b)

def rvBoundedGradedGroupCompletion {b : ℕ} :
    RVBoundedGradedKPlus (M := M) S b →+ RVBoundedGradedKGroup S b :=
  Algebra.GrothendieckAddGroup.of

def rvBoundedGradedGroupClass {b : ℕ} (U : RVBoundedGradedObject (M := M) S b) :
    RVBoundedGradedKGroup S b := rvBoundedGradedGroupCompletion (rvBoundedGradedClass U)

def rvBoundedGradedGroupUniversalEquiv {b : ℕ} {G : Type} [AddCommGroup G] :
    (RVBoundedGradedKPlus (M := M) S b →+ G) ≃ (RVBoundedGradedKGroup S b →+ G) :=
  Algebra.GrothendieckAddGroup.lift

theorem rvBoundedGradedGroupClass_difference_surjective {b : ℕ}
    (x : RVBoundedGradedKGroup (M := M) S b) :
    ∃ U V : RVBoundedGradedObject (M := M) S b,
      x = rvBoundedGradedGroupClass U - rvBoundedGradedGroupClass V := by
  obtain ⟨a, c, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := rvBoundedGradedClass_surjective a
  obtain ⟨V, rfl⟩ := rvBoundedGradedClass_surjective c
  exact ⟨U, V, he⟩

abbrev RVFiniteBoundedGradedKPlus (S : Set M) (b : ℕ) :=
  ↥(rvFiniteGradedBoundedPositive (M := M) S b)

def rvFiniteBoundedGradedClass {b : ℕ} (U : RVFiniteBoundedGradedObject (M := M) S b) :
    RVFiniteBoundedGradedKPlus S b :=
  ⟨rvFiniteGradedFamilyClass U.obj,
    (rvFiniteGradedFamilyClass_bounded_iff U.obj b).mpr U.property⟩

def rvFiniteBoundedGradedIsoOfAmbient {b : ℕ} {U V : RVFiniteBoundedGradedObject (M := M) S b}
    (e : U.obj ≅ V.obj) : U ≅ V where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := by apply ObjectProperty.hom_ext; exact e.hom_inv_id
  inv_hom_id := by apply ObjectProperty.hom_ext; exact e.inv_hom_id

theorem rvFiniteBoundedGradedClass_eq_iff_iso {b : ℕ}
    (U V : RVFiniteBoundedGradedObject (M := M) S b) :
    rvFiniteBoundedGradedClass U = rvFiniteBoundedGradedClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    obtain ⟨e⟩ := (rvFiniteGradedFamilyClass_eq_iff_iso U.obj V.obj).mp (congrArg Subtype.val h)
    exact ⟨rvFiniteBoundedGradedIsoOfAmbient e⟩
  · rintro ⟨e⟩
    apply Subtype.ext
    exact (rvFiniteGradedFamilyClass_eq_iff_iso U.obj V.obj).mpr
      ⟨(rvBoundedFiniteGradingProperty S b).ι.mapIso e⟩

theorem rvFiniteBoundedGradedClass_surjective {b : ℕ} :
    Function.Surjective (rvFiniteBoundedGradedClass (M := M) (S := S) (b := b)) := by
  intro x
  obtain ⟨U, hU⟩ := rvFiniteGradedFamilyClass_surjective x.val
  have hmem : rvFiniteGradedFamilyClass U ∈ rvFiniteGradedBoundedPositive S b := hU.symm ▸ x.property
  exact ⟨⟨U, (rvFiniteGradedFamilyClass_bounded_iff U b).mp hmem⟩, Subtype.ext hU⟩

abbrev RVFiniteBoundedGradedKGroup (S : Set M) (b : ℕ) :=
  Algebra.GrothendieckAddGroup (RVFiniteBoundedGradedKPlus (M := M) S b)

def rvFiniteBoundedGradedGroupCompletion {b : ℕ} :
    RVFiniteBoundedGradedKPlus (M := M) S b →+ RVFiniteBoundedGradedKGroup S b :=
  Algebra.GrothendieckAddGroup.of

def rvFiniteBoundedGradedGroupClass {b : ℕ} (U : RVFiniteBoundedGradedObject (M := M) S b) :
    RVFiniteBoundedGradedKGroup S b :=
  rvFiniteBoundedGradedGroupCompletion (rvFiniteBoundedGradedClass U)

def rvFiniteBoundedGradedGroupUniversalEquiv {b : ℕ} {G : Type} [AddCommGroup G] :
    (RVFiniteBoundedGradedKPlus (M := M) S b →+ G) ≃ (RVFiniteBoundedGradedKGroup S b →+ G) :=
  Algebra.GrothendieckAddGroup.lift

theorem rvFiniteBoundedGradedGroupClass_difference_surjective {b : ℕ}
    (x : RVFiniteBoundedGradedKGroup (M := M) S b) :
    ∃ U V : RVFiniteBoundedGradedObject (M := M) S b,
      x = rvFiniteBoundedGradedGroupClass U - rvFiniteBoundedGradedGroupClass V := by
  obtain ⟨a, c, he⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨U, rfl⟩ := rvFiniteBoundedGradedClass_surjective a
  obtain ⟨V, rfl⟩ := rvFiniteBoundedGradedClass_surjective c
  exact ⟨U, V, he⟩

end SpecialTransformations.Section4

end
