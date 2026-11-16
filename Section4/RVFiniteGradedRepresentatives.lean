module

public import Section4.RVGradedRepresentatives
public import Section4.RVFiniteGradedSemiring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem rvFiniteClass_eq_zero_iff {k : ℕ} (U : RVFiniteObject (M := M) S k) :
    rvFiniteClass U = 0 ↔ U.obj.domain.carrier = ∅ := by
  constructor
  · intro h
    apply (rvClass_eq_zero_iff U.obj).mp
    rw [← rvFiniteForgetKPlus_class, h, map_zero]
  · intro h
    apply rvFiniteForgetKPlus_injective
    rw [rvFiniteForgetKPlus_class, map_zero]
    exact (rvClass_eq_zero_iff U.obj).mpr h

def rvFiniteGradedRepresentative (x : RVFiniteGradedKPlus (M := M) S) : RVFiniteGradedObject (M := M) S := by
  let G : RVGradedObject (M := M) S := ⟨fun k => (rvFiniteClassRepresentative (x k)).obj, by
    apply (DFinsupp.finite_support x).subset
    intro k hk hx
    have he : rvFiniteClass (rvFiniteClassRepresentative (x k)) = 0 :=
      (rvFiniteClassRepresentative_class (x k)).trans hx
    have hempty := (rvFiniteClass_eq_zero_iff _).mp he
    change (rvFiniteClassRepresentative (x k)).obj.domain.carrier.Nonempty at hk
    exact Set.not_nonempty_empty (hempty ▸ hk)⟩
  exact ⟨G, fun k => (rvFiniteClassRepresentative (x k)).property⟩

def rvFiniteGradedFamilyClass (U : RVFiniteGradedObject (M := M) S) : RVFiniteGradedKPlus (M := M) S :=
  DFinsupp.mk U.obj.property.toFinset
    (fun k => rvFiniteClass (⟨U.obj.obj k.val, U.property k.val⟩ : RVFiniteObject S k.val))

@[simp] theorem rvFiniteGradedFamilyClass_apply (U : RVFiniteGradedObject (M := M) S) (k : ℕ) :
    rvFiniteGradedFamilyClass U k = rvFiniteClass (⟨U.obj.obj k, U.property k⟩ : RVFiniteObject S k) := by
  by_cases hk : k ∈ U.obj.property.toFinset
  · exact DFinsupp.mk_of_mem hk
  · change DFinsupp.mk U.obj.property.toFinset
      (fun i => rvFiniteClass (⟨U.obj.obj i.val, U.property i.val⟩ : RVFiniteObject S i.val)) k = _
    rw [DFinsupp.mk_of_notMem hk]
    symm
    apply (rvFiniteClass_eq_zero_iff _).mpr
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hk (U.obj.property.mem_toFinset.mpr hn)

@[simp] theorem rvFiniteGradedRepresentative_class (x : RVFiniteGradedKPlus (M := M) S) :
    rvFiniteGradedFamilyClass (rvFiniteGradedRepresentative x) = x := by
  ext k
  rw [rvFiniteGradedFamilyClass_apply]
  exact rvFiniteClassRepresentative_class (x k)

theorem rvFiniteGradedFamilyClass_surjective :
    Function.Surjective (rvFiniteGradedFamilyClass (M := M) (S := S)) :=
  fun x => ⟨rvFiniteGradedRepresentative x, rvFiniteGradedRepresentative_class x⟩

@[simp] theorem rvFiniteGradedFamilyClass_forget (U : RVFiniteGradedObject (M := M) S) :
    rvFiniteGradedForget (rvFiniteGradedFamilyClass U) = rvGradedFamilyClass U.obj := by
  ext k
  simp only [rvFiniteGradedForget, DirectSum.map_apply, rvFiniteGradedFamilyClass_apply,
    rvGradedFamilyClass_apply, rvFiniteForgetKPlus_class]

def rvFiniteGradedIsoOfAmbient {U V : RVFiniteGradedObject (M := M) S} (e : U.obj ≅ V.obj) : U ≅ V where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := by apply ObjectProperty.hom_ext; exact e.hom_inv_id
  inv_hom_id := by apply ObjectProperty.hom_ext; exact e.inv_hom_id

theorem rvFiniteGradedFamilyClass_eq_iff_iso (U V : RVFiniteGradedObject (M := M) S) :
    rvFiniteGradedFamilyClass U = rvFiniteGradedFamilyClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro he
    have h := congrArg rvFiniteGradedForget he
    rw [rvFiniteGradedFamilyClass_forget, rvFiniteGradedFamilyClass_forget] at h
    obtain ⟨e⟩ := (rvGradedFamilyClass_eq_iff_iso U.obj V.obj).mp h
    exact ⟨rvFiniteGradedIsoOfAmbient e⟩
  · rintro ⟨e⟩
    apply rvFiniteGradedForget_injective
    rw [rvFiniteGradedFamilyClass_forget, rvFiniteGradedFamilyClass_forget]
    exact (rvGradedFamilyClass_eq_iff_iso U.obj V.obj).mpr
      ⟨(rvGradedFiniteVolumeProperty S).ι.mapIso e⟩

end SpecialTransformations.Section4

end
