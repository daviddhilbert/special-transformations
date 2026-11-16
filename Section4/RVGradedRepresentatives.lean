module

public import Section4.RVGradedSemiring
public import Section4.RVGrading
public import Section4.RVGradedCoproduct

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem rvClass_eq_zero_iff {k : ℕ} (U : RVObject (M := M) S k) :
    rvClass U = 0 ↔ U.domain.carrier = ∅ := by
  constructor
  · intro h
    have he : rvClass U = rvClass (RVObject.empty S k) := h.trans rvClass_empty.symm
    obtain ⟨e⟩ := rvClass_eq_iff_iso.mp he
    apply Set.Subset.antisymm
    · intro a ha
      exact (e.hom.map ⟨a, ha⟩).property
    · exact Set.empty_subset _
  · intro h
    exact (rvClass_iso (rvEmptyIso U h)).trans rvClass_empty

/-- The direct-sum positive classes are represented by genuine finite
graded families. Empty components are controlled by their actual classes. -/
def rvGradedRepresentative (x : RVGradedKPlus (M := M) S) : RVGradedObject (M := M) S := by
  refine ⟨fun k => rvClassRepresentative (x k), (DFinsupp.finite_support x).subset ?_⟩
  intro k hk hx
  have he : rvClass (rvClassRepresentative (x k)) = 0 :=
    (rvClassRepresentative_class (x k)).trans hx
  have hempty := (rvClass_eq_zero_iff _).mp he
  change (rvClassRepresentative (x k)).domain.carrier.Nonempty at hk
  exact Set.not_nonempty_empty (hempty ▸ hk)

def rvGradedFamilyClass (U : RVGradedObject (M := M) S) : RVGradedKPlus (M := M) S :=
  DFinsupp.mk U.property.toFinset (fun k => rvClass (U.obj k.val))

@[simp] theorem rvGradedFamilyClass_apply (U : RVGradedObject (M := M) S) (k : ℕ) :
    rvGradedFamilyClass U k = rvClass (U.obj k) := by
  by_cases hk : k ∈ U.property.toFinset
  · exact DFinsupp.mk_of_mem hk
  · change DFinsupp.mk U.property.toFinset (fun i => rvClass (U.obj i.val)) k = _
    rw [DFinsupp.mk_of_notMem hk]
    symm
    apply (rvClass_eq_zero_iff _).mpr
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hk (U.property.mem_toFinset.mpr hn)

@[simp] theorem rvGradedRepresentative_class (x : RVGradedKPlus (M := M) S) :
    rvGradedFamilyClass (rvGradedRepresentative x) = x := by
  ext k
  rw [rvGradedFamilyClass_apply]
  exact rvClassRepresentative_class (x k)

theorem rvGradedFamilyClass_surjective :
    Function.Surjective (rvGradedFamilyClass (M := M) (S := S)) :=
  fun x => ⟨rvGradedRepresentative x, rvGradedRepresentative_class x⟩

theorem rvGradedFamilyClass_eq_iff_iso (U V : RVGradedObject (M := M) S) :
    rvGradedFamilyClass U = rvGradedFamilyClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro he
    apply (rvGradedIso_iff U V).mpr
    intro k
    apply rvClass_eq_iff_iso.mp
    have h := congrArg (fun x : RVGradedKPlus S => x k) he
    simpa only [rvGradedFamilyClass_apply] using h
  · intro he
    ext k
    rw [rvGradedFamilyClass_apply, rvGradedFamilyClass_apply]
    exact rvClass_eq_iff_iso.mpr ((rvGradedIso_iff U V).mp he k)

theorem rvGradedFamilyClass_coprod (U V : RVGradedObject (M := M) S) :
    rvGradedFamilyClass (rvGradedCoprod U V) = rvGradedFamilyClass U + rvGradedFamilyClass V := by
  ext k
  simp only [DirectSum.add_apply, rvGradedFamilyClass_apply]
  exact rvClass_coprod (U.obj k) (V.obj k)

end SpecialTransformations.Section4

end
