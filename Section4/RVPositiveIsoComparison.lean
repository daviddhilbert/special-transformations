module

public import Section4.RVIsoClassScissors
public import Section4.RVRepresentatives

@[expose] public section

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-- Equality in the positive scissor quotient is exactly isomorphism in
the actual RV category, before group completion. -/
theorem rvClass_eq_iff_iso {U V : RVObject (M := M) S k} :
    rvClass U = rvClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    apply rvIsoClass_eq_iff.mp
    simpa only [rvKPlusToIsoClasses_class] using congrArg rvKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact rvClass_iso e

theorem rvKPlusToIsoClasses_bijective :
    Function.Bijective (rvKPlusToIsoClasses (M := M) (S := S) (k := k)) := by
  constructor
  · intro a b h
    obtain ⟨U, rfl⟩ := rvClass_surjective a
    obtain ⟨V, rfl⟩ := rvClass_surjective b
    apply rvClass_eq_iff_iso.mpr
    apply rvIsoClass_eq_iff.mp
    simpa only [rvKPlusToIsoClasses_class] using h
  · intro a
    obtain ⟨U, rfl⟩ := rvIsoClass_surjective a
    exact ⟨rvClass U, rvKPlusToIsoClasses_class U⟩

/-- The actual positive additive monoid is the monoid of genuine
isomorphism classes, with addition given by definable disjoint union. -/
def rvPositiveIsoEquiv : RVKPlus (M := M) S k ≃+ RVIsoClasses (M := M) S k :=
  AddEquiv.ofBijective rvKPlusToIsoClasses rvKPlusToIsoClasses_bijective

end SpecialTransformations.Section4

end
