module

public import Section8.IsolationDimension
public import Section8.GammaBalls

@[expose] public section

/-! The isolation predicate uses the paper's actual Gamma radii. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

/-- Every ordinary Gamma radius has a nonzero VF representative. -/
theorem gamma_has_vf_representative (γ : Values.Gamma (M := M)) :
    ∃ r : VFType (M := M), r ≠ 0 ∧ Values.vfValueHom r = γ.val := by
  obtain ⟨t, ht0, htγ⟩ := Values.gamma_has_nonzero_representative γ
  obtain ⟨r, hrt⟩ := CanonicalRV.encodedRv_surjective t
  refine ⟨r, ?_, (congrArg Values.vrv hrt).trans htγ⟩
  intro hz
  exact ht0 ((congrArg Subtype.val hrt).symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr hz))

private theorem gamma_of_nonzero_vf (r : VFType (M := M)) (hr : r ≠ 0) :
    ∃ γ : Values.Gamma (M := M), Values.vfValueHom r = γ.val := by
  have hrv : (CanonicalRV.encodedRv r).val ≠ iRVZero :=
    fun hz => hr ((CanonicalRV.encodedRv_zero_iff r).mp hz)
  exact ⟨Values.gammaOf (CanonicalRV.encodedRv r) hrv, rfl⟩

/-- Membership in the exceptional locus is exactly the singleton
intersection of the input polydisc with the inverse image of the
output polydisc, for some two ordinary Gamma radii. -/
theorem mem_isolatedInputs_iff_gamma
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) :
    vfValues a ∈ isolatedInputs (vfGraph f) ↔
      ∃ δ ε : Values.Gamma (M := M),
        {b | vfValues b ∈ gammaUniformBall (vfValues a) δ ∧
          vfValues (f b) ∈ gammaUniformBall (vfValues (f a)) ε} = {a} := by
  rw [mem_isolatedInputs_iff]
  constructor
  · rintro ⟨r, s, hr, hs, h⟩
    obtain ⟨δ, hδ⟩ := gamma_of_nonzero_vf r hr
    obtain ⟨ε, hε⟩ := gamma_of_nonzero_vf s hs
    refine ⟨δ, ε, ?_⟩
    rw [gammaUniformBall_eq_uniformBall _ _ r hr hδ, gammaUniformBall_eq_uniformBall _ _ s hs hε]
    ext b
    refine ⟨fun hb => Set.mem_singleton_iff.mpr (h b hb.1 hb.2), ?_⟩
    intro hb
    have hba : b = a := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨fun i => rawOpenBall_self Values.presentationValuation Values.presentation_compatible
      (a i).property r.property (fun hz => hr (Subtype.ext hz)),
      fun i => rawOpenBall_self Values.presentationValuation Values.presentation_compatible
        (f a i).property s.property (fun hz => hs (Subtype.ext hz))⟩
  · rintro ⟨δ, ε, h⟩
    obtain ⟨r, hr, hδ⟩ := gamma_has_vf_representative δ
    obtain ⟨s, hs, hε⟩ := gamma_has_vf_representative ε
    rw [gammaUniformBall_eq_uniformBall _ _ r hr hδ, gammaUniformBall_eq_uniformBall _ _ s hs hε] at h
    refine ⟨r, s, hr, hs, fun b hb hfb => Set.mem_singleton_iff.mp ?_⟩
    rw [← h]
    exact ⟨hb, hfb⟩

end SpecialTransformations.Section8
