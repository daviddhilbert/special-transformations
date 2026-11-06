import Section3.TupleCompactness
import Mathlib.Data.Fintype.EquivFin

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

/-- The accepted genuine-saturation finite-cover theorem, reindexed from
Fin n to any finite real-coordinate index. -/
theorem definable_finite_subcover_index {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {ι : Type} [Finite ι]
    (A : Set (ι → M)) (hA : S.Definable LRV A)
    (C : Set (Set (ι → M))) (hC : ∀ c ∈ C, S.Definable LRV c)
    (hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c) :
    ∃ D : Set (Set (ι → M)), D.Finite ∧ D ⊆ C ∧
      ∀ a ∈ A, ∃ c ∈ D, a ∈ c := by
  letI := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let U (c : Set (ι → M)) : Set (Fin (Fintype.card ι) → M) :=
    {z | z ∘ e ∈ c}
  have hU : Function.Injective U := by
    intro c d h
    ext a
    have hh := Set.ext_iff.mp h (a ∘ e.symm)
    simpa [U, Function.comp_def] using hh
  have hcov : ∀ z ∈ U A, ∃ d ∈ U '' C, z ∈ d := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcover (z ∘ e) hz
    exact ⟨U c, ⟨c, hc, rfl⟩, hzc⟩
  obtain ⟨D, hD, hsub, hcovD⟩ := hs.definable_finite_subcover_tuple S hsmall
    (U A) (hA.preimage_comp e) (U '' C)
    (by rintro _ ⟨c, hc, rfl⟩; exact (hC c hc).preimage_comp e) hcov
  refine ⟨{c | c ∈ C ∧ U c ∈ D}, (hD.preimage hU.injOn).subset
    (fun _ h => h.2), fun _ h => h.1, ?_⟩
  intro a ha
  have hz : a ∘ e.symm ∈ U A := by simpa [U, Function.comp_def] using ha
  obtain ⟨d, hd, hzd⟩ := hcovD _ hz
  obtain ⟨c, hc, hcd⟩ := hsub hd
  refine ⟨c, ⟨hc, hcd.symm ▸ hd⟩, ?_⟩
  rw [← hcd] at hzd
  simpa [U, Function.comp_def] using hzd

end SpecialTransformations.Section4

end
