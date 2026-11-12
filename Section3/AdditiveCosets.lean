module

public import Section3.AdditiveClassification
public import Section3.BallFibreConstancy
public import Section3.BallTranslation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.AdditiveCosets
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem coset_discs (H : AddSubgroup (VFType (M := M)))
    (hH : IsBall (Subtype.val '' (H : Set (VFType (M := M)))))
    (d : VFType (M := M) ⧸ H) :
    ∃ a, (∃ r : Balls.OpenRadius Γ, {x | QuotientAddGroup.mk' H x = d} = Balls.openDisc v a r) ∨
      (∃ r : Balls.Radius Γ, {x | QuotientAddGroup.mk' H x = d} = Balls.closedDisc v a r) := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective H d
  obtain ⟨a, ⟨r, he⟩ | ⟨r, he⟩⟩ := encodedBall_disc v hv _ hH
  · refine ⟨a + c, Or.inl ⟨r, ?_⟩⟩
    ext x
    change QuotientAddGroup.mk' H x = d ↔ _
    rw [← hc]
    change (x : VFType (M := M) ⧸ H) = c ↔ _
    rw [QuotientAddGroup.eq_iff_sub_mem]
    have hmem : (x - c) ∈ H ↔ (x - c).val ∈ Subtype.val '' (H : Set (VFType (M := M))) := by
      constructor
      · intro h; exact ⟨x - c, h, rfl⟩
      · rintro ⟨z, hz, hez⟩; exact (Subtype.ext hez : z = x - c) ▸ hz
    exact hmem.trans ((Set.ext_iff.mp he (x - c)).trans (by
      simpa only [add_sub_cancel_right] using Balls.sub_mem_openDisc_iff v (a + c) c x r))
  · refine ⟨a + c, Or.inr ⟨r, ?_⟩⟩
    ext x
    change QuotientAddGroup.mk' H x = d ↔ _
    rw [← hc]
    change (x : VFType (M := M) ⧸ H) = c ↔ _
    rw [QuotientAddGroup.eq_iff_sub_mem]
    have hmem : (x - c) ∈ H ↔ (x - c).val ∈ Subtype.val '' (H : Set (VFType (M := M))) := by
      constructor
      · intro h; exact ⟨x - c, h, rfl⟩
      · rintro ⟨z, hz, hez⟩; exact (Subtype.ext hez : z = x - c) ▸ hz
    exact hmem.trans ((Set.ext_iff.mp he (x - c)).trans (by
      simpa only [add_sub_cancel_right] using Balls.sub_mem_closedDisc_iff v (a + c) c x r))

end SpecialTransformations.Section3.AdditiveCosets
namespace SpecialTransformations.Section3.AdditiveCosets
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma 3.18(1), with the additive subgroup's ball classification proved
internally and the full original-base set-valued graph. -/
theorem lemma_3_18_1 (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAt S .vf (Subtype.val '' (H : Set (VFType (M := M)))))
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : DefinableOver S MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    {d : VFType (M := M) ⧸ H | ∃ x y,
      QuotientAddGroup.mk' H x = d ∧ QuotientAddGroup.mk' H y = d ∧ f x ≠ f y}.Finite := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  exact BallFibreConstancy.finite_exceptions S f hf hgraph (QuotientAddGroup.mk' H) v hv
    (coset_discs v hv H (AdditiveBalls.subgroup_isBall v hv h00 S H hH))

end SpecialTransformations.Section3.AdditiveCosets
namespace SpecialTransformations.Section3
export AdditiveCosets (lemma_3_18_1)
end SpecialTransformations.Section3
