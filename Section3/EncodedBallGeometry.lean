import Section3.CanonicalParameters
import Section3.BallGeometry
import VFValued
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_difference_normalize (x a : M) (hx : iVF x) (ha : iVF a) :
    @iRv M (CanonicalStructure.normalize (M := M))
      (@iVFAdd M (CanonicalStructure.normalize (M := M)) x
        (@iVFNeg M (CanonicalStructure.normalize (M := M)) a)) =
      iRv (iVFAdd x (iVFNeg a)) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hneg : @iVFNeg M N a = iVFNeg a := CanonicalStructure.normalize_fun Fn.vfNeg ![a]
    (by intro i; fin_cases i; exact ha)
  have hnegVF : iVF (iVFNeg a) := vf_neg_mem hM ha
  have hadd : @iVFAdd M N x (iVFNeg a) = iVFAdd x (iVFNeg a) :=
    CanonicalStructure.normalize_fun Fn.vfAdd ![x, iVFNeg a]
      (by intro i; fin_cases i; exact hx; exact hnegVF)
  have hdiff : @iVFAdd M N x (@iVFNeg M N a) = iVFAdd x (iVFNeg a) :=
    (congrArg (@iVFAdd M N x) hneg).trans hadd
  have hrv : @iRv M N (iVFAdd x (iVFNeg a)) = iRv (iVFAdd x (iVFNeg a)) :=
    CanonicalStructure.normalize_fun Fn.rvMap ![iVFAdd x (iVFNeg a)]
      (by intro i; fin_cases i; exact vf_add_mem hM hx hnegVF)
  exact (congrArg (@iRv M N) hdiff).trans hrv

omit hM in
theorem rv_le_normalize (t u : M) (ht : iRV t) (hu : iRV u) :
    @iLe M (CanonicalStructure.normalize (M := M)) t u ↔ iLe t u :=
  CanonicalStructure.normalize_rel Rel.rvLe ![t, u]
    (by intro i; fin_cases i; exact ht; exact hu)

theorem closedBall_set_normalize (a t : M) (ha : iVF a) (ht : iRV t) :
    {x | @iVF M (CanonicalStructure.normalize (M := M)) x ∧
      @iLe M (CanonicalStructure.normalize (M := M)) t
        (@iRv M (CanonicalStructure.normalize (M := M))
          (@iVFAdd M (CanonicalStructure.normalize (M := M)) x
            (@iVFNeg M (CanonicalStructure.normalize (M := M)) a)))} =
    {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a)))} := by
  ext x
  by_cases hx : iVF x
  · change (iVF x ∧ _) ↔ (iVF x ∧ _)
    simp only [hx, true_and]
    rw [rv_difference_normalize x a hx ha]
    exact rv_le_normalize t _ ht (rv_mem hM (vf_add_mem hM hx (vf_neg_mem hM ha)))
  · change (iVF x ∧ _) ↔ (iVF x ∧ _)
    simp only [hx, false_and]

theorem openBall_set_normalize (a t : M) (ha : iVF a) (ht : iRV t) :
    {x | @iVF M (CanonicalStructure.normalize (M := M)) x ∧
      @iLe M (CanonicalStructure.normalize (M := M)) t
        (@iRv M (CanonicalStructure.normalize (M := M))
          (@iVFAdd M (CanonicalStructure.normalize (M := M)) x
            (@iVFNeg M (CanonicalStructure.normalize (M := M)) a))) ∧
      ¬ @iLe M (CanonicalStructure.normalize (M := M))
        (@iRv M (CanonicalStructure.normalize (M := M))
          (@iVFAdd M (CanonicalStructure.normalize (M := M)) x
            (@iVFNeg M (CanonicalStructure.normalize (M := M)) a))) t} =
    {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a))) ∧
      ¬ iLe (iRv (iVFAdd x (iVFNeg a))) t} := by
  ext x
  by_cases hx : iVF x
  · change (iVF x ∧ _ ∧ _) ↔ (iVF x ∧ _ ∧ _)
    simp only [hx, true_and]
    rw [rv_difference_normalize x a hx ha]
    have hd : iRV (iRv (iVFAdd x (iVFNeg a))) := rv_mem hM (vf_add_mem hM hx (vf_neg_mem hM ha))
    exact and_congr (rv_le_normalize t _ ht hd) (not_congr (rv_le_normalize _ t hd ht))
  · change (iVF x ∧ _ ∧ _) ↔ (iVF x ∧ _ ∧ _)
    simp only [hx, false_and]

/-- Every ball of the frozen encoding survives canonical normalization.
This transfers the actual set predicate, without equating field instances. -/
theorem isBall_normalize (B : Set M) (hB : IsBall B) :
    @IsBall M (CanonicalStructure.normalize (M := M)) B := by
  have hz : @iRVZero M (CanonicalStructure.normalize (M := M)) = iRVZero :=
    CanonicalStructure.sortZero_normalize .rv
  rcases hB with hB | ⟨a, t, ha, ht, ht0, hB⟩ | (⟨a, t, ha, ht, ht0, hB⟩ | ⟨a, ha, hB⟩)
  · exact Or.inl hB
  · exact Or.inr (Or.inl ⟨a, t, ha, ht, (by simpa only [hz] using ht0),
      hB.trans (closedBall_set_normalize a t ha ht).symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, t, ha, ht, (by simpa only [hz] using ht0),
      hB.trans (openBall_set_normalize a t ha ht).symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, ha, hB⟩))

end SpecialTransformations.Section3

set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M]

theorem isBall_subset_vf (B : Set M) (hB : IsBall B) : B ⊆ {x | iVF x} := by
  rcases hB with rfl | ⟨a, t, ha, ht, ht0, rfl⟩ | (⟨a, t, ha, ht, ht0, rfl⟩ | ⟨a, ha, rfl⟩)
  · exact Set.Subset.rfl
  · exact fun _ h => h.1
  · exact fun _ h => h.1
  · exact fun _ h => h.1

variable [hM : M ⊨ Axioms.ACVF]

theorem encodedBall_disc {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (B : Set M) (hB : IsBall B) :
    ∃ a ρ, {x : VFType (M := M) | x.val ∈ B} = Balls.openDisc v a ρ ∨
      {x : VFType (M := M) | x.val ∈ B} = Balls.closedDisc v a ρ := by
  rcases hB with hB | ⟨a, t, ha, ht, ht0, hB⟩ | (⟨a, t, ha, ht, ht0, hB⟩ | ⟨a, ha, hB⟩)
  · refine ⟨0, ⊥, Or.inr ?_⟩
    ext x
    change x.val ∈ B ↔ True
    rw [hB]
    exact iff_true_intro x.property
  · let a' : VFType (M := M) := ⟨a, ha⟩
    obtain ⟨b, hb⟩ := CanonicalRV.encodedRv_surjective (⟨t, ht⟩ : CanonicalRV.RVSort M)
    have hb' : iRv b.val = t := congrArg Subtype.val hb
    refine ⟨a', ↑(OrderDual.toDual (v b)), Or.inr ?_⟩
    apply Set.ext
    intro (x : VFType (M := M))
    change x.val ∈ B ↔ v (x - a') ≤ v b
    rw [hB]
    change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a)))) ↔ _
    rw [and_iff_right x.property]
    have hd : (x - a').val = iVFAdd x.val (iVFNeg a) := by rw [sub_eq_add_neg]; rfl
    have he := hv (x - a') b
    change iLe (iRv b.val) (iRv (x - a').val) ↔ _ at he
    rw [hb', hd] at he
    exact he
  · let a' : VFType (M := M) := ⟨a, ha⟩
    obtain ⟨b, hb⟩ := CanonicalRV.encodedRv_surjective (⟨t, ht⟩ : CanonicalRV.RVSort M)
    have hb' : iRv b.val = t := congrArg Subtype.val hb
    have hb0 : b ≠ 0 := by
      intro he
      exact ht0 (hb'.symm.trans ((CanonicalRV.encodedRv_zero_iff b).mpr he))
    have hvb : v b ≠ 0 := (map_ne_zero v).mpr hb0
    refine ⟨a', ↑(OrderDual.toDual (v b)), Or.inl ?_⟩
    apply Set.ext
    intro (x : VFType (M := M))
    change x.val ∈ B ↔ x ∈ Balls.openDisc v a' (↑(OrderDual.toDual (v b)))
    rw [hB]
    simp only [Balls.openDisc, OrderDual.ofDual_toDual, if_neg hvb, Set.mem_ofPred_eq]
    change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a))) ∧
      ¬ iLe (iRv (iVFAdd x.val (iVFNeg a))) t) ↔ v (x - a') < v b
    rw [and_iff_right x.property]
    have hd : (x - a').val = iVFAdd x.val (iVFNeg a) := by rw [sub_eq_add_neg]; rfl
    have hle := hv (x - a') b
    have hge := hv b (x - a')
    change iLe (iRv b.val) (iRv (x - a').val) ↔ _ at hle
    change iLe (iRv (x - a').val) (iRv b.val) ↔ _ at hge
    rw [hb', hd] at hle hge
    rw [hle, hge, lt_iff_le_not_ge]
  · let a' : VFType (M := M) := ⟨a, ha⟩
    refine ⟨a', ↑(0 : OrderDual Γ), Or.inr ?_⟩
    rw [Balls.closedDisc_infinity]
    apply Set.ext
    intro (x : VFType (M := M))
    change x.val ∈ B ↔ x = a'
    rw [hB]
    change (iVF x.val ∧ x.val = a) ↔ x = a'
    rw [and_iff_right x.property]
    constructor
    · intro he
      exact Subtype.ext he
    · intro he
      exact congrArg Subtype.val he

end SpecialTransformations.Section3
