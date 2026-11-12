module

public import Section3.MeanInBalls
public import Section3.ValueQuotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem positive_multiples_rv_injective (h00 : M ⊨ Axioms.ACVF00)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (b : VFType (M := M)) (hb : b ≠ 0) :
    Function.Injective (fun n : ℕ => CanonicalRV.encodedRv (((n + 1 : ℕ) : VFType (M := M)) * b)) := by
  let a (n : ℕ) : VFType (M := M) := ((n + 1 : ℕ) : VFType (M := M)) * b
  have ha0 (n : ℕ) : a n ≠ 0 := mul_ne_zero
    (Barycentre.natCast_ne_zero h00 (n + 1) (Nat.succ_ne_zero n)) hb
  have hva (n : ℕ) : v (a n) = v b := by
    change v (((n + 1 : ℕ) : VFType (M := M)) * b) = v b
    rw [map_mul, Barycentre.natCast_value_one v hv h00 (n + 1) (Nat.succ_ne_zero n), one_mul]
  have hpair (n m : ℕ) (hnm : n < m) : CanonicalRV.encodedRv (a n) ≠ CanonicalRV.encodedRv (a m) := by
    intro he
    have hnle : n ≤ m := hnm.le
    have hdiff : a m - a n = ((m - n : ℕ) : VFType (M := M)) * b := by
      rw [Nat.cast_sub hnle]
      simp only [a, Nat.cast_add, Nat.cast_one]
      ring
    have hdiffval : v (a n - a m) = v b := by
      rw [Valuation.map_sub_swap, hdiff, map_mul,
        Barycentre.natCast_value_one v hv h00 (m - n) (Nat.ne_of_gt (Nat.sub_pos_of_lt hnm)), one_mul]
    have hraw : iRv (a n).val = iRv (a m).val := congrArg Subtype.val he
    have hnot := (CanonicalRV.encoded_eq_iff_close (a n).property (a m).property
      (fun he => ha0 m (Subtype.ext he))).mp hraw
    have hle : v (a m) ≤ v (a n - a m) := by rw [hva m, hdiffval]
    have hp := (hv (a m) (a n - a m)).mpr hle
    have hd : (a n - a m).val = iVFAdd (a n).val (iVFNeg (a m).val) := by rw [sub_eq_add_neg]; rfl
    change iLe (iRv (a n - a m).val) (iRv (a m).val) at hp
    rw [hd] at hp
    exact hnot hp
  intro n m he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hpair n m h he
  · exact hpair m n h he.symm

/-- Every non-infinity value class has infinitely many RV points. The
construction uses residue characteristic zero, without naming a section. -/
theorem infinite_gamma_fibre (h00 : M ⊨ Axioms.ACVF00) (γ : Gamma (M := M)) :
    {t : CanonicalRV.RVSort M | vrv t = γ.val}.Infinite := by
  obtain ⟨t, ht0, htγ⟩ := gamma_has_nonzero_representative γ
  obtain ⟨b, hb⟩ := CanonicalRV.encodedRv_surjective t
  have hb0 : b ≠ 0 := by
    intro h
    exact ht0 ((congrArg Subtype.val hb).symm.trans ((CanonicalRV.encodedRv_zero_iff b).mpr h))
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let f (n : ℕ) : CanonicalRV.RVSort M :=
    CanonicalRV.encodedRv (((n + 1 : ℕ) : VFType (M := M)) * b)
  have hf : Function.Injective f := positive_multiples_rv_injective h00 v hv b hb0
  have hmem (n : ℕ) : f n ∈ {t : CanonicalRV.RVSort M | vrv t = γ.val} := by
    have he : vrv (f n) = vrv (CanonicalRV.encodedRv b) :=
      (vf_value_eq_iff v hv _ b).mpr (by
        rw [map_mul, Barycentre.natCast_value_one v hv h00 (n + 1) (Nat.succ_ne_zero n), one_mul])
    exact he.trans ((congrArg vrv hb).trans htγ)
  exact Set.infinite_of_injective_forall_mem hf hmem

end SpecialTransformations.Section3.Values
