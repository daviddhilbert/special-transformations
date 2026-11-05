import Section3.InfiniteValueFibres
import Section3.AngularPattern
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.AdditiveBalls
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

noncomputable def multiples (b : VFType (M := M)) (n : ℕ) : VFType (M := M) :=
  ((n + 1 : ℕ) : VFType (M := M)) * b

theorem multiples_value (h00 : M ⊨ Axioms.ACVF00) (b : VFType (M := M)) (n : ℕ) :
    v (multiples b n) = v b := by
  change v (((n + 1 : ℕ) : VFType (M := M)) * b) = v b
  rw [map_mul, Barycentre.natCast_value_one v hv h00 (n + 1) (Nat.succ_ne_zero n), one_mul]

theorem multiples_sub_value (h00 : M ⊨ Axioms.ACVF00) (b : VFType (M := M))
    {n m : ℕ} (hnm : n ≠ m) : v (multiples b n - multiples b m) = v b := by
  suffices hh : ∀ n m : ℕ, n < m → v (multiples b n - multiples b m) = v b by
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hh n m h
    · rw [Valuation.map_sub_swap]; exact hh m n h
  intro n m hnm
  have he : multiples b m - multiples b n = ((m - n : ℕ) : VFType (M := M)) * b := by
    rw [Nat.cast_sub hnm.le]
    simp only [multiples, Nat.cast_add, Nat.cast_one]
    ring
  rw [Valuation.map_sub_swap, he, map_mul,
    Barycentre.natCast_value_one v hv h00 (m - n) (Nat.ne_of_gt (Nat.sub_pos_of_lt hnm)), one_mul]

theorem affine_rv_injective (h00 : M ⊨ Axioms.ACVF00)
    (b c : VFType (M := M)) (hb : b ≠ 0) (hc : v c ≤ v b) :
    Function.Injective (fun n : ℕ => CanonicalRV.encodedRv (c + multiples b n)) := by
  intro n m he
  by_contra hnm
  have hd : v ((c + multiples b n) - (c + multiples b m)) = v b := by
    rw [add_sub_add_left_eq_sub]
    exact multiples_sub_value v hv h00 b hnm
  have hle : v (c + multiples b m) ≤ v b :=
    v.map_add_le hc (le_of_eq (multiples_value v hv h00 b m))
  have hm0 : c + multiples b m ≠ 0 := by
    intro hm
    have hn : c + multiples b n = 0 := (CanonicalRV.encodedRv_zero_iff _).mp
      ((congrArg Subtype.val he).trans ((CanonicalRV.encodedRv_zero_iff _).mpr hm))
    rw [hn, hm, sub_self, map_zero] at hd
    exact hb ((map_eq_zero v).mp hd.symm)
  have hnot := (CanonicalRV.encoded_eq_iff_close (c + multiples b n).property
    (c + multiples b m).property (fun h => hm0 (Subtype.ext h))).mp (congrArg Subtype.val he)
  have hp := (hv (c + multiples b m) ((c + multiples b n) - (c + multiples b m))).mpr
    (by rw [hd]; exact hle)
  exact hnot hp

theorem affine_small_finite (h00 : M ⊨ Axioms.ACVF00) (b c : VFType (M := M))
    (hc : v c ≤ v b) : {n : ℕ | v (c + multiples b n) ≠ v b}.Finite := by
  apply Set.Subsingleton.finite
  intro n hn m hm
  by_contra hnm
  have hn' : v (c + multiples b n) < v b := lt_of_le_of_ne
    (v.map_add_le hc (le_of_eq (multiples_value v hv h00 b n))) hn
  have hm' : v (c + multiples b m) < v b := lt_of_le_of_ne
    (v.map_add_le hc (le_of_eq (multiples_value v hv h00 b m))) hm
  have hlt := v.map_sub_lt hn' hm'
  have hd : v ((c + multiples b n) - (c + multiples b m)) = v b := by
    rw [add_sub_add_left_eq_sub]
    exact multiples_sub_value v hv h00 b hnm
  rw [hd] at hlt
  exact lt_irrefl _ hlt

theorem affine_ball_finite (h00 : M ⊨ Axioms.ACVF00)
    (b c : VFType (M := M)) (hb : b ≠ 0) (hc : v c ≤ v b)
    (B : Set M) (hB : IsBall B) (hz : (0 : VFType (M := M)).val ∉ B) :
    {n : ℕ | (c + multiples b n).val ∈ B}.Finite := by
  obtain ⟨t, _, ht⟩ := ball_avoiding_zero_rv v hv B hB hz
  apply Set.Subsingleton.finite
  intro n hn m hm
  apply affine_rv_injective v hv h00 b c hb hc
  apply Subtype.ext
  exact (ht _ hn).trans (ht _ hm).symm

/-- A definable additive subgroup contains every element whose absolute
value is at most that of one of its elements. No RV parameter is named. -/
theorem subgroup_downward (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAt S .vf (Subtype.val '' (H : Set (VFType (M := M)))))
    (b c : VFType (M := M)) (hb : b ∈ H) (hc : v c ≤ v b) : c ∈ H := by
  by_cases hb0 : b = 0
  · have hc0 : c = 0 := (map_eq_zero v).mp (le_zero_iff.mp (by simpa only [hb0, map_zero] using hc))
    simpa only [hc0] using H.zero_mem
  by_contra hcH
  obtain ⟨F, hF, hdet⟩ := BooleanCombinations.finite_basis hH.isBoolComb_balls
  let E : Set ℕ := {n | v (c + multiples b n) ≠ v b} ∪
    ⋃ B ∈ F, if (0 : VFType (M := M)).val ∈ B then ∅ else
      {n | (multiples b n).val ∈ B} ∪ {n | (c + multiples b n).val ∈ B}
  have hE : E.Finite := by
    apply Set.Finite.union (affine_small_finite v hv h00 b c hc)
    apply Set.Finite.biUnion F.finite_toSet
    intro B hB
    by_cases hz : (0 : VFType (M := M)).val ∈ B
    · simp only [if_pos hz, Set.finite_empty]
    · rw [if_neg hz]
      have hfirst := affine_ball_finite v hv h00 b 0 hb0 (by simp only [map_zero]; exact zero_le) B (hF B hB) hz
      simpa only [zero_add] using hfirst.union (affine_ball_finite v hv h00 b c hb0 hc B (hF B hB) hz)
  obtain ⟨n, hn⟩ := hE.exists_notMem
  have hnval : v (c + multiples b n) = v b := by
    by_contra h
    exact hn (Or.inl h)
  have hpattern : ∀ B ∈ F, (multiples b n).val ∈ B ↔ (c + multiples b n).val ∈ B := by
    intro B hB
    by_cases hz : (0 : VFType (M := M)).val ∈ B
    · exact ball_zero_radial v hv B (hF B hB) hz _ _ ((multiples_value v hv h00 b n).trans hnval.symm)
    · have hbad : ¬ ((multiples b n).val ∈ B ∨ (c + multiples b n).val ∈ B) := by
        intro h
        apply hn
        right
        exact Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨hB, by simpa only [if_neg hz, Set.mem_union, Set.mem_ofPred_eq] using h⟩⟩
      exact iff_of_false (fun h => hbad (Or.inl h)) (fun h => hbad (Or.inr h))
  have hmem : multiples b n ∈ H := by
    change ((n + 1 : ℕ) : VFType (M := M)) * b ∈ H
    rw [← nsmul_eq_mul]
    exact H.nsmul_mem hb (n + 1)
  have he := (hdet _ _ hpattern).mp ⟨multiples b n, hmem, rfl⟩
  have hcplus : c + multiples b n ∈ H := by
    rcases he with ⟨x, hx, he⟩
    exact (Subtype.ext he : x = c + multiples b n) ▸ hx
  exact hcH (by simpa only [add_sub_cancel_right] using H.sub_mem hcplus hmem)

end SpecialTransformations.Section3.AdditiveBalls
