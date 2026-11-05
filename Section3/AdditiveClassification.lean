import Section3.AdditiveRadial
import Section3.BallInitial
import Section3.InitialSegments
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

theorem move_away (h00 : M ⊨ Axioms.ACVF00)
    (F : Finset (Set M)) (hF : ∀ B ∈ F, IsBall B) (x : VFType (M := M)) :
    ∃ y : VFType (M := M), v y = v x ∧
      ∀ B ∈ F, (0 : VFType (M := M)).val ∉ B → y.val ∉ B := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx], fun _ _ h => h⟩
  let E : Set ℕ := ⋃ B ∈ F, if (0 : VFType (M := M)).val ∈ B then ∅ else
    {n | (multiples x n).val ∈ B}
  have hE : E.Finite := by
    apply Set.Finite.biUnion F.finite_toSet
    intro B hB
    by_cases hz : (0 : VFType (M := M)).val ∈ B
    · simp only [if_pos hz, Set.finite_empty]
    · rw [if_neg hz]
      simpa only [zero_add] using affine_ball_finite v hv h00 x 0 hx
        (by simp only [map_zero]; exact zero_le) B (hF B hB) hz
  obtain ⟨n, hn⟩ := hE.exists_notMem
  refine ⟨multiples x n, multiples_value v hv h00 x n, ?_⟩
  intro B hB hz hmem
  apply hn
  exact Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨hB, by simpa only [if_neg hz, Set.mem_ofPred_eq] using hmem⟩⟩

theorem subgroup_isBall (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAt S .vf (Subtype.val '' (H : Set (VFType (M := M))))) :
    IsBall (Subtype.val '' (H : Set (VFType (M := M)))) := by
  have hdown := subgroup_downward v hv h00 S H hH
  by_cases hwhole : (H : Set (VFType (M := M))) = Set.univ
  · left
    rw [hwhole]
    ext z
    change (∃ x : VFType (M := M), x ∈ Set.univ ∧ x.val = z) ↔ iVF z
    exact ⟨fun ⟨x, _, he⟩ => he ▸ x.property, fun hz => ⟨⟨z, hz⟩, trivial, rfl⟩⟩
  obtain ⟨F, hF, hdet⟩ := BooleanCombinations.finite_basis hH.isBoolComb_balls
  let G : Finset (Set M) := F.filter (fun B => (0 : VFType (M := M)).val ∈ B)
  let pull (B : Set M) : Set (VFType (M := M)) := {x | x.val ∈ B}
  let P : Finset (Set (VFType (M := M))) := G.image pull
  have hP : ∀ C ∈ P, InitialSegments.IsInitial v C ∧ (0 : VFType (M := M)) ∈ C := by
    intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
    have hh := Finset.mem_filter.mp hB
    exact ⟨fun {_ _} hx hyx => ball_zero_downward v hv B (hF B hh.1) hh.2 hx hyx, hh.2⟩
  have hpattern : ∀ x y : VFType (M := M),
      (∀ C ∈ P, x ∈ C ↔ y ∈ C) → (x ∈ H ↔ y ∈ H) := by
    intro x y hxy
    obtain ⟨x', hxv, hxF⟩ := move_away v hv h00 F hF x
    obtain ⟨y', hyv, hyF⟩ := move_away v hv h00 F hF y
    have hpat : ∀ B ∈ F, x'.val ∈ B ↔ y'.val ∈ B := by
      intro B hB
      by_cases hz : (0 : VFType (M := M)).val ∈ B
      · exact (ball_zero_radial v hv B (hF B hB) hz x' x hxv).trans
          ((hxy (pull B) (Finset.mem_image.mpr ⟨B, Finset.mem_filter.mpr ⟨hB, hz⟩, rfl⟩)).trans
            (ball_zero_radial v hv B (hF B hB) hz y' y hyv).symm)
      · exact iff_of_false (hxF B hB hz) (hyF B hB hz)
    have hraw := hdet x'.val y'.val hpat
    have hmem (z : VFType (M := M)) : z.val ∈ Subtype.val '' (H : Set (VFType (M := M))) ↔ z ∈ H := by
      constructor
      · rintro ⟨w, hw, he⟩
        exact (Subtype.ext he : w = z) ▸ hw
      · intro hz; exact ⟨z, hz, rfl⟩
    rw [hmem x', hmem y'] at hraw
    have hxx : x ∈ H ↔ x' ∈ H := ⟨fun h => hdown x x' h hxv.le,
      fun h => hdown x' x h hxv.ge⟩
    have hyy : y ∈ H ↔ y' ∈ H := ⟨fun h => hdown y y' h hyv.le,
      fun h => hdown y' y h hyv.ge⟩
    exact hxx.trans (hraw.trans hyy.symm)
  obtain ⟨C, hC, heC⟩ := InitialSegments.eq_basis v P (H : Set (VFType (M := M))) 0
    hP (fun {_ _} hx hxy => hdown _ _ hx hxy) H.zero_mem hpattern hwhole
  obtain ⟨B, hB, hBC⟩ := Finset.mem_image.mp hC
  have hh := Finset.mem_filter.mp hB
  have he : Subtype.val '' (H : Set (VFType (M := M))) = B := by
    apply Set.ext
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxC : x ∈ C := heC ▸ hx
      change x ∈ pull B
      rw [hBC]
      exact hxC
    · intro hz
      let x : VFType (M := M) := ⟨z, isBall_subset_vf B (hF B hh.1) hz⟩
      have hxC : x ∈ C := hBC ▸ hz
      exact ⟨x, heC.symm ▸ hxC, rfl⟩
  exact he.symm ▸ hF B hh.1
end SpecialTransformations.Section3.AdditiveBalls

namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The ball classification of every original-base definable additive
subgroup, in every ACVF(0,0) model. A compatible valuation is internal. -/
theorem definable_additive_subgroup_isBall (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAt S .vf (Subtype.val '' (H : Set (VFType (M := M))))) :
    IsBall (Subtype.val '' (H : Set (VFType (M := M)))) := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  exact AdditiveBalls.subgroup_isBall v hv h00 S H hH

end SpecialTransformations.Section3
