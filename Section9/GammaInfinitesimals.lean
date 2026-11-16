module

public import Section9.GammaCoarsening
public import Section8.UnaryGerm
public import Section7.DefinableTupleQuantifiers

@[expose] public section

/-! Realize an infinitesimally positive additive value over a small
parameter field. In Mathlib's order it is below one and above every
specified nonzero value below one. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
local notation "VF" => VFType (M := M)

/-- Saturation realizes a positive infinitesimal over the indicated
small collection of VF parameters. No rank assumption is required. -/
theorem exists_value_above_small_thresholds
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hzero : (0 : VF).val ∈ S) (hone : (1 : VF).val ∈ S)
    (w : Valuation VF Γ) (hw : ∀ a b : VF, VFValued.predV a b ↔ w a ≤ w b)
    (C : Set VF) (hCS : ∀ c ∈ C, c.val ∈ S) (hC : ∀ c ∈ C, c ≠ 0 ∧ w c < 1) :
    ∃ a : VF, a ≠ 0 ∧ w a < 1 ∧ ∀ c ∈ C, w c < w a := by
  classical
  let Z := rawOpenBall (0 : VF).val (1 : VF).val
  let A := Z ∩ {(0 : VF).val}ᶜ
  have hz : DefinableClosureAt S .vf (0 : VF).val :=
    definableClosureAt_of_mem hzero (0 : VF).property
  have hA : S.Definable₁ LRV A := (rawOpenBall_definable hzero hone).inter
    hz.raw_definable.compl
  have hmem (a : VF) : a.val ∈ A ↔ a ≠ 0 ∧ w a < 1 := by
    change (a.val ∈ Z ∧ a.val ≠ (0 : VF).val) ↔ _
    have he := mem_rawOpenBall_iff w hw (0 : VF) (1 : VF) a one_ne_zero
    rw [show a.val ∈ Z ↔ w a < 1 by simpa only [Z, sub_zero, map_one] using he, and_comm]
    exact and_congr_left (fun _ => not_congr Subtype.val_inj)
  let bad (c : C) : Set M := {x | iLe (iRv c.val.val) (iRv x)}
  have hbad (c : C) : S.Definable₁ LRV (bad c) := by
    let F (z : Fin 1 → M) : Fin 2 → M := ![c.val.val, z 0]
    have hF : S.DefinableMap LRV F := by
      intro i
      fin_cases i
      · exact LRV.definableFun_const (Fin 1) (hCS c.val c.property)
      · exact Set.DefinableFun.proj LRV
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ bad c}
    have he := (GammaParameters.raw_le_definable S).preimage_map
      (Section7.definable_rvTuple (ι := Fin 2) S)
    exact he.preimage_map hF
  have hbadmem (c : C) (a : VF) : a.val ∈ bad c ↔ w a ≤ w c.val := hw a c.val
  by_contra hn
  have hcov : ∀ z ∈ A, ∃ B ∈ Set.range bad, z ∈ B := by
    intro z hz
    let a : VF := ⟨z, hz.1.2.1⟩
    obtain ⟨ha, hav⟩ := (hmem a).mp hz
    have he : ∃ c : C, w a ≤ w c.val := by
      by_contra h
      exact hn ⟨a, ha, hav, fun c hc => lt_of_not_ge (fun he => h ⟨⟨c, hc⟩, he⟩)⟩
    obtain ⟨c, hc⟩ := he
    exact ⟨bad c, Set.mem_range_self c, (hbadmem c a).mpr hc⟩
  obtain ⟨B, hBfin, hsub, hBc⟩ := hs.definable_finite_subcover S hsmall A hA (Set.range bad)
    (by rintro _ ⟨c, rfl⟩; exact hbad c) hcov
  letI : Fintype B := hBfin.fintype
  let c (b : B) := Classical.choose (hsub b.property)
  have hc (b : B) : bad (c b) = b.val := Classical.choose_spec (hsub b.property)
  letI : Valued VF Γ := Valued.mk' w
  obtain ⟨e, he₀, he⟩ := model_valuation_nontrivial (Γ := Γ) hw
  let Q := insert e (Finset.univ.image (fun b : B => (c b).val))
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image Q w ⟨e, Finset.mem_insert_self _ _⟩
  have hr' : r ≠ 0 ∧ w r < 1 := by
    rcases Finset.mem_insert.mp hr with h | h
    · exact h.symm ▸ ⟨he₀, he⟩
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      exact hC _ (c b).property
  letI : IsAlgClosed VF := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq r (by decide : 0 < 2)
  have ha₀ : a ≠ 0 := fun h => hr'.1 (by rw [← ha, h]; norm_num)
  have hvpow : w a ^ 2 = w r := by rw [← map_pow, ha]
  have hav : w a < 1 := lt_of_not_ge (fun h =>
    hr'.2.not_ge (hvpow ▸ (by simpa only [one_pow] using pow_le_pow_left' h 2)))
  have hrv : w r < w a := by
    rw [← hvpow, pow_two]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hav
      (pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr ha₀))
  obtain ⟨D, hD, haD⟩ := hBc a.val ((hmem a).mpr ⟨ha₀, hav⟩)
  let b : B := ⟨D, hD⟩
  have hvb := (hbadmem (c b) a).mp ((hc b).symm ▸ haD)
  have hcb : (c b).val ∈ Q :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩))
  exact hrv.not_ge (hvb.trans (hmax _ hcb))

end SpecialTransformations.Section9
