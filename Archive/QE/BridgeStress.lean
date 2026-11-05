/-
**Stress tests for `ValueGroupBridge`.**

Every hypothesis and every tempting-but-false strengthening is checked here, in the style of
`QE/M5Ledger.lean` §11:

* `exists_vGamma_lt_one` / `nontrivial_gammaOf` — the canonical valuation is **not the trivial
  one**: the axiom `axNontrivialRV` (`∃ x ≠ 0, ¬ v x ≤ v 1`) gives an element of the maximal
  ideal, so `Γ(M)` is a nontrivial ordered group and `valueGroup_vGamma_eq_top` in
  `ValueGroupBridge.lean` says something.  (There is no gate, no saturation and no cardinality
  hypothesis anywhere in `ValueGroupBridge.lean`, so the `SaturatedFS`/`#M ≤ #N` stress pattern of
  the frontier does not apply; the analogue here is that the *only* hypothesis, the compatibility
  `hw`, is inhabited — machine-checked as `hypothesis_inhabited`.)
* `maximal_ideal_is_proper` — `vGamma x < 1` and `vGamma x⁻¹`-freely: the maximal ideal and the
  valuation ring are disjoint at the level of the ring condition, i.e. `vGamma x < 1` together with
  `vGamma x ≤ 1` never for the same `x`; and the ring condition is *not* vacuous.
* `wrong_direction` — **the direction brief's order-translation statement is false as written.**
  It asks for `gammaVal a ≤ gammaVal b ↔ w a ≤ w b`; for the canonical `w = vGammaValuation` the
  pair `(1, x)` with `x` from `axNontrivialRV` refutes it: `gv 1 ≤ gv x` holds (the paper's
  `v 1 ≤ v x`) while `vGamma 1 ≤ vGamma x` fails.  The corrected statement, which
  `ValueGroupBridge.le_iff_gv_le_of_valuation` proves, has the two sides exchanged:
  `w x ≤ w y ↔ gv y ≤ gv x`.
-/
import ValueGroupBridge
import Sec3Fibre

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.GammaGroup
open SpecialTransformations.Milestone0.VGBridge

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0.VGBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. Non-degeneracy: the valuation is not the trivial one -/

/-- **`axNontrivialRV` in `vGamma`'s language**: some nonzero field element has value `< 1`, i.e.
lies in the maximal ideal.  This is the frozen encoding's own nontriviality axiom
(`BallSec3.nontrivial_ax`), so the statement is not an extra hypothesis. -/
theorem exists_vGamma_lt_one :
    ∃ x : Transfer.VFType (M := M), x ≠ 0 ∧ vGamma x < 1 := by
  obtain ⟨x, hxVF, hx0, hlt⟩ := M6Fibre.exists_maximal_ideal (M := M) hM
  let X : Transfer.VFType (M := M) := ⟨x, hxVF⟩
  have hX : X ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  exact ⟨X, hX, (vGamma_lt_one_iff (M := M) hX).mpr hlt⟩

/-- **`Γ(M)` is nontrivial**: the value group of the canonical valuation is not the trivial group.
This is what makes `valueGroup_vGamma_eq_top` and the order-translation lemmas non-vacuous. -/
theorem nontrivial_gammaOf : Nontrivial (GammaOf M) := by
  obtain ⟨x, hx, hlt⟩ := exists_vGamma_lt_one (M := M)
  refine ⟨gv x hx, 1, fun h => ?_⟩
  have hv : vGamma x = 1 := by
    rw [vGamma_of_ne (M := M) hx, h, inv_one, WithZero.coe_one]
  rw [hv] at hlt
  exact (lt_irrefl (1 : WithZero (GammaOf M))) hlt

/-- The valuation ring is inhabited by a non-unit (`O ⊋ K`): a concrete element with
`vGamma x ≤ 1` that is not a unit. -/
theorem exists_vGamma_le_one :
    ∃ x : Transfer.VFType (M := M), x ≠ 0 ∧ vGamma x ≤ 1 := by
  obtain ⟨x, hx, hlt⟩ := exists_vGamma_lt_one (M := M)
  exact ⟨x, hx, le_of_lt hlt⟩

/-! ## 2. The transposed order translation is false -/

/-- **The direction brief's order-translation statement is refuted.**  The claim would be
`gv x ≤ gv y ↔ w x ≤ w y` for the canonical `w = vGammaValuation`; the pair `(1, x)` with `x` an
`axNontrivialRV` witness has `gv 1 ≤ gv x` (i.e. `v 1 ≤ v x`) but `vGamma 1 ≤ vGamma x` is false,
because a Mathlib `Valuation` carries the absolute-value order (`map_add_le_max`), which is the
*opposite* of the paper's.  The correct form exchanges the sides — see
`le_iff_gv_le_of_valuation`. -/
theorem wrong_direction :
    ¬ ∀ (x y : Transfer.VFType (M := M)) (hx : x ≠ 0) (hy : y ≠ 0),
        (gv x hx ≤ gv y hy ↔ vGamma x ≤ vGamma y) := by
  intro h
  obtain ⟨x, hx, hlt⟩ := exists_vGamma_lt_one (M := M)
  have hnot : ¬ iLe (iRv x.1) (iRVOne (M := M)) := (vGamma_lt_one_iff (M := M) hx).mp hlt
  have hle : gv (1 : Transfer.VFType (M := M)) one_ne_zero_VF ≤ gv x hx := by
    rw [gv_le_iff (M := M) one_ne_zero_VF hx,
      show ((1 : Transfer.VFType (M := M))).1 = Transfer.iVFOne (M := M) from rfl,
      RVCalc.rv_one hM]
    rcases RVCalc.le_total_rv hM (Transfer.rv_one_mem (M := M) hM) (Transfer.rv_mem hM x.2) with
      h' | h'
    · exact h'
    · exact absurd h' hnot
  have hnot' : ¬ vGamma (1 : Transfer.VFType (M := M)) ≤ vGamma x := by
    rw [vGamma_one (M := M)]
    exact not_le.mpr hlt
  exact hnot' ((h 1 x one_ne_zero_VF hx).mp hle)

/-- The corrected form, specialised to the canonical valuation: the sides must be exchanged. -/
theorem right_direction {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0) :
    gv y hy ≤ gv x hx ↔ vGamma x ≤ vGamma y :=
  (vGamma_le_iff (M := M) hx hy).symm

end

end SpecialTransformations.Milestone0.VGBridge

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.VGBridge.vGammaValuation
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_mul
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_add_le_max
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_le_iff
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_le_one_iff
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_lt_one_iff
#print axioms SpecialTransformations.Milestone0.VGBridge.gv_surjective
#print axioms SpecialTransformations.Milestone0.VGBridge.valueGroup_vGamma_eq_top
#print axioms SpecialTransformations.Milestone0.VGBridge.le_iff_gv_le_of_valuation
#print axioms SpecialTransformations.Milestone0.VGBridge.eq_iff_gv_eq_of_valuation
#print axioms SpecialTransformations.Milestone0.VGBridge.hypothesis_inhabited
#print axioms SpecialTransformations.Milestone0.VGBridge.exists_vGamma_lt_one
#print axioms SpecialTransformations.Milestone0.VGBridge.nontrivial_gammaOf
#print axioms SpecialTransformations.Milestone0.VGBridge.wrong_direction
#print axioms SpecialTransformations.Milestone0.VGBridge.right_direction

#print axioms SpecialTransformations.Milestone0.VGBridge.gv_mul
#print axioms SpecialTransformations.Milestone0.VGBridge.gv_le_iff
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_eq_zero_iff
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_one
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_le_iff_predV
#print axioms SpecialTransformations.Milestone0.VGBridge.vGamma_surj_units
#print axioms SpecialTransformations.Milestone0.VGBridge.mul_ne_zero_VF
#print axioms SpecialTransformations.Milestone0.VGBridge.vf_mul_eq_zero_M
#print axioms SpecialTransformations.Milestone0.VGBridge.exists_vGamma_le_one
