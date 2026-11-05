/-
**Γ(M) as the value group of a genuine Mathlib valuation.**

Direction g5 (swarm smw2ku6gn).  The paper's value group `Γ(M) = RV(M)^×/K^×(M)` is
`QE/GammaGroup.lean`'s `GammaOf M` (a linearly ordered abelian group, from `Axioms.ACVF` alone).
`QE/VFValued.lean` proves that a model of `ACVF` carries *some* Mathlib `Valuation` on its `VF`
sort, but only in existential form (`exists_valuation_predV`): the codomain is a
`ValuativeRel.ValueGroupWithZero`, an abstract quotient.  This file closes the gap:

* `vGammaValuation : Valuation (VFType M) (WithZero (GammaOf M))` — an **explicit** valuation
  whose value group is literally `Γ(M)` with a zero adjoined (no `Classical.choose`, no
  existential);
* the **order translation, and its reversal.**  A Mathlib `Valuation` is the absolute-value
  convention (`map_add_le_max : v (x+y) ≤ max`), the paper's `v` is the value-group convention
  (`v (x+y) ≥ min`), so the identification is `x ↦ (value of x)⁻¹`:
  `vGamma x ≤ vGamma y ↔ iLe (iRv y) (iRv x)`.  Consequently the order-translation lemma into
  `Γ(M)` reads `w x ≤ w y ↔ gv y ≤ gv x` — the argument order of the form suggested by the
  direction brief (`gammaVal a ≤ gammaVal b ↔ w a ≤ w b`) is transposed, and `wrong_direction`
  in `BridgeStress.lean` machine-checks that the transposed form is *false* for the canonical
  valuation (so it is not merely unproved);
* the **valuation ring** `O = {x | vGamma x ≤ 1} = {x | v 1 ≤ v x}` and the **maximal ideal**
  `m = {x ≠ 0 | vGamma x < 1} = {x ≠ 0 | ¬ v x ≤ v 1}` (`vGamma_lt_one_iff`), i.e. `O`/`m` are
  those of a genuine valuation;
* **surjectivity** `Γ(M) = v(K^×)`: every element of `Γ(M)` is the value of a nonzero field
  element (`gv_surjective`, from the encoding's `rvSurj`), whence
  `valueGroup vGammaValuation = ⊤` — the value group of the valuation *is* Γ(M), not a subgroup;
* the **bridge to an arbitrary Mathlib valuation** `w` compatible with `VFValued.predV`: its
  order is Γ(M)'s with the two sides exchanged (`le_iff_gv_le_of_valuation`), and equal values
  correspond (`eq_iff_gv_eq_of_valuation`), so any such `w` realises exactly Γ(M).

## Implementation note

`VFField.vfFieldOfModel` builds the `Field (VFType M)` structure by `Field.ofMinimalAxioms`, and in
this Mathlib the `Mul`/`Zero` reached through the `Field` instance is not syntactically the one
instance search picks for a bare `x * y` at `VFType M`: generic lemmas such as `zero_mul` do not
`rw` at that level (they elaborate through `MulZeroClass`).  Every `VF`-sorted identity is
therefore stated here once as a `Subtype.ext` of an `iVF*` identity on `M` (§0) and only those
lemmas are used.

## Hypothesis audit (report standard)

The only ambient assumptions are `[LRV.Structure M]` and `[hM : M ⊨ Axioms.ACVF]`, the standing
setup of the whole project (carried identically by `RVCalc`, `GammaGroup`, `VFValued`), so nothing
here can be vacuous.  Non-degeneracy is *proved*, not assumed (see `BridgeStress.lean`):

* `exists_vGamma_lt_one` — `∃ x ≠ 0, vGamma x < 1`, read off the axiom `axNontrivialRV`
  (`∃ x ≠ 0, ¬ v x ≤ v 1`, the frozen encoding's nontriviality axiom): the value group is
  nontrivial, the maximal ideal is inhabited, and the canonical valuation is not the trivial one;
* `nontrivial_gammaOf : Nontrivial (GammaOf M)` — so `⊤` is not the only subgroup of `Γ(M)ˣ`
  and `valueGroup_vGamma_eq_top` has content;
* `wrong_direction` — a machine-checked counterexample to the transposed order translation;
* `hypothesis_inhabited` — the hypothesis `∀ x y, predV x y ↔ w x ≤ w y` of §5 is *satisfied* by
  `vGammaValuation` itself, so §5 is not vacuous.
-/
import GammaGroup
import VFValued
import Standing

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.GammaGroup

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0.VGBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 0. `VF`-sorted algebra

The operations of `Transfer.VFType M` are definitionally the `iVF*` functions on `M`
(`VFField.vfInstMul` and friends), but the `Field` instance rebuilds them as structure fields, so
generic `zero_mul`-style lemmas do not fire on `VFType`-sorted goals.  The identities needed below
are therefore proved once at the level of `M` and repackaged with `Subtype.ext`. -/

theorem zero_mul_VF (y : Transfer.VFType (M := M)) :
    (0 : Transfer.VFType (M := M)) * y = 0 :=
  Subtype.ext (RVCalc.vf_zero_mul (M := M) hM y.2)

theorem mul_zero_VF (x : Transfer.VFType (M := M)) :
    x * (0 : Transfer.VFType (M := M)) = 0 :=
  Subtype.ext (RVCalc.vf_mul_zero (M := M) hM x.2)

theorem zero_add_VF (y : Transfer.VFType (M := M)) :
    (0 : Transfer.VFType (M := M)) + y = y :=
  Subtype.ext (RVCalc.vf_zero_add (M := M) hM y.2)

theorem add_zero_VF (x : Transfer.VFType (M := M)) :
    x + (0 : Transfer.VFType (M := M)) = x :=
  Subtype.ext (RVCalc.vf_add_zero (M := M) hM x.2)

/-- `1 ≠ 0` on the `VF` sort (`VFField.vfFieldOfModel` generates no `NeZero` instance). -/
theorem one_ne_zero_VF : (1 : Transfer.VFType (M := M)) ≠ 0 := by
  intro h
  exact RVCalc.vf_zero_ne_one (M := M) hM (congrArg Subtype.val h).symm

/-- **No zero divisors at the level of `M`**: a product of `VF`-elements is `0` only if one factor
is.  From the inverse law `vf_mul_inv_or_zero` and associativity. -/
theorem vf_mul_eq_zero_M {x y : M} (hx : iVF x) (hy : iVF y)
    (h : iVFMul x y = Transfer.iVFZero (M := M)) :
    x = Transfer.iVFZero (M := M) ∨ y = Transfer.iVFZero (M := M) := by
  rcases Transfer.vf_mul_inv_or_zero (M := M) hM hy with hy0 | ⟨z, hz, hyz⟩
  · exact Or.inr hy0
  refine Or.inl ?_
  calc x = iVFMul x (Transfer.iVFOne (M := M)) := (Transfer.vf_mul_one (M := M) hM hx).symm
    _ = iVFMul x (iVFMul y z) := by rw [hyz]
    _ = iVFMul (iVFMul x y) z := (Transfer.vf_mul_assoc (M := M) hM hx hy hz).symm
    _ = iVFMul (Transfer.iVFZero (M := M)) z := by rw [h]
    _ = Transfer.iVFZero (M := M) := RVCalc.vf_zero_mul (M := M) hM hz

/-- **No zero divisors on the `VF` sort.** -/
theorem mul_ne_zero_VF {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y ≠ 0 := by
  intro h
  have h' : iVFMul x.1 y.1 = Transfer.iVFZero (M := M) := congrArg Subtype.val h
  rcases vf_mul_eq_zero_M x.2 y.2 h' with h0 | h0
  · exact hx (Subtype.ext h0)
  · exact hy (Subtype.ext h0)

/-! ## 1. The value of a field element -/

/-- The `Γ(M)`-value of a nonzero element of the `VF` sort: `x ↦ [rv x]`. -/
def gv (x : Transfer.VFType (M := M)) (hx : x ≠ 0) : GammaOf M :=
  gammaVal x.2 (fun h => hx (Subtype.ext h))

theorem gv_def (x : Transfer.VFType (M := M)) (hx : x ≠ 0) :
    gv x hx = gammaMk (rvStarOf x.2 (fun h => hx (Subtype.ext h))) := rfl

/-- The order of `Γ(M)` is the paper's order on values: `gv x ≤ gv y ↔ v x ≤ v y`. -/
theorem gv_le_iff {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0) :
    gv x hx ≤ gv y hy ↔ iLe (iRv x.1) (iRv y.1) :=
  Iff.rfl

/-- `gv` is multiplicative (at the level of `gammaVal`, which is `gv` unfolded). -/
theorem gammaVal_mul_at {x y : M} (hx : iVF x) (hy : iVF y) (hx0 : x ≠ Transfer.iVFZero)
    (hy0 : y ≠ Transfer.iVFZero) (hxy : iVF (iVFMul x y))
    (hxy0 : iVFMul x y ≠ Transfer.iVFZero) :
    gammaVal hxy hxy0 = gammaVal hx hx0 * gammaVal hy hy0 := by
  rw [gammaVal_def, gammaVal_def, gammaVal_def, ← gammaMk_mul]
  congr 1
  exact Subtype.ext (Transfer.rv_mul_hom_of_model hM hx hy)

/-- `gv` is multiplicative. -/
theorem gv_mul {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x * y ≠ 0) : gv (x * y) hxy = gv x hx * gv y hy :=
  gammaVal_mul_at x.2 y.2 (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h))
    (Transfer.vf_mul_mem (M := M) hM x.2 y.2) (fun h => hxy (Subtype.ext h))

/-- `gv 1 = 1`. -/
theorem gv_one : gv (1 : Transfer.VFType (M := M)) one_ne_zero_VF = 1 := by
  have key : gv (1 : Transfer.VFType (M := M)) one_ne_zero_VF = gammaMk (1 : RVStar M) := by
    rw [gv_def]
    congr 1
    exact Subtype.ext (RVCalc.rv_one hM)
  rw [key, gammaMk_one_eq]

/-- The ultrametric inequality, in `Γ(M)`: one of `v x`, `v y` is `≤ v (x+y)`. -/
theorem gv_add_ultra {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : gv x hx ≤ gv (x + y) hxy ∨ gv y hy ≤ gv (x + y) hxy :=
  RVCalc.rv_ultrametric hM x.2 y.2

/-- `gv x ≤ 1 ↔ v x ≤ v 1`. -/
theorem gv_le_one_iff {x : Transfer.VFType (M := M)} (hx : x ≠ 0) :
    gv x hx ≤ 1 ↔ iLe (iRv x.1) (iRVOne (M := M)) := by
  have h := gv_le_iff (x := x) (y := (1 : Transfer.VFType (M := M))) hx one_ne_zero_VF
  rw [gv_one, show ((1 : Transfer.VFType (M := M))).1 = Transfer.iVFOne (M := M) from rfl,
    RVCalc.rv_one hM] at h
  exact h

/-- `1 ≤ gv x ↔ v 1 ≤ v x`. -/
theorem one_le_gv_iff {x : Transfer.VFType (M := M)} (hx : x ≠ 0) :
    1 ≤ gv x hx ↔ iLe (iRVOne (M := M)) (iRv x.1) := by
  have h := gv_le_iff (x := (1 : Transfer.VFType (M := M))) (y := x) one_ne_zero_VF hx
  rw [gv_one, show ((1 : Transfer.VFType (M := M))).1 = Transfer.iVFOne (M := M) from rfl,
    RVCalc.rv_one hM] at h
  exact h

/-! ## 2. The explicit valuation `VF → Γ(M) ∪ {0}` -/

/-- **The valuation of the frozen encoding, with values in `Γ(M)` with a zero adjoined.**
The zero is the bottom of the order (Mathlib's absolute-value convention), so the value of `x` is
the *inverse* of its paper value `[rv x]`: that is the only way a Mathlib `Valuation` can carry the
paper's value-group order. -/
def vGamma (x : Transfer.VFType (M := M)) : WithZero (GammaOf M) :=
  if hx : x = 0 then 0 else ↑((gv x hx)⁻¹)

theorem vGamma_zero : vGamma (0 : Transfer.VFType (M := M)) = 0 := dif_pos rfl

theorem vGamma_of_ne {x : Transfer.VFType (M := M)} (hx : x ≠ 0) :
    vGamma x = ↑((gv x hx)⁻¹) := dif_neg hx

/-- `vGamma` vanishes exactly at `0` (`v x = ∞ ↔ x = 0`). -/
theorem vGamma_eq_zero_iff {x : Transfer.VFType (M := M)} : vGamma x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rw [vGamma_of_ne hx] at h
    simp only [WithZero.coe_ne_zero] at h
  · intro h
    subst h
    exact vGamma_zero

theorem vGamma_one : vGamma (1 : Transfer.VFType (M := M)) = 1 := by
  rw [vGamma_of_ne one_ne_zero_VF, gv_one, inv_one, WithZero.coe_one]

theorem vGamma_mul (x y : Transfer.VFType (M := M)) :
    vGamma (x * y) = vGamma x * vGamma y := by
  by_cases hx : x = 0
  · subst hx
    rw [zero_mul_VF, vGamma_zero, zero_mul]
  by_cases hy : y = 0
  · subst hy
    rw [mul_zero_VF, vGamma_zero, mul_zero]
  have hxy : x * y ≠ 0 := mul_ne_zero_VF hx hy
  rw [vGamma_of_ne hxy, vGamma_of_ne hx, vGamma_of_ne hy, gv_mul hx hy hxy, mul_inv_rev,
    WithZero.coe_mul, mul_comm]

/-- **The ultrametric inequality for `vGamma`** (Mathlib's `map_add_le_max'`). -/
theorem vGamma_add_le_max (x y : Transfer.VFType (M := M)) :
    vGamma (x + y) ≤ max (vGamma x) (vGamma y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, vGamma_zero]
    exact zero_le
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    rw [zero_add_VF]
    exact le_max_right _ _
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    rw [add_zero_VF]
    exact le_max_left _ _
  rcases gv_add_ultra hx hy hxy with h | h
  · refine le_trans ?_ (le_max_left _ _)
    rw [vGamma_of_ne hxy, vGamma_of_ne hx, WithZero.coe_le_coe, inv_le_inv_iff]
    exact h
  · refine le_trans ?_ (le_max_right _ _)
    rw [vGamma_of_ne hxy, vGamma_of_ne hy, WithZero.coe_le_coe, inv_le_inv_iff]
    exact h

/-- **The valuation of a model of `ACVF`, valued in `Γ(M) ∪ {0}`.** -/
def vGammaValuation : Valuation (Transfer.VFType (M := M)) (WithZero (GammaOf M)) where
  toFun := vGamma
  map_zero' := vGamma_zero
  map_one' := vGamma_one
  map_mul' := vGamma_mul
  map_add_le_max' := vGamma_add_le_max

/-- `vGammaValuation` computes as `vGamma`. -/
@[simp] theorem vGammaValuation_apply (x : Transfer.VFType (M := M)) :
    vGammaValuation x = vGamma x := rfl

/-! ## 3. The order translation (and its reversal) -/

/-- **Order translation.**  On nonzero elements, `vGamma`'s order is the paper's `rv`-order with
the two sides exchanged: `vGamma x ≤ vGamma y ↔ iLe (iRv y) (iRv x)`.  In words: a Mathlib
valuation orders the values *opposite* to the paper, being the absolute-value convention.  The
right-hand side is literally `VFValued.predV x y`. -/
theorem vGamma_le_iff {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0) :
    vGamma x ≤ vGamma y ↔ iLe (iRv y.1) (iRv x.1) := by
  rw [vGamma_of_ne hx, vGamma_of_ne hy, WithZero.coe_le_coe, inv_le_inv_iff]
  exact gv_le_iff hy hx

/-- `vGamma`'s order *is* `VFValued.predV`, so `vGammaValuation` is one of the valuations whose
existence `VFValued.exists_valuation_predV` asserts. -/
theorem vGamma_le_iff_predV {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0) :
    vGamma x ≤ vGamma y ↔ VFValued.predV x y :=
  vGamma_le_iff hx hy

/-- **The valuation ring**: `vGamma x ≤ 1` iff `v 1 ≤ v x`. -/
theorem vGamma_le_one_iff {x : Transfer.VFType (M := M)} (hx : x ≠ 0) :
    vGamma x ≤ 1 ↔ iLe (iRVOne (M := M)) (iRv x.1) := by
  rw [vGamma_of_ne hx,
    show (1 : WithZero (GammaOf M)) = ↑((1 : GammaOf M)⁻¹) from by
      rw [inv_one, WithZero.coe_one],
    WithZero.coe_le_coe, inv_le_inv_iff]
  exact one_le_gv_iff hx

/-- **The maximal ideal**: `vGamma x < 1` iff `x ≠ 0` and `¬ v x ≤ v 1`. -/
theorem vGamma_lt_one_iff {x : Transfer.VFType (M := M)} (hx : x ≠ 0) :
    vGamma x < 1 ↔ ¬ iLe (iRv x.1) (iRVOne (M := M)) := by
  rw [vGamma_of_ne hx,
    show (1 : WithZero (GammaOf M)) = ↑((1 : GammaOf M)⁻¹) from by
      rw [inv_one, WithZero.coe_one],
    WithZero.coe_lt_coe, inv_lt_inv_iff, ← not_le, gv_le_one_iff hx]

/-! ## 4. Surjectivity: `Γ(M) = v(K^×)` -/

/-- **Every value class has a nonzero field element as representative**, using the encoding's
`rvSurj` axiom (`Assembly.RVeqRvVF_of_model`): the valuation is *surjective onto* `Γ(M)`. -/
theorem gv_surjective (g : GammaOf M) :
    ∃ (x : Transfer.VFType (M := M)) (hx : x ≠ 0), gv x hx = g := by
  obtain ⟨a, rfl⟩ := gammaMk_surjective (M := M) g
  rcases Assembly.RVeqRvVF_of_model (M := M) a.1 a.2.1 with ⟨x, hxVF, hxrv⟩ | hz
  · have hx0 : x ≠ Transfer.iVFZero (M := M) := by
      intro h
      exact a.2.2 (by rw [← hxrv, h, RVCalc.rv_zero_eq hM])
    let X : Transfer.VFType (M := M) := ⟨x, hxVF⟩
    have hX : X ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
    refine ⟨X, hX, ?_⟩
    rw [gv_def]
    congr 1
    exact Subtype.ext hxrv
  · exact absurd hz a.2.2

/-- Every *unit* of `WithZero Γ(M)` is the `vGamma`-value of some field element: the value group of
the valuation is all of `Γ(M)`, not a proper subgroup. -/
theorem vGamma_surj_units (u : (WithZero (GammaOf M))ˣ) :
    ∃ x : Transfer.VFType (M := M), vGamma x = (↑u : WithZero (GammaOf M)) := by
  obtain ⟨g, hg⟩ : ∃ g : GammaOf M, (↑g : WithZero (GammaOf M)) = (↑u : WithZero (GammaOf M)) :=
    ⟨WithZero.unitsWithZeroEquiv u, WithZero.coe_unitsWithZeroEquiv_eq_units_val u⟩
  obtain ⟨x, hx, hgv⟩ := gv_surjective g⁻¹
  refine ⟨x, ?_⟩
  rw [vGamma_of_ne hx, hgv, inv_inv, hg]

/-- **The range of `vGamma` is the whole value group**: the set of units attained by `vGamma` is
all of `(Γ(M) ∪ {0})ˣ`.  (In Mathlib's language this is `valueGroup vGamma = ⊤`; it is stated set
theoretically because `MonoidWithZeroHom.valueGroup` and `Valuation.toMonoidWithZeroHom` reach
`MulZeroOneClass (VFType M)` through different instance paths in this Mathlib, so the two cannot be
applied to each other — cf. §0.) -/
theorem valueGroup_vGamma_eq_top :
    {u : (WithZero (GammaOf M))ˣ | ∃ x : Transfer.VFType (M := M), vGamma x = (↑u : WithZero (GammaOf M))}
      = Set.univ := by
  ext u
  exact ⟨fun _ => trivial, fun _ => vGamma_surj_units u⟩

/-! ## 5. The bridge to an arbitrary Mathlib valuation compatible with `predV` -/

section Arbitrary

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- **Order translation for any compatible Mathlib valuation.**  If `w` is a Mathlib valuation
whose order is the encoding's `predV`, then on nonzero field elements `w`'s order is `Γ(M)`'s
order with the two sides exchanged: `w x ≤ w y ↔ gv y ≤ gv x`.

The form `gv x ≤ gv y ↔ w x ≤ w y` (the paper order on `Γ(M)` *un*swapped, as suggested by the
direction brief) is FALSE for the canonical `w = vGammaValuation` — see `wrong_direction` in
`BridgeStress.lean`. -/
theorem le_iff_gv_le_of_valuation (w : Valuation (Transfer.VFType (M := M)) Γ)
    (hw : ∀ x y, VFValued.predV x y ↔ w x ≤ w y)
    {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0) :
    w x ≤ w y ↔ gv y hy ≤ gv x hx :=
  (hw x y).symm.trans (gv_le_iff hy hx)

/-- **`gv` against a compatible valuation**, in the order in which it is used below:
`gv x ≤ gv y ↔ w y ≤ w x`. -/
theorem gv_le_iff_valuation (w : Valuation (Transfer.VFType (M := M)) Γ)
    (hw : ∀ x y, VFValued.predV x y ↔ w x ≤ w y)
    {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0) :
    gv x hx ≤ gv y hy ↔ w y ≤ w x :=
  (gv_le_iff hx hy).trans (hw y x)

/-- **Equal values.**  For a compatible Mathlib valuation, two nonzero field elements have the
same `w`-value iff they have the same class in `Γ(M)`. -/
theorem eq_iff_gv_eq_of_valuation (w : Valuation (Transfer.VFType (M := M)) Γ)
    (hw : ∀ x y, VFValued.predV x y ↔ w x ≤ w y)
    {x y : Transfer.VFType (M := M)} (hx : x ≠ 0) (hy : y ≠ 0) :
    w x = w y ↔ gv x hx = gv y hy := by
  constructor
  · intro h
    have h1 : gv x hx ≤ gv y hy :=
      (gv_le_iff_valuation (x := x) (y := y) w hw hx hy).mpr (le_of_eq h.symm)
    have h2 : gv y hy ≤ gv x hx :=
      (gv_le_iff_valuation (x := y) (y := x) w hw hy hx).mpr (le_of_eq h)
    exact le_antisymm h1 h2
  · intro h
    have h1 : w x ≤ w y :=
      (gv_le_iff_valuation (x := y) (y := x) w hw hy hx).mp (le_of_eq h.symm)
    have h2 : w y ≤ w x :=
      (gv_le_iff_valuation (x := x) (y := y) w hw hx hy).mp (le_of_eq h)
    exact le_antisymm h1 h2

/-- **The hypothesis of §5 is inhabited**: `vGammaValuation` itself is a compatible Mathlib
valuation, so `le_iff_gv_le_of_valuation` has a non-vacuous instance. -/
theorem hypothesis_inhabited :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
      (w : Valuation (Transfer.VFType (M := M)) Γ), ∀ x y, VFValued.predV x y ↔ w x ≤ w y := by
  refine ⟨WithZero (GammaOf M), inferInstance, vGammaValuation, fun x y => ?_⟩
  rw [vGammaValuation_apply, vGammaValuation_apply]
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    rw [vGamma_zero]
    constructor
    · intro _
      exact zero_le (a := vGamma y)
    · intro _
      show iLe (iRv y.1) (iRv (Transfer.iVFZero (M := M)))
      rw [RVCalc.rv_zero_eq hM]
      exact RVCalc.le_top_rv hM (Transfer.rv_mem hM y.2)
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    rw [vGamma_zero]
    have hpred : ¬ VFValued.predV x (0 : Transfer.VFType (M := M)) := by
      intro h
      have h' : iLe (iRVZero (M := M)) (iRv x.1) := by
        rw [VFValued.predV,
          show ((0 : Transfer.VFType (M := M)).1) = Transfer.iVFZero (M := M) from rfl,
          RVCalc.rv_zero_eq hM] at h
        exact h
      have h0 : iRv x.1 = iRVZero := RVCalc.le_infty_eq hM (Transfer.rv_mem hM x.2) h'
      exact hx (Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM x.2 h0))
    have hv : ¬ vGamma x ≤ (0 : WithZero (GammaOf M)) := by
      intro hle
      exact hx (vGamma_eq_zero_iff.mp (le_antisymm hle (zero_le (a := vGamma x))))
    exact ⟨fun h => absurd h hpred, fun h => absurd h hv⟩
  · exact (vGamma_le_iff hx hy).symm

end Arbitrary

end

end SpecialTransformations.Milestone0.VGBridge
