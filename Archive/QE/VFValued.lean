/-
**A Mathlib `Valuation` on the frozen encoding's `VF` sort.**

`QE/VFField.lean` gives `Field (Transfer.VFType M)` from `M ⊨ Axioms.ACVF`; this file adds the
valuation.  The predicate is the paper's `v x ≤ v y`, which in the encoding is `iLe (rv y) (rv x)` —
the two orders are reversed, because Mathlib's `Valuation` is the absolute-value convention and the
paper's is the value-group order (`Milestone0/DECISION.md`).

`IsValPred` and the construction of a `Valuation` from it are copied from `QE/Assembly_val.lean`
(proved there against that file's own copy of the encoding).  The proof that `predV` satisfies the
axioms is new here and uses `QE/RVCalc.lean`'s order calculus, which is the layer the frozen encoding
never had.

Payoff: with `Field (VFType M)` and `Valuation (VFType M) Γ` both available over `Enc`, the paper's
valuation-theoretic lemmas (`rv:root:lift:vf` / 3.2, `lift:divisible:hull` / 3.5, `e:transc` / 3.7)
can be *instantiated* at a model of the frozen `ACVF` instead of re-proved.
-/
import VFField

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.VFValued

/-! ## The semantic axiom set, and a valuation from it (copied from `Assembly_val`) -/

/-- The semantic axioms of a valued field, stated for a predicate `p` on a commutative ring.
They are exactly the sentences of `valFieldCore` (`axRefl`, `axTrans`, `axZeroLe`, `axZeroEq`,
`axUltra`, `axScale`), read in a ring with the ring operations in place of the function symbols. -/
structure IsValPred {R : Type*} [CommRing R] (p : R → R → Prop) : Prop where
  refl : ∀ x, p x x
  trans : ∀ x y z, p x y → p y z → p x z
  zero_le : ∀ x, p 0 x
  zero_eq : ∀ x, p x 0 → x = 0
  ultra : ∀ x y, p (x + y) x ∨ p (x + y) y
  total : ∀ x y, p x y ∨ p y x
  scale : ∀ x y z, z ≠ 0 → (p x y ↔ p (x * z) (y * z))

/-! ## 13. From a valued predicate to a Mathlib valuation -/

/-- **A predicate satisfying the axioms of `valField` is a `ValuativeRel`.**  This is what makes
the `L_val` side of the development talk to Mathlib's valuation theory: `ultra` in the form
`p (x + y) x ∨ p (x + y) y` gives the additive axiom, and `scale` (an iff) gives both
multiplicativity and cancellation.  `scale` only applies to nonzero multipliers, which is why
`vle_mul_cancel` splits on `z = 0`. -/
def valuativeRelOfIsValPred {K : Type*} [Field K] {p : K → K → Prop} (h : IsValPred p) :
    ValuativeRel K where
  vle := p
  vle_total := h.total
  vle_trans := fun hxy hyz => h.trans _ _ _ hxy hyz
  vle_add := fun {_ _ _} hxz hyz =>
    (h.ultra _ _).elim (fun h' => h.trans _ _ _ h' hxz) (fun h' => h.trans _ _ _ h' hyz)
  mul_vle_mul_left := fun {_ _} hxy z => by
    rcases eq_or_ne z 0 with rfl | hz
    · simpa using h.refl 0
    · exact (h.scale _ _ z hz).mp hxy
  vle_mul_cancel := fun {_ _ z} hz hxyz => by
    rcases eq_or_ne z 0 with rfl | hz0
    · exact absurd (h.refl 0) hz
    · exact (h.scale _ _ z hz0).mpr hxyz
  not_vle_one_zero := fun h10 => one_ne_zero (h.zero_eq 1 h10)
  vle_mul_comm := fun {x y} => by
    rw [mul_comm y x]
    exact h.refl (x * y)

/-- **Every valued predicate comes from a genuine valuation**, with the same relation.  Together
with `isValPred_of_valuation` this identifies the models of `valField` with Mathlib's valued
fields. -/
theorem exists_valuation_of_isValPred {K : Type} [Field K] {p : K → K → Prop}
    (h : IsValPred p) :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (v : Valuation K Γ),
      ∀ x y : K, p x y ↔ v x ≤ v y := by
  letI : ValuativeRel K := valuativeRelOfIsValPred h
  exact ⟨ValuativeRel.ValueGroupWithZero K, inferInstance, ValuativeRel.valuation K,
    fun x y => Valuation.vle_iff_le (ValuativeRel.valuation K)⟩



/-! ## `predV` satisfies it -/

section Model

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The `Field` structure on the `VF` sort, as an instance, so that `IsValPred`'s `CommRing`
requirement is discharged by typeclass search. -/
noncomputable instance instFieldVFType : Field (Transfer.VFType (M := M)) :=
  Transfer.vfFieldOfModel (M := M) (hM := hM)

/-- The paper's `v x ≤ v y` on the `VF` sort: `iLe (rv y) (rv x)`. -/
def predV (x y : Transfer.VFType (M := M)) : Prop := iLe (iRv y.1) (iRv x.1)

/-- `rv` of a nonzero `VF`-element is not `∞`. -/
theorem rv_ne_zero_of_ne_zero {z : M} (hz : iVF z) (hz0 : z ≠ Transfer.iVFZero) :
    iRv z ≠ iRVZero := by
  intro h
  exact hz0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hz h)

/-- **`predV` is a valuation predicate.**  All seven fields come from `RVCalc`: the preorder laws,
`∞` as top, the ultrametric inequality, and scale invariance (`le_mul_iff`) together with
multiplicativity of `rv` (`rv_mul_hom_of_model`). -/
theorem isValPred_predV : IsValPred (predV (M := M)) where
  refl := fun x => RVCalc.le_refl_rv hM (Transfer.rv_mem hM x.2)
  trans := fun x y z h1 h2 =>
    RVCalc.le_trans_rv hM (Transfer.rv_mem hM z.2) (Transfer.rv_mem hM y.2)
      (Transfer.rv_mem hM x.2) h2 h1
  zero_le := fun x => by
    have h0 : ((0 : Transfer.VFType (M := M))).1 = Transfer.iVFZero := rfl
    show iLe (iRv x.1) (iRv ((0 : Transfer.VFType (M := M))).1)
    rw [h0, RVCalc.rv_zero_eq hM]
    exact RVCalc.le_top_rv hM (Transfer.rv_mem hM x.2)
  zero_eq := fun x h => by
    have h0 : ((0 : Transfer.VFType (M := M))).1 = Transfer.iVFZero := rfl
    have hh : iLe (iRv ((0 : Transfer.VFType (M := M))).1) (iRv x.1) := h
    rw [h0, RVCalc.rv_zero_eq hM] at hh
    exact Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM x.2
      (RVCalc.le_infty_eq hM (Transfer.rv_mem hM x.2) hh))
  ultra := fun x y => RVCalc.rv_ultrametric hM x.2 y.2
  total := fun x y =>
    (RVCalc.le_total_rv hM (Transfer.rv_mem hM x.2) (Transfer.rv_mem hM y.2)).elim
      Or.inr Or.inl
  scale := fun x y z hz => by
    have hz' : iRv z.1 ≠ iRVZero :=
      rv_ne_zero_of_ne_zero z.2 (fun h => hz (Subtype.ext h))
    have h := RVCalc.le_mul_iff hM (Transfer.rv_mem hM y.2) (Transfer.rv_mem hM x.2)
      (Transfer.rv_mem hM z.2) hz'
    have hy : (y * z).1 = iVFMul y.1 z.1 := rfl
    have hx : (x * z).1 = iVFMul x.1 z.1 := rfl
    show iLe (iRv y.1) (iRv x.1) ↔ iLe (iRv (y * z).1) (iRv (x * z).1)
    rw [hy, hx, Transfer.rv_mul_hom_of_model hM y.2 z.2,
      Transfer.rv_mul_hom_of_model hM x.2 z.2]
    exact h

/-- **Every model of the frozen `ACVF` carries a genuine Mathlib valuation on its `VF` sort**, and
`predV` is that valuation's order: `iLe (rv y) (rv x) ↔ w x ≤ w y`. -/
theorem exists_valuation_predV :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
      (w : Valuation (Transfer.VFType (M := M)) Γ),
      ∀ x y : Transfer.VFType (M := M), predV x y ↔ w x ≤ w y :=
  exists_valuation_of_isValPred (isValPred_predV (M := M))

end Model

end SpecialTransformations.Milestone0.VFValued
