module

public import Mathlib

@[expose] public section

/-!
# Basic constructions: valued fields and the RV sort

This file starts the algebraic layer of the paper, independent of model theory.

Reference: Yin, *Special transformations in algebraically closed valued fields*,
Section 2 (arXiv:1006.2467).
-/
open Valuation

namespace SpecialTransformations

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The RV sort with the point at infinity: `RV = RV× ∪ {∞}`.
`none` is `∞`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- `RV0 = RV ∪ {0}`.  The outer `none` is the added `0`. -/
abbrev RV0 : Type _ := Option (RV v)

/-- The quotient map `rv : K → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk (Units.mk0 x h))

/- The valuation `vrv : RV → Γ ∪ {∞}` induced by `v`.
TODO: define via the quotient lift; needs the comparison between `v` and
`v.valuationSubring.valuation`. -/
-- def vrv : RV v → Γ₀ := ...

end SpecialTransformations
