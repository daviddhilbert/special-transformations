/-
Copyright: none.  Ultramath swarm smw2ngn1z, member m2 (direction d3).

# The value-group step of Lemma 3.6 instantiated at the tree's value group

`RatRank.lean` proves the group-theoretic step

  `H` divisible + `RatRankZero H K` (`K/H` torsion) ⟹ `K = H`

for `[CommGroup G] [LinearOrder G] [IsOrderedMonoid G]`.  This file checks that the tree's value
group `GammaOf M` of a model `M ⊨ ACVF` (`QE/GammaGroup.lean`: `gammaOfCommGroup`,
`gammaOfLinearOrder`, `gammaIsOrderedMonoid`) satisfies exactly those instances, that its
divisibility as recorded in `QE/GammaDiv.lean` (`gamma_divisible`, `gammaOfRootableBy`) is the
hypothesis `DivisibleSubgroup`, and that the step therefore fires at `GammaOf M` with no further
translation.

What is *not* here (it is direction d1's work): identifying the tree's `GammaEq S T` — "adjoining
`e` does not change `Γ`" as a statement about value *classes* of a substructure
(`QE/M5Ledger.lean`) — with a subgroup inclusion/equality in `GammaOf M`.  Once `Γ(Ŝ) ≤ Γ(M)` is
realised as `H ≤ K` with `H` divisible and `K/H` of rational rank `0` (the PE quote), this file's
theorems give `K = H`; the translation of `GammaEq` into that shape is the remaining wiring.
-/
import GammaDiv
import RatRank

set_option autoImplicit false
set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.GammaGroup

namespace Ultramath.M2RR

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **Lemma 3.6's value-group step at the tree's `Γ(M)`**: for subgroups `H ≤ K` of `GammaOf M`,
if `H` is divisible and `K/H` has rational rank `0`, then `K = H`.  This is
`eq_of_divisible_of_ratRankZero` applied at `GammaOf M`; the types check with no translation
because `GammaGroup.gammaOfCommGroup`, `gammaOfLinearOrder`, `gammaIsOrderedMonoid` are exactly
the instances the abstract theorem asks for. -/
theorem gamma_eq_of_divisible_of_ratRankZero {H K : Subgroup (GammaOf M)} (hHK : H ≤ K)
    (hdiv : DivisibleSubgroup H) (hrank : RatRankZero H K) : K = H :=
  eq_of_divisible_of_ratRankZero hHK hdiv hrank

/-- The `K = ⊤` form at `GammaOf M`: a divisible `Γ(Ŝ)` of rational rank `0` in `Γ(M)` is `Γ(M)`. -/
theorem gamma_eq_top_of_divisible_of_ratRankZero {H : Subgroup (GammaOf M)}
    (hdiv : DivisibleSubgroup H) (hrank : RatRankZero H ⊤) : H = ⊤ :=
  eq_top_of_divisible_of_ratRankZero_top hdiv hrank

/-- **`Γ(M)` is divisible** in the sense of this development, from `GammaDiv.gamma_divisible`. -/
theorem gamma_top_divisible : DivisibleSubgroup (⊤ : Subgroup (GammaOf M)) := by
  intro x _ n hn
  obtain ⟨b, hb⟩ := GammaDiv.gamma_divisible (M := M) n hn x
  exact ⟨b, trivial, hb⟩

/-- The same, from the `RootableBy` instance `GammaDiv.gammaOfRootableBy` — this is the form in
which the tree records divisibility of `Γ(M)`. -/
theorem gamma_top_divisible_of_rootableBy [RootableBy (GammaOf M) ℕ] :
    DivisibleSubgroup (⊤ : Subgroup (GammaOf M)) := by
  intro x _ n hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨y, hy⟩ := RootableBy.surjective_pow (A := GammaOf M) (α := ℕ) (n := n) hn0 x
  exact ⟨y, trivial, hy⟩

/-- `eq_of_divisible_of_ratRankZero` at `GammaOf M` with `H = ⊤`: the nontrivial instance that
the step is satisfiable in the tree's value group. -/
theorem gamma_paper_step_fires {K : Subgroup (GammaOf M)} (hK : (⊤ : Subgroup (GammaOf M)) ≤ K)
    (hrank : RatRankZero ⊤ K) : K = ⊤ :=
  eq_of_divisible_of_ratRankZero hK gamma_top_divisible hrank

end Ultramath.M2RR

/-! ## Axiom check -/

#print axioms Ultramath.M2RR.gamma_eq_of_divisible_of_ratRankZero
#print axioms Ultramath.M2RR.gamma_eq_top_of_divisible_of_ratRankZero
#print axioms Ultramath.M2RR.gamma_top_divisible
#print axioms Ultramath.M2RR.gamma_top_divisible_of_rootableBy
#print axioms Ultramath.M2RR.gamma_paper_step_fires
