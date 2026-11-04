/-
**Wire-in: the Prestel–Engler quotations of `QE/ClassicalProps.lean` apply at a model of `ACVF`
with the paper's own value group `Γ(M)`.**

`QE/ClassicalProps.lean` states the two PE quotations as `Prop`s over an *arbitrary* valued field
`(K, v : Valuation K Γ)` with `[LinearOrderedCommGroupWithZero Γ]`.  To *use* them at a model `M`
of the frozen `ACVF` one needs `Valuation (VFType M) Γ` with `Γ` the paper's value group — that is
exactly what `ValueGroupBridge.vGammaValuation` provides:

* `henselization_at_model` — PE's henselization quotation specialised to `(VFType M, vGamma)`:
  there is a henselization `L` with **the same value group** `WithZero (Γ(M))` and an embedding
  `VFType M →+* L` preserving values.  Since `Γ(M) = v(K^×)` (`gv_surjective`), not a value is
  lost or added on either side; `same_value` is the field of the quotation that says so, restated
  as `henselization_same_value` for the record.
* `divisibleHull_at_model` — PE's divisible-hull quotation specialised to `Additive (Γ(M))`, in
  the additive notation `n • h = j g` in which the quotation is stated.  **Honest scope note**:
  at a model of `ACVF` the hull quote is *not* where the content is — `Γ(M)` is already divisible
  (`GammaDiv.gammaAdditiveDivisibleByNat : DivisibleBy (Additive (GammaOf M)) ℕ`), so the
  quotation is discharged with `H = Additive (Γ(M))`, `j = id`, `n = 1`.  The real content of
  `lift:divisible:hull` sits at *proper* substructures `S < M` (`M5Ledger.GammaHullInitial`,
  `GammaDiv.GammaHullInitialQ`), whose `Γ(S)` is not the value group of a model of `ACVF`; the
  top-model bridge of `ValueGroupBridge.lean` says nothing about those, and this file does not
  either.  What *is* checked here is that the quotation's interface (additive, ordered, `ℕ`-hull
  of `Γ(M)`) type-checks at the paper's value group.

Both theorems take the quotation as a **hypothesis** (`HenselizationExists`,
`DivisibleHullExists`) and prove nothing new — they are the machine check that the interface fits,
i.e. that the bridge's codomain really is the value group the quotes quantify over.  No axiom is
introduced: the quotations are `def`s of type `Prop` in `QE/ClassicalProps.lean`.
-/
import ValueGroupBridge
import ClassicalProps

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.GammaGroup
open SpecialTransformations.Milestone0.VGBridge

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SpecialTransformations.Milestone0.VGBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **PE's henselization quotation at a model of `ACVF`, with the paper's value group.** -/
theorem henselization_at_model (hPE : ClassicalProps.HenselizationExists) :
    Nonempty (ClassicalProps.HenselizationOf (vGammaValuation (M := M))) :=
  hPE (v := vGammaValuation (M := M))

/-- **The henselization's value group is `Γ(M)`**: every nonzero element of the henselization has
the value of a base element, the two values being taken in the *same* group
`WithZero (Γ(M))` (`HenselizationOf.same_value`, stated for the record). -/
theorem henselization_same_value (H : ClassicalProps.HenselizationOf (vGammaValuation (M := M))) :
    letI := H.fieldL
    ∀ {x : H.L}, x ≠ 0 → ∃ k : Transfer.VFType (M := M), vGammaValuation k = H.w x := by
  letI := H.fieldL
  intro x hx
  exact H.same_value x hx

/-- **PE's divisible-hull quotation applied to `Γ(M)`** (additive notation, as the quotation is
stated): `Γ(M)` embeds monotonically and injectively into a divisible ordered abelian group, with
every element of the hull a positive multiple of an image.  This is the group-level input of the
`lift:divisible:hull` case lemma. -/
theorem divisibleHull_at_model (hPE : ClassicalProps.DivisibleHullExists) :
    ∃ (H : Type) (_ : AddCommGroup H) (_ : LinearOrder H) (_ : IsOrderedAddMonoid H)
      (_ : DivisibleBy H ℕ) (j : Additive (GammaOf M) →+ H),
      Function.Injective j ∧ Monotone j ∧
        (∀ h : H, ∃ n : ℕ, 0 < n ∧ ∃ g : Additive (GammaOf M), n • h = j g) :=
  hPE (Additive (GammaOf M))

end

end SpecialTransformations.Milestone0.VGBridge

#print axioms SpecialTransformations.Milestone0.VGBridge.henselization_at_model
#print axioms SpecialTransformations.Milestone0.VGBridge.henselization_same_value
#print axioms SpecialTransformations.Milestone0.VGBridge.divisibleHull_at_model
