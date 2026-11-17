module

public import Section10.WeightedZeroScissors

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Concrete RV- and Gamma-valued zero-degree forms of 10.4–10.6. -/

set_option autoImplicit false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem theorem_10_4_rv_zero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : MeasuredVFZero hc (C.base : Set M) rvVolumeScale) :
    ∃ U : MeasuredRVZero (C.base : Set M) rvVolumeScale, Nonempty (A ≅ U.lift hc) :=
  theorem_10_4_weighted_zero hc C.uncountable.le C.saturated C.model00 C.small A

theorem theorem_10_4_gamma_zero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : MeasuredVFZero hc (C.base : Set M) (gammaVolumeScale hc)) :
    ∃ U : MeasuredRVZero (C.base : Set M) (gammaVolumeScale hc), Nonempty (A ≅ U.lift hc) :=
  theorem_10_4_weighted_zero hc C.uncountable.le C.saturated C.model00 C.small A

theorem theorem_10_5_rv_zero (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    {U V : MeasuredRVZero S rvVolumeScale} (e : U ≅ V) : Nonempty (U.lift hc ≅ V.lift hc) :=
  MeasuredRVZero.theorem_10_5_weighted_zero hc e

theorem theorem_10_5_gamma_zero (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    {U V : MeasuredRVZero S (gammaVolumeScale hc)} (e : U ≅ V) :
    Nonempty (U.lift hc ≅ V.lift hc) :=
  MeasuredRVZero.theorem_10_5_weighted_zero hc e

theorem corollary_10_6_rv_zero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Function.Surjective (MeasuredRVZero.liftHom (S := (C.base : Set M)) (d := rvVolumeScale) hc) :=
  MeasuredRVZero.corollary_10_6_weighted_zero hc C.uncountable.le C.saturated C.model00 C.small

theorem corollary_10_6_gamma_zero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Function.Surjective (MeasuredRVZero.liftHom (S := (C.base : Set M)) (d := gammaVolumeScale hc) hc) :=
  MeasuredRVZero.corollary_10_6_weighted_zero hc C.uncountable.le C.saturated C.model00 C.small

/-- Equality of the represented weights is exact Gamma equality. -/
theorem gammaZeroForm_weight_eq_iff {hc : CanonicalStructure.IsCanonical (M := M)}
    {P Q : DefinableGeometry.Space LRV M} {S : Set M}
    {A : DefinableGeometry.DefSet P S} {B : DefinableGeometry.DefSet Q S}
    (ω : ZeroForm (gammaVolumeScale hc) A) (η : ZeroForm (gammaVolumeScale hc) B)
    (a : A) (b : B) :
    ω.weight a = η.weight b ↔
      gammaFormValue (hc := hc) ω.map a = gammaFormValue (hc := hc) η.map b := by
  change (gammaFormValue (hc := hc) ω.map a).val = (gammaFormValue (hc := hc) η.map b).val ↔ _
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end SpecialTransformations.Section10
