module

public import Section5.GammaDimensionalPresentation
public import Section5.GammaDimension
public import Section5.GammaFiniteFibres

@[expose] public section

/-! Corollary 5.7 for sets and isomorphisms definable over a base
with named Gamma values. The VF coefficient field is the convention
immediately before Convention 2.5. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace SpecialTransformations.Section5.Paper

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem corollary_5_7_gamma {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (F : VFFieldBase B.real) {n m k : ℕ}
    (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A)
    (hdim : GammaHasVFDimLE B A k) :
    ∃ U : GammaRVObject B k, Nonempty (GammaIso B A U.lift) :=
  gammaLift_of_rank hκ hs h00 B hsmall F A hA (gamma_rank_of_dimension hdim)

theorem corollary_5_7_finite_gamma {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (F : VFFieldBase B.real) {n m k : ℕ}
    (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A)
    (hdim : GammaHasVFDimLE B A k)
    (hfin : ∀ x : Fin n → VF (M := M), {t : Fin m → RV (M := M) | (x, t) ∈ A}.Finite) :
    ∃ U : GammaRVFiniteObject B k, Nonempty (GammaIso B A U.toGammaRVObject.lift) := by
  have hrank := gamma_rank_of_dimension hdim
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  exact Section5.corollary_5_7_finite_gamma h00 v hv
    (uniformVerticalObstacles hs hsmall v hv)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_fieldBase B F)
    (gammaPresentationInput B) A
    (gammaDimensionalPresentation_of_rank hκ hs h00 B hsmall A hA hrank)
    (fun _ e => finiteRVFibres_of_gammaIso hκ hs B hsmall e hrank hfin)

end SpecialTransformations.Section5.Paper
