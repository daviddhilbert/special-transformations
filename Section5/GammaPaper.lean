import Section5.GammaExistence
import Section5.GammaInvariantLogic
import Section5.Surjectivity

/-! Theorems 5.4 and 5.5 over a base with named Gamma parameters, with no
remaining inputs. The three inputs of `theorem_5_4_gamma` and
`theorem_5_5_gamma` are discharged: `gammaLogicInput` holds for every base,
`uniformVerticalObstacles` follows from saturation and a small real base, and
the polynomial-support input follows from either base convention.

* `*_of_fieldBase`: the VF part of the real base is a field (`VFFieldBase`).
* the unsuffixed forms: the base is VF-Gamma-generated (`VFGammaGeneratedBase`),
  the convention of the paper. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section5.Paper

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Section3.GammaParameters.Base (M := M)} {S : Set M} {n m k : ℕ}

theorem theorem_5_5_finite_gamma_of_fieldBase {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (F : VFFieldBase B.real)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ i e, ((p i).coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier E) ∧
        ∀ b c : E, SameRV b.val c.val → ∀ i,
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) (p i)) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) (p i)) :=
  Section5.theorem_5_5_finite_gamma h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_fieldBase B F) hBS τ hτ p hc

theorem theorem_5_5_gamma_of_fieldBase {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (F : VFFieldBase B.real)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : MvPolynomial (Fin n) (VF (M := M))) (hc : ∀ e, (p.coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier E) ∧
        ∀ b c : E, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) p) :=
  Section5.theorem_5_5_gamma h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_fieldBase B F) hBS τ hτ p hc

theorem theorem_5_4_gamma_of_fieldBase {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (F : VFFieldBase B.real)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (u : Fin n → RV (M := M)) (hFibre : carrier A₀ = {p | ∀ i, rv (vfAt p i) = u i})
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : MvPolynomial (Fin n) (VF (M := M))) (hc : ∀ e, (p.coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        ∀ b c : E, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) p) :=
  Section5.theorem_5_4_gamma h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_fieldBase B F) hBS u hFibre τ hτ p hc

/-- Theorem 5.5 for finitely many polynomials over a VF-Gamma-generated base. -/
theorem theorem_5_5_finite_gamma {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : Section3.GammaParameters.VFGammaGeneratedBase B)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ i e, ((p i).coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier E) ∧
        ∀ b c : E, SameRV b.val c.val → ∀ i,
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) (p i)) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) (p i)) :=
  Section5.theorem_5_5_finite_gamma h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_generatedBase B hB) hBS τ hτ p hc

/-- Theorem 5.5 over a VF-Gamma-generated base. -/
theorem theorem_5_5_gamma {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : Section3.GammaParameters.VFGammaGeneratedBase B)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : MvPolynomial (Fin n) (VF (M := M))) (hc : ∀ e, (p.coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier E) ∧
        ∀ b c : E, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) p) :=
  Section5.theorem_5_5_gamma h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_generatedBase B hB) hBS τ hτ p hc

/-- Theorem 5.4 over a VF-Gamma-generated base. -/
theorem theorem_5_4_gamma {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : Section3.GammaParameters.VFGammaGeneratedBase B)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (u : Fin n → RV (M := M)) (hFibre : carrier A₀ = {p | ∀ i, rv (vfAt p i) = u i})
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : MvPolynomial (Fin n) (VF (M := M))) (hc : ∀ e, (p.coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        ∀ b c : E, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) p) :=
  Section5.theorem_5_4_gamma h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_generatedBase B hB) hBS u hFibre τ hτ p hc

end SpecialTransformations.Section5.Paper
