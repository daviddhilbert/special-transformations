import Section4.VFDimensionRank
import Section3.NormalizationSaturation

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The dimension/transcendence-degree equality with the actual Gamma
quotient in the canonical normalization of the released language. -/
theorem lemma_4_4_actual_gamma {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {n r : ℕ} :
    let N := @CanonicalStructure.normalize M sM
    let Γ : @DefinableGeometry.Space LRV M N := @gammaSpace M sM hM
    let hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
    letI := N
    letI : M ⊨ Axioms.ACVF := hN
    ∀ A : DefSet (rawMixedSpace (M := M) n r) S, vfDim Γ A = vfTrdeg A := by
  dsimp only
  let N := @CanonicalStructure.normalize M sM
  let Γ : @DefinableGeometry.Space LRV M N := @gammaSpace M sM hM
  have hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
  have hcan : @CanonicalStructure.IsCanonical M N := @CanonicalStructure.normalize_isCanonical M sM
  have hΓ : @DefinableGeometry.Space.RVCoded M N Γ := @gammaSpace_rvCoded M sM hM
  have hsN : @Saturated M N κ := @Saturated.normalize M sM κ hs
  letI := N
  letI : M ⊨ Axioms.ACVF := hN
  intro A
  exact @lemma_4_4 M N hN hcan κ hsN S hsmall Γ hΓ n r A

end SpecialTransformations.Section4
