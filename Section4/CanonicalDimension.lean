import Section4.VFDimension
import Section4.Spaces
import Section3.NormalizationSaturation
import Section3.CanonicalContext

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! The dimension theorem with the actual Gamma quotient, in the canonical
normalization of the released LRV language. Earlier-section normalization,
model, and saturation results are used as given. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem lemma_4_2_actual_gamma (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {n r : ℕ} :
    let N := @CanonicalStructure.normalize M sM
    let Γ : @DefinableGeometry.Space LRV M N := @gammaSpace M sM hM
    let hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
    letI := N
    letI : M ⊨ Axioms.ACVF := hN
    ∀ (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ),
      vfDim Γ A ≤ k ↔ ∃ i : AuxiliaryCoordinates, ∃ f : Map A
        (DefSet.univ ((rawVFSpace k).prod (i.space Γ)) S), Function.Injective f := by
  dsimp only
  let N := @CanonicalStructure.normalize M sM
  let Γ : @DefinableGeometry.Space LRV M N := @gammaSpace M sM hM
  have hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
  have hN00 : @Theory.Model LRV M N Axioms.ACVF00 := @normalized_model00 M sM hM h00
  have hsN : @Saturated M N κ := @Saturated.normalize M sM κ hs
  letI := N
  letI : M ⊨ Axioms.ACVF := hN
  intro A k
  exact @lemma_4_2 M N hN Γ S n r hN00 κ hsN hsmall A k

end SpecialTransformations.Section4
