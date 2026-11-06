import Section4.ParameterInvariance
import Section4.RVPolydiscBound
import Section4.LiftBijections
import VFValued

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The released model itself supplies the compatible valuation. -/
theorem vfDim_parameter_invariant_model
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S T : Set M}
    (hS : Cardinal.mk S < κ) (hT : Cardinal.mk T < κ) (hST : S ⊆ T)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) :
    vfDim Δ (A.extend hST) = vfDim Δ A := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VFType (M := M)) Γ := Valued.mk' v
  exact vfDim_parameter_invariant hcan hs hS hT hST Δ hΔ hv A

theorem corollary_4_7_model (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n k r : ℕ} (A : DefSet (rawMixedSpace (M := M) (n + k) r) S)
    (t : Fin k → CanonicalRV.RVSort M) (ht : ∀ i, (t i).val ≠ iRVZero)
    (s : Fin r → CanonicalRV.RVSort M)
    (hcontains : ∀ a : Fin k → VFType (M := M), tupleRV a = t →
      (zeroPrefix n a, s) ∈ A.carrier) : k ≤ vfDim Δ A := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VFType (M := M)) Γ := Valued.mk' v
  exact corollary_4_7 hcan hs hsmall Δ hΔ hv A t ht s hcontains

theorem lemma_4_20_model (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {k : ℕ} {U V : RVObject (M := M) S k}
    (F : Map U.domain V.domain) (G : Map (rvLift U) (rvLift V))
    (hcomm : LiftCommutes F G) (hinj : Function.Injective G) :
    ∃ H : RVHom U V, H.map = F := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VFType (M := M)) Γ := Valued.mk' v
  exact lemma_4_20 hcan hκ hs hsmall Δ hΔ hv F G hcomm hinj

end SpecialTransformations.Section4

end
