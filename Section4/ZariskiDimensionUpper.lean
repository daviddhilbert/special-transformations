module

public import Section4.AffineKrullDimension
public import Section4.ZariskiPrimeBound
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

/-- Bounding all prime components bounds the actual quotient-ring Krull
dimension, including the zero ring. -/
theorem ringKrullDim_quotient_le_of_prime_quotient_le
    {R : Type} [CommRing R] (I : Ideal R) (k : ℕ)
    (h : ∀ P : Ideal R, P.IsPrime → I ≤ P → ringKrullDim (R ⧸ P) ≤ k) :
    ringKrullDim (R ⧸ I) ≤ k := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro p
  have he : ringKrullDim (R ⧸ p.val.asIdeal) =
      (Order.coheight p.val : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient]
    change Order.krullDim (Set.Ici p.val) = (Order.coheight p.val : WithBot ℕ∞)
    exact (Order.coheight_eq_krullDim_Ici p.val).symm
  calc
    (Order.coheight p : WithBot ℕ∞) ≤ (Order.coheight p.val : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr (Order.coheight_le_coheight_apply_of_strictMono
        Subtype.val (fun _ _ hp => hp) p)
    _ = ringKrullDim (R ⧸ p.val.asIdeal) := he.symm
    _ ≤ k := h p.val.asIdeal p.val.isPrime p.property

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfZariski_dimension_le (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) :
    ringKrullDim (MvPolynomial (Fin n) (VFType (M := M)) ⧸ vfVanishingIdeal A) ≤ vfDim Δ A := by
  apply ringKrullDim_quotient_le_of_prime_quotient_le
  intro P hP hIP
  letI := hP
  rw [AffineKrullDimension.ringKrullDim_eq_trdeg_toNat (VFType (M := M)) _]
  exact_mod_cast prime_quotient_trdeg_le_vfDim hcan hs hsmall Δ hΔ A P hIP

end SpecialTransformations.Section4

end
