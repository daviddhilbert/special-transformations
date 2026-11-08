import Section3.MeanInBalls
import CanonicalResidue

/-!
# Residue characteristic zero in the actual ACVF model

The later derivative and integer determinant arguments need characteristic
zero of the residue field. Use the checked Section 3 valuation of positive
integers, derived from ACVF00, and the released actual residue projection.
-/

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace SpecialTransformations.Section7

variable {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]

theorem residueField_charZero_of_model00 (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
    (h00 : M ⊨ Axioms.ACVF00) : CharZero (ResidueField v.valuationSubring) := by
  apply charZero_of_inj_zero
  intro n hn
  by_contra hn0
  have hval : v (v.valuationSubring.subtype (n : v.valuationSubring)) = 1 := by
    rw [map_natCast]
    exact Barycentre.natCast_value_one v hv h00 n hn0
  have hnonzero : residue v.valuationSubring (n : v.valuationSubring) ≠ 0 :=
    (CanonicalResidue.residue_nonzero_iff v _).mpr hval
  exact hnonzero (by simpa only [map_natCast] using hn)

end SpecialTransformations.Section7
