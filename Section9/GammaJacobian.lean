module

public import Section3.GammaValueLaws

@[expose] public section

/-! The Gamma part of Definition 9.14 on nondegenerate RV volume labels.
The paper writes the value group additively. The released Lean
presentation writes it multiplicatively. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped BigOperators

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

noncomputable def rvVolumeGamma (t : Fin n → CanonicalRV.RVSort M)
    (ht : ∀ i, (t i).val ≠ iRVZero) : Values.Gamma (M := M) :=
  ∏ i, Values.gammaOf (t i) (ht i)

/-- The difference of target and source total values. -/
noncomputable def rvGammaJacobian (t s : Fin n → CanonicalRV.RVSort M)
    (ht : ∀ i, (t i).val ≠ iRVZero) (hs : ∀ i, (s i).val ≠ iRVZero) :
    Values.Gamma (M := M) :=
  rvVolumeGamma s hs / rvVolumeGamma t ht

theorem rvGammaJacobian_self (t : Fin n → CanonicalRV.RVSort M)
    (ht : ∀ i, (t i).val ≠ iRVZero) : rvGammaJacobian t t ht ht = 1 := by
  simp [rvGammaJacobian]

theorem rvGammaJacobian_comp (t s u : Fin n → CanonicalRV.RVSort M)
    (ht : ∀ i, (t i).val ≠ iRVZero) (hs : ∀ i, (s i).val ≠ iRVZero)
    (hu : ∀ i, (u i).val ≠ iRVZero) :
    rvGammaJacobian t u ht hu = rvGammaJacobian s u hs hu * rvGammaJacobian t s ht hs := by
  unfold rvGammaJacobian
  symm
  calc
    _ = (rvVolumeGamma u hu * ((rvVolumeGamma s hs)⁻¹ * rvVolumeGamma s hs)) *
        (rvVolumeGamma t ht)⁻¹ := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = _ := by rw [inv_mul_cancel, mul_one, div_eq_mul_inv]

end SpecialTransformations.Section9
