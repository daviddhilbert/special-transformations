import Section7.GeneralizedHensel
import Section7.EncodedResidueRoots
import VFAlgClosed

/-! Lemma 7.2 on the actual VF/RV sorts of the pinned ACVF language.
The compatible valuation and the quotient equivalence are the published
interfaces; algebraic closedness is derived from the actual ACVF model. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

def EncodedSimpleCommonResidueRoot {n : ℕ} (t : Fin n → CanonicalRV.RVSort M)
    (α : Fin n → Γ) (F : Fin n → MvPolynomial (Fin n) (VFType (M := M))) : Prop :=
  IsSimpleCommonResidueRoot v (fun i => (CanonicalRV.equiv v hv).symm (t i)) α F

theorem encoded_generalized_hensel {n : ℕ} {t : Fin n → CanonicalRV.RVSort M}
    {α : Fin n → Γ} {F : Fin n → MvPolynomial (Fin n) (VFType (M := M))}
    (h : EncodedSimpleCommonResidueRoot v hv t α F) :
    ∃! a : Fin n → VFType (M := M), a ∈ EncodedRVFibre t ∧ ∀ i, (F i).eval a = 0 := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  rw [encodedRVFibre_eq v hv t]
  exact generalized_hensel v h

end SpecialTransformations.Section7
