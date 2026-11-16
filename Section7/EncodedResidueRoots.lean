module

public import Section7.GammaPolynomial
public import CanonicalRV

@[expose] public section

/-! The Definition 7.1 result on the VF and RV sorts of the released language.
`CanonicalRV.equiv` is the proved quotient/encoded-sort bridge from ACVF-QE.
The valuation compatibility assumption displays the reversal of the paper's
order; no new saturation, characteristic or polynomial-normalization input
is used by the residue-root independence theorem. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

def EncodedRVFibre {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    Set (Fin n → VFType (M := M)) :=
  {a | ∀ i, CanonicalRV.encodedRv (a i) = t i}

theorem encodedRVFibre_eq {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    EncodedRVFibre t = RVFibre v (fun i => (CanonicalRV.equiv v hv).symm (t i)) := by
  ext a
  apply forall_congr'
  intro i
  rw [← CanonicalRV.equiv_rv v hv (a i)]
  exact (Equiv.eq_symm_apply _).symm

/-- The "some (hence all)" assertion with actual encoded RV parameters. -/
theorem encoded_residueRoot_iff_exists {n : ℕ} (t : Fin n → CanonicalRV.RVSort M)
    (ht : ∀ i, t i ≠ CanonicalRV.encodedRv (0 : VFType (M := M)))
    {α : Γ} {F : MvPolynomial (Fin n) (VFType (M := M))}
    (hF : IsGammaPolynomial v
      (fun i => _root_.RVCalc.vrv v ((CanonicalRV.equiv v hv).symm (t i))) α F) :
    (∀ a ∈ EncodedRVFibre t, v (F.eval a) < α) ↔
      ∃ a ∈ EncodedRVFibre t, v (F.eval a) < α := by
  have ht' (i : Fin n) : (CanonicalRV.equiv v hv).symm (t i) ≠ none := by
    intro he
    apply ht i
    have heq := congrArg (CanonicalRV.equiv v hv) he
    rw [Equiv.apply_symm_apply] at heq
    have hz : CanonicalRV.equiv v hv none =
        CanonicalRV.encodedRv (0 : VFType (M := M)) := by
      have hzero : _root_.RVCalc.rv v (0 : VFType (M := M)) = none :=
        _root_.RVCalc.rv_zero
      exact (congrArg (CanonicalRV.equiv v hv) hzero.symm).trans
        (CanonicalRV.equiv_rv v hv (0 : VFType (M := M)))
    exact heq.trans hz
  rw [encodedRVFibre_eq v hv t]
  exact residueRoot_iff_exists v ht' hF

end SpecialTransformations.Section7
