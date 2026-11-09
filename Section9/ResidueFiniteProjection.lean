import Section9.ResidueSimpleEquations
import Section4.FiniteCorrespondence
import Section4.TupleIndependence

/-! A point of a finite-to-finite residue correspondence has
independent target coordinates whenever its source coordinates
are independent over the same field. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem residue_independent_target_of_finite_reverse
    {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (E : Subfield K) (C : Set (Fin (n + n) → K)) (hC : Relative.Def E C)
    (x y : Fin n → K) (hxy : productTuple x y ∈ C)
    (hfin : {u | productTuple u y ∈ C}.Finite) (hx : AlgebraicIndependent E x) :
    AlgebraicIndependent E y := by
  let q : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  let e := (q.symm.trans (_root_.Equiv.sumComm (Fin n) (Fin n))).trans q
  have hs (a b : Fin n → K) : productTuple a b ∘ e = productTuple b a := by
    apply productTuple_ext
    · intro i
      have h : e (productLeft n n i) = productRight n n i :=
        congrArg (fun j => q (_root_.Equiv.sumComm (Fin n) (Fin n) j)) (q.symm_apply_apply (Sum.inl i))
      change productTuple a b (e (productLeft n n i)) = _
      rw [h, productTuple_right, productTuple_left]
    · intro i
      have h : e (productRight n n i) = productLeft n n i :=
        congrArg (fun j => q (_root_.Equiv.sumComm (Fin n) (Fin n) j)) (q.symm_apply_apply (Sum.inr i))
      change productTuple a b (e (productRight n n i)) = _
      rw [h, productTuple_left, productTuple_right]
  let D := {p | p ∘ e ∈ C}
  have hD : Relative.Def E D := hC.preimage_comp e
  have hp : productTuple y x ∈ D := by
    change productTuple y x ∘ e ∈ C
    rwa [hs]
  have hrow : {u | productTuple y u ∈ D}.Finite := by
    convert hfin using 1
    ext u
    change productTuple y u ∘ e ∈ C ↔ productTuple u y ∈ C
    rw [hs]
  have hAlg i := finite_residue_row_coordinate_isAlgebraic E D hD y x hp hrow i
  have h := tupleField_trdeg_mono_of_isAlgebraic E y x hAlg
  rw [(tupleField_trdeg_eq_arity_iff E x).mpr hx] at h
  exact (tupleField_trdeg_eq_arity_iff E y).mp ((tupleField_trdeg_le E y).antisymm h)

end SpecialTransformations.Section9
