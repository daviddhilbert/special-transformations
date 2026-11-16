module

public import Section9.MixedGenericDifferentiation
public import Section9.ImplicitScalarDerivations

@[expose] public section

/-! The entries of the VF Jacobian of a definable map can be computed
by coordinate derivations in any field containing the graph point and
embedded over the original coefficient field. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF

set_option maxHeartbeats 450000 in
theorem hasMixedVFDerivativeAt_of_graph_derivations [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    {G : Type} [LinearOrderedCommGroupWithZero G] [Valued VF G]
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) (p : A)
    (hi : AlgebraicIndependent (vfParameterField S) p.val.1)
    {K : Type} [Field K] [Algebra (vfParameterField S) K]
    (g : K →ₐ[vfParameterField S] VF) (x y : Fin n → K)
    (hx : ∀ i, g (x i) = p.val.1 i) (hy : ∀ i, g (y i) = (f p).val.1 i)
    (D : Fin n → Derivation (vfParameterField S) K K)
    (hD : ∀ j i, D j (x i) = if j = i then 1 else 0) :
    HasMixedVFDerivativeAt f p (Matrix.toLin' (Matrix.of (fun i j => g (D j (y i))))) := by
  choose P hP hP' using fun j => exists_simpleRoot_equation_of_tupleField _ p.val.1 ((f p).val.1 j)
    (map_output_vf_coordinate_isAlgebraic hc f p j)
  have h := mixedDifferentiableAt_of_independent_of_simple_equations hc hκ hs hsmall hv f p hi P hP hP'
  obtain ⟨F, hF, hDer⟩ := h
  refine ⟨F, hF, ?_⟩
  have he (i : Fin n) (Q : MvPolynomial (Fin n ⊕ Unit) (vfParameterField S)) :
      g (aeval (Sum.elim x (fun _ => y i)) Q) =
        aeval (Sum.elim p.val.1 (fun _ => (f p).val.1 i)) Q := by
    have hh : g ∘ Sum.elim x (fun _ : Unit => y i) = Sum.elim p.val.1 (fun _ => (f p).val.1 i) := by
      funext j
      cases j with
      | inl j => exact hx j
      | inr _ => exact hy i
    rw [comp_aeval_apply]
    change aeval (g ∘ Sum.elim x (fun _ : Unit => y i)) Q = _
    rw [hh]
  have heval (i j : Fin n) :
      implicitScalarSlope (P i) (Sum.elim p.val.1 (fun _ => (f p).val.1 i)) (Pi.single j 1) =
        g (D j (y i)) := by
    have hzero : aeval (Sum.elim x (fun _ => y i)) (P i) = 0 :=
      g.injective ((he i (P i)).trans ((hP i).trans (map_zero g).symm))
    have hsimple : aeval (Sum.elim x (fun _ => y i)) (pderiv (Sum.inr ()) (P i)) ≠ 0 := by
      intro hzero
      exact hP' i ((he i _).symm.trans (by rw [hzero, map_zero]))
    rw [← implicitScalarSlope_eq_derivation (P i) x (y i) hzero hsimple j (D j) (hD j)]
    rw [implicitScalarSlope_single, implicitScalarSlope_single, map_div₀, map_neg, he, he]
  have hmat : LinearMap.toMatrix' (LinearMap.pi fun i =>
      implicitScalarSlope (P i) (Sum.elim p.val.1 (fun _ => (f p).val.1 i))) =
      Matrix.of (fun i j => g (D j (y i))) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    exact heval i j
  rw [← hmat, Matrix.toLin'_toMatrix']
  exact hDer

end SpecialTransformations.Section9
