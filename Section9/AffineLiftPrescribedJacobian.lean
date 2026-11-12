module

public import Section9.AffineLift
public import Section9.AffineLiftJacobian
public import Section9.MixedGenericDifferentiation

@[expose] public section

/-! An affine lift realizes the prescribed determinant at generic
points as soon as the head determinant has the required value. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {k m : ℕ}
local notation "VF" => VFType (M := M)

theorem exists_affineLift_with_jacobian [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    (U V : RVFiniteObject (M := M) S (k + m))
    (hU : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (hV : (rvHeadVolume V.obj (productLeft k m)).FiniteFibres)
    (F : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (rvLift (rvFiniteHead V (productLeft k m) hV).obj)) (hF : Function.Bijective F)
    (a b : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) m) S))
    (D c : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) 1) S)) (j : Fin m)
    (ha : ∀ p i, (a p).val i ≠ 0) (hb : ∀ p i, (b p).val i ≠ 0)
    (haRV : ∀ p, tupleRV (a p).val = U.obj.value
      (liftLabelMap (rvFiniteHead U (productLeft k m) hU).obj p) ∘ productRight k m)
    (hbRV : ∀ p, tupleRV (b p).val = V.obj.value
      (liftLabelMap (rvFiniteHead V (productLeft k m) hV).obj (F p)) ∘ productRight k m)
    (hD : ∀ p L, HasMixedVFDerivativeAt F p L → (D p).val 0 = (LinearMap.toMatrix' L).det)
    (hgood : ∀ p : rvLift (rvFiniteHead U (productLeft k m) hU).obj,
      AlgebraicIndependent (vfParameterField S) p.val.1 →
      affineTailCorrectionGood v (a p).val (b p).val ((D p).val 0) ((c p).val 0)) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧
      (∀ p : rvLift U.obj, (G p).val.2 = (F (rvLiftHeadSelect U (productLeft k m) hU p)).val.2) ∧
      ∀ p : rvLift U.obj, AlgebraicIndependent (vfParameterField S) p.val.1 →
        HasMixedVFJacobianAt G p ((c (rvLiftHeadSelect U (productLeft k m) hU p)).val 0) := by
  obtain ⟨G, hG, hEq⟩ := exists_affineLift_of_headLift v hv U V hU hV F hF a b D c j ha hb haRV hbRV
  refine ⟨G, hG, fun p => congrArg Prod.snd (hEq p), ?_⟩
  letI : Valued VF Γ := Valued.mk' v
  intro p hp
  let x := rvLiftHeadSelect U (productLeft k m) hU p
  have hx : AlgebraicIndependent (vfParameterField S) x.val.1 :=
    hp.comp (productLeft k m) (productLeft k m).injective
  obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv G p hp
  obtain ⟨L₁, hL₁⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv F x hx
  let s p := affineTailSlopesForHead v (a p).val (b p).val j ((D p).val 0) ((c p).val 0)
  have hdet := det_affineLift_of_mixed_derivatives U V hU hV F G (fun p => (a p).val) (fun p => (b p).val) s
    (fun p => congrArg Prod.fst (hEq p)) p L₁ L hL₁ hL
  have hval : (LinearMap.toMatrix' L).det = (c x).val 0 := by
    rw [hdet, ← hD x L₁ hL₁]
    exact (affineTailSlopesForHead_spec v (a x).val (b x).val j ((D x).val 0) ((c x).val 0)
      (ha x) (hb x)).2 (hgood x hx)
  obtain ⟨Q, hQ, hder⟩ := hL
  exact ⟨Q, hQ, hval ▸ hder.hasJacobianAt⟩

end SpecialTransformations.Section9
