module

public import Section9.WeightedAffineLift
public import Section9.RVJacobianException
public import Section9.GammaCompatibility

@[expose] public section

/-! Theorem 9.16 on a piece with finite head projections already in
first position on both sides. The assumptions on the prescribed form
use the paper's Gamma quotient. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {k m : ℕ}
local notation "VF" => VFType (M := M)

theorem exists_prescribed_lift_with_finite_heads_ae [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {U V : RVFiniteObject (M := M) B.real (k + m)} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hheadU : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (hheadV : (rvHeadVolume V.obj (productLeft k m)).FiniteFibres) (j : Fin m)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) B.real))
    (hω : let E := (finiteVolumeProperty B.real (k + m)).ι.mapIso e
      ∀ u : U.obj.domain, Values.vrv ((ω u).val 0) =
        (rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty B.real (k + m)).ι.mapIso e).hom.map.graph p.val.2 (G p).val.2) ∧
      ∃ Z : DefSet (rawMixedSpace (M := M) (k + m) U.obj.arity) B.real,
        Z.carrier ⊆ (rvLift U.obj).carrier ∧ vfDim (rawRVSpace (M := M) 1) Z < k + m ∧
        ∀ p : rvLift U.obj, p.val ∉ Z.carrier → ∃ J : VF, HasMixedVFJacobianAt G p J ∧
          CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  let E := (finiteVolumeProperty B.real (k + m)).ι.mapIso e
  have hω₀ (u : U.obj.domain) : ((ω u).val 0).val ≠ iRVZero :=
    rv_nonzero_of_gammaJacobian_value _ _ (hU u) (hV (E.hom.map u)) _ (hω u)
  obtain ⟨G, hG, hGlabel, hGjac⟩ := exists_prescribed_lift_of_finite_heads hc hκ hs h00 B hsmall hB v hv e
    hU hV hheadU hheadV j ω hω₀ (fun u x y c hx hy hrep =>
      rvGammaJacobian_value_of_representatives v hv _ _ (hU u) (hV (E.hom.map u)) _ (hω u) x y c hx hy hrep)
  have hpos : 0 < k + m := by have := j.isLt; omega
  letI : Valued VF Γ := Valued.mk' v
  refine ⟨G, hG, hGlabel, exists_mixedRVJacobian_exception hc hs hsmall hpos G (ω.comp (liftLabelMap U.obj)) ?_⟩
  intro p hp
  obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv G p hp
  obtain ⟨J, hJ, hrep⟩ := hGjac p hp
  have he : (LinearMap.toMatrix' L).det = J := by
    obtain ⟨F, hF, hDer⟩ := hL
    exact (show HasMixedVFJacobianAt G p _ from ⟨F, hF, hDer.hasJacobianAt⟩).unique hJ
  exact ⟨L, hL, (congrArg CanonicalRV.encodedRv he).trans hrep⟩

end SpecialTransformations.Section9
