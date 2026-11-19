import Section9.PrescribedVolumeLift
import Section9.GammaRepairLift
import Section9.GammaLiftDiscrepancy

/-! **Gamma Theorem 9.16** (finite-volume statement in positive arity) for
RV objects coded over a base context whose volume maps, isomorphism and
prescribed form have Gamma graphs over a VF-Gamma-generated base `B` with
`B.real` inside the code set. The lift has a Gamma graph over `B`.

Proof: the Gamma weighted lift; the Gamma discrepancy locus (Lemma L) is
contained in the RV-small discrepancy candidate of the raw comparison, so it
is RV-small; the Gamma repair on it. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
local notation "VF" => VFType (M := M)
local notation "n" => (k + 1)

theorem gamma_theorem_9_16_finite_volume [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) (hB : VFGammaGeneratedBase B) (hBS : B.real ⊆ (C.base : Set M))
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hUΓ : RVMapGamma U.obj.volume B) (hVΓ : RVMapGamma V.obj.volume B)
    (heΓ : RVMapGamma ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map B)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (hωΓ : RVMapGamma ω B)
    (hΓ : let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
      ∀ u : U.obj.domain, Values.vrv ((ω u).val 0) =
        (rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val)
    (hRV : let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
      ∃ X : DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M), rvDim X < n ∧
        ∀ u : U.obj.domain, u.val ∉ X.carrier →
          IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
            (U.obj.value u) (V.obj.value (E.hom.map u)) ((ω u).val 0))
    (hgraph : HenselizedGaussGraphInput VF) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧ MixedMapGamma G B ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map.graph
        p.val.2 (G p).val.2) ∧
      ∃ Z : DefSet (rawMixedSpace (M := M) n U.obj.arity) (C.base : Set M),
        Z.carrier ⊆ (rvLift U.obj).carrier ∧ vfDim (rawRVSpace (M := M) 1) Z < n ∧
        ∀ p : rvLift U.obj, p.val ∉ Z.carrier → ∃ J : VF, HasMixedVFJacobianAt G p J ∧
          CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
  let v := Values.presentationValuation (M := M)
  have hsmallB : Cardinal.mk B.real < C.κ := (Cardinal.mk_le_mk_of_subset hBS).trans_lt C.small
  obtain ⟨f, hf, hfΓ, hlabel, _⟩ := gamma_exists_weighted_liftMap_of_rvIso hc C.uncountable.le C.saturated
    C.model00 B hsmallB hB hBS C.small v Values.presentation_compatible E hU hV hUΓ hVΓ heΓ
  obtain ⟨X, hX, hω⟩ := hRV
  obtain ⟨D, hD, hsmallD, hgood⟩ := exists_small_liftComparison_discrepancy hc C (Nat.zero_lt_succ k)
    e hU hV f hf hlabel ω X hX hω hgraph
  have hω0 : ∀ u, (ω u).val 0 ≠ 0 := by
    intro u h0
    have := rv_nonzero_of_gammaJacobian_value _ _ (hU u) (hV (E.hom.map u)) _ (hΓ u)
    exact this ((congrArg Subtype.val h0).trans RVOperations.zero_val)
  obtain ⟨Eset, hEsub, hEΓ, hEchar⟩ := gamma_liftJacobian_discrepancy hc (Nat.zero_lt_succ k) U.obj V.obj f
    hfΓ ω hωΓ hω0
  have hED : Eset.carrier ⊆ D.carrier := by
    intro z hz
    let u : U.obj.domain := ⟨z, hEsub hz⟩
    obtain ⟨p, hp, hbad⟩ := (hEchar u).mp hz
    by_contra hzD
    have hpD : p.val.2 ∉ D.carrier := by
      have : p.val.2 = z := congrArg Subtype.val hp
      rw [this]
      exact hzD
    obtain ⟨L, hL, hdet⟩ := hgood p hpD
    exact hbad ⟨L, hL, hp ▸ hdet⟩
  have hdE : rvDim Eset < n := by
    let i : Map Eset D := Map.inclusion hED
    have hi : Function.Injective i := fun a b h => Subtype.ext (congrArg (fun z : D => z.val) h)
    exact (rvDim_le_of_finite_map i (Map.finiteFibres_of_injective hi)).trans_lt hsmallD
  apply gamma_repaired_lift_on_small_labels hc C B hB hBS v Values.presentation_compatible e hU hV
    hUΓ hVΓ heΓ ω hωΓ hΓ f hf hfΓ hlabel Eset hEsub hEΓ hdE
  intro p hp _
  have hnot : ¬ ∃ q : rvLift U.obj, liftLabelMap U.obj q = liftLabelMap U.obj p ∧
      ¬ ∃ L, HasMixedVFDerivativeAt f q L ∧
        CanonicalRV.encodedRv (LinearMap.toMatrix' L).det = (ω (liftLabelMap U.obj p)).val 0 :=
    fun h => hp ((hEchar (liftLabelMap U.obj p)).mpr h)
  push_neg at hnot
  obtain ⟨L, ⟨F, hF, hDer⟩, hrep⟩ := hnot p rfl
  exact ⟨_, ⟨F, hF, hDer.hasJacobianAt⟩, hrep⟩

end SpecialTransformations.Section9.GammaLift
