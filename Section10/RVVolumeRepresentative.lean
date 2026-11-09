import Section10.EssentialVFMap
import Section10.RVVolumeLift

/-! The pointwise RV-valued representative in Theorem 10.5. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9

namespace SpecialTransformations.Section10

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "Δ" => rawRVSpace (M := M) 1
local notation "n" => (k + 1)

/-- Definition 10.1's pointwise equation on an essential VF bijection. -/
def RVMeasurePreserving {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : EssentialVFMap A B) (ω : RVVolumeForm A) (η : RVVolumeForm B) : Prop :=
  ∀ p : f.source, ∃ J : VF, HasMixedVFJacobianAt f.map p J ∧
    ω.value ⟨p.val, f.source_subset p.property⟩ =
      η.value ⟨(f.map p).val, f.target_subset (f.map p).property⟩ * CanonicalRV.encodedRv J

/-- The positive-degree RV-valued case of Theorem 10.5. The
representative is defined between co-small subsets of the full lifts,
and the Jacobian in the measure equation belongs to that representative. -/
theorem theorem_10_5_rv_volume [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hB : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    (hfinite : FiniteHenselianExtensionReference)
    {U V : RVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e.labels
    ∃ g : EssentialVFMap (rvLift U.underlying.obj) (rvLift V.underlying.obj),
      RVMeasurePreserving g U.liftForm V.liftForm ∧
        ∀ p : g.source, E.hom.map.graph p.val.2 (g.map p).val.2 := by
  obtain ⟨f, hf, hlabel, Z, _, hZ, _, hJ⟩ := theorem_10_5_rv_volume_ae hc C Ξ hB hfinite e
  obtain ⟨g, hg⟩ := EssentialVFMap.exists_restriction_preserving_jacobian hc C.saturated C.small
    (Nat.zero_lt_succ k) f hf Z hZ
  let g' := g.widen hc C.saturated C.small
    (fun p hp => ((mem_rvEssentialLift U.underlying.obj p).mp hp).1)
    (fun p hp => ((mem_rvEssentialLift V.underlying.obj p).mp hp).1)
    (rvEssentialLift_complement_dim_lt Δ U.underlying.obj)
    (rvEssentialLift_complement_dim_lt Δ V.underlying.obj)
  refine ⟨g', ?_, ?_⟩
  · intro p
    obtain ⟨hz, hval, htransfer⟩ := hg p
    obtain ⟨J, hder, hdet⟩ := hJ ⟨p.val, g.source_subset p.property⟩ hz
    refine ⟨J, htransfer J hder, ?_⟩
    have he : V.liftForm.value ⟨(g'.map p).val, g'.target_subset (g'.map p).property⟩ =
        V.essential.liftForm.value (f ⟨p.val, g.source_subset p.property⟩) := by
      change V.form.value _ = V.form.value _
      exact congrArg V.form.value (Subtype.ext (congrArg Prod.snd hval))
    rw [he]
    exact hdet
  · intro p
    have he := congrArg Prod.snd (hg p).2.1
    exact he.symm ▸ hlabel ⟨p.val, g.source_subset p.property⟩

end SpecialTransformations.Section10
