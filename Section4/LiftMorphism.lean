module

public import Section4.MapAlgebraicity
public import Section4.RVCoordinates
public import Section4.RVTupleFibres
public import Section3.SmallFiniteParameters

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ} {U V : RVObject (M := M) S k}

/-- The two components of the commuting diagram in 4.19, expressed on the
actual lifts and the actual definable underlying map. -/
def LiftCommutes (F : Map U.domain V.domain) (G : Map (rvLift U) (rvLift V)) : Prop :=
  ∀ (p : rvLift U) (u : U.domain), p.val.2 = u.val →
    (tupleRV (G p).val.1, (G p).val.2) = (V.value (F u), (F u).val)

theorem volume_relation_definable (F : Map U.domain V.domain) :
    (rawRVSpace (M := M) k).RelationDefinable (rawRVSpace k) S
      (fun t s => ∃ u : U.domain, U.value u = t ∧ V.value (F u) = s) := by
  let P := rawRVSpace (M := M) U.arity
  let Q := rawRVSpace (M := M) k
  let H := V.volume.comp F
  exact ((U.volume.graph_definable.swap P Q).comp Q P Q H.graph_definable).congr Q Q (by
    intro t s
    constructor
    · rintro ⟨x, ⟨u, hux, hut⟩, ⟨v, hvx, hvs⟩⟩
      have he : v = u := Subtype.ext (hvx.trans hux.symm)
      subst v
      exact ⟨u, hut, hvs⟩
    · rintro ⟨u, hut, hvs⟩
      exact ⟨u.val, ⟨u, rfl, hut⟩, ⟨u, rfl, hvs⟩⟩)

def volumeFibreSet (F : Map U.domain V.domain) (t : Fin k → CanonicalRV.RVSort M) :
    DefSet (rawRVSpace (M := M) k) (S ∪ Set.range (rvValues t)) :=
  relationFibre (volume_relation_definable F) t ⟨rvValues t, ⟨t, rfl⟩⟩ (decode_rvValues t)

@[simp] theorem volumeFibreSet_carrier (F : Map U.domain V.domain)
    (t : Fin k → CanonicalRV.RVSort M) :
    (volumeFibreSet F t).carrier = U.volumeFibreImage V F t := rfl

/-- The algebraicity step in 4.19, proved from the actual commuting lift.
The VF-to-RV descent is an accepted Section 3 input. -/
theorem lift_volume_algebraic (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (F : Map U.domain V.domain)
    (G : Map (rvLift U) (rvLift V)) (hcomm : LiftCommutes F G)
    (u : U.domain) (j : Fin k) :
    AlgebraicAt (S ∪ Set.range (rvValues (U.value u))) .rv (V.value (F u) j).val := by
  let t := U.value u
  apply corollary_3_2_vf hκ hs S (rvValues t)
    (small_union_range hκ S hsmall (rvValues t)) (tupleRVFibre (rvValues t))
    (V.value (F u) j).val .rv (rvTupleFibre_definable hcan S t)
    (rvTupleFibre_nonempty t) (Set.Subset.refl _)
  intro z hz
  let a : Fin k → VFType (M := M) := fun i => ⟨z i, (hz i).1⟩
  have ha : tupleRV a = U.value u := by
    funext i
    exact Subtype.ext (hz i).2
  let p : rvLift U := ⟨(a, u.val), u, rfl, ha.symm⟩
  have he : iRv ((G p).val.1 j).val = (V.value (F u) j).val :=
    congrArg (fun q : (Fin k → CanonicalRV.RVSort M) ×
      (Fin V.arity → CanonicalRV.RVSort M) => (q.1 j).val) (hcomm p u rfl)
  have h := map_output_rv_algebraic hcan G p j
  change AlgebraicAt (S ∪ Set.range z) .rv (iRv ((G p).val.1 j).val) at h
  rwa [he] at h

theorem lift_volume_fibre_images_finite (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (F : Map U.domain V.domain)
    (G : Map (rvLift U) (rvLift V)) (hcomm : LiftCommutes F G)
    (t : Fin k → CanonicalRV.RVSort M) : (U.volumeFibreImage V F t).Finite := by
  have hfinite : (volumeFibreSet F t).carrier.Finite :=
    finite_rv_set_of_algebraic hs (small_union_range hκ S hsmall (rvValues t))
      (volumeFibreSet F t) (by
        rintro ⟨s, u, hu, hv⟩ j
        have h := lift_volume_algebraic hcan hκ hs hsmall F G hcomm u j
        simpa only [hu, hv] using h)
  exact hfinite

def rvHom_of_commuting_lift (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (F : Map U.domain V.domain)
    (G : Map (rvLift U) (rvLift V)) (hcomm : LiftCommutes F G)
    (hvol : ∀ u, rvWeight (U.value u) ≤ rvWeight (V.value (F u))) : RVHom U V where
  map := F
  volumetric := hvol
  finite_volume_images := lift_volume_fibre_images_finite hcan hκ hs hsmall F G hcomm

/-- Lemma 4.19, including the finite-image conclusion. -/
theorem lemma_4_19 (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (F : Map U.domain V.domain)
    (G : Map (rvLift U) (rvLift V)) (hcomm : LiftCommutes F G)
    (hvol : ∀ u, rvWeight (U.value u) ≤ rvWeight (V.value (F u))) :
    ∃ H : RVHom U V, H.map = F :=
  ⟨rvHom_of_commuting_lift hcan hκ hs hsmall F G hcomm hvol, rfl⟩

end SpecialTransformations.Section4

end
