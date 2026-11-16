module

public import Section4.RVLabelCompression
public import Section4.RVRestrictions
public import Section4.MapParameters
public import Section4.Fibres

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def labelCompressionOver (S : Set M) (k : ℕ) :
    Map (lowZeroLabels (M := M) S k) (DefSet.univ (rawRVSpace k) S) :=
  (labelCompression k).extend (Set.empty_subset S)

theorem labelCompressionOver_finite (S : Set M) (k : ℕ) :
    (labelCompressionOver (M := M) S k).FiniteFibres :=
  (labelCompression_finite k).extend (Set.empty_subset S)

def compressRVValue (t : Fin (k + 1) → CanonicalRV.RVSort M) : Fin k → CanonicalRV.RVSort M :=
  if h : ∃ i, (t i).val = iRVZero then (labelCompression k ⟨t, h⟩).val else Fin.init t

theorem compressRVValue_of_zero (t : Fin (k + 1) → CanonicalRV.RVSort M)
    (ht : ∃ i, (t i).val = iRVZero) :
    compressRVValue t = (labelCompression k ⟨t, ht⟩).val := dif_pos ht

def rvLowWeightProperty (S : Set M) (k : ℕ) : ObjectProperty (RVObject (M := M) S (k + 1)) :=
  fun U => ∀ u : U.domain, rvWeight (U.value u) ≤ k

abbrev RVLowWeightObject (S : Set M) (k : ℕ) :=
  (rvLowWeightProperty (M := M) S k).FullSubcategory

def rvCompressObject (U : RVObject (M := M) S (k + 1))
    (hU : rvLowWeightProperty S k U) : RVObject (M := M) S k where
  arity := U.arity
  domain := U.domain
  volume := (labelCompressionOver S k).comp
    (U.volume.corestrict (fun u => (rvWeight_le_pred_iff_zero (U.value u)).mp (hU u)))

theorem rvCompressObject_value (U : RVObject (M := M) S (k + 1))
    (hU : rvLowWeightProperty S k U) (u : U.domain) :
    (rvCompressObject U hU).value u = compressRVValue (U.value u) :=
  (compressRVValue_of_zero (U.value u) ((rvWeight_le_pred_iff_zero _).mp (hU u))).symm

theorem rvCompressObject_weight (U : RVObject (M := M) S (k + 1))
    (hU : rvLowWeightProperty S k U) (u : U.domain) :
    rvWeight ((rvCompressObject U hU).value u) = rvWeight (U.value u) :=
  labelCompression_weight ⟨U.value u, (rvWeight_le_pred_iff_zero _).mp (hU u)⟩

def rvCompressHom {U V : RVObject (M := M) S (k + 1)}
    (hU : rvLowWeightProperty S k U) (hV : rvLowWeightProperty S k V) (f : RVHom U V) :
    RVHom (rvCompressObject U hU) (rvCompressObject V hV) where
  map := f.map
  volumetric a := by
    rw [rvCompressObject_weight, rvCompressObject_weight]
    exact f.volumetric a
  finite_volume_images r := by
    let c := labelCompressionOver (M := M) S k
    let L := c.fibreCarrier ⟨r, Set.mem_univ _⟩
    have hL : L.Finite := c.fibreCarrier_finite (labelCompressionOver_finite S k) _
    have hfinite := hL.biUnion (fun t _ => f.finite_volume_images t)
    apply (hfinite.image (compressRVValue (M := M) (k := k))).subset
    rintro s ⟨a, ha, he⟩
    refine ⟨V.value (f.map a), ?_, ?_⟩
    · have hsource : U.value a ∈ L := by
        let t : lowZeroLabels (M := M) S k :=
          ⟨U.value a, (rvWeight_le_pred_iff_zero _).mp (hU a)⟩
        exact ⟨t, rfl, Subtype.ext ha⟩
      exact Set.mem_iUnion.mpr ⟨U.value a, Set.mem_iUnion.mpr
        ⟨hsource, ⟨a, rfl, rfl⟩⟩⟩
    · exact (rvCompressObject_value V hV (f.map a)).symm.trans he

/-- Label compression is a genuine functor on the full subcategory of
objects of weight at most k, with both RV morphism conditions proved. -/
def rvCompressionFunctor (S : Set M) (k : ℕ) :
    RVLowWeightObject (M := M) S k ⥤ RVObject (M := M) S k where
  obj U := rvCompressObject U.obj U.property
  map f := rvCompressHom _ _ f.hom
  map_id _ := by apply RVHom.ext; rfl
  map_comp _ _ := by apply RVHom.ext; rfl

end SpecialTransformations.Section4

end
