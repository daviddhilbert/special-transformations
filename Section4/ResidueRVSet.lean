import Section4.ResidueTupleRank
import Section4.RVDimensionRank

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {n : ℕ}

theorem rvPreimage_residueFieldImage (D : Set (Fin n → ModelResidue M)) :
    (rawRVSpace (M := M) n).preimage ((fun a => residueRV ∘ a) '' D) = residueFieldImage D := by
  ext z
  constructor
  · rintro ⟨hz, a, ha, he⟩
    refine ⟨a, ha, ?_⟩
    change rvValues (residueRV ∘ a) = z
    exact (congrArg (rvValues (M := M) (n := n)) he).trans (rvValues_decode ⟨z, hz⟩)
  · rintro ⟨a, ha, he⟩
    rw [← he]
    refine ⟨⟨residueRV ∘ a, rfl⟩, a, ha, ?_⟩
    exact (decode_rvValues (residueRV ∘ a)).symm

/-- The actual RV image of a pure residue-field set, over the displayed
parameter set. The carrier is its genuine injective field interpretation. -/
def residueRVSet (hcan : CanonicalStructure.IsCanonical (M := M))
    (E : Subfield (ModelResidue M)) (S : Set M) (hE : E ≤ residueDefinableField S)
    (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def E D) :
    DefSet (rawRVSpace (M := M) n) S where
  carrier := (fun a => residueRV ∘ a) '' D
  definable := by
    change S.Definable LRV _
    rw [rvPreimage_residueFieldImage]
    exact (residueFieldImage_definable_of_definable_names hcan E S
      (fun c => hE c.property) D hD).raw_definable

theorem residueTupleRank_le_dimension
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    (B : LRV.Substructure M) (D : Set (Fin n → ModelResidue M))
    (hD : Relative.Def (residueParameterField B) D) (a : D) :
    relativeTrdeg (residueParameterField B) (tupleField (residueParameterField B) a.val)
      (le_tupleField _ _) ≤
      (rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
        (residueParameterField_le_definableField B) D hD) : Cardinal) := by
  rw [residue_trdeg_eq_rvTupleRank hcan hex]
  exact_mod_cast rvTupleRank_le_rvDim hcan hex
    (residueRVSet hcan (residueParameterField B) (B : Set M)
      (residueParameterField_le_definableField B) D hD)
    ⟨residueRV ∘ a.val, a.val, a.property, rfl⟩

theorem exists_residue_point_of_maximum_rank
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M)
    (hsmall : Cardinal.mk B < κ) (D : Set (Fin n → ModelResidue M))
    (hD : Relative.Def (residueParameterField B) D) (hne : D.Nonempty) :
    ∃ a ∈ D, relativeTrdeg (residueParameterField B) (tupleField (residueParameterField B) a)
      (le_tupleField _ _) =
      (rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
        (residueParameterField_le_definableField B) D hD) : Cardinal) := by
  let A := residueRVSet hcan (residueParameterField B) (B : Set M)
    (residueParameterField_le_definableField B) D hD
  have hA : A.carrier.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨residueRV ∘ a, a, ha, rfl⟩
  obtain ⟨t, ht⟩ := exists_point_of_maximum_rv_rank hcan hex hs hsmall A hA
  obtain ⟨a, ha, he⟩ := t.property
  refine ⟨a, ha, ?_⟩
  rw [residue_trdeg_eq_rvTupleRank hcan hex]
  exact congrArg (fun k : ℕ => (k : Cardinal))
    ((congrArg (rvTupleRank hcan hex (B : Set M)) he).trans ht)

end SpecialTransformations.Section4.ResiduePurity

end
