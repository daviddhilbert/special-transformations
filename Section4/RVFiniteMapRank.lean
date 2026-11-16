module

public import Section4.RVRank
public import Section4.RVCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n m : ℕ}

theorem rvCoordinateSet_finite (A : DefSet (rawRVSpace (M := M) n) S)
    (hA : A.carrier.Finite) (i : Fin n) : (rvCoordinateSet A i).Finite := by
  convert hA.image (fun t => (t i).val) using 1
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.val, a.property, ha⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a, ha⟩, he⟩

variable [hM : M ⊨ Axioms.ACVF]

/-- A finite definable fibre gives actual algebraic-closure witnesses for
every input RV coordinate, over the original base and the output tuple. -/
theorem finite_map_rv_coordinate_algebraic
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) n) S}
    {B : DefSet (rawRVSpace (M := M) m) S}
    (f : Map A B) (hf : f.FiniteFibres) (a : A) (i : Fin n) :
    AlgebraicAt (S ∪ Set.range (rvValues (f a).val)) .rv (a.val i).val := by
  let F := f.fibre (f a) ⟨rvValues (f a).val, ⟨(f a).val, rfl⟩⟩
    (decode_rvValues (f a).val)
  have hfin : F.carrier.Finite := f.fibreCarrier_finite hf (f a)
  apply (algebraicAt_iff_raw hcan _ .rv _).mpr
  exact ⟨⟨rvCoordinateSet F i, rvCoordinateSet_definable F i,
    rvCoordinateSet_finite F hfin i, ⟨⟨a.val, ⟨a, rfl, rfl⟩⟩, rfl⟩⟩,
    (a.val i).property⟩

theorem rvTupleRank_le_of_finite_map
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {A : DefSet (rawRVSpace (M := M) n) S}
    {B : DefSet (rawRVSpace (M := M) m) S}
    (f : Map A B) (hf : f.FiniteFibres) (a : A) :
    rvTupleRank hcan hex S a.val ≤ rvTupleRank hcan hex S (f a).val :=
  rvTupleRank_le_of_algebraic hcan hex S (f a).val a.val
    (finite_map_rv_coordinate_algebraic hcan f hf a)

/-- The lower half of the RV dimension/rank comparison. No rank
description of Definition 4.9 is assumed. -/
theorem rvTupleRank_le_rvDim
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    (A : DefSet (rawRVSpace (M := M) n) S) (a : A) :
    rvTupleRank hcan hex S a.val ≤ rvDim A := by
  obtain ⟨f, hf⟩ := rvDim_attained A
  exact (rvTupleRank_le_of_finite_map hcan hex f hf a).trans
    (rvTupleRank_le_arity hcan hex S (f a).val)

end SpecialTransformations.Section4

end
