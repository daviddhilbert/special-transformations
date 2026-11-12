module

public import Section4.RVBaseAlgebraicity
public import Section4.RVFiniteMapRank
public import Section4.MapAlgebraicity
public import Section4.LiftFibres

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r m s : ℕ}

theorem mixed_map_output_rv_coordinate_algebraic
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) (a : A) (j : Fin s) :
    AlgebraicAt ((S ∪ Set.range (vfValues a.val.1)) ∪ Set.range (rvValues a.val.2))
      .rv ((f a).val.2 j).val := by
  let g := (rvTailMap B).comp f
  let c : (rawMixedSpace (M := M) n r).domain :=
    ⟨mixedValues a.val, mixedValues_mem_domain a.val⟩
  let F := relationFibre g.graph_definable a.val c (decode_mixedValues a.val)
  have hraw : RawClosure.AlgebraicOver (S ∪ Set.range (mixedValues a.val))
      ((f a).val.2 j).val :=
    ⟨rvCoordinateSet F j, rvCoordinateSet_definable F j,
      rvCoordinateSet_finite F (g.graph_values_finite a.val) j,
      ⟨⟨(g a).val, ⟨a, rfl, rfl⟩⟩, rfl⟩⟩
  have he : Set.range (mixedValues a.val) =
      Set.range (vfValues a.val.1) ∪ Set.range (rvValues a.val.2) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl (Set.mem_range_self i)
      | inr i => exact Or.inr (Set.mem_range_self i)
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨.inl i, rfl⟩
      · exact ⟨.inr i, rfl⟩
  rw [he, ← Set.union_assoc] at hraw
  exact (algebraicAt_iff_raw hcan _ .rv _).mpr ⟨hraw, ((f a).val.2 j).property⟩

theorem mixed_map_vf_base_algebraic
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) (a : A) :
    S ∪ Set.range (vfValues (f a).val.1) ⊆
      algebraicClosureSet (S ∪ Set.range (vfValues a.val.1)) := by
  rintro x (hx | ⟨j, rfl⟩)
  · exact subset_algebraicClosureSet _ (Or.inl hx)
  · refine ⟨.vf, (algebraicAt_vf_iff_parameterField _ _).mpr ?_⟩
    rw [vfParameterField_union_tuple]
    exact map_output_vf_coordinate_isAlgebraic hcan f a j

theorem mixed_bijection_point_rv_rank
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B)
    (hf : Function.Bijective f) (a : A) :
    rvTupleRank hcan hex (S ∪ Set.range (vfValues (f a).val.1)) (f a).val.2 =
      rvTupleRank hcan hex (S ∪ Set.range (vfValues a.val.1)) a.val.2 := by
  have hforward := mixed_map_vf_base_algebraic hcan f a
  have hbackward := mixed_map_vf_base_algebraic hcan (f.inverse hf) (f a)
  rw [Map.inverse_apply] at hbackward
  have hbase {d : ℕ} (t : Fin d → CanonicalRV.RVSort M) :=
    rvTupleRank_eq_of_mutually_algebraic hcan hex hforward hbackward t
  apply Nat.le_antisymm
  · rw [hbase]
    exact rvTupleRank_le_of_algebraic hcan hex _ a.val.2 (f a).val.2
      (mixed_map_output_rv_coordinate_algebraic hcan f a)
  · rw [← hbase]
    have h := rvTupleRank_le_of_algebraic hcan hex _ (f a).val.2
      ((f.inverse hf) (f a)).val.2
      (mixed_map_output_rv_coordinate_algebraic hcan (f.inverse hf) (f a))
    simpa only [Map.inverse_apply] using h

end SpecialTransformations.Section4

end
