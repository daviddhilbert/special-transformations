module

public import Section4.MapParameters
public import Section4.RelationFibres
public import Section3.AlgebraicTransitivity
public import Section3.SortedFunctionClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem algebraicAt_rv_of_vf {S : Set M} (b : VFType (M := M))
    (hb : AlgebraicAt S .vf b.val) : AlgebraicAt S .rv (iRv b.val) := by
  have hd : DefinableClosureAt ({b.val} : Set M) .rv (iRv b.val) :=
    definableClosureAt_function_symbol {b.val} Fn.rvMap ![b.val]
      (by intro i; fin_cases i; exact b.property)
      (by intro i; fin_cases i; exact definableClosureAt_of_mem (Set.mem_singleton b.val) b.property)
  apply hd.algebraic.eliminate_algebraic_params
  rintro x hx
  have he : x = b.val := Set.mem_singleton_iff.mp hx
  subst x
  exact ⟨.vf, hb⟩

variable {S : Set M} {n r m s : ℕ}

/-- Output coordinates of any definable function are algebraic over the VF
input coordinates and the original base; input RV names do not contribute
to the coefficient field. -/
theorem map_output_vf_coordinate_isAlgebraic
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) (a : A) (j : Fin m) :
    IsAlgebraic (tupleField (vfParameterField S) a.val.1) ((f a).val.1 j) :=
  finite_relation_vf_coordinate_isAlgebraic hcan f.graph_definable
    a.val (f a).val ⟨a, rfl, rfl⟩ (f.graph_values_finite a.val) j

theorem map_output_rv_algebraic
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) (a : A) (j : Fin m) :
    AlgebraicAt (S ∪ Set.range (vfValues a.val.1)) .rv (iRv ((f a).val.1 j).val) := by
  apply algebraicAt_rv_of_vf
  apply (algebraicAt_vf_iff_parameterField _ _).mpr
  rw [vfParameterField_union_tuple]
  exact map_output_vf_coordinate_isAlgebraic hcan f a j

end SpecialTransformations.Section4
