module

public import Section3.AclFieldImages
public import Section3.SmallFiniteParameters
public import Mathlib.FieldTheory.Cardinality
public import Mathlib.RingTheory.Algebraic.Cardinality

@[expose] public section

/-! Enlarge the parameter set in the proof by the names of a small
algebraically closed coefficient field. The final theorem can retain
its original parameter set. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "VF" => VFType (M := M)

theorem exists_small_algClosed_vfParameter_extension
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (S : Set M) (hS : Cardinal.mk S < κ)
    {m : ℕ} (x : Fin m → VF) :
    ∃ T : Set M, S ⊆ T ∧ Cardinal.mk T < κ ∧ Cardinal.mk (vfParameterField T) < κ ∧
      IsAlgClosed (vfParameterField T) ∧ ∀ i, x i ∈ vfParameterField T := by
  let S₀ := S ∪ Set.range (fun i => (x i).val)
  let E := vfParameterField S₀
  let B := algebraicClosure E VF
  let H := vfAlgebraicClosureField S₀
  have hS₀ := small_union_range hκ.le S hS (fun i => (x i).val)
  have hE : Cardinal.mk E < κ := by
    let U := {a : VF | a.val ∈ S₀}
    have hU : Cardinal.mk U ≤ Cardinal.mk S₀ := Cardinal.mk_le_of_injective
      (f := fun a : U => (⟨a.val.val, a.property⟩ : S₀))
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : S₀ => z.val) h)))
    exact (Subfield.cardinalMk_closure_le_max U).trans_lt (max_lt_iff.mpr ⟨hU.trans_lt hS₀,hκ⟩)
  letI : Module.IsTorsionFree E B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap E B).injective
  have hH : Cardinal.mk H < κ := (Algebra.IsAlgebraic.cardinalMk_le_max E B).trans_lt
    (max_lt_iff.mpr ⟨hE, hκ⟩)
  let names (a : H) : M := a.val.val
  let T := S₀ ∪ Set.range names
  have hT : Cardinal.mk T < κ := (Cardinal.mk_union_le _ _).trans_lt
    (Cardinal.add_lt_of_lt hκ.le hS₀ (Cardinal.mk_range_le.trans_lt hH))
  have hEH : E ≤ H := fun a ha => B.algebraMap_mem (⟨a, ha⟩ : E)
  have he : vfParameterField T = H := by
    apply le_antisymm
    · apply Subfield.closure_le.mpr
      rintro a (ha | ⟨b, hb⟩)
      · exact hEH (Subfield.subset_closure ha)
      · have he : b.val = a := Subtype.ext hb
        exact he ▸ b.property
    · intro a ha
      exact Subfield.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  refine ⟨T, Set.subset_union_left.trans Set.subset_union_left, hT, ?_, ?_, ?_⟩
  · rwa [he]
  · rw [he]
    exact inferInstanceAs (IsAlgClosed (vfAlgebraicClosureField S₀))
  · intro i
    exact Subfield.subset_closure (Or.inl (Or.inr (Set.mem_range_self i)))

end SpecialTransformations.Section9
