module

public import Section3.AlgebraicTransitivity
public import Section3.ClosureConventions

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Model-theoretic algebraic closure in the two actual sorts. -/
def algebraicClosureSet (S : Set M) : Set M := {x | ∃ σ, AlgebraicAt S σ x}

theorem subset_algebraicClosureSet (S : Set M) : S ⊆ algebraicClosureSet S := by
  intro x hx
  obtain ⟨σ, hd⟩ := subset_definableClosure S hx
  exact ⟨σ, hd.algebraic⟩

omit hM in
theorem algebraicClosureSet_mono {S T : Set M} (h : S ⊆ T) :
    algebraicClosureSet S ⊆ algebraicClosureSet T := by
  rintro x ⟨σ, hx⟩
  exact ⟨σ, hx.mono h⟩

theorem algebraicAt_algebraicClosureSet_iff (S : Set M) (σ : SortTag) (x : M) :
    AlgebraicAt (algebraicClosureSet S) σ x ↔ AlgebraicAt S σ x := by
  exact ⟨fun hx => hx.eliminate_algebraic_params (fun b hb => hb),
    AlgebraicAt.mono (subset_algebraicClosureSet S)⟩

theorem algebraicClosureSet_idempotent (S : Set M) :
    algebraicClosureSet (algebraicClosureSet S) = algebraicClosureSet S := by
  ext x
  exact exists_congr (fun σ => algebraicAt_algebraicClosureSet_iff S σ x)

omit hM in
theorem definableClosure_subset_algebraicClosureSet (S : Set M) :
    definableClosure S ⊆ algebraicClosureSet S := by
  rintro x ⟨σ, hx⟩
  exact ⟨σ, hx.algebraic⟩

theorem definableClosure_algebraicClosureSet (S : Set M) :
    definableClosure (algebraicClosureSet S) = algebraicClosureSet S := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← algebraicClosureSet_idempotent S]
    exact definableClosure_subset_algebraicClosureSet _ hx
  · exact subset_definableClosure _

/-- The actual algebraic closure is a substructure on canonical tagged models.
This asserts no modelhood, residue-field surjectivity or ball-center theorem. -/
noncomputable def algebraicClosureSubstructure
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) : LRV.Substructure M where
  carrier := algebraicClosureSet S
  fun_mem := by
    intro n f xs hxs
    let C := Set.range xs
    have hargs (i : Fin n) : C.Definable₁ LRV {xs i} := by
      rcases TypedModelMap.sort_cover (M := M) (xs i) with hi | hi
      · exact (definableClosureAt_of_mem (A := C) (σ := .vf)
          (Set.mem_range_self i) hi).raw_definable
      · exact (definableClosureAt_of_mem (A := C) (σ := .rv)
          (Set.mem_range_self i) hi).raw_definable
    have hf : RawClosure.AlgebraicOver C (Structure.funMap (L := LRV) f xs) :=
      ⟨_, DefinableConstants.function_symbol f xs hargs, Set.finite_singleton _,
        Set.mem_singleton _⟩
    have hC (b : M) (hb : b ∈ C) : RawClosure.AlgebraicOver S b := by
      obtain ⟨i, rfl⟩ := hb
      obtain ⟨σ, hx⟩ := hxs i
      exact hx.raw_finite_witness
    have halg := RawClosure.eliminate_algebraic_parameters S C hC _ hf
    rcases TypedModelMap.sort_cover (M := M) (Structure.funMap (L := LRV) f xs) with hi | hi
    · exact ⟨.vf, (algebraicAt_iff_raw hc S .vf _).mpr ⟨halg, hi⟩⟩
    · exact ⟨.rv, (algebraicAt_iff_raw hc S .rv _).mpr ⟨halg, hi⟩⟩

end SpecialTransformations.Section3
