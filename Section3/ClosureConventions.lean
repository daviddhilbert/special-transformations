module

public import Section3.VFDefinableClosure

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The closure used in Convention 2.5: definable closure, rather than the
smaller collection of values of language terms. -/
def definableClosure (S : Set M) : Set M := {x | ∃ σ, DefinableClosureAt S σ x}

theorem mem_definableClosure_iff_raw (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (x : M) : x ∈ definableClosure S ↔ S.Definable₁ LRV {x} := by
  constructor
  · rintro ⟨σ, h⟩
    exact h.raw_definable
  · intro h
    rcases TypedModelMap.sort_cover (M := M) x with hx | hx
    · exact ⟨.vf, (definableClosureAt_iff_raw hc S .vf x).mpr ⟨h, hx⟩⟩
    · exact ⟨.rv, (definableClosureAt_iff_raw hc S .rv x).mpr ⟨h, hx⟩⟩

theorem subset_definableClosure (S : Set M) : S ⊆ definableClosure S := by
  intro x hx
  rcases TypedModelMap.sort_cover (M := M) x with hs | hs
  · exact ⟨.vf, definableClosureAt_of_mem hx hs⟩
  · exact ⟨.rv, definableClosureAt_of_mem hx hs⟩

omit hM in
theorem definableClosure_mono {S T : Set M} (h : S ⊆ T) :
    definableClosure S ⊆ definableClosure T := by
  rintro x ⟨σ, hx⟩
  exact ⟨σ, hx.mono h⟩

theorem definableClosure_idempotent (S : Set M) :
    definableClosure (definableClosure S) = definableClosure S := by
  apply Set.Subset.antisymm
  · rintro x ⟨σ, hx⟩
    exact ⟨σ, hx.eliminate_sorted_definable_params (fun b hb => hb)⟩
  · exact subset_definableClosure (definableClosure S)

theorem algebraicAt_definableClosure_iff (S : Set M) (σ : SortTag) (x : M) :
    AlgebraicAt (definableClosure S) σ x ↔ AlgebraicAt S σ x := by
  constructor
  · exact fun hx => hx.eliminate_sorted_definable_params (fun b hb => hb)
  · exact AlgebraicAt.mono (subset_definableClosure S)

noncomputable def definableClosureSubstructure
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) : LRV.Substructure M where
  carrier := definableClosure S
  fun_mem := by
    intro n f xs hxs
    apply (mem_definableClosure_iff_raw hc S _).mpr
    exact DefinableConstants.function_symbol f xs
      (fun i => (mem_definableClosure_iff_raw hc S (xs i)).mp (hxs i))

def VFGenerated (S : Set M) : Prop :=
  ∃ A : Set M, (∀ a ∈ A, iVF a) ∧ S = definableClosure A

def VFRVGenerated (S : Set M) : Prop :=
  ∃ A B : Set M, (∀ a ∈ A, iVF a) ∧ (∀ b ∈ B, iRV b) ∧
    S = definableClosure (A ∪ B)

end SpecialTransformations.Section3
