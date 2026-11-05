import Section3.SortedBoolean
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A finite set of algebraic elements is contained in a finite definable
set over the original base. The elements themselves are not named. -/
theorem finite_definable_cover {S D : Set M} {σ : SortTag} (hD : D.Finite)
    (hacl : ∀ x ∈ D, AlgebraicAt S σ x) :
    ∃ E : Set M, DefinableAt S σ E ∧ E.Finite ∧ D ⊆ E := by
  letI : Fintype D := hD.fintype
  have h (x : D) : ∃ E : Set M, DefinableAt S σ E ∧ E.Finite ∧ x.val ∈ E := hacl x.val x.property
  choose E hEd hEf hEx using h
  refine ⟨⋃ x : D, E x,?_,Set.finite_iUnion hEf,?_⟩
  · simpa only [Finset.mem_univ,Set.iUnion_true] using
      (DefinableAt.finite_iUnion (S := S) (σ := σ) (Finset.univ : Finset D) E (fun x _ => hEd x))
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hEx ⟨x,hx⟩⟩

end SpecialTransformations.Section3
