module

public import Section3.ModelContext

@[expose] public section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M]

theorem small_union_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set M) (hS : Cardinal.mk S < κ) (F : Set M) (hF : F.Finite) :
    Cardinal.mk ↥(S ∪ F) < κ := by
  classical
  suffices h : ∀ T : Finset M, Cardinal.mk ↥(S ∪ (T : Set M)) < κ by
    simpa using h hF.toFinset
  intro T
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.coe_empty,Set.union_empty] using hS
  | @insert a T ha ih =>
    have he : S ∪ ((insert a T : Finset M) : Set M) = insert a (S ∪ (T : Set M)) := by
      ext x
      simp only [Finset.coe_insert,Set.mem_union,Set.mem_insert_iff]
      tauto
    rw [he]
    exact small_insert hκ _ ih a

theorem small_union_range {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set M) (hS : Cardinal.mk S < κ) {n : ℕ} (a : Fin n → M) :
    Cardinal.mk ↥(S ∪ Set.range a) < κ :=
  small_union_finite hκ S hS _ (Set.finite_range a)

end SpecialTransformations.Section3
