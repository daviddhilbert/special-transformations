module

public import Section3.RawAlgebraicity
public import Section3.DefinableCompactness
public import Section3.FiniteRelations

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure
variable {M : Type} [LRV.Structure M]

theorem uniform_intersection_definable (S A : Set M) (hA : S.Definable₁ LRV A)
    (R : Set (M × M)) (hR : S.Definable₂ LRV R) :
    S.Definable₁ LRV {x | ∀ a ∈ A, (a, x) ∈ R} := by
  have hr := hR.preimage_comp (![Sum.inr 0, Sum.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have ha := hA.preimage_comp (fun _ : Fin 1 => (Sum.inr 0 : Fin 1 ⊕ Fin 1))
  have h := (ha.compl.union hr).forall_of_finite
  change S.Definable LRV {x : Fin 1 → M | ∀ a ∈ A, (a, x 0) ∈ R}
  convert h using 1
  ext x
  simp only [Set.preimage_ofPred_eq, Set.mem_ofPred_eq, Set.mem_union,
    Set.mem_compl_iff, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro hx a
    by_cases ha : a 0 ∈ A
    · exact Or.inr (hx (a 0) ha)
    · exact Or.inl ha
  · intro hx a ha
    exact (hx ![a]).resolve_left (not_not.mpr ha)

theorem algebraicity_descent_raw {κ : Cardinal} (hs : Saturated M κ)
    (S A : Set M) (b : M) (hsmall : Cardinal.mk ↥(insert b S) < κ)
    (hA : S.Definable₁ LRV A) (hne : A.Nonempty)
    (hb : ∀ a ∈ A, AlgebraicOver (insert a S) b) : AlgebraicOver S b := by
  classical
  let slice (R : GoodRelation S) : Set M := {a | (a, b) ∈ R.val}
  let C : Set (Set M) := Set.range slice
  have hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨R, hR⟩ := good_relation_of_algebraic S a b (hb a ha)
    exact ⟨slice R, Set.mem_range_self _, hR⟩
  obtain ⟨C₀, hC₀, hsub, hcover⟩ := hs.definable_finite_subcover
    (insert b S) hsmall A (hA.mono (Set.subset_insert b S)) C
    (by rintro _ ⟨R, rfl⟩; exact slice_definable S b R) hcov
  haveI : Finite C₀ := hC₀.to_subtype
  have hchoice (c : C₀) : ∃ R : GoodRelation S, slice R = c.val := hsub c.property
  let rel (c : C₀) := Classical.choose (hchoice c)
  have hrel (c : C₀) : slice (rel c) = c.val := Classical.choose_spec (hchoice c)
  let R : Set (M × M) := {p | ∃ c : C₀, p ∈ (rel c).val}
  have hR : S.Definable₂ LRV R := by
    have hu := Set.definable_iUnion_of_finite (fun c : C₀ => (rel c).property.1)
    simpa only [Set.Definable₂, R, Set.mem_ofPred_eq, Set.iUnion_ofPred] using hu
  let T : Set M := {x | ∀ a ∈ A, (a, x) ∈ R}
  refine ⟨T, uniform_intersection_definable S A hA R hR, ?_, ?_⟩
  · obtain ⟨a₀, ha₀⟩ := hne
    have hfin : {x | (a₀, x) ∈ R}.Finite := by
      have hf := Set.finite_iUnion (fun c : C₀ => (rel c).property.2 a₀)
      simpa only [R, Set.iUnion_ofPred, Set.mem_ofPred_eq] using hf
    exact hfin.subset (fun x hx => hx a₀ ha₀)
  · intro a ha
    obtain ⟨c, hc, hac⟩ := hcover a ha
    refine ⟨⟨c, hc⟩, ?_⟩
    change a ∈ slice (rel ⟨c, hc⟩)
    rw [hrel]
    exact hac

end SpecialTransformations.Section3.RawClosure