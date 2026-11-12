module

public import Section9.HenselizedGraphData

@[expose] public section

namespace SpecialTransformations.Section9

variable {K ι : Type} [Field K]

theorem map_adjoin_range_subfield (E L : Subfield K) (hEL : E ≤ L) (x : ι → L) :
    (IntermediateField.adjoin (E.comap L.subtype) (Set.range x)).toSubfield.map L.subtype =
      (IntermediateField.adjoin E (Set.range (L.subtype ∘ x))).toSubfield := by
  simp only [IntermediateField.adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    Set.range_comp]
  have h : L.subtype '' Set.range (algebraMap (E.comap L.subtype) L) =
      Set.range (algebraMap E K) := by
    rw [← Set.range_comp]
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨⟨(b.val : K), b.property⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨⟨b.val, hEL b.property⟩, b.property⟩, rfl⟩
  rw [h]

theorem isAlgebraic_in_nested_gaussField (E L : Subfield K) (hEL : E ≤ L) (x : ι → L) (z : L)
    (hz : IsAlgebraic (IntermediateField.adjoin E (Set.range (L.subtype ∘ x))) (z : K)) :
    IsAlgebraic (IntermediateField.adjoin (E.comap L.subtype) (Set.range x)) z := by
  let F := IntermediateField.adjoin (E.comap L.subtype) (Set.range x)
  let H := IntermediateField.adjoin E (Set.range (L.subtype ∘ x))
  let f : F →+* H :=
    { toFun := fun a => ⟨a.val.val, by
        change a.val.val ∈ H.toSubfield
        rw [← map_adjoin_range_subfield E L hEL x]
        exact ⟨a.val, a.property, rfl⟩⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro a
    have ha : (a : K) ∈ F.toSubfield.map L.subtype := by
      rw [map_adjoin_range_subfield E L hEL x]
      exact a.property
    obtain ⟨b, hb, he⟩ := ha
    exact ⟨⟨b, hb⟩, Subtype.ext he⟩
  exact hz.of_ringHom_of_comp_eq f L.subtype hf Subtype.val_injective (RingHom.ext fun _ => rfl)


end SpecialTransformations.Section9
