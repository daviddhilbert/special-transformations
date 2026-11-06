import Section4.PositiveAdditivePresentation

noncomputable section

namespace SpecialTransformations.Section4.PositiveAdditiveGrothendieck

universe u

variable {Obj : Type u} (P : Presentation Obj)

/-- If an actual binary operation on objects represents addition, every
element of the positive presentation is represented by one object. -/
theorem of_surjective (sum : Obj → Obj → Obj)
    (hsum : ∀ a b, of P (sum a b) = of P a + of P b) : Function.Surjective (of P) := by
  intro z
  obtain ⟨p, rfl⟩ := (congruence P).mk'_surjective z
  change ∃ a, of P a = quotientHom P p
  refine Finsupp.induction_linear
    (motive := fun p => ∃ a, of P a = quotientHom P p) p ?_ ?_ ?_
  · refine ⟨P.empty, ?_⟩
    rw [of_empty, map_zero]
  · intro f g hf hg
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    refine ⟨sum a b, ?_⟩
    rw [hsum, ha, hb, map_add]
  · intro a n
    induction n with
    | zero =>
      refine ⟨P.empty, ?_⟩
      rw [Finsupp.single_zero, map_zero, of_empty]
    | succ n ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨sum b a, ?_⟩
      rw [hsum, hb, Finsupp.single_add, map_add]
      rfl

end SpecialTransformations.Section4.PositiveAdditiveGrothendieck

end
