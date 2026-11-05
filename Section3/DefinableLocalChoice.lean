import Section3.FiniteGluing
import Section3.FibrePromotion
import Section3.TupleRelations
import Section3.TupleCompactness
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

def GoodChoice (S : Set M) (P : Set ((Fin n → M) × M)) :=
  {R : Set ((Fin n → M) × M) // RelationDefinable S R ∧ SingleValued R ∧ R ⊆ P}

theorem good_choice_of_definable (S : Set M) (P : Set ((Fin n → M) × M))
    (hP : RelationDefinable S P) (a : Fin n → M) (b : M) (hab : (a, b) ∈ P)
    (hb : (S ∪ Set.range a).Definable₁ LRV {b}) :
    ∃ R : GoodChoice S P, (a, b) ∈ R.val := by
  classical
  obtain ⟨R, hR, haR⟩ := promote_definable_fibre S a {b} hb
  let Q := R ∩ P
  have hQ : RelationDefinable S Q := hR.inter hP
  have haQ : {x | (a, x) ∈ Q} = {b} := by
    ext x
    change ((a, x) ∈ R ∧ (a, x) ∈ P) ↔ x = b
    have haRx : (a, x) ∈ R ↔ x = b := Set.ext_iff.mp haR x
    rw [haRx]
    exact ⟨And.left, fun h => ⟨h, by subst x; exact hab⟩⟩
  let U : Set ((Fin n → M) × M) := {p | p ∈ Q ∧ p.1 ∉ HasMore Q 1}
  have hU : RelationDefinable S U :=
    hQ.inter ((hasMore_definable S Q hQ 1).compl.preimage_comp
      (Sum.inl : Fin n → Fin n ⊕ Fin 1))
  have haU : a ∉ HasMore Q 1 := by
    apply (no_inj_iff_finite_ncard_le (s := {x | (a, x) ∈ Q}) (k := 1)).mpr
    rw [haQ]
    exact ⟨Set.finite_singleton b, by simp⟩
  refine ⟨⟨U, hU, ?_, fun p hp => hp.1.2⟩, ?_⟩
  · intro c x y hx hy
    obtain ⟨hf, hn⟩ := (no_inj_iff_finite_ncard_le (s := {z | (c, z) ∈ Q})
      (k := 1)).mp hx.2
    exact (Set.ncard_le_one_iff hf).mp hn hx.1 hy.1
  · refine ⟨?_, haU⟩
    change b ∈ {x | (a, x) ∈ Q}
    rw [haQ]
    rfl

/-- Pointwise choices lying in definable closure give a definable choice
graph over the same small base, using genuine saturation. -/
theorem definable_choice_graph {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → M)) (hA : S.Definable LRV A)
    (P : Set ((Fin n → M) × M)) (hP : RelationDefinable S P)
    (hlocal : ∀ a ∈ A, ∃ b, (a, b) ∈ P ∧
      (S ∪ Set.range a).Definable₁ LRV {b}) :
    ∃ U : Set ((Fin n → M) × M), RelationDefinable S U ∧ SingleValued U ∧
      U ⊆ P ∧ ∀ a ∈ A, ∃ b, (a, b) ∈ U := by
  classical
  let dom (R : GoodChoice S P) : Set (Fin n → M) := {a | ∃ b, (a, b) ∈ R.val}
  let C := Set.range dom
  have hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨b, hab, hb⟩ := hlocal a ha
    obtain ⟨R, haR⟩ := good_choice_of_definable S P hP a b hab hb
    exact ⟨dom R, Set.mem_range_self R, b, haR⟩
  obtain ⟨C₀, hfin, hsub, hcov⟩ := hs.definable_finite_subcover_tuple S hsmall A hA C
    (by rintro c ⟨R, rfl⟩; exact domain_definable S R.val R.property.1) hcover
  let rel (c : C₀) : GoodChoice S P := Classical.choose (hsub c.property)
  have hrel (c : C₀) : dom (rel c) = c.val := Classical.choose_spec (hsub c.property)
  let D := (fun c : C₀ => (rel c).val) '' Set.univ
  have hD : D.Finite := by
    haveI : Finite C₀ := hfin.to_subtype
    simpa only [D, Set.image_univ] using Set.finite_range (fun c : C₀ => (rel c).val)
  have hgood : ∀ R ∈ D, RelationDefinable S R ∧ SingleValued R := by
    rintro R ⟨c, _, rfl⟩
    exact ⟨(rel c).property.1, (rel c).property.2.1⟩
  obtain ⟨U, hU, hsU, hUD, hdom⟩ := glue_finite S D hD hgood
  refine ⟨U, hU, hsU, ?_, ?_⟩
  · intro p hp
    obtain ⟨R, ⟨c, _, rfl⟩, hpR⟩ := hUD p hp
    exact (rel c).property.2.2 hpR
  · intro a ha
    obtain ⟨c, hc, hac⟩ := hcov a ha
    apply (hdom a).mpr
    refine ⟨(rel ⟨c, hc⟩).val, Set.mem_image_of_mem _ (Set.mem_univ _), ?_⟩
    change a ∈ dom (rel ⟨c, hc⟩)
    rw [hrel]
    exact hac

/-- A genuine partial function with its complete graph definable over S. -/
theorem definable_choice {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → M)) (hA : S.Definable LRV A)
    (P : Set ((Fin n → M) × M)) (hP : RelationDefinable S P)
    (hlocal : ∀ a ∈ A, ∃ b, (a, b) ∈ P ∧
      (S ∪ Set.range a).Definable₁ LRV {b}) :
    ∃ f : A → M, (∀ a, (a.val, f a) ∈ P) ∧
      S.Definable LRV {z : Fin n ⊕ Fin 1 → M |
        ∃ a : A, a.val = z ∘ Sum.inl ∧ f a = z (.inr 0)} := by
  classical
  obtain ⟨U, hU, hsU, hUP, hcov⟩ := definable_choice_graph hs S hsmall A hA P hP hlocal
  let f (a : A) : M := Classical.choose (hcov a.val a.property)
  have hf (a : A) : (a.val, f a) ∈ U := Classical.choose_spec (hcov a.val a.property)
  refine ⟨f, fun a => hUP (hf a), ?_⟩
  have he : {z : Fin n ⊕ Fin 1 → M |
      ∃ a : A, a.val = z ∘ Sum.inl ∧ f a = z (.inr 0)} =
      {z | z ∘ Sum.inl ∈ A ∧ (z ∘ Sum.inl, z (.inr 0)) ∈ U} := by
    ext z
    constructor
    · rintro ⟨a, ha, hb⟩
      exact ⟨ha ▸ a.property, ha ▸ hb ▸ hf a⟩
    · rintro ⟨ha, hb⟩
      exact ⟨⟨z ∘ Sum.inl, ha⟩, rfl, hsU _ _ _ (hf _) hb⟩
  rw [he]
  exact (hA.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin 1)).inter hU

end SpecialTransformations.Section3.RawClosure.Tuple
