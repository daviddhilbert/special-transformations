import Section3.TuplePromotion
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

def SingleValued (R : Set ((Fin n → M) × M)) : Prop :=
  ∀ a b c, (a, b) ∈ R → (a, c) ∈ R → b = c

theorem domain_definable (S : Set M) (R : Set ((Fin n → M) × M))
    (hR : RelationDefinable S R) : S.Definable LRV {a | ∃ b, (a, b) ∈ R} := by
  have h := hR.exists_of_finite
  convert h using 1
  ext a
  change (∃ b, (a, b) ∈ R) ↔ ∃ y : Fin 1 → M, (a, y 0) ∈ R
  exact ⟨fun ⟨b, hb⟩ => ⟨![b], hb⟩, fun ⟨y, hy⟩ => ⟨y 0, hy⟩⟩

/-- Resolve overlaps by using the left graph on its domain. -/
theorem glue_two (S : Set M) (R Q : Set ((Fin n → M) × M))
    (hR : RelationDefinable S R) (hQ : RelationDefinable S Q)
    (hsR : SingleValued R) (hsQ : SingleValued Q) :
    ∃ U : Set ((Fin n → M) × M), RelationDefinable S U ∧ SingleValued U ∧
      U ⊆ R ∪ Q ∧ ∀ a, (∃ b, (a, b) ∈ U) ↔
        (∃ b, (a, b) ∈ R) ∨ ∃ b, (a, b) ∈ Q := by
  classical
  let U : Set ((Fin n → M) × M) :=
    {p | p ∈ R ∨ p ∈ Q ∧ ¬ ∃ b, (p.1, b) ∈ R}
  have hdom := (domain_definable S R hR).compl.preimage_comp
    (Sum.inl : Fin n → Fin n ⊕ Fin 1)
  refine ⟨U, hR.union (hQ.inter hdom), ?_, ?_, ?_⟩
  · intro a b c hb hc
    rcases hb with hb | ⟨hb, hnb⟩
    · rcases hc with hc | ⟨_, hnc⟩
      · exact hsR a b c hb hc
      · exact (hnc ⟨b, hb⟩).elim
    · rcases hc with hc | ⟨hc, _⟩
      · exact (hnb ⟨c, hc⟩).elim
      · exact hsQ a b c hb hc
  · rintro p (hp | ⟨hp, _⟩)
    · exact Or.inl hp
    · exact Or.inr hp
  · intro a
    constructor
    · rintro ⟨b, hb | ⟨hb, _⟩⟩
      · exact Or.inl ⟨b, hb⟩
      · exact Or.inr ⟨b, hb⟩
    · intro ha
      by_cases hr : ∃ b, (a, b) ∈ R
      · obtain ⟨b, hb⟩ := hr
        exact ⟨b, Or.inl hb⟩
      · obtain ⟨b, hb⟩ := ha.resolve_left hr
        exact ⟨b, Or.inr ⟨hb, hr⟩⟩

/-- A finite family of definable partial functions can be glued without
introducing parameters, preserving their union of domains. -/
theorem glue_finite (S : Set M) (C : Set (Set ((Fin n → M) × M))) (hfin : C.Finite)
    (hC : ∀ R ∈ C, RelationDefinable S R ∧ SingleValued R) :
    ∃ U : Set ((Fin n → M) × M), RelationDefinable S U ∧ SingleValued U ∧
      (∀ p ∈ U, ∃ R ∈ C, p ∈ R) ∧
      ∀ a, (∃ b, (a, b) ∈ U) ↔ ∃ R ∈ C, ∃ b, (a, b) ∈ R := by
  induction C, hfin using Set.Finite.induction_on with
  | empty =>
    refine ⟨∅, Set.definable_empty, ?_, ?_, ?_⟩
    · intro a b c hb; exact hb.elim
    · intro p hp; exact hp.elim
    · intro a; simp
  | @insert R C hRnot hfin ih =>
    obtain ⟨U, hU, hsU, hsub, hdom⟩ := ih (fun Q hQ => hC Q (Or.inr hQ))
    obtain ⟨V, hV, hsV, hVU, hdomV⟩ := glue_two S R U (hC R (Or.inl rfl)).1 hU
      (hC R (Or.inl rfl)).2 hsU
    refine ⟨V, hV, hsV, ?_, ?_⟩
    · intro p hp
      rcases hVU hp with hp | hp
      · exact ⟨R, Or.inl rfl, hp⟩
      · obtain ⟨Q, hQ, hp⟩ := hsub p hp
        exact ⟨Q, Or.inr hQ, hp⟩
    · intro a
      rw [hdomV, hdom]
      simp only [Set.mem_insert_iff, or_and_right, exists_or, exists_eq_left]

end SpecialTransformations.Section3.RawClosure.Tuple
