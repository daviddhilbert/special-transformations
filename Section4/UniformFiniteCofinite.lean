module

public import Section4.UniformFinite

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

/-- Uniform finiteness in a definable family of finite/cofinite sets.
Counting both a set and its complement prevents a limit row in which both
are infinite. The two rows here partition an infinite definable universe. -/
theorem uniform_finite_cofinite_bound {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {n : ℕ}
    (P : Set (Fin n → M)) (hP : S.Definable LRV P)
    (R C : Set ((Fin n → M) × M))
    (hR : RawClosure.Tuple.RelationDefinable S R)
    (hC : RawClosure.Tuple.RelationDefinable S C)
    (hsplit : ∀ p ∈ P, {x | (p, x) ∈ R}.Finite ∨ {x | (p, x) ∈ C}.Finite)
    (hinf : ∀ p ∈ P, ¬ ({x | (p, x) ∈ R}.Finite ∧ {x | (p, x) ∈ C}.Finite)) :
    ∃ N : ℕ, ∀ p ∈ P, {x | (p, x) ∈ R}.Finite → {x | (p, x) ∈ R}.ncard ≤ N := by
  let U (k : ℕ) := (RawClosure.Tuple.HasMore R k)ᶜ ∪ (RawClosure.Tuple.HasMore C k)ᶜ
  have hU (k : ℕ) : S.Definable LRV (U k) :=
    (RawClosure.Tuple.hasMore_definable S R hR k).compl.union
      (RawClosure.Tuple.hasMore_definable S C hC k).compl
  have hcover : ∀ p ∈ P, ∃ c ∈ Set.range U, p ∈ c := by
    intro p hp
    rcases hsplit p hp with hr | hc
    · refine ⟨U {x | (p, x) ∈ R}.ncard, Set.mem_range_self _, Or.inl ?_⟩
      exact RawClosure.no_inj_iff_finite_ncard_le.mpr ⟨hr, le_rfl⟩
    · refine ⟨U {x | (p, x) ∈ C}.ncard, Set.mem_range_self _, Or.inr ?_⟩
      exact RawClosure.no_inj_iff_finite_ncard_le.mpr ⟨hc, le_rfl⟩
  obtain ⟨D, hD, hsub, hcov⟩ := hs.definable_finite_subcover_tuple S hsmall P hP
    (Set.range U) (by rintro _ ⟨k, rfl⟩; exact hU k) hcover
  letI : Fintype D := hD.fintype
  have hindex (d : D) : ∃ k, U k = d.val := hsub d.property
  let k (d : D) := Classical.choose (hindex d)
  have hk (d : D) : U (k d) = d.val := Classical.choose_spec (hindex d)
  refine ⟨∑ d : D, k d, ?_⟩
  intro p hp hr
  obtain ⟨d, hd, hpd⟩ := hcov p hp
  let d' : D := ⟨d, hd⟩
  have hpU : p ∈ U (k d') := by rw [hk]; exact hpd
  rcases hpU with hpR | hpC
  · exact ((RawClosure.no_inj_iff_finite_ncard_le
      (s := {x | (p, x) ∈ R}) (k := k d')).mp hpR).2.trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d'))
  · exact False.elim (hinf p hp ⟨hr, ((RawClosure.no_inj_iff_finite_ncard_le
      (s := {x | (p, x) ∈ C}) (k := k d')).mp hpC).1⟩)

theorem infinite_row_iff_hasMore {n : ℕ} (R : Set ((Fin n → M) × M))
    (N : ℕ) (p : Fin n → M)
    (hbound : {x | (p, x) ∈ R}.Finite → {x | (p, x) ∈ R}.ncard ≤ N) :
    {x | (p, x) ∈ R}.Infinite ↔ p ∈ RawClosure.Tuple.HasMore R N := by
  constructor
  · intro hi
    by_contra hnot
    exact hi ((RawClosure.no_inj_iff_finite_ncard_le
      (s := {x | (p, x) ∈ R}) (k := N)).mp hnot).1
  · intro hmore hfinite
    exact (RawClosure.no_inj_iff_finite_ncard_le.mpr ⟨hfinite, hbound hfinite⟩) hmore

end SpecialTransformations.Section4

end
