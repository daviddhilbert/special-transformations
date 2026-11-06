import Section3.TupleCompactness
import Section3.TupleRelations
set_option linter.style.haveILetI false

/-!
# Uniform bounds on definable finite fibres

The bound follows from genuine small-parameter saturation. It is not an
assumption of the dimension or coding interfaces.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Section3

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

theorem uniform_finite_fibre_bound {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {n : ℕ}
    (R : Set ((Fin n → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R)
    (hfinite : ∀ a, {x | (a, x) ∈ R}.Finite) :
    ∃ N : ℕ, ∀ a, {x | (a, x) ∈ R}.ncard ≤ N := by
  let U (k : ℕ) : Set (Fin n → M) := (RawClosure.Tuple.HasMore R k)ᶜ
  have hU (k : ℕ) : S.Definable LRV (U k) :=
    (RawClosure.Tuple.hasMore_definable S R hR k).compl
  have hcover : ∀ a ∈ (Set.univ : Set (Fin n → M)), ∃ c ∈ Set.range U, a ∈ c := by
    intro a _
    refine ⟨U {x | (a, x) ∈ R}.ncard, Set.mem_range_self _, ?_⟩
    exact RawClosure.no_inj_iff_finite_ncard_le.mpr ⟨hfinite a, le_rfl⟩
  obtain ⟨C, hC, hsub, hcover⟩ := hs.definable_finite_subcover_tuple S hsmall
    Set.univ (Set.definable_univ (A := S) (L := LRV)) (Set.range U)
    (by rintro _ ⟨k, rfl⟩; exact hU k) hcover
  letI : Fintype C := hC.fintype
  have hindex (c : C) : ∃ k, U k = c.val := hsub c.property
  let k (c : C) : ℕ := Classical.choose (hindex c)
  have hk (c : C) : U (k c) = c.val := Classical.choose_spec (hindex c)
  refine ⟨∑ c : C, k c, ?_⟩
  intro a
  obtain ⟨c, hc, hac⟩ := hcover a (Set.mem_univ a)
  let c' : C := ⟨c, hc⟩
  have ha : a ∈ U (k c') := by rw [hk]; exact hac
  have ha' : ¬ ∃ u : Fin (k c' + 1) → M, Function.Injective u ∧
      ∀ i, u i ∈ {x | (a, x) ∈ R} := ha
  have hb := (RawClosure.no_inj_iff_finite_ncard_le.mp ha').2
  exact hb.trans (Finset.single_le_sum (fun c _ => Nat.zero_le (k c)) (Finset.mem_univ c'))

end SpecialTransformations.Section4
