module

public import Section4.RVSequenceIndependence
public import Section3.SortedFunctionClosure

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem RVSequenceIndependent.mono_base {S T : Set M} (hST : S ⊆ T)
    {n : ℕ} {t : Fin n → CanonicalRV.RVSort M} (ht : RVSequenceIndependent T t) :
    RVSequenceIndependent S t := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact ⟨ih ht.1, fun h => ht.2 (h.mono (Set.union_subset_union_left _ hST))⟩

theorem RVSequenceIndependent.not_algebraic {S : Set M}
    {n : ℕ} {t : Fin n → CanonicalRV.RVSort M} (ht : RVSequenceIndependent S t) :
    ∀ i, ¬ AlgebraicAt S .rv (t i).val := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ih ht.1 i)
    exact fun h => ht.2 (h.mono Set.subset_union_left)

theorem RVSequenceIndependent.nonzero {S : Set M}
    {n : ℕ} {t : Fin n → CanonicalRV.RVSort M} (ht : RVSequenceIndependent S t) :
    ∀ i, (t i).val ≠ iRVZero := by
  intro i hi
  apply ht.not_algebraic i
  rw [hi]
  exact (definableClosureAt_function_symbol S Fn.rvZero Fin.elim0
    (fun j => j.elim0) (fun j => j.elim0)).algebraic

theorem rvTupleRank_eq_arity_of_sequence
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    (S : Set M) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M)
    (ht : RVSequenceIndependent S t) : rvTupleRank hcan hex S t = n := by
  obtain ⟨hi, hI⟩ := (rvSequenceIndependent_iff hcan hex S t).mp ht
  have he : (Set.range t).encard = (n : ℕ∞) := by
    rw [← Set.image_univ, hi.encard_image, Set.encard_univ]
    simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  change ((rvAlgebraicMatroid hcan hex S).eRk (Set.range t)).toNat = n
  rw [hI.eRk_eq_encard, he]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.toNat_natCast]

theorem rvTupleRank_subsequence_le
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    (S : Set M) {n k : ℕ} (t : Fin n → CanonicalRV.RVSort M) (v : Fin k → Fin n) :
    rvTupleRank hcan hex S (t ∘ v) ≤ rvTupleRank hcan hex S t := by
  apply ENat.toNat_le_toNat
    ((rvAlgebraicMatroid hcan hex S).eRk_mono (Set.range_comp_subset_range v t))
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (rvTupleERank_le_arity hcan hex S t))

end SpecialTransformations.Section4

end
