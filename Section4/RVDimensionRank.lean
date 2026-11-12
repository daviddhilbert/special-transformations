module

public import Section4.RVCoordinatePieces
public import Section4.RVFiniteMapRank
public import Section4.FiniteCover
public import Section4.FiniteGluing

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_coordinate_piece_of_algebraic {S : Set M} {n k d : ℕ} (hd : d ≤ k)
    (v : Fin d → Fin n) (a : (rawRVSpace (M := M) n).Carrier)
    (ha : ∀ j, RawClosure.AlgebraicOver (S ∪ Set.range (rvValues (a ∘ v))) (a j).val) :
    ∃ D : RVCoordinatePiece (M := M) S n k, a ∈ D.source.carrier := by
  have h (j : Fin n) := RawClosure.Tuple.good_relation_of_algebraic S
    (rvValues (a ∘ v)) (a j).val (ha j)
  choose R hR using h
  exact ⟨⟨d, hd, v, R⟩, hR⟩

/-- Compactness over the original base gives finitely many coordinate
pieces. Gluing their actual maps proves the upper bound in Definition 4.9. -/
theorem rvDim_le_of_coordinate_algebraicity
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) (k : ℕ)
    (halg : ∀ a : A, ∃ d ≤ k, ∃ v : Fin d → Fin n,
      ∀ j, RawClosure.AlgebraicOver (S ∪ Set.range (rvValues (a.val ∘ v))) (a.val j).val) :
    rvDim A ≤ k := by
  let P := rawRVSpace (M := M) n
  let Data := RVCoordinatePiece (M := M) S n k
  let U (D : Data) := P.preimage D.source.carrier
  have hU (D : Data) : S.Definable LRV (U D) := D.source.definable
  have hcover : ∀ z ∈ P.preimage A.carrier, ∃ c ∈ Set.range U, z ∈ c := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨P.decode ⟨z, hz⟩, ha⟩
    obtain ⟨d, hd, v, hv⟩ := halg a
    obtain ⟨D, hD⟩ := rv_coordinate_piece_of_algebraic hd v a.val hv
    exact ⟨U D, Set.mem_range_self D, hz, hD⟩
  obtain ⟨C, hC, hsub, hcov⟩ := definable_finite_subcover_index hs S hsmall
    (P.preimage A.carrier) A.definable (Set.range U)
    (by rintro _ ⟨D, rfl⟩; exact hU D) hcover
  letI : Fintype C := hC.fintype
  have hchoice (c : C) : ∃ D : Data, U D = c.val := hsub c.property
  let D (c : C) : Data := Classical.choose (hchoice c)
  have hD (c : C) : U (D c) = c.val := Classical.choose_spec (hchoice c)
  let B := DefSet.univ (rawRVSpace (M := M) k) S
  have hcover' : ∀ a : A, ∃ c : C, a.val ∈ (D c).source.carrier := by
    intro a
    have ha : rvValues a.val ∈ P.preimage A.carrier :=
      ⟨⟨a.val, rfl⟩, by simpa only [P, decode_rvValues] using a.property⟩
    obtain ⟨c, hc, hac⟩ := hcov _ ha
    let c' : C := ⟨c, hc⟩
    refine ⟨c', ?_⟩
    have hac' := (Set.ext_iff.mp (hD c') (rvValues a.val)).mpr hac
    have hmem := (P.preimage_decode (D c').source.carrier
      ⟨rvValues a.val, ⟨a.val, rfl⟩⟩).mp hac'
    simpa only [P, decode_rvValues] using hmem
  obtain ⟨f, hf⟩ := finite_cover_finite_map A B (fun c : C => (D c).source)
    (fun c => (D c).paddedProjection) (fun c => (D c).paddedProjection_finite) hcover'
  exact (rvDim_le_iff A k).mpr ⟨k, le_rfl, f, hf⟩

variable (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))

theorem rvDim_le_of_point_rank
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) (k : ℕ)
    (hrank : ∀ a : A, rvTupleRank hcan hex S a.val ≤ k) : rvDim A ≤ k := by
  apply rvDim_le_of_coordinate_algebraicity hs hsmall A k
  intro a
  obtain ⟨v, hv⟩ := exists_rv_coordinate_basis hcan hex S a.val
  exact ⟨rvTupleRank hcan hex S a.val, hrank a, v,
    fun j => (hv j).raw_finite_witness⟩

theorem rvDim_le_iff_point_rank
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) (k : ℕ) :
    rvDim A ≤ k ↔ ∀ a : A, rvTupleRank hcan hex S a.val ≤ k := by
  exact ⟨fun h a => (rvTupleRank_le_rvDim hcan hex A a).trans h,
    rvDim_le_of_point_rank hcan hex hs hsmall A k⟩

def rvPointRankMaximum {S : Set M} {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) : ℕ :=
  ⨆ a : A, rvTupleRank hcan hex S a.val

theorem rvPointRankMaximum_bounded {S : Set M} {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) :
    BddAbove (Set.range (fun a : A => rvTupleRank hcan hex S a.val)) :=
  ⟨n, by rintro _ ⟨a, rfl⟩; exact rvTupleRank_le_arity hcan hex S a.val⟩

/-- Definition 4.9 equals the maximum rank in genuine RV algebraic closure.
The exchange hypothesis is exactly the accepted earlier-section principle. -/
theorem rvDim_eq_point_rank_maximum
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) :
    rvDim A = rvPointRankMaximum hcan hex A := by
  apply Nat.le_antisymm
  · apply rvDim_le_of_point_rank hcan hex hs hsmall A
    intro a
    exact le_ciSup (rvPointRankMaximum_bounded hcan hex A) a
  · exact ciSup_le' (fun a => rvTupleRank_le_rvDim hcan hex A a)

theorem exists_point_of_maximum_rv_rank
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) (hne : A.carrier.Nonempty) :
    ∃ a : A, rvTupleRank hcan hex S a.val = rvDim A := by
  obtain ⟨a, ha⟩ := hne
  have hrange : (Set.range (fun a : A => rvTupleRank hcan hex S a.val)).Nonempty :=
    ⟨_, ⟨a, ha⟩, rfl⟩
  obtain ⟨p, hp⟩ := Nat.sSup_mem hrange (rvPointRankMaximum_bounded hcan hex A)
  exact ⟨p, hp.trans (rvDim_eq_point_rank_maximum hcan hex hs hsmall A).symm⟩

/-- The independent subsequence assertion immediately after Definition 4.9. -/
theorem exists_independent_rv_subsequence_of_dimension
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S) (hne : A.carrier.Nonempty) :
    ∃ a : A, ∃ v : Fin (rvDim A) → Fin n, Function.Injective v ∧
      (rvAlgebraicMatroid hcan hex S).Indep (Set.range (a.val ∘ v)) := by
  obtain ⟨a, ha⟩ := exists_point_of_maximum_rv_rank hcan hex hs hsmall A hne
  obtain ⟨v, hv, _, hind, _⟩ := exists_rv_coordinate_basis_independent hcan hex S a.val
  refine ⟨a, ?_⟩
  rw [← ha]
  exact ⟨v, hv, hind⟩

end SpecialTransformations.Section4

end
