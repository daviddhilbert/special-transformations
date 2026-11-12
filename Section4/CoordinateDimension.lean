module

public import Section4.CoordinatePieces
public import Section4.FiniteCover
public import Section4.FiniteGluing
public import Section4.VFDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem coordinate_piece_of_algebraic {S : Set M} {n r k d : ℕ} (hd : d ≤ k)
    (v : Fin d → Fin n) (a : (rawMixedSpace (M := M) n r).Carrier)
    (ha : ∀ j, RawClosure.AlgebraicOver (S ∪ Set.range (vfValues (a.1 ∘ v)))
      (a.1 j).val) :
    ∃ D : CoordinatePiece (M := M) S n k, a ∈ (D.source r).carrier := by
  have h (j : Fin n) := RawClosure.Tuple.good_relation_of_algebraic S
    (vfValues (a.1 ∘ v)) (a.1 j).val (ha j)
  choose R hR using h
  exact ⟨⟨d, hd, v, R⟩, hR⟩

/-- Uniformize coordinate algebraicity over the original small parameter
base. Saturation gives finitely many finite-relation pieces, and finite
gluing gives a genuine finite-to-one witness with k VF coordinates. -/
theorem finite_mixed_map_of_coordinate_algebraicity
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ)
    (halg : ∀ a : A, ∃ d ≤ k, ∃ v : Fin d → Fin n,
      ∀ j, RawClosure.AlgebraicOver (S ∪ Set.range (vfValues (a.val.1 ∘ v)))
        (a.val.1 j).val) :
    ∃ f : Map A (DefSet.univ (rawMixedSpace (M := M) k r) S), f.FiniteFibres := by
  let P := rawMixedSpace (M := M) n r
  let Data := CoordinatePiece (M := M) S n k
  let U (D : Data) := P.preimage (D.source r).carrier
  have hU (D : Data) : S.Definable LRV (U D) := (D.source r).definable
  have hcover : ∀ z ∈ P.preimage A.carrier, ∃ c ∈ Set.range U, z ∈ c := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨P.decode ⟨z, hz⟩, ha⟩
    obtain ⟨d, hd, v, hv⟩ := halg a
    obtain ⟨D, hD⟩ := coordinate_piece_of_algebraic hd v a.val hv
    exact ⟨U D, Set.mem_range_self D, hz, hD⟩
  obtain ⟨C, hC, hsub, hcov⟩ := definable_finite_subcover_index hs S hsmall
    (P.preimage A.carrier) A.definable (Set.range U)
    (by rintro _ ⟨D, rfl⟩; exact hU D) hcover
  letI : Fintype C := hC.fintype
  have hchoice (c : C) : ∃ D : Data, U D = c.val := hsub c.property
  let D (c : C) : Data := Classical.choose (hchoice c)
  have hD (c : C) : U (D c) = c.val := Classical.choose_spec (hchoice c)
  let B := DefSet.univ (rawMixedSpace (M := M) k r) S
  have hcover' : ∀ a : A, ∃ c : C, a.val ∈ ((D c).source r).carrier := by
    intro a
    have ha : mixedValues a.val ∈ P.preimage A.carrier :=
      ⟨mixedValues_mem_domain a.val, by simpa only [P, decode_mixedValues] using a.property⟩
    obtain ⟨c, hc, hac⟩ := hcov _ ha
    let c' : C := ⟨c, hc⟩
    refine ⟨c', ?_⟩
    have hac' := (Set.ext_iff.mp (hD c') (mixedValues a.val)).mpr hac
    have hmem := (P.preimage_decode ((D c').source r).carrier
      ⟨mixedValues a.val, mixedValues_mem_domain a.val⟩).mp hac'
    simpa only [P, decode_mixedValues] using hmem
  exact finite_cover_finite_map A B (fun c : C => (D c).source r)
    (fun c => (D c).paddedProjection r) (fun c => (D c).paddedProjection_finite r) hcover'

theorem vfDim_le_of_coordinate_algebraicity
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ)
    (halg : ∀ a : A, ∃ d ≤ k, ∃ v : Fin d → Fin n,
      ∀ j, RawClosure.AlgebraicOver (S ∪ Set.range (vfValues (a.val.1 ∘ v)))
        (a.val.1 j).val) :
    vfDim Γ A ≤ k := by
  obtain ⟨f, hf⟩ := finite_mixed_map_of_coordinate_algebraicity hs hsmall A k halg
  exact (vfDim_le_iff Γ A k).mpr ⟨k, le_rfl, .rv r, f, hf⟩

end SpecialTransformations.Section4

end
