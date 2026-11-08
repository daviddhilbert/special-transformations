import Section5.GammaInvariantLogic
import Section5.GammaLift
import Section5.CategoryPresentations
import Section4.VFDimensionRank

/-! A dimension-controlled real envelope and its restriction to a set
with named Gamma parameters. The restriction uses the full invariant
graph over the original base. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

/-- Cover a low-rank set defined over a larger parameter set by a
low-dimensional set over the original real base. In applications the
extra names are RV representatives of named Gamma parameters. -/
private theorem finite_mixed_cover_of_point_trdeg {κ : Cardinal} (hs : Saturated M κ)
    {S T : Set M} (hST : S ⊆ T) (hsmall : Cardinal.mk T < κ)
    {n r : ℕ} (A : DefinableGeometry.DefSet (rawMixedSpace (M := M) n r) T) (k : ℕ)
    (hdeg : ∀ a : A, vfTupleTrdeg S a.val.1 ≤ (k : Cardinal)) :
    ∃ C : DefinableGeometry.DefSet (rawMixedSpace (M := M) n r) S, A.carrier ⊆ C.carrier ∧
      ∃ f : DefinableGeometry.Map C
        (DefinableGeometry.DefSet.univ (rawMixedSpace (M := M) k r) S), f.FiniteFibres := by
  let P := rawMixedSpace (M := M) n r
  let Data := CoordinatePiece (M := M) S n k
  let U (D : Data) := P.preimage (D.source r).carrier
  have hU (D : Data) : T.Definable LRV (U D) :=
    Set.Definable.mono (show S.Definable LRV (U D) from (D.source r).definable) hST
  have hcover : ∀ z ∈ P.preimage A.carrier, ∃ c ∈ Set.range U, z ∈ c := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨P.decode ⟨z, hz⟩, ha⟩
    obtain ⟨d, hd, v, hv⟩ := exists_algebraic_coordinate_basis
      (vfParameterField S) a.val.1 (hdeg a)
    have hcoord (j : Fin n) : RawClosure.AlgebraicOver
        (S ∪ Set.range (vfValues (a.val.1 ∘ v))) (a.val.1 j).val := by
      apply AlgebraicAt.raw_finite_witness
      apply (algebraicAt_vf_iff_parameterField _ (a.val.1 j)).mpr
      rw [vfParameterField_union_tuple]
      exact hv j
    obtain ⟨D, hD⟩ := coordinate_piece_of_algebraic hd v a.val hcoord
    exact ⟨U D, Set.mem_range_self D, hz, hD⟩
  obtain ⟨J, hJ, hsub, hcov⟩ := definable_finite_subcover_index hs T hsmall
    (P.preimage A.carrier) A.definable (Set.range U)
    (by rintro _ ⟨D, rfl⟩; exact hU D) hcover
  letI : Fintype J := hJ.fintype
  have chooseData (j : J) : ∃ D : Data, U D = j.val := hsub j.property
  let D (j : J) := Classical.choose (chooseData j)
  have hD (j : J) : U (D j) = j.val := Classical.choose_spec (chooseData j)
  let C₀ := ⋃ j : J, ((D j).source r).carrier
  have hC : P.Definable S C₀ := by
    change S.Definable LRV (P.preimage C₀)
    convert Set.definable_iUnion_of_finite (fun j : J => ((D j).source r).definable) using 1
    ext z
    constructor
    · rintro ⟨hz, h⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨j, hz, hj⟩
    · intro h
      obtain ⟨j, hz, hj⟩ := Set.mem_iUnion.mp h
      exact ⟨hz, Set.mem_iUnion.mpr ⟨j, hj⟩⟩
  let C : DefinableGeometry.DefSet P S := ⟨C₀, hC⟩
  have hAC : A.carrier ⊆ C.carrier := by
    intro x hx
    have hx' : mixedValues x ∈ P.preimage A.carrier :=
      ⟨mixedValues_mem_domain x, by simpa only [P, decode_mixedValues] using hx⟩
    obtain ⟨j, hj, hxj⟩ := hcov _ hx'
    let j' : J := ⟨j, hj⟩
    have hxD : mixedValues x ∈ U (D j') := (hD j').symm ▸ hxj
    have hxD' := (P.preimage_decode ((D j').source r).carrier
      ⟨mixedValues x, mixedValues_mem_domain x⟩).mp hxD
    exact Set.mem_iUnion.mpr ⟨j', by simpa only [P, decode_mixedValues] using hxD'⟩
  refine ⟨C, hAC, ?_⟩
  exact finite_cover_finite_map C (DefinableGeometry.DefSet.univ (rawMixedSpace k r) S)
    (fun j => (D j).source r) (fun j => (D j).paddedProjection r)
    (fun j => (D j).paddedProjection_finite r) (fun a => Set.mem_iUnion.mp a.property)

private def pointPresentation {S : Set M} {n m : ℕ}
    (C : PresentedSet (rawPointSpace (M := M) n m) S) : DefSet (M := M) S n m := by
  let W := PresentedSet.univ (pointSpace (M := M) n m) S
  let f := rawPointMap W
  have hp := Map.definable_preimage f (setDefinable C)
  refine PresentedSet.mk (carrier (P := rawPointSpace (M := M) n m) C) ?_
  convert hp using 1
  ext p
  constructor
  · intro h
    exact ⟨⟨p, Set.mem_univ _⟩, rfl, h⟩
  · rintro ⟨a, rfl, ha⟩
    exact ha

private def mapFromPointPresentation {S : Set M} {n m : ℕ}
    (C : PresentedSet (rawPointSpace (M := M) n m) S) :
    Map (pointPresentation C) C :=
  Map.mk (fun a => ⟨a.val, a.property⟩) (Map.graph_definable (rawPointMap (pointPresentation C)))

private theorem realLowDimensionEnvelope {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n m k : ℕ} (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A)
    (hRank : ∀ p ∈ A, @vfTupleTrdeg M N hN B.real n p.1 ≤ (k : Cardinal)) :
    ∃ C : PresentedSet (rawPointSpace (M := M) n m) B.real, A ⊆ carrier (P := rawPointSpace (M := M) n m) C ∧
      @vfDim M N (@Section4.gammaSpace M sM hM) (rawPointSpace n m) B.real C ≤ k := by
  obtain ⟨d, t, _, D, hD⟩ := gammaPresentationInput B A hA
  let T := B.real ∪ Set.range (GammaParameters.rawTuple t)
  let g := rawPointMap D
  let E := Map.image g
  have hE : carrier E = A := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      exact hD ▸ a.property
    · intro hp
      have hpD : p ∈ carrier D := hD.symm ▸ hp
      exact ⟨⟨p, hpD⟩, rfl⟩
  have hsmallT : Cardinal.mk T < κ := small_union_range hκ B.real hsmall
    (GammaParameters.rawTuple t)
  let hsN : @Saturated M N κ := hs.normalize
  let Δ := @Section4.gammaSpace M sM hM
  obtain ⟨C, hAC, f, hf⟩ := @finite_mixed_cover_of_point_trdeg M N hN κ hsN
    B.real T Set.subset_union_left hsmallT n m E k
    (fun p => hRank p.val (hE ▸ p.property))
  exact ⟨C, hE ▸ hAC, (@vfDim_le_iff M N hN Δ B.real n m C k).mpr ⟨k, le_rfl, .rv m, f, hf⟩⟩

theorem gammaDimensionalPresentation_of_rank {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) {n m k : ℕ}
    (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A)
    (hRank : ∀ p ∈ A, @vfTupleTrdeg M N hN B.real n p.1 ≤ (k : Cardinal)) :
    ∃ l : ℕ, ∃ D : Set (Point (M := M) k l), Nonempty (GammaIso B A D) := by
  obtain ⟨C, hAC, hd⟩ := realLowDimensionEnvelope hκ hs B hsmall A hA hRank
  let Δ := @Section4.gammaSpace M sM hM
  let O : normalizedVFObject Δ B.real k := by
    letI : LRV.Structure M := N
    exact ⟨⟨(n, m), C⟩, hd⟩
  obtain ⟨l, D, f, hf⟩ := dimensional_presentation hs h00 hsmall Δ gammaSpace_rvCoded k O
  let f' : Map C D := f
  let g := Map.comp f' (mapFromPointPresentation C)
  let q (a : A) : Point (M := M) k l := (g ⟨a.val, hAC a.property⟩).val
  have hq : Function.Injective q := by
    intro a b he
    have he' : f' (⟨a.val, hAC a.property⟩ : C) =
        f' (⟨b.val, hAC b.property⟩ : C) := Subtype.ext he
    exact Subtype.ext (congrArg (fun x : C => x.val) (hf.1 he'))
  let e := Equiv.ofInjective q hq
  let hΓ := gammaLogicInput B
  refine ⟨l, Set.range q, ⟨⟨e, ?_⟩⟩⟩
  apply GammaGraphDefinable.congr (hΓ.restrict_graph hA (hΓ.real_map_graph g))
  intro p y
  constructor
  · rintro ⟨hp, a, ha, hy⟩
    refine ⟨⟨p, hp⟩, rfl, ?_⟩
    have he : (⟨p, hAC hp⟩ : pointPresentation C) = a := Subtype.ext ha.symm
    change (g (⟨p, hAC hp⟩ : pointPresentation C)).val = y
    rw [he]
    exact hy
  · rintro ⟨a, rfl, hy⟩
    exact ⟨a.property, ⟨a.val, hAC a.property⟩, rfl, hy⟩

theorem gammaLift_of_rank {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (F : VFFieldBase B.real) {n m k : ℕ}
    (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A)
    (hRank : ∀ p ∈ A, @vfTupleTrdeg M N hN B.real n p.1 ≤ (k : Cardinal)) :
    ∃ U : GammaRVObject B k, Nonempty (GammaIso B A U.lift) :=
  corollary_5_7_gamma h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_fieldBase B F) (gammaPresentationInput B) A
    (gammaDimensionalPresentation_of_rank hκ hs h00 B hsmall A hA hRank)

end SpecialTransformations.Section5
