import Section9.FiniteHeadCover
import Section9.GammaRankBound
import Section9.GammaRawRelations

/-! Gamma counterpart of `exists_finite_head_cover`: a Gamma-definable RV
set of RV dimension at most `k`, coded over a base context, is covered by
finitely many Gamma-definable pieces with finite projections to `k`
coordinates. The coordinate pieces are cut out by good relations over the
real base; the Gamma rank bound replaces the rank bound over the code set. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (gammaLogicInput)

namespace SpecialTransformations.Section9.GammaLift

private theorem gamma_exists_head_embedding {d k n : ℕ} (v : Fin d → Fin n)
    (hv : Function.Injective v) (hdk : d ≤ k) (hkn : k ≤ n) :
    ∃ w : Fin k ↪ Fin n, Set.range v ⊆ Set.range w := by
  classical
  let s := Finset.univ.image v
  have hs : s.card = d := by rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
  obtain ⟨t, hst, ht⟩ := Finset.exists_superset_card_eq (hs.trans_le hdk)
    (by simpa only [Fintype.card_fin] using hkn)
  let e : Fin k ≃ t := (Fintype.equivFinOfCardEq ((Fintype.card_coe t).trans ht)).symm
  let w : Fin k ↪ Fin n := ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective⟩
  refine ⟨w, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := e.surjective ⟨v i, hst (Finset.mem_image_of_mem v (Finset.mem_univ i))⟩
  exact ⟨j, congrArg Subtype.val hj⟩

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gamma_exists_finite_head_cover
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) (hBS : B.real ⊆ (C.base : Set M)) {n k : ℕ} (hkn : k ≤ n)
    (A : DefSet (rawRVSpace (M := M) n) (C.base : Set M)) (hAΓ : RVSetGamma A B) (hA : rvDim A ≤ k) :
    ∃ m : ℕ, ∃ P : Fin m → DefSet (rawRVSpace (M := M) n) (C.base : Set M), ∃ v : Fin m → Fin k ↪ Fin n,
      (∀ i, (P i).carrier ⊆ A.carrier ∧ RVSetGamma (P i) B ∧ (rvHeadSelect (v i) (P i)).FiniteFibres) ∧
      ∀ a : A, ∃ i, a.val ∈ (P i).carrier := by
  have hκ : Cardinal.aleph0 ≤ C.κ := C.uncountable.le
  have hs := C.saturated
  have h00 := C.model00
  have hsmall := C.small
  let S := B.real
  classical
  let hex := rvExchangeInput_of_earlier hκ hs h00
  let Data := (Fin k ↪ Fin n) × (Fin n → RawClosure.Tuple.GoodRelation (n := k) S)
  let D (p : Data) : RVCoordinatePiece (M := M) S n k := ⟨k, le_rfl, p.1, p.2⟩
  let Q := rawRVSpace (M := M) n
  let U (p : Data) := Q.preimage ((D p).source.extend hBS).carrier
  have hcover : ∀ z ∈ Q.preimage A.carrier, ∃ d ∈ Set.range U, z ∈ d := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨Q.decode ⟨z, hz⟩, ha⟩
    obtain ⟨v, hv, _, _, hrel⟩ := exists_rv_coordinate_basis_independent hc hex S a.val
    obtain ⟨w, hw⟩ := gamma_exists_head_embedding v hv ((gamma_rank_le_rvDim hc C B hBS A hAΓ a).trans hA) hkn
    have hsub : Set.range (rvValues (a.val ∘ v)) ⊆ Set.range (rvValues (a.val ∘ w)) := by
      rintro _ ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := hw (Set.mem_range_self j)
      exact ⟨i, congrArg (fun l => (a.val l).val) hi⟩
    have halg (j : Fin n) : RawClosure.AlgebraicOver (S ∪ Set.range (rvValues (a.val ∘ w)))
        (a.val j).val := ((hrel j).mono (Set.union_subset_union_right S hsub)).raw_finite_witness
    choose R hR using fun j => RawClosure.Tuple.good_relation_of_algebraic S
      (rvValues (a.val ∘ w)) (a.val j).val (halg j)
    exact ⟨U (w,R), Set.mem_range_self (w,R), hz, hR⟩
  obtain ⟨J, hJ, hsub, hJcov⟩ := definable_finite_subcover_index hs (C.base : Set M) hsmall
    (Q.preimage A.carrier) A.definable (Set.range U)
    (by rintro _ ⟨p, rfl⟩; exact ((D p).source.extend hBS).definable) hcover
  letI : Fintype J := hJ.fintype
  let e := (Fintype.equivFin J).symm
  choose p hp using fun i => hsub (e i).property
  let P (i : Fin (Fintype.card J)) := A.inter ((D (p i)).source.extend hBS)
  have hP (i : Fin (Fintype.card J)) : (P i).carrier ⊆ (D (p i)).source.carrier := fun _ h => h.2
  refine ⟨_, P, fun i => (p i).1, ?_, ?_⟩
  · intro i
    refine ⟨fun _ h => h.1, ?_, ?_⟩
    · have hsrc := rv_set_gamma_of_raw (B := B) hc (D (p i)).codeSet (D (p i)).codeSet_definable
      exact (gammaLogicInput B).inter hAΓ hsrc
    intro y
    have hfin := (D (p i)).projection_finite ⟨y.val, Set.mem_univ _⟩
    let ι : P i → (D (p i)).source := fun x => ⟨x.val, hP i x.property⟩
    apply Set.Finite.of_finite_image (f := ι) ?_ (fun a _ b _ h => Subtype.ext (congrArg (fun z : (D (p i)).source => z.val) h))
    apply hfin.subset
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    exact congrArg Subtype.val hx
  · intro a
    have ha : rvValues a.val ∈ Q.preimage A.carrier :=
      ⟨⟨a.val, rfl⟩, by simpa only [Q, decode_rvValues] using a.property⟩
    obtain ⟨d, hd, had⟩ := hJcov _ ha
    obtain ⟨i, hi⟩ := e.surjective (⟨d, hd⟩ : J)
    have hp' : U (p i) = d := (hp i).trans (congrArg Subtype.val hi)
    have hb : rvValues a.val ∈ U (p i) := hp'.symm ▸ had
    have hmem := (Q.preimage_decode ((D (p i)).source.extend hBS).carrier
      ⟨rvValues a.val, ⟨a.val, rfl⟩⟩).mp hb
    exact ⟨i, a.property, by simpa only [Q, decode_rvValues] using hmem⟩

end SpecialTransformations.Section9.GammaLift
