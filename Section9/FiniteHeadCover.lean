import Section9.RVFiniteHead
import Section4.EarlierRVInputs
import Section7.TupleCoordinates
import Mathlib.Data.Fintype.EquivFin

/-! A lower-dimensional RV set can be covered by finitely many
same-base pieces with finite coordinate projections of one arity. The
head uses actual coordinates, so the complementary coordinates remain
available for the affine tail. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

private theorem exists_head_embedding {d k n : ℕ} (v : Fin d → Fin n)
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

/-- A selected head can be placed first while retaining all
complementary coordinates as a tail. -/
theorem exists_head_reindex {k m : ℕ} (v : Fin k ↪ Fin (k + m)) :
    ∃ e : Fin (k + m) ≃ Fin (k + m), ∀ i, e (Section7.productLeft k m i) = v i := by
  classical
  let T := Set.range v
  let l : Fin k ≃ T := Equiv.ofInjective v v.injective
  have hl : Fintype.card T = k := (Fintype.card_congr l).symm.trans (Fintype.card_fin k)
  have hr : Fintype.card (↥Tᶜ : Type) = m := by
    rw [Fintype.card_compl_set, Fintype.card_fin, hl]
    omega
  let r : Fin m ≃ (↥Tᶜ : Type) := (Fintype.equivFinOfCardEq hr).symm
  let e := finSumFinEquiv.symm.trans ((l.sumCongr r).trans (Equiv.Set.sumCompl T))
  refine ⟨e, fun i => ?_⟩
  simp [e, Section7.productLeft, l]
  rfl

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_finite_head_cover
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {n k : ℕ} (hkn : k ≤ n)
    (A : DefSet (rawRVSpace (M := M) n) S) (hA : rvDim A ≤ k) :
    ∃ m : ℕ, ∃ P : Fin m → DefSet (rawRVSpace (M := M) n) S, ∃ v : Fin m → Fin k ↪ Fin n,
      (∀ i, (P i).carrier ⊆ A.carrier ∧ (rvHeadSelect (v i) (P i)).FiniteFibres) ∧
      ∀ a : A, ∃ i, a.val ∈ (P i).carrier := by
  classical
  let hex := rvExchangeInput_of_earlier hκ hs h00
  let Data := (Fin k ↪ Fin n) × (Fin n → RawClosure.Tuple.GoodRelation (n := k) S)
  let D (p : Data) : RVCoordinatePiece (M := M) S n k := ⟨k, le_rfl, p.1, p.2⟩
  let Q := rawRVSpace (M := M) n
  let U (p : Data) := Q.preimage (D p).source.carrier
  have hcover : ∀ z ∈ Q.preimage A.carrier, ∃ d ∈ Set.range U, z ∈ d := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨Q.decode ⟨z, hz⟩, ha⟩
    obtain ⟨v, hv, _, _, hrel⟩ := exists_rv_coordinate_basis_independent hc hex S a.val
    obtain ⟨w, hw⟩ := exists_head_embedding v hv ((rvTupleRank_le_rvDim hc hex A a).trans hA) hkn
    have hsub : Set.range (rvValues (a.val ∘ v)) ⊆ Set.range (rvValues (a.val ∘ w)) := by
      rintro _ ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := hw (Set.mem_range_self j)
      exact ⟨i, congrArg (fun l => (a.val l).val) hi⟩
    have halg (j : Fin n) : RawClosure.AlgebraicOver (S ∪ Set.range (rvValues (a.val ∘ w)))
        (a.val j).val := ((hrel j).mono (Set.union_subset_union_right S hsub)).raw_finite_witness
    choose R hR using fun j => RawClosure.Tuple.good_relation_of_algebraic S
      (rvValues (a.val ∘ w)) (a.val j).val (halg j)
    exact ⟨U (w,R), Set.mem_range_self (w,R), hz, hR⟩
  obtain ⟨J, hJ, hsub, hJcov⟩ := definable_finite_subcover_index hs S hsmall
    (Q.preimage A.carrier) A.definable (Set.range U)
    (by rintro _ ⟨p, rfl⟩; exact (D p).source.definable) hcover
  letI : Fintype J := hJ.fintype
  let e := (Fintype.equivFin J).symm
  choose p hp using fun i => hsub (e i).property
  let P (i : Fin (Fintype.card J)) := A.inter (D (p i)).source
  have hP (i : Fin (Fintype.card J)) : (P i).carrier ⊆ (D (p i)).source.carrier := fun _ h => h.2
  refine ⟨_, P, fun i => (p i).1, ?_, ?_⟩
  · intro i
    refine ⟨fun _ h => h.1, ?_⟩
    have he : ((D (p i)).projection.restrict (hP i)) = rvHeadSelect (p i).1 (P i) := by
      apply Map.ext
      intro a
      rfl
    rw [← he]
    exact (D (p i)).projection_finite.restrict (hP i)
  · intro a
    have ha : rvValues a.val ∈ Q.preimage A.carrier :=
      ⟨⟨a.val, rfl⟩, by simpa only [Q, decode_rvValues] using a.property⟩
    obtain ⟨d, hd, had⟩ := hJcov _ ha
    obtain ⟨i, hi⟩ := e.surjective (⟨d, hd⟩ : J)
    have hp' : U (p i) = d := (hp i).trans (congrArg Subtype.val hi)
    have hb : rvValues a.val ∈ U (p i) := hp'.symm ▸ had
    have hmem := (Q.preimage_decode (D (p i)).source.carrier
      ⟨rvValues a.val, ⟨a.val, rfl⟩⟩).mp hb
    exact ⟨i, a.property, by simpa only [Q, decode_rvValues] using hmem⟩

end SpecialTransformations.Section9
