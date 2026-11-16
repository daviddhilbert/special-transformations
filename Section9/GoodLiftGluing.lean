module

public import Section7.LiftingDefinability

@[expose] public section

/-! Glue local lifts on prescribed definable good domains. Restricting
the VF relations to those domains lets the existing Section 7 gluing
choose a branch with the desired property on every indicated RV pair. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

private theorem rawTupleFibre_nonempty_of_sorted (t : Fin n → M) (ht : ∀ i, iRV (t i)) :
    (rawTupleFibre t).Nonempty := by
  have h (i : Fin n) := CanonicalRV.encodedRv_surjective (⟨t i, ht i⟩ : CanonicalRV.RVSort M)
  choose a ha using h
  exact ⟨fun i => (a i).val, fun i => ⟨(a i).property, congrArg Subtype.val (ha i)⟩⟩

private def restrictLiftToRV (A D : Set (Fin (n + n) → M)) : Set (Fin (n + n) → M) :=
  A ∩ (fun x => iRv ∘ x) ⁻¹' D

private theorem restrictLiftToRV_definable (S : Set M) {A D : Set (Fin (n + n) → M)}
    (hA : S.Definable LRV A) (hD : S.Definable LRV D) :
    S.Definable LRV (restrictLiftToRV A D) :=
  hA.inter (hD.preimage_map (definable_rvTuple S))

private theorem restrictLiftToRV_agrees {A D : Set (Fin (n + n) → M)} {z : Fin (n + n) → M}
    (hz : z ∈ D) {a b : Fin n → M}
    (ha : a ∈ rawTupleFibre (z ∘ productLeft n n))
    (hb : b ∈ rawTupleFibre (z ∘ productRight n n)) :
    productTuple a b ∈ restrictLiftToRV A D ↔ productTuple a b ∈ A := by
  change (productTuple a b ∈ A ∧ iRv ∘ productTuple a b ∈ D) ↔ _
  rw [productTuple_rv_of_rawTupleFibre ha hb, and_iff_left hz]

private theorem mem_rawLiftDomain_restrict_iff
    {A D : Set (Fin (n + n) → M)} {z : Fin (n + n) → M} (hz : ∀ i, iRV (z i)) :
    z ∈ rawLiftDomain (restrictLiftToRV A D) ↔ z ∈ D ∧ z ∈ rawLiftDomain A := by
  have hiff (hD : z ∈ D) :
      z ∈ rawLiftDomain (restrictLiftToRV A D) ↔ z ∈ rawLiftDomain A := by
    constructor
    · intro h
      exact ⟨fun a ha => (existsUnique_congr (fun b => and_congr_right (fun hb =>
        restrictLiftToRV_agrees hD ha hb))).mp (h.1 a ha),
        fun b hb => (existsUnique_congr (fun a => and_congr_right (fun ha =>
          restrictLiftToRV_agrees hD ha hb))).mp (h.2 b hb)⟩
    · intro h
      exact ⟨fun a ha => (existsUnique_congr (fun b => and_congr_right (fun hb =>
        restrictLiftToRV_agrees hD ha hb))).mpr (h.1 a ha),
        fun b hb => (existsUnique_congr (fun a => and_congr_right (fun ha =>
          restrictLiftToRV_agrees hD ha hb))).mpr (h.2 b hb)⟩
  constructor
  · intro h
    obtain ⟨a, ha⟩ := rawTupleFibre_nonempty_of_sorted (z ∘ productLeft n n)
      (fun i => hz (productLeft n n i))
    obtain ⟨b, ⟨hb, hab⟩, _⟩ := h.1 a ha
    have hD : z ∈ D := productTuple_rv_of_rawTupleFibre ha hb ▸ hab.2
    exact ⟨hD, (hiff hD).mp h⟩
  · exact fun ⟨hD, h⟩ => (hiff hD).mpr h

/-- A finite definable cover by good local lift domains yields a
definable graph that equals one good local graph on each RV pair. The
property of the local graphs is carried by the chosen domain. -/
theorem exists_gluedLift_on_good_domains
    {κ : Cardinal} (hs : Saturated M κ) (S T : Set M) (hST : S ⊆ T)
    (hsmall : Cardinal.mk T < κ) (C : Set (Fin (n + n) → M))
    (hC : T.Definable LRV C) (hRV : ∀ z ∈ C, ∀ i, iRV (z i))
    (Good : (Fin (n + n) → M) → Set (Fin (n + n) → M) → Prop)
    (hloc : ∀ z ∈ C, ∃ A D : Set (Fin (n + n) → M),
      S.Definable LRV A ∧ S.Definable LRV D ∧ z ∈ D ∧ D ⊆ rawLiftDomain A ∧
      ∀ w ∈ D, Good w A) :
    ∃ F : Set (Fin (n + n) → M), S.Definable LRV F ∧ C ⊆ rawLiftDomain F ∧
      ∀ z ∈ C, ∃ A, Good z A ∧ ∀ a ∈ rawTupleFibre (z ∘ productLeft n n),
        ∀ b ∈ rawTupleFibre (z ∘ productRight n n),
          (productTuple a b ∈ F ↔ productTuple a b ∈ A) := by
  classical
  let V := {p : Set (Fin (n + n) → M) × Set (Fin (n + n) → M) //
    S.Definable LRV p.1 ∧ S.Definable LRV p.2 ∧ p.2 ⊆ rawLiftDomain p.1 ∧
      ∀ w ∈ p.2, Good w p.1}
  let D (p : V) := p.val.2
  let domains := Set.range D
  have hcover : ∀ z ∈ C, ∃ d ∈ domains, z ∈ d := by
    intro z hz
    obtain ⟨A, D, hA, hD, hzD, hsub, hgood⟩ := hloc z hz
    exact ⟨D, ⟨⟨(A, D), hA, hD, hsub, hgood⟩, rfl⟩, hzD⟩
  obtain ⟨J, hJ, hsub, hJcov⟩ := hs.definable_finite_subcover_tuple T hsmall C hC domains
    (by rintro _ ⟨p, rfl⟩; exact p.property.2.1.mono hST) hcover
  letI : Fintype J := hJ.fintype
  let e := (Fintype.equivFin J).symm
  choose p hp using fun i => hsub (e i).property
  let A (i : Fin (Fintype.card J)) := restrictLiftToRV (p i).val.1 (p i).val.2
  have ha (i : Fin (Fintype.card J)) : S.Definable LRV (A i) :=
    restrictLiftToRV_definable S (p i).property.1 (p i).property.2.1
  have hhas (z : Fin (n + n) → M) (hz : z ∈ C) : ∃ i, z ∈ rawLiftDomain (A i) := by
    obtain ⟨d, hd, hzD⟩ := hJcov z hz
    obtain ⟨i, hi⟩ := e.surjective (⟨d, hd⟩ : J)
    have hh : z ∈ (p i).val.2 := by
      change z ∈ D (p i)
      rw [hp, hi]
      exact hzD
    exact ⟨i, (mem_rawLiftDomain_restrict_iff (hRV z hz)).mpr
      ⟨hh, (p i).property.2.2.1 hh⟩⟩
  refine ⟨gluedLift A, gluedLift_definable S A ha,
    fun z hz => gluedLift_good A (hhas z hz), fun z hz => ?_⟩
  let I := Finset.univ.filter (fun i => z ∈ rawLiftDomain (A i))
  have hI : I.Nonempty := by
    obtain ⟨i, hi⟩ := hhas z hz
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := I.min' hI
  have hi : z ∈ firstLiftPiece A i := by
    refine ⟨(Finset.mem_filter.mp (I.min'_mem hI)).2, fun j hji hj => ?_⟩
    exact (not_le_of_gt hji) (I.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
  have hDi := ((mem_rawLiftDomain_restrict_iff (hRV z hz)).mp hi.1).1
  refine ⟨(p i).val.1, (p i).property.2.2.2 z hDi, fun a ha b hb => ?_⟩
  change (∃ j, productTuple a b ∈ A j ∧ iRv ∘ productTuple a b ∈ firstLiftPiece A j) ↔ _
  rw [productTuple_rv_of_rawTupleFibre ha hb]
  constructor
  · rintro ⟨j, h, hj⟩
    have he : j = i := by
      rcases lt_trichotomy j i with h | h | h
      · exact (hi.2 j h hj.1).elim
      · exact h
      · exact (hj.2 i h hi.1).elim
    subst j
    exact (restrictLiftToRV_agrees hDi ha hb).mp h
  · intro h
    exact ⟨i, (restrictLiftToRV_agrees hDi ha hb).mpr h, hi⟩

end SpecialTransformations.Section9
