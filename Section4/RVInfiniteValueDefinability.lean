import Section4.RVValueCofiniteness
import Section3.GammaCodeDefinability
import Section3.ClosureBridge

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rawRVValuePart {n : ℕ} (R : Set ((Fin n → M) × M)) (positive : Bool) :
    Set ((Fin (n + 1) → M) × M) :=
  {p | SameScalar p.2 (p.1 (Fin.last n)) ∧
    (if positive then (Fin.init p.1, p.2) ∈ R else (Fin.init p.1, p.2) ∉ R)}

theorem rawRVValuePart_definable {S : Set M} {n : ℕ}
    (R : Set ((Fin n → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R)
    (positive : Bool) : RawClosure.Tuple.RelationDefinable S (rawRVValuePart R positive) := by
  let α := Fin (n + 1) ⊕ Fin 1
  have hr := hR.preimage_comp
    (Sum.elim (fun i : Fin n => (Sum.inl i.castSucc : α)) (fun _ : Fin 1 => Sum.inr 0))
  have hs := (same_scalar_definable (M := M) S).preimage_comp
    (![Sum.inr 0, Sum.inl (Fin.last n)] : Fin 2 → α)
  cases positive
  · exact hs.inter hr.compl
  · exact hs.inter hr

theorem rawRVRow_sorted_definable
    (hcan : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
    (R : Set ((Fin n → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R)
    (p : Fin (n + 1) → M) :
    DefinableAt (S ∪ Set.range p) .rv {x | iRV x ∧ (Fin.init p, x) ∈ R} := by
  let T := S ∪ Set.range p
  let F (z : Fin 1 → M) := Sum.elim (Fin.init p) (fun _ : Fin 1 => z 0)
  have hF : T.DefinableMap LRV F := by
    intro i
    cases i with
    | inl i =>
      change T.DefinableFun LRV (fun _ : Fin 1 → M => p i.castSucc)
      exact LRV.definableFun_const (Fin 1) (Or.inr (Set.mem_range_self i.castSucc))
    | inr i => exact Set.DefinableFun.proj LRV
  have hr := (hR.mono (Set.subset_union_left : S ⊆ T)).preimage_map hF
  exact raw_definable_sorted hcan T _ .rv
    (((definableAt_sort T .rv).raw_definable).inter hr) (fun _ hx => hx.1)

theorem rawRVValuePart_finite_or_cofinite
    (hcan : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {n : ℕ}
    (R : Set ((Fin n → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R)
    (p : Fin (n + 1) → M) (hw : NonzeroRV (p (Fin.last n))) :
    {x | (p, x) ∈ rawRVValuePart R true}.Finite ∨
      {x | (p, x) ∈ rawRVValuePart R false}.Finite := by
  let w : CanonicalRV.RVSort M := ⟨p (Fin.last n), hw.1⟩
  let A : Set M := {x | iRV x ∧ (Fin.init p, x) ∈ R}
  have hA := rawRVRow_sorted_definable hcan R hR p
  rcases rv_value_finite_or_cofinite (S ∪ Set.range p) A hA (Values.vrv w) with hf | hf
  · left
    apply (hf.image Subtype.val).subset
    rintro x ⟨hSame, hx⟩
    refine ⟨⟨x, hSame.1.1⟩, ?_, rfl⟩
    exact ⟨(Values.vrv_eq_iff _ w).mpr ⟨hSame.2.2.1, hSame.2.2.2⟩,
      hSame.1.1, hx⟩
  · right
    apply (hf.image Subtype.val).subset
    rintro x ⟨hSame, hx⟩
    refine ⟨⟨x, hSame.1.1⟩, ?_, rfl⟩
    exact ⟨(Values.vrv_eq_iff _ w).mpr ⟨hSame.2.2.1, hSame.2.2.2⟩,
      fun h => hx h.2⟩

theorem rawRVValuePart_not_both_finite (h00 : M ⊨ Axioms.ACVF00) {n : ℕ}
    (R : Set ((Fin n → M) × M)) (p : Fin (n + 1) → M)
    (hw : NonzeroRV (p (Fin.last n))) :
    ¬ ({x | (p, x) ∈ rawRVValuePart R true}.Finite ∧
      {x | (p, x) ∈ rawRVValuePart R false}.Finite) := by
  rintro ⟨hr, hc⟩
  let w : CanonicalRV.RVSort M := ⟨p (Fin.last n), hw.1⟩
  have hi := Values.infinite_gamma_fibre h00 (Values.gammaOf w hw.2)
  apply hi
  apply ((hr.union hc).preimage Subtype.val_injective.injOn).subset
  intro t ht
  have htz : t.val ≠ iRVZero := by
    intro hz
    exact hw.2 ((Values.vrv_eq_infinity_iff w).mp
      (ht.symm.trans ((Values.vrv_eq_infinity_iff t).mpr hz)))
  have he := (Values.vrv_eq_iff t w).mp ht
  have hSame : SameScalar t.val w.val := ⟨⟨t.property, htz⟩, hw, he.1, he.2⟩
  by_cases hx : (Fin.init p, t.val) ∈ R
  · exact Or.inl ⟨hSame, hx⟩
  · exact Or.inr ⟨hSame, hx⟩

/-- A uniform bound for every finite RV value fibre in an arbitrary
definable family. It follows from the given angular-pattern theorem and
genuine saturation, rather than assuming elimination of infinity. -/
theorem uniform_finite_RV_value_bound
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (R : Set ((Fin n → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R) :
    ∃ N : ℕ, ∀ p : Fin (n + 1) → M, NonzeroRV (p (Fin.last n)) →
      {x | (p, x) ∈ rawRVValuePart R true}.Finite →
      {x | (p, x) ∈ rawRVValuePart R true}.ncard ≤ N := by
  let P : Set (Fin (n + 1) → M) := {p | NonzeroRV (p (Fin.last n))}
  have hP : S.Definable LRV P := (nonzero_rv_definable S).preimage_comp
    (fun _ : Fin 1 => Fin.last n)
  exact uniform_finite_cofinite_bound hs S hsmall P hP
    (rawRVValuePart R true) (rawRVValuePart R false)
    (rawRVValuePart_definable R hR true) (rawRVValuePart_definable R hR false)
    (fun p hp => rawRVValuePart_finite_or_cofinite hcan R hR p hp)
    (fun p hp => rawRVValuePart_not_both_finite h00 R p hp)

/-- Infinite value fibres have a first-order defining relation over the
original S, uniformly in all real parameters and all value representatives. -/
theorem infinite_RV_value_fibres_definable
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (R : Set ((Fin n → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R) :
    S.Definable LRV {p : Fin (n + 1) → M | NonzeroRV (p (Fin.last n)) ∧
      {x | (p, x) ∈ rawRVValuePart R true}.Infinite} := by
  obtain ⟨N, hN⟩ := uniform_finite_RV_value_bound hcan h00 hs hsmall R hR
  have hP := (nonzero_rv_definable (M := M) S).preimage_comp
    (fun _ : Fin 1 => Fin.last n)
  have hCount := RawClosure.Tuple.hasMore_definable S _
    (rawRVValuePart_definable R hR true) N
  convert hP.inter hCount using 1
  ext p
  change (NonzeroRV (p (Fin.last n)) ∧ _) ↔ (NonzeroRV (p (Fin.last n)) ∧ _)
  exact and_congr_right (fun hp => infinite_row_iff_hasMore _ N p (hN p hp))

end SpecialTransformations.Section4

end
