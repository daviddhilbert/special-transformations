import Section4.RVAlgebraicMatroid
import Section4.RVDimension
import Mathlib.Combinatorics.Matroid.Rank.ENat

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))

def rvTupleERank (S : Set M) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) : ℕ∞ :=
  (rvAlgebraicMatroid hcan hex S).eRk (Set.range t)

def rvTupleRank (S : Set M) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) : ℕ :=
  (rvTupleERank hcan hex S t).toNat

theorem rvParameterNames_range {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    rvParameterNames (Set.range t) = Set.range (rvValues t) := by
  change Subtype.val '' Set.range t = Set.range (Subtype.val ∘ t)
  exact (Set.range_comp Subtype.val t).symm

theorem rvTupleERank_le_arity (S : Set M) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    rvTupleERank hcan hex S t ≤ n := by
  apply ((rvAlgebraicMatroid hcan hex S).eRk_le_encard (Set.range t)).trans
  simpa only [Set.image_univ, Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] using
    Set.encard_image_le t Set.univ

theorem rvTupleRank_le_arity (S : Set M) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    rvTupleRank hcan hex S t ≤ n :=
  ENat.toNat_le_of_le_natCast (rvTupleERank_le_arity hcan hex S t)

theorem rvTupleERank_le_of_algebraic (S : Set M) {n m : ℕ}
    (a : Fin n → CanonicalRV.RVSort M) (b : Fin m → CanonicalRV.RVSort M)
    (hb : ∀ j, AlgebraicAt (S ∪ Set.range (rvValues a)) .rv (b j).val) :
    rvTupleERank hcan hex S b ≤ rvTupleERank hcan hex S a := by
  let N := rvAlgebraicMatroid hcan hex S
  have hsub : Set.range b ⊆ N.closure (Set.range a) := by
    rw [rvAlgebraicMatroid_closure]
    rintro _ ⟨j, rfl⟩
    change AlgebraicAt (S ∪ rvParameterNames (Set.range a)) .rv (b j).val
    simpa only [rvParameterNames_range] using hb j
  exact (N.eRk_mono hsub).trans_eq (N.eRk_closure_eq _)

theorem rvTupleRank_le_of_algebraic (S : Set M) {n m : ℕ}
    (a : Fin n → CanonicalRV.RVSort M) (b : Fin m → CanonicalRV.RVSort M)
    (hb : ∀ j, AlgebraicAt (S ∪ Set.range (rvValues a)) .rv (b j).val) :
    rvTupleRank hcan hex S b ≤ rvTupleRank hcan hex S a :=
  ENat.toNat_le_toNat (rvTupleERank_le_of_algebraic hcan hex S a b hb)
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (rvTupleERank_le_arity hcan hex S a))

/-- A basis consists of original RV coordinates, with length measured by
the rank of genuine sorted algebraic closure. -/
theorem exists_rv_coordinate_basis_independent (S : Set M) {n : ℕ}
    (t : Fin n → CanonicalRV.RVSort M) :
    ∃ v : Fin (rvTupleRank hcan hex S t) → Fin n,
      Function.Injective v ∧
      Function.Injective (t ∘ v) ∧
      (rvAlgebraicMatroid hcan hex S).Indep (Set.range (t ∘ v)) ∧
      ∀ j, AlgebraicAt (S ∪ Set.range (rvValues (t ∘ v))) .rv (t j).val := by
  let N := rvAlgebraicMatroid hcan hex S
  obtain ⟨B, hB⟩ := N.exists_isBasis (Set.range t) (by
    change Set.range t ⊆ Set.univ
    exact Set.subset_univ _)
  have hBfin : B.Finite := (Set.finite_range t).subset hB.subset
  letI : Fintype B := hBfin.fintype
  let d := Fintype.card B
  let e : Fin d ≃ B := (Fintype.equivFin B).symm
  let v : Fin d → Fin n := fun i => Classical.choose (hB.subset (e i).property)
  have hv (i : Fin d) : t (v i) = (e i).val := Classical.choose_spec (hB.subset (e i).property)
  have hrange : Set.range (t ∘ v) = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change t (v i) ∈ B
      rw [hv i]
      exact (e i).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, (hv i).trans (congrArg Subtype.val hi)⟩
  have hvinj : Function.Injective v := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (hv i).symm.trans ((congrArg t hij).trans (hv j))
  have hvaluesinj : Function.Injective (t ∘ v) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (hv i).symm.trans (hij.trans (hv j))
  have hind : N.Indep (Set.range (t ∘ v)) := by
    rw [hrange]
    exact hB.indep
  have hd : d = rvTupleRank hcan hex S t := by
    change d = (N.eRk (Set.range t)).toNat
    rw [← hB.encard_eq_eRk]
    simp only [Set.encard, ENat.card_eq_coe_fintype_card, ENat.toNat_natCast]
    rfl
  have halg (j : Fin n) : AlgebraicAt (S ∪ Set.range (rvValues (t ∘ v))) .rv (t j).val := by
    have h := hB.subset_closure (Set.mem_range_self j)
    rw [rvAlgebraicMatroid_closure] at h
    change AlgebraicAt (S ∪ rvParameterNames B) .rv (t j).val at h
    rw [← hrange] at h
    simpa only [rvParameterNames_range] using h
  exact hd ▸ (show ∃ v : Fin d → Fin n, Function.Injective v ∧
    Function.Injective (t ∘ v) ∧
    N.Indep (Set.range (t ∘ v)) ∧
    ∀ j, AlgebraicAt (S ∪ Set.range (rvValues (t ∘ v))) .rv (t j).val from
      ⟨v, hvinj, hvaluesinj, hind, halg⟩)

theorem exists_rv_coordinate_basis (S : Set M) {n : ℕ}
    (t : Fin n → CanonicalRV.RVSort M) :
    ∃ v : Fin (rvTupleRank hcan hex S t) → Fin n,
      ∀ j, AlgebraicAt (S ∪ Set.range (rvValues (t ∘ v))) .rv (t j).val := by
  obtain ⟨v, _, _, _, hv⟩ := exists_rv_coordinate_basis_independent hcan hex S t
  exact ⟨v, hv⟩

end SpecialTransformations.Section4

end
