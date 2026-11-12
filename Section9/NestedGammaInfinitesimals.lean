module

public import Section9.GammaInfinitesimals
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality

@[expose] public section

/-! Enlarge the small coefficient field after choosing each positive
infinitesimal. Closing the enlarged field algebraically makes all
roots of its values available as thresholds at the next step. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Algebra
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section9

private theorem exists_small_algClosedSubfield_extension
    {K : Type} [Field K] [IsAlgClosed K] {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (E : Subfield K) (hE : Cardinal.mk E < κ) (x : K) :
    ∃ H : Subfield K, E ≤ H ∧ x ∈ H ∧ Cardinal.mk H < κ ∧ IsAlgClosed H := by
  let A := IntermediateField.adjoin E ({x} : Set K)
  let B := algebraicClosure A K
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap A B).injective
  letI : IsAlgClosure A B := algebraicClosure.isAlgClosure A K
  have hx : x ∈ A := IntermediateField.subset_adjoin _ _ (Set.mem_singleton x)
  have hA : Cardinal.mk A < κ := by
    apply (IntermediateField.cardinalMk_adjoin_le E ({x} : Set K)).trans_lt
    exact sup_lt_iff.mpr ⟨sup_lt_iff.mpr ⟨hE, (Set.finite_singleton x).lt_aleph0.trans hκ⟩, hκ⟩
  have hB : Cardinal.mk B < κ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max A B).trans_lt (max_lt_iff.mpr ⟨hA, hκ⟩)
  have hBAlg : IsAlgClosed B := IsAlgClosure.isAlgClosed A
  have hAB (y : K) (hy : y ∈ A) : y ∈ B := B.algebraMap_mem (⟨y, hy⟩ : A)
  exact ⟨B.toSubfield, fun y hy => hAB y (A.algebraMap_mem (⟨y, hy⟩ : E)), hAB x hx, hB,
    hBAlg⟩

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
local notation "VF" => VFType (M := M)

theorem exists_nested_positive_infinitesimals
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (w : Valuation VF Γ) (hw : ∀ a b : VF, VFValued.predV a b ↔ w a ≤ w b)
    (E : Subfield VF) [IsAlgClosed E] (hE : Cardinal.mk E < κ) (n : ℕ) :
    ∃ (x : Fin n → VF) (B : Fin n → Subfield VF),
      (∀ j, IsAlgClosed (B j)) ∧ (∀ j, E ≤ B j) ∧ (∀ i j, i < j → x i ∈ B j) ∧
      (∀ i, x i ≠ 0) ∧ (∀ i, w (x i) < 1) ∧
      ∀ j (c : B j), (c : VF) ≠ 0 → w (c : VF) < 1 → w (c : VF) < w (x j) := by
  letI : IsAlgClosed VF := VFAlgClosed.isAlgClosed_vfType
  induction n generalizing E with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i <;> exact i.elim0
  | succ n ih =>
    let name (c : E) : M := c.val.val
    let S := Set.range name
    let T : Set VF := {c | c ∈ E ∧ c ≠ 0 ∧ w c < 1}
    have hS : Cardinal.mk S < κ := Cardinal.mk_range_le.trans_lt hE
    have hz : (0 : VF).val ∈ S := ⟨⟨0, E.zero_mem⟩, rfl⟩
    have ho : (1 : VF).val ∈ S := ⟨⟨1, E.one_mem⟩, rfl⟩
    obtain ⟨x, hx₀, hx, hxt⟩ := exists_value_above_small_thresholds hs S hS hz ho w hw T
      (fun c hc => ⟨⟨c, hc.1⟩, rfl⟩) (fun _ hc => hc.2)
    obtain ⟨H, hEH, hxH, hH, hAlg⟩ := exists_small_algClosedSubfield_extension hκ E hE x
    letI : IsAlgClosed H := hAlg
    obtain ⟨y, B, hB, hHB, hprev, hy₀, hy, hyt⟩ := ih H hH
    refine ⟨Fin.cons x y, Fin.cons E B, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact inferInstanceAs (IsAlgClosed E)
      · exact hB j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact le_rfl
      · exact hEH.trans (hHB j)
    · intro i j hij
      revert i
      refine Fin.cases ?_ (fun j => ?_) j
      · intro i hi
        exact (Fin.not_lt_zero _ hi).elim
      · intro i hi
        revert hi
        refine Fin.cases ?_ (fun i => ?_) i
        · intro _
          exact hHB j hxH
        · intro hi
          exact hprev i j (Fin.succ_lt_succ_iff.mp hi)
    · intro i
      refine Fin.cases hx₀ hy₀ i
    · intro i
      refine Fin.cases hx hy i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro c hc₀ hc
        exact hxt c ⟨c.property, hc₀, hc⟩
      · exact hyt j

end SpecialTransformations.Section9
