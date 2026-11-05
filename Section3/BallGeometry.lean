import VFValued
import CanonicalRV

/-!
# Definitions 2.6 and Notation 2.9

Radii have the paper's order: `OrderDual Γ` reverses Mathlib's multiplicative
valuation order, so valuation zero is radius infinity. `WithBot` adds radius
minus infinity for the whole field. The open-disc-at-infinity convention is
explicit and is distinct from the strict inequality at an ordinary radius.
There is one absorbing RV element, inherited from the released language.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section3.Balls

variable {K : Type} [Field K] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

abbrev Radius (Γ : Type) [LinearOrderedCommGroupWithZero Γ] := WithBot (OrderDual Γ)

def closedDisc (v : Valuation K Γ) (a : K) : Radius Γ → Set K
  | ⊥ => Set.univ
  | (γ : OrderDual Γ) => {x | v (x - a) ≤ (OrderDual.ofDual γ)}

def openDisc (v : Valuation K Γ) (a : K) : Radius Γ → Set K
  | ⊥ => Set.univ
  | (γ : OrderDual Γ) => if (OrderDual.ofDual γ) = 0 then {a} else {x | v (x - a) < (OrderDual.ofDual γ)}

@[simp] theorem closedDisc_bottom (v : Valuation K Γ) (a : K) :
    closedDisc v a ⊥ = Set.univ := rfl

@[simp] theorem openDisc_bottom (v : Valuation K Γ) (a : K) :
    openDisc v a ⊥ = Set.univ := rfl

@[simp] theorem closedDisc_infinity (v : Valuation K Γ) (a : K) :
    closedDisc v a (↑(0 : OrderDual Γ)) = {a} := by
  ext x
  change v (x - a) ≤ (0 : Γ) ↔ x = a
  rw [le_zero_iff, map_eq_zero, sub_eq_zero]

@[simp] theorem openDisc_infinity (v : Valuation K Γ) (a : K) :
    openDisc v a (↑(0 : OrderDual Γ)) = {a} := by
  simp [openDisc]

theorem centre_mem_closedDisc (v : Valuation K Γ) (a : K) (r : Radius Γ) :
    a ∈ closedDisc v a r := by
  cases r with
  | none => trivial
  | some γ =>
    change v (a - a) ≤ OrderDual.ofDual γ
    rw [sub_self, map_zero]
    exact zero_le

theorem centre_mem_openDisc (v : Valuation K Γ) (a : K) (r : Radius Γ) :
    a ∈ openDisc v a r := by
  cases r with
  | none => trivial
  | some γ =>
    by_cases hγ : (OrderDual.ofDual γ) = 0
    · simp [openDisc, hγ]
    · change a ∈ (if OrderDual.ofDual γ = 0 then {a} else {x | v (x - a) < OrderDual.ofDual γ})
      rw [if_neg hγ]
      change v (a - a) < OrderDual.ofDual γ
      rw [sub_self, map_zero]
      exact pos_iff_ne_zero.mpr hγ

/-- The extra RV coordinates of a polydisc are fixed, as in Definition 2.6. -/
def polydisc {R : Type} {n m : ℕ} (B : Fin n → Set K) (t : Fin m → R) :
    Set ((Fin n → K) × (Fin m → R)) := {p | (∀ i, p.1 i ∈ B i) ∧ p.2 = t}

def closedPolydisc (v : Valuation K Γ) {n : ℕ} (a : Fin n → K)
    (r : Fin n → Radius Γ) : Set (Fin n → K) := {x | ∀ i, x i ∈ closedDisc v (a i) (r i)}

def openPolydisc (v : Valuation K Γ) {n : ℕ} (a : Fin n → K)
    (r : Fin n → Radius Γ) : Set (Fin n → K) := {x | ∀ i, x i ∈ openDisc v (a i) (r i)}

/-- Minimum in the paper's radius order, including infinity for zero coordinates. -/
noncomputable def polydiscRadius {n : ℕ} (r : Fin n → Radius Γ) : Radius Γ :=
  Finset.univ.inf r

@[simp] theorem closedPolydisc_infinity (v : Valuation K Γ) {n : ℕ} (a : Fin n → K) :
    closedPolydisc v a (fun _ => ↑(0 : OrderDual Γ)) = {a} := by
  ext x
  simp only [closedPolydisc, Set.mem_ofPred_eq, closedDisc_infinity, Set.mem_singleton_iff]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

@[simp] theorem openPolydisc_infinity (v : Valuation K Γ) {n : ℕ} (a : Fin n → K) :
    openPolydisc v a (fun _ => ↑(0 : OrderDual Γ)) = {a} := by
  ext x
  simp only [openPolydisc, Set.mem_ofPred_eq, openDisc_infinity, Set.mem_singleton_iff]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

section Encoded

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev VF (M : Type) [LRV.Structure M] := VFType (M := M)
abbrev RV (M : Type) [LRV.Structure M] := {t : M // iRV t}

def rvFibre (t : RV M) : Set (VF M) := {x | iRv x.val = t.val}

def tupleRV {n : ℕ} (x : Fin n → VF M) : Fin n → RV M :=
  fun i => ⟨iRv (x i).val, rv_mem hM (x i).property⟩

def rvPolydisc {n m : ℕ} (t : Fin n → RV M) (s : Fin m → RV M) :=
  polydisc (fun i => rvFibre (t i)) s

def Degenerate {n : ℕ} (t : Fin n → RV M) : Prop := ∃ i, (t i).val = iRVZero

theorem rvFibre_zero (t : RV M) (ht : t.val = iRVZero) :
    rvFibre t = {(0 : VF M)} := by
  ext x
  simp only [rvFibre, Set.mem_ofPred_eq, Set.mem_singleton_iff, ht]
  exact CanonicalRV.encodedRv_zero_iff x

theorem rvFibre_eq_openDisc (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (a : VF M) (ha : a ≠ 0) :
    rvFibre (CanonicalRV.encodedRv a) =
      openDisc v a (↑(OrderDual.toDual (v a))) := by
  have hva : v a ≠ 0 := (map_ne_zero v).mpr ha
  ext x
  simp only [rvFibre, Set.mem_ofPred_eq, CanonicalRV.encodedRv, openDisc]
  change iRv x.val = iRv a.val ↔ x ∈ (if v a = 0 then {a} else {x | v (x - a) < v a})
  rw [if_neg hva]
  rw [CanonicalRV.encoded_eq_iff_close x.property a.property
    (fun h => ha (Subtype.ext h))]
  change (¬ VFValued.predV a (x - a)) ↔ v (x - a) < v a
  rw [hv, not_le]

end Encoded
end SpecialTransformations.Section3.Balls
