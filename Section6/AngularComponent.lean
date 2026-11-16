module

public import ResidueTransportCore
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

/-!
The algebraic splitting used in Corollary 6.5. The source is the actual
leading-term quotient from the pinned dependency. An angular component
is a multiplicative map to the actual residue field, agreeing with
reduction on valuation-one elements. The value group is the image of
the valuation on units, so no surjectivity to an oversized ambient group
is assumed. No henselian or QE conclusion is built into this definition.
-/

noncomputable section
open Classical

namespace SpecialTransformations.Section6.AngularComponent

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

abbrev Residue (v : Valuation K Γ) := IsLocalRing.ResidueField v.valuationSubring

structure Data (v : Valuation K Γ) where
  ac : K →*₀ Residue v
  agrees : ∀ (x : v.valuationSubring), v (x : K) = 1 →
    ac (x : K) = IsLocalRing.residue v.valuationSubring x

def unitValue (v : Valuation K Γ) : Kˣ →* Γˣ :=
  Units.map v.toMonoidWithZeroHom.toMonoidHom

abbrev ValueGroup (v : Valuation K Γ) := (unitValue v).range

def coordinates (v : Valuation K Γ) (a : Data v) :
    Kˣ →* (Residue v)ˣ × ValueGroup v :=
  (Units.map a.ac.toMonoidHom).prod (unitValue v).rangeRestrict

theorem residue_eq_one_iff (v : Valuation K Γ) (x : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring x = 1 ↔ v ((x : K) - 1) < 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue v.valuationSubring), ← map_sub,
    IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  rfl

theorem value_one_of_principal (v : Valuation K Γ) (x : K)
    (h : v (x - 1) < 1) : v x = 1 := by
  have he : x = (x - 1) + 1 := by ring
  rw [he, Valuation.map_add_eq_of_lt_right v (by simpa using h), map_one]

theorem coordinates_kernel (v : Valuation K Γ) (a : Data v) :
    RVCalc.principalUnits v = (coordinates v a).ker := by
  ext u
  change v ((u : K) - 1) < 1 ↔ coordinates v a u = 1
  constructor
  · intro hu
    have hv := value_one_of_principal v (u : K) hu
    have hr : a.ac (u : K) = 1 :=
      (a.agrees ⟨(u : K), by simpa [Valuation.mem_valuationSubring_iff] using hv.le⟩ hv).trans
        ((residue_eq_one_iff v _).mpr hu)
    apply Prod.ext
    · exact Units.ext hr
    · apply Subtype.ext
      exact Units.ext hv
  · intro hu
    have hac : a.ac (u : K) = 1 := congrArg (fun p => (p.1 : Residue v)) hu
    have hv : v (u : K) = 1 := congrArg (fun p => (p.2.val : Γ)) hu
    let x : v.valuationSubring := ⟨(u : K), by simpa [Valuation.mem_valuationSubring_iff] using hv.le⟩
    apply (residue_eq_one_iff v x).mp
    exact (a.agrees x hv).symm.trans hac

theorem residue_lift_value_one (v : Valuation K Γ) (r : (Residue v)ˣ) :
    ∃ x : v.valuationSubring, v (x : K) = 1 ∧
      IsLocalRing.residue v.valuationSubring x = r := by
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (r : Residue v)
  have hle : v (x : K) ≤ 1 := (Valuation.mem_valuationSubring_iff v _).mp x.property
  have hn : ¬ v (x : K) < 1 := by
    intro h
    have hz : IsLocalRing.residue v.valuationSubring x = 0 :=
      (IsLocalRing.residue_eq_zero_iff x).mpr (by
        rw [Valuation.mem_maximalIdeal_iff]
        exact h)
    exact Units.ne_zero r (hx.symm.trans hz)
  have hv : v (x : K) = 1 := le_antisymm hle (le_of_not_gt hn)
  exact ⟨x, hv, hx⟩

theorem coordinates_surjective (v : Valuation K Γ) (a : Data v) :
    Function.Surjective (coordinates v a) := by
  rintro ⟨r, g⟩
  obtain ⟨x, hx⟩ := g.property
  let c : (Residue v)ˣ := r / Units.map a.ac.toMonoidHom x
  obtain ⟨b, hb, hres⟩ := residue_lift_value_one v c
  have hb0 : (b : K) ≠ 0 := by
    intro he
    have hc := hb
    rw [he, map_zero] at hc
    exact zero_ne_one hc
  let y : Kˣ := Units.mk0 (b : K) hb0
  have hay : Units.map a.ac.toMonoidHom y = c := by
    apply Units.ext
    exact (a.agrees b hb).trans hres
  have hνy : unitValue v y = 1 := Units.ext hb
  refine ⟨x * y, ?_⟩
  apply Prod.ext
  · change Units.map a.ac.toMonoidHom (x * y) = r
    rw [map_mul, hay]
    dsimp [c]
    simp [div_eq_mul_inv, mul_left_comm]
  · apply Subtype.ext
    change unitValue v (x * y) = g.val
    rw [map_mul, hνy, mul_one]
    exact hx

/-- The actual nonzero RV quotient splits as residue units times the
actual value group. This proves, rather than assumes, the splitting. -/
def splitting (v : Valuation K Γ) (a : Data v) :
    RVCalc.RVUnit v ≃* (Residue v)ˣ × ValueGroup v :=
  QuotientGroup.liftEquiv (RVCalc.principalUnits v)
    (coordinates_surjective v a) (coordinates_kernel v a)

theorem splitting_mk (v : Valuation K Γ) (a : Data v) (x : Kˣ) :
    splitting v a (QuotientGroup.mk' (RVCalc.principalUnits v) x) =
      (Units.map a.ac.toMonoidHom x, (unitValue v).rangeRestrict x) := rfl

/-- Add exactly the existing absorbing point; no second zero/infinity. -/
def splittingWithZero (v : Valuation K Γ) (a : Data v) :
    RVCalc.RV v ≃ Option ((Residue v)ˣ × ValueGroup v) :=
  Equiv.optionCongr (splitting v a).toEquiv

theorem splittingWithZero_zero (v : Valuation K Γ) (a : Data v) :
    splittingWithZero v a (RVCalc.rv v 0) = none := by
  rw [RVCalc.rv_zero]
  rfl

theorem splittingWithZero_rv (v : Valuation K Γ) (a : Data v) (x : K) (hx : x ≠ 0) :
    splittingWithZero v a (RVCalc.rv v x) =
      some (Units.map a.ac.toMonoidHom (Units.mk0 x hx),
        (unitValue v).rangeRestrict (Units.mk0 x hx)) := by
  rw [RVCalc.rv_of_ne hx]
  rfl

end SpecialTransformations.Section6.AngularComponent
