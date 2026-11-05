import RVInverseObstruction
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Order.WithBot

/-! The finite inverse obstruction as a graded inverse-free RV reduct, with an absorbing zero,
residue addition and negation on grade zero, and zero junk values elsewhere.
This is not yet an ACVF model: the valued-field sort is deliberately absent. -/

namespace RVInverseObstruction
namespace Reduct

noncomputable section
open Classical

abbrev RV := WithZero Graded
abbrev Source := WithZero positiveMonoid

def includeSource : Source →*₀ RV := WithZero.map' positiveMonoid.subtype
def cubeRV : RV →*₀ RV := WithZero.map' cube
def embed : Source →*₀ RV := WithZero.map' positiveCube

theorem embed_eq (x : Source) : embed x = cubeRV (includeSource x) := by
  induction x using WithZero.recZeroCoe <;> rfl

theorem embed_injective : Function.Injective embed :=
  WithZero.map'_injective positiveCube_injective

def inK : RV → Prop
  | none => True
  | some g => g.1 = 1

def coeff : RV → F8
  | none => 0
  | some g => g.2

def lift (a : F8) : RV := if h : a = 0 then 0 else ((1, Units.mk0 a h) : Graded)

@[simp] theorem lift_zero : lift 0 = 0 := by simp [lift]
@[simp] theorem lift_one : lift 1 = 1 := by
  simp only [lift, one_ne_zero, dite_false]
  congr 1
  ext <;> rfl

@[simp] theorem coeff_lift (a : F8) : coeff (lift a) = a := by
  by_cases h : a = 0 <;> simp [lift, h, coeff]

@[simp] theorem inK_lift (a : F8) : inK (lift a) := by
  by_cases h : a = 0 <;> simp [lift, h, inK]

theorem lift_injective : Function.Injective lift := by
  intro a b h
  simpa using congrArg coeff h

@[simp] theorem cubeRV_inK (x : RV) : inK (cubeRV x) ↔ inK x := by
  induction x using WithZero.recZeroCoe <;> rfl

@[simp] theorem cubeRV_lift (a : F8) : cubeRV (lift a) = lift (a ^ 3) := by
  by_cases h : a = 0
  · simp [h]
  · simp only [lift, h, pow_ne_zero 3 h, dite_false, cubeRV, WithZero.map'_coe]
    congr 1
    apply Prod.ext
    · rfl
    · apply Units.ext
      rfl

def kAdd (x y : RV) : RV :=
  if inK x ∧ inK y then lift (coeff x + coeff y) else 0

def kNeg (x : RV) : RV := if inK x then lift (-coeff x) else 0

@[simp] theorem kAdd_lift (a b : F8) : kAdd (lift a) (lift b) = lift (a + b) := by
  simp [kAdd]

@[simp] theorem kNeg_lift (a : F8) : kNeg (lift a) = lift (-a) := by
  simp [kNeg]

@[simp] theorem kAdd_zero_zero : kAdd 0 0 = 0 := by
  simpa using kAdd_lift 0 0
@[simp] theorem kAdd_zero_one : kAdd 0 1 = 1 := by
  simpa using kAdd_lift 0 1
@[simp] theorem kAdd_one_zero : kAdd 1 0 = 1 := by
  simpa using kAdd_lift 1 0
@[simp] theorem kAdd_one_one : kAdd 1 1 = 0 := by
  have htwo : (1 : F8) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharP.cast_eq_zero F8 2
  simpa only [lift_one, htwo, lift_zero] using kAdd_lift 1 1
@[simp] theorem kNeg_zero : kNeg 0 = 0 := by
  simpa using kNeg_lift 0
@[simp] theorem kNeg_one : kNeg 1 = lift (-1) := by
  simpa using kNeg_lift 1

theorem source_inK_cases (x : Source) (hx : inK (includeSource x)) :
    includeSource x = 0 ∨ includeSource x = 1 := by
  induction x using WithZero.recZeroCoe with
  | zero => exact Or.inl rfl
  | coe a =>
    right
    have hz : (a : Graded).1 = 1 := hx
    have ha : (a : Graded) = 1 := by
      rcases a.2 with hpos | h1
      · have : (a : Graded).1.toAdd = 0 := congrArg Multiplicative.toAdd hz
        omega
      · exact h1
    change ((a : Graded) : RV) = 1
    rw [ha, WithZero.coe_one]

theorem kAdd_preserved (x y : Source) :
    cubeRV (kAdd (includeSource x) (includeSource y)) = kAdd (embed x) (embed y) := by
  rw [embed_eq, embed_eq]
  by_cases hx : inK (includeSource x)
  · by_cases hy : inK (includeSource y)
    · rcases source_inK_cases x hx with hx | hx <;>
        rcases source_inK_cases y hy with hy | hy <;>
        rw [hx, hy] <;>
        simp
    · simp [kAdd, hx, hy]
  · simp [kAdd, hx]

theorem kNeg_preserved (x : Source) :
    cubeRV (kNeg (includeSource x)) = kNeg (embed x) := by
  rw [embed_eq]
  by_cases hx : inK (includeSource x)
  · rcases source_inK_cases x hx with hx | hx <;> rw [hx] <;>
      simp <;> congr 1 <;> ring
  · simp [kNeg, hx]

def grade : RV → WithTop ℤ
  | none => ⊤
  | some g => g.1.toAdd

theorem grade_preserved (x : Source) : grade (embed x) = grade (includeSource x) := by
  induction x using WithZero.recZeroCoe <;> rfl

theorem order_preserved (x y : Source) :
    grade (includeSource x) ≤ grade (includeSource y) ↔ grade (embed x) ≤ grade (embed y) := by
  rw [grade_preserved, grade_preserved]

/-- This formula recovers addition of ratios after existentially adjoining inverses. -/
def RatioAdd (t b c : RV) : Prop :=
  ∃ u v : RV, t * u = b ∧ t * v = c ∧ kAdd u 1 = v

theorem ratioAdd_source (t : RV) (a : F8) :
    RatioAdd t (t * lift a) (t * lift (a + 1)) := by
  refine ⟨lift a, lift (a + 1), rfl, rfl, ?_⟩
  simpa only [lift_one] using kAdd_lift a 1

theorem ratioAdd_not_target (t : RV) (ht : t ≠ 0) (a : F8)
    (ha : (a + 1) ^ 3 ≠ a ^ 3 + 1) :
    ¬ RatioAdd (cubeRV t) (cubeRV (t * lift a)) (cubeRV (t * lift (a + 1))) := by
  rintro ⟨u, v, hu, hv, huv⟩
  have ht' : cubeRV t ≠ 0 := by
    intro h
    apply ht
    exact (WithZero.map'_injective cube_injective) (h.trans (map_zero cubeRV).symm)
  rw [map_mul] at hu hv
  have hu' : u = cubeRV (lift a) := mul_left_cancel₀ ht' hu
  have hv' : v = cubeRV (lift (a + 1)) := mul_left_cancel₀ ht' hv
  rw [hu', hv', cubeRV_lift, cubeRV_lift, ← lift_one, kAdd_lift] at huv
  exact ha (lift_injective huv).symm

def uniformizer : RV := ((Multiplicative.ofAdd 1, 1) : Graded)

theorem include_ray (u : F8ˣ) :
    includeSource (ray u : Source) = uniformizer * lift (u : F8) := by
  simp only [includeSource, WithZero.map'_coe, lift, Units.ne_zero, dite_false, uniformizer]
  rw [← WithZero.coe_mul]
  congr 1
  ext <;> simp [uniformizer, ray]

/-- A tuple in the actual source submonoid whose existential ratio-addition
property is destroyed by the injective operation-preserving map. -/
theorem separating_source_tuple :
    ∃ t b c : Source,
      RatioAdd (includeSource t) (includeSource b) (includeSource c) ∧
      ¬ RatioAdd (embed t) (embed b) (embed c) := by
  obtain ⟨a, ha⟩ := exists_cube_add_failure
  have ha0 : a ≠ 0 := by
    intro h
    simpa [h] using ha
  have ha1 : a + 1 ≠ 0 := by
    intro h
    have heq : a = -1 := eq_neg_of_add_eq_zero_left h
    norm_num [heq] at ha
  let u : F8ˣ := Units.mk0 a ha0
  let v : F8ˣ := Units.mk0 (a + 1) ha1
  refine ⟨ray 1, ray u, ray v, ?_, ?_⟩
  · rw [include_ray, include_ray, include_ray]
    simpa [u, v] using ratioAdd_source uniformizer a
  · rw [embed_eq, embed_eq, embed_eq, include_ray, include_ray, include_ray]
    simpa [u, v] using
      ratioAdd_not_target uniformizer (WithZero.coe_ne_zero) a ha

end
end Reduct
end RVInverseObstruction

#print axioms RVInverseObstruction.Reduct.embed_injective
#print axioms RVInverseObstruction.Reduct.kAdd_preserved
#print axioms RVInverseObstruction.Reduct.kNeg_preserved
#print axioms RVInverseObstruction.Reduct.order_preserved
#print axioms RVInverseObstruction.Reduct.ratioAdd_source
#print axioms RVInverseObstruction.Reduct.ratioAdd_not_target
#print axioms RVInverseObstruction.Reduct.separating_source_tuple
