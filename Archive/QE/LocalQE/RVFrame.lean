import ResidueTranscendentalTransport
import RVValueMap

/-!
Ordinary laws of the prescribed partial RV-map relation, including its action
on all residue units. These laws imply valuation-ring and residue compatibility
for every related pair, so field-map consumers need not assume those separately.
-/

open ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

structure RVFrame (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) (R : RVCalc.RV v → RVCalc.RV w → Prop) : Prop where
  zero : R none none
  mul : ∀ a b a' b', R a a' → R b b' →
    R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b')
  inv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a')
  order : ∀ a b a' b', R a a' → R b b' →
    (RVCalc.vrv v a ≤ RVCalc.vrv v b ↔ RVCalc.vrv w a' ≤ RVCalc.vrv w b')
  unit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
    R (RVCalc.rv v x) (RVCalc.rv w y) ↔
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le

namespace RVFrame

variable {v : Valuation K Γ} {w : Valuation L Δ}
  {ρ : Residue v →+* Residue w} {R : RVCalc.RV v → RVCalc.RV w → Prop}
  (h : RVFrame v w ρ R)

include h

theorem one : R (RVCalc.rv v 1) (RVCalc.rv w 1) := by
  apply (h.unit 1 1 (map_one v) (map_one w)).mpr
  rw [M7.vres_one, M7.vres_one, map_one]

theorem integral {x : K} {y : L} (hxy : R (RVCalc.rv v x) (RVCalc.rv w y))
    (hx : v x ≤ 1) : w y ≤ 1 := by
  have hh := h.order _ _ _ _ hxy h.one
  simp only [RVCalc.vrv_rv, map_one] at hh
  exact hh.mp hx

theorem value_one {x : K} {y : L} (hxy : R (RVCalc.rv v x) (RVCalc.rv w y))
    (hx : v x = 1) : w y = 1 := by
  have hlo := h.order _ _ _ _ hxy h.one
  have hhi := h.order _ _ _ _ h.one hxy
  simp only [RVCalc.vrv_rv, map_one] at hlo hhi
  exact le_antisymm (hlo.mp hx.le) (hhi.mp hx.ge)

theorem small {x : K} {y : L} (hxy : R (RVCalc.rv v x) (RVCalc.rv w y))
    (hx : v x < 1) : w y < 1 := by
  have hlo := h.order _ _ _ _ hxy h.one
  have hhi := h.order _ _ _ _ h.one hxy
  simp only [RVCalc.vrv_rv, map_one] at hlo hhi
  rw [lt_iff_le_not_ge] at hx ⊢
  exact ⟨hlo.mp hx.1, fun h' => hx.2 (hhi.mpr h')⟩

theorem residue {x : K} {y : L} (hxy : R (RVCalc.rv v x) (RVCalc.rv w y))
    (hx : v x ≤ 1) (hy : w y ≤ 1) :
    ρ (M7.vres v x hx) = M7.vres w y hy := by
  by_cases hx1 : v x = 1
  · exact (h.unit x y hx1 (h.value_one hxy hx1)).mp hxy
  · have hlt : v x < 1 := lt_of_le_of_ne hx hx1
    have hlt' : w y < 1 := h.small hxy hlt
    rw [(M7.vres_eq_zero_iff v _ hx).mpr hlt,
      (M7.vres_eq_zero_iff w _ hy).mpr hlt', map_zero]

end RVFrame

#print axioms RVFrame.one
#print axioms RVFrame.integral
#print axioms RVFrame.value_one
#print axioms RVFrame.small
#print axioms RVFrame.residue
