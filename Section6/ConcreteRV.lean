module

public import CanonicalRV
public import RVKernelResidue

@[expose] public section

/-! The ordinary residue field in the leading-term quotient. The construction
uses the value-one subgroup and applies with or without an angular component. -/

noncomputable section
open Classical
open ResidueTranscendentalTransport RVGroupGraph

namespace SpecialTransformations.Section6.ConcreteRV

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)

abbrev Residue := IsLocalRing.ResidueField v.valuationSubring

def residueCode (r : Residue v) : RVCalc.RV v :=
  if h : r = 0 then none
  else some (((RVKernelResidue.equiv v).symm (Units.mk0 r h)) : RVCalc.RVUnit v)

@[simp] theorem residueCode_zero : residueCode v 0 = none := dif_pos rfl

@[simp] theorem residueCode_one : residueCode v 1 = some 1 := by
  rw [residueCode, dif_neg one_ne_zero, Units.mk0_one, map_one, OneMemClass.coe_one]

theorem residueCode_injective : Function.Injective (residueCode v) := by
  intro r s h
  by_cases hr : r = 0 <;> by_cases hs : s = 0
  · exact hr.trans hs.symm
  · simp [residueCode, hr, hs] at h
  · simp [residueCode, hr, hs] at h
  · rw [residueCode, dif_neg hr, residueCode, dif_neg hs, Option.some.injEq] at h
    exact congrArg Units.val ((RVKernelResidue.equiv v).symm.injective (Subtype.ext h))

@[simp] theorem value_residueCode {r : Residue v} (hr : r ≠ 0) :
    RVCalc.vrv v (residueCode v r) = 1 := by
  rw [residueCode, dif_neg hr, RVCalc.vrv_some]
  exact MonoidHom.mem_ker.mp ((RVKernelResidue.equiv v).symm (Units.mk0 r hr)).property

theorem residueCode_range : Set.range (residueCode v) =
    {q | q = none ∨ RVCalc.vrv v q = 1} := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    rcases eq_or_ne r 0 with rfl | hr
    · exact Or.inl (residueCode_zero v)
    · exact Or.inr (value_residueCode v hr)
  · rintro (rfl | h)
    · exact ⟨0, residueCode_zero v⟩
    · cases q with
      | none => exact ⟨0, residueCode_zero v⟩
      | some q =>
        let z : (RVCalc.vrvUnit v).ker := ⟨q, MonoidHom.mem_ker.mpr h⟩
        let r := RVKernelResidue.equiv v z
        refine ⟨r.val, ?_⟩
        rw [residueCode, dif_neg r.ne_zero]
        congr 1
        have hr : Units.mk0 r.val r.ne_zero = r := Units.ext rfl
        rw [hr]
        exact congrArg Subtype.val ((RVKernelResidue.equiv v).symm_apply_apply z)

theorem residueCode_mul (r s : Residue v) :
    residueCode v (r * s) = RVCalc.rvMul v (residueCode v r) (residueCode v s) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [RVCalc.rvMul]
  rcases eq_or_ne s 0 with rfl | hs
  · rw [mul_zero, residueCode_zero]
    cases residueCode v r <;> rfl
  rw [residueCode, dif_neg (mul_ne_zero hr hs), residueCode, dif_neg hr,
    residueCode, dif_neg hs, RVCalc.rvMul_some]
  have h : Units.mk0 (r * s) (mul_ne_zero hr hs) = Units.mk0 r hr * Units.mk0 s hs :=
    Units.ext rfl
  rw [h, map_mul]
  rfl

theorem residueCode_reduction (x : v.valuationSubring) :
    residueCode v (IsLocalRing.residue v.valuationSubring x) =
      if v (x : K) = 1 then RVCalc.rv v x.val else none := by
  by_cases hx : v (x : K) = 1
  · rw [if_pos hx]
    let z := unitClass v x.val hx
    let r := RVKernelResidue.equiv v z
    have hr : r.val = IsLocalRing.residue v.valuationSubring x :=
      RVKernelResidue.residue_unitClass v x.val hx
    rw [← hr, residueCode, dif_neg r.ne_zero, rv_unitClass v x.val hx]
    have he : Units.mk0 r.val r.ne_zero = r := Units.ext rfl
    rw [he]
    exact congrArg (fun q : (RVCalc.vrvUnit v).ker => some q.val)
      ((RVKernelResidue.equiv v).symm_apply_apply z)
  · rw [if_neg hx]
    have hvx : v (x : K) ≤ 1 := (Valuation.mem_valuationSubring_iff v _).mp x.property
    have hr : IsLocalRing.residue v.valuationSubring x = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
      exact lt_of_le_of_ne hvx hx
    rw [hr, residueCode_zero]

end SpecialTransformations.Section6.ConcreteRV
