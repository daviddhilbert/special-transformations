module

public import Section6.AngularComponent

@[expose] public section

/-! Residue/value codes for the actual RV quotient. Zero has one RV image;
its value coordinate is ignored. These codes are onto, and RV quantifiers
split into residue and value-group quantifiers without any field witness.
This supplies the binder part of the Denef–Pas interpretation. Atomic
formula translation remains separate from these semantic coding lemmas.
-/

noncomputable section
open Classical

namespace SpecialTransformations.Section6.AngularComponent

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def encode (v : Valuation K Γ) (a : Data v) (r : Residue v) (g : ValueGroup v) : RVCalc.RV v :=
  (splittingWithZero v a).symm
    (if h : r = 0 then none else some (Units.mk0 r h, g))

theorem encode_zero (v : Valuation K Γ) (a : Data v) (g : ValueGroup v) :
    encode v a 0 g = none := by
  simp [encode, splittingWithZero]

theorem encode_ne_zero (v : Valuation K Γ) (a : Data v)
    (r : Residue v) (hr : r ≠ 0) (g : ValueGroup v) :
    encode v a r g = some ((splitting v a).symm (Units.mk0 r hr, g)) := by
  rw [encode, dif_neg hr]
  rfl

theorem encode_surjective (v : Valuation K Γ) (a : Data v) :
    Function.Surjective (fun p : Residue v × ValueGroup v => encode v a p.1 p.2) := by
  intro q
  cases hq : splittingWithZero v a q with
  | none =>
    refine ⟨(0, 1), ?_⟩
    apply (splittingWithZero v a).injective
    change (splittingWithZero v a) (encode v a 0 1) = _
    rw [encode_zero, hq]
    rfl
  | some p =>
    refine ⟨((p.1 : Residue v), p.2), ?_⟩
    apply (splittingWithZero v a).injective
    change (splittingWithZero v a) (encode v a (p.1 : Residue v) p.2) = _
    rw [encode_ne_zero v a _ (Units.ne_zero p.1)]
    change some (splitting v a ((splitting v a).symm (Units.mk0 (p.1 : Residue v) _, p.2))) = _
    rw [MulEquiv.apply_symm_apply, hq]
    congr 2
    exact Units.ext rfl

def residueCoordinate (v : Valuation K Γ) (a : Data v) (q : RVCalc.RV v) : Residue v :=
  match splittingWithZero v a q with
  | none => 0
  | some p => p.1

theorem residueCoordinate_encode (v : Valuation K Γ) (a : Data v)
    (r : Residue v) (g : ValueGroup v) : residueCoordinate v a (encode v a r g) = r := by
  by_cases hr : r = 0
  · simp [residueCoordinate, encode, hr]
  · simp [residueCoordinate, encode, hr]

/-- Equality of codes ignores the value coordinate precisely at zero. -/
theorem encode_eq_encode (v : Valuation K Γ) (a : Data v)
    (r s : Residue v) (g h : ValueGroup v) :
    encode v a r g = encode v a s h ↔ r = s ∧ (r ≠ 0 → g = h) := by
  rw [← (splittingWithZero v a).injective.eq_iff]
  by_cases hr : r = 0 <;> by_cases hs : s = 0 <;>
    simp [encode, hr, hs, Units.ext_iff] <;> aesop

theorem encode_mul (v : Valuation K Γ) (a : Data v)
    (r s : Residue v) (g h : ValueGroup v) :
    RVCalc.rvMul v (encode v a r g) (encode v a s h) = encode v a (r * s) (g * h) := by
  by_cases hr : r = 0
  · subst r
    simp [encode_zero]
  by_cases hs : s = 0
  · subst s
    simp [encode_zero]
  rw [encode_ne_zero v a r hr, encode_ne_zero v a s hs,
    encode_ne_zero v a (r * s) (mul_ne_zero hr hs), RVCalc.rvMul_some, ← map_mul]
  congr 2
  apply Prod.ext
  · exact Units.ext rfl
  · rfl

theorem encode_one (v : Valuation K Γ) (a : Data v) :
    encode v a 1 1 = some 1 := by
  rw [encode_ne_zero v a 1 one_ne_zero]
  congr 1
  apply (splitting v a).injective
  rw [MulEquiv.apply_symm_apply, map_one]
  exact Prod.ext (Units.ext rfl) rfl

/-- The existing RV inverse is totalized at its single zero. -/
theorem encode_inverse (v : Valuation K Γ) (a : Data v)
    (r : Residue v) (g : ValueGroup v) :
    (encode v a r g).map Inv.inv = encode v a r⁻¹ g⁻¹ := by
  by_cases hr : r = 0
  · subst r
    simp [encode_zero]
  rw [encode_ne_zero v a r hr, encode_ne_zero v a r⁻¹ (inv_ne_zero hr)]
  change some (((splitting v a).symm (Units.mk0 r hr, g))⁻¹) = _
  rw [← map_inv]
  congr 1
  apply congrArg (splitting v a).symm
  exact Prod.ext (Units.ext rfl) rfl

/-- A single RV existential becomes two auxiliary existentials. -/
theorem exists_encode (v : Valuation K Γ) (a : Data v) (P : RVCalc.RV v → Prop) :
    (∃ q, P q) ↔ ∃ r : Residue v, ∃ g : ValueGroup v, P (encode v a r g) := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨⟨r, g⟩, rfl⟩ := encode_surjective v a q
    exact ⟨r, g, hq⟩
  · rintro ⟨r, g, hp⟩
    exact ⟨encode v a r g, hp⟩

theorem forall_encode (v : Valuation K Γ) (a : Data v) (P : RVCalc.RV v → Prop) :
    (∀ q, P q) ↔ ∀ r : Residue v, ∀ g : ValueGroup v, P (encode v a r g) := by
  constructor
  · exact fun hall r g => hall _
  · intro hall q
    obtain ⟨⟨r, g⟩, rfl⟩ := encode_surjective v a q
    exact hall r g

end SpecialTransformations.Section6.AngularComponent
