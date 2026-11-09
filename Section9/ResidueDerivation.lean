import Section9.GaussEvaluation

/-! Reduction of a valuation-bounded derivation. The bound preserves the
maximal ideal, so the induced map is a derivation over the residue field
of the coefficient subfield. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

namespace SpecialTransformations.Section9

variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G]

private theorem residue_eq_iff_value_sub_lt (v : Valuation K G) (a b : v.valuationSubring) :
    residue v.valuationSubring a = residue v.valuationSubring b ↔ v ((a : K) - (b : K)) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  rfl

/-- A valuation-bounded derivation reduces to the corresponding
derivation of the residue extension. -/
theorem exists_residue_derivation
    (v : Valuation K G) (E : Subfield K) (D : Derivation E K K)
    (hD : ∀ x : K, v (D x) ≤ v x) :
    let A := (v.comap E.subtype).valuationSubring
    let B := v.valuationSubring
    letI : Algebra (ResidueField A) (ResidueField B) := (residueFieldInclusion v E).toAlgebra
    ∃ d : Derivation (ResidueField A) (ResidueField B) (ResidueField B),
      ∀ x : B, d (residue B x) = residue B ⟨D (x : K), (hD x).trans x.property⟩ := by
  classical
  let A := (v.comap E.subtype).valuationSubring
  let B := v.valuationSubring
  let I : A →+* B := valuationRingInclusion v E
  let j := residueFieldInclusion v E
  letI : Algebra (ResidueField A) (ResidueField B) := j.toAlgebra
  let D' (a : B) : B := ⟨D (a : K), (hD a).trans a.property⟩
  let rep (z : ResidueField B) : B := Classical.choose (residue_surjective (R := B) z)
  have hrep (z : ResidueField B) : residue B (rep z) = z :=
    Classical.choose_spec (residue_surjective (R := B) z)
  let d (z : ResidueField B) : ResidueField B := residue B (D' (rep z))
  have hd (a : B) : d (residue B a) = residue B (D' a) := by
    apply (residue_eq_iff_value_sub_lt v _ _).mpr
    change v (D (rep (residue B a) : K) - D (a : K)) < 1
    rw [← map_sub]
    exact (hD _).trans_lt ((residue_eq_iff_value_sub_lt v _ _).mp (hrep (residue B a)))
  have hDa (a b : B) : D' (a + b) = D' a + D' b := Subtype.ext (D.map_add _ _)
  have hDm (a b : B) : D' (a * b) = a * D' b + b * D' a := by
    apply Subtype.ext
    exact D.leibniz _ _
  have hDc (a : A) : D' (I a) = 0 := Subtype.ext (D.map_algebraMap a.val)
  have hD1 : D' 1 = 0 := Subtype.ext D.map_one_eq_zero
  let d' : Derivation (ResidueField A) (ResidueField B) (ResidueField B) :=
    { toFun := d
      map_add' := by
        intro a b
        rw [← hrep a, ← hrep b, ← map_add, hd, hd, hd, hDa, map_add]
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := residue_surjective (R := A) c
        rw [← hrep x, RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
        change d (j (residue A a) * residue B (rep x)) =
          j (residue A a) * d (residue B (rep x))
        rw [show j (residue A a) = residue B (I a) from ResidueField.map_residue I a,
          ← map_mul, hd, hd, hDm, hDc, mul_zero, add_zero, map_mul]
      map_one_eq_zero' := by
        change d 1 = 0
        rw [← (residue B).map_one, hd, hD1, map_zero]
      leibniz' := by
        intro a b
        change d (a * b) = a * d b + b * d a
        rw [← hrep a, ← hrep b, ← map_mul, hd, hd, hd, hDm, map_add, map_mul, map_mul] }
  exact ⟨d', hd⟩

end SpecialTransformations.Section9
