import Section4.ResidueRelativeScaled
import Section4.ResidueScaledPredicates

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {K : Type} [Field K] {ι : Type}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem relative_zero_cases {E : Subfield K} {f : (ι → K) → K} (hf : Relative.Fun E f)
    {P Q : (ι → K) → Prop} (hP : Relative.Def E {x | P x}) (hQ : Relative.Def E {x | Q x}) :
    Relative.Def E {x | if f x = 0 then P x else Q x} := by
  have hz := hf.eq_const 0 E.zero_mem
  convert (hz.inter hP).union (hz.compl.inter hQ) using 1
  ext x
  by_cases hx : f x = 0 <;> simp [hx]

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {C : CoefficientContext M}

theorem ScaledOver.eq {f g : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : ScaledOver C f) (hg : ScaledOver C g) : Relative.Def C.field {x | f x = g x} := by
  obtain ⟨c, hcC, p, hp, hf⟩ := hf
  obtain ⟨d, hdC, q, hq, hg⟩ := hg
  by_cases hc : c = 0
  · by_cases hd : d = 0
    · convert Relative.proposition (ι := ι) C.field True using 1
      ext x
      simp [hf, hg, hc, hd]
    · convert hq.eq_const 0 C.field.zero_mem using 1
      ext x
      change f x = g x ↔ q x = 0
      rw [hf, hg, hc, zero_mul]
      constructor
      · intro hz
        exact (residueRV_eq_zero _).mp ((mul_eq_zero.mp hz.symm).resolve_left hd)
      · intro hq0
        rw [hq0, residueRV_zero, mul_zero]
  · by_cases hd : d = 0
    · convert hp.eq_const 0 C.field.zero_mem using 1
      ext x
      change f x = g x ↔ p x = 0
      rw [hf, hg, hd, zero_mul]
      simp [hc]
    · let a := c⁻¹ * d
      by_cases ha : ValuedModelMap.inK a
      · let b := residuePart a
        have hb : b ∈ C.field := C.residuePart_mem (C.mul_mem (C.inv_mem hcC) hdC)
        have hbc : c * residueRV b = d := by
          rw [residueRV_part ha]
          dsimp only [a]
          rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
        convert hp.eq ((Relative.constant b hb).mul hq) using 1
        ext x
        change f x = g x ↔ p x = b * q x
        rw [hf, hg]
        constructor
        · intro he
          apply residueRV_injective
          apply mul_left_cancel₀ hc
          rw [residueRV_mul, ← mul_assoc, hbc]
          exact he
        · intro he
          rw [he, residueRV_mul, ← mul_assoc, hbc]
      · convert (hp.eq_const 0 C.field.zero_mem).inter (hq.eq_const 0 C.field.zero_mem) using 1
        ext x
        change f x = g x ↔ p x = 0 ∧ q x = 0
        rw [hf, hg]
        constructor
        · intro he
          have hq0 : q x = 0 := by
            by_contra hq0
            have he' : a * residueRV (q x) = residueRV (p x) := by
              dsimp only [a]
              rw [mul_assoc, ← he, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
            have hK : ValuedModelMap.inK (a * residueRV (q x)) := he'.symm ▸ residueRV_inK (p x)
            exact ((inK_mul_residueRV a (q x)).mp hK).elim ha hq0
          have hz : c * residueRV (p x) = 0 := by
            rw [he, hq0, residueRV_zero, mul_zero]
          have hp0 : p x = 0 := (residueRV_eq_zero _).mp ((mul_eq_zero.mp hz).resolve_left hc)
          exact ⟨hp0, hq0⟩
        · rintro ⟨hp0, hq0⟩
          rw [hp0, hq0, residueRV_zero, mul_zero, mul_zero]

theorem ScaledOver.units {f : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : ScaledOver C f) : Relative.Def C.field {x | iUnits (f x).val} := by
  obtain ⟨c, hc, p, hp, hf⟩ := hf
  have h := (Relative.proposition (ι := ι) C.field
    (ValuedModelMap.inK c ∧ c ≠ 0)).inter (hp.eq_const 0 C.field.zero_mem).compl
  convert h using 1
  ext x
  change iUnits (f x).val ↔ (ValuedModelMap.inK c ∧ c ≠ 0) ∧ p x ≠ 0
  rw [hf, units_iff_inK_ne_zero, inK_mul_residueRV, mul_ne_zero_iff, residueRV_ne_zero]
  change ((ValuedModelMap.inK c ∨ p x = 0) ∧ c ≠ 0 ∧ p x ≠ 0) ↔
    (ValuedModelMap.inK c ∧ c ≠ 0) ∧ p x ≠ 0
  tauto

theorem ScaledOver.le {f g : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : ScaledOver C f) (hg : ScaledOver C g) :
    Relative.Def C.field {x | iLe (f x).val (g x).val} := by
  obtain ⟨c, hc, p, hp, hf⟩ := hf
  obtain ⟨d, hd, q, hq, hg⟩ := hg
  let ac := RVOperations.absoluteHom c
  let ad := RVOperations.absoluteHom d
  have h := relative_zero_cases hp
    (relative_zero_cases hq (Relative.proposition C.field (0 ≤ (0 * ac)))
      (Relative.proposition C.field (ad ≤ (0 * ac))))
    (relative_zero_cases hq (Relative.proposition C.field (0 ≤ ac))
      (Relative.proposition C.field (ad ≤ ac)))
  convert h using 1
  ext x
  have hord := Values.valueEquiv_rv_le Values.presentationValuation Values.presentation_compatible
    (f x) (g x)
  change iLe (f x).val (g x).val ↔
    RVOperations.absoluteHom (g x) ≤ RVOperations.absoluteHom (f x) at hord
  change iLe (f x).val (g x).val ↔
    (if p x = 0 then (if q x = 0 then 0 ≤ 0 * ac else ad ≤ 0 * ac)
      else (if q x = 0 then 0 ≤ ac else ad ≤ ac))
  rw [hord, hf, hg, map_mul, map_mul, absolute_residue, absolute_residue]
  by_cases hp0 : p x = 0 <;> by_cases hq0 : q x = 0 <;>
    simp [hp0, hq0, ac, ad]

end SpecialTransformations.Section4.ResiduePurity

end
