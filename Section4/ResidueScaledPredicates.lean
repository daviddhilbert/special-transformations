module

public import Section4.ResidueScaledFunctions
public import Mathlib.Tactic.Tauto

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {K : Type} [Field K] {ι : Type}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem pure_zero_cases {f : (ι → K) → K} (hf : PureFun f)
    {P Q : (ι → K) → Prop} (hP : PureDef {x | P x}) (hQ : PureDef {x | Q x}) :
    PureDef {x | if f x = 0 then P x else Q x} := by
  have hz := hf.eq_const 0
  convert (hz.inter hP).union (hz.compl.inter hQ) using 1
  ext x
  by_cases hx : f x = 0 <;> simp [hx]

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem Scaled.eq {f g : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : Scaled f) (hg : Scaled g) : PureDef {x | f x = g x} := by
  obtain ⟨c, p, hp, hf⟩ := hf
  obtain ⟨d, q, hq, hg⟩ := hg
  by_cases hc : c = 0
  · by_cases hd : d = 0
    · convert pure_proposition (K := ModelResidue M) (ι := ι) True using 1
      ext x
      simp [hf, hg, hc, hd]
    · convert hq.eq_const 0 using 1
      ext x
      change f x = g x ↔ q x = 0
      rw [hf, hg, hc, zero_mul]
      constructor
      · intro hz
        exact (residueRV_eq_zero _).mp ((mul_eq_zero.mp hz.symm).resolve_left hd)
      · intro hq0
        rw [hq0, residueRV_zero, mul_zero]
  · by_cases hd : d = 0
    · convert hp.eq_const 0 using 1
      ext x
      change f x = g x ↔ p x = 0
      rw [hf, hg, hd, zero_mul]
      simp [hc]
    · let a := c⁻¹ * d
      by_cases ha : ValuedModelMap.inK a
      · let b := residuePart a
        have hbc : c * residueRV b = d := by
          rw [residueRV_part ha]
          dsimp only [a]
          rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
        convert hp.eq ((pure_const b).mul hq) using 1
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
      · convert (hp.eq_const 0).inter (hq.eq_const 0) using 1
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

theorem units_iff_inK_ne_zero (t : CanonicalRV.RVSort M) :
    iUnits t.val ↔ ValuedModelMap.inK t ∧ t ≠ 0 := by
  constructor
  · intro ht
    refine ⟨Or.inl ht, ?_⟩
    intro hz
    exact ValuedModelMap.units_ne_zero ht (by rw [hz, RVOperations.zero_val])
  · rintro ⟨ht, hz⟩
    exact ht.elim id (fun h => (hz (h.trans RVOperations.zeroRV_eq)).elim)

theorem Scaled.units {f : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : Scaled f) : PureDef {x | iUnits (f x).val} := by
  obtain ⟨c, p, hp, hf⟩ := hf
  have h := (pure_proposition (K := ModelResidue M) (ι := ι)
    (ValuedModelMap.inK c ∧ c ≠ 0)).inter (hp.eq_const 0).compl
  convert h using 1
  ext x
  change iUnits (f x).val ↔ (ValuedModelMap.inK c ∧ c ≠ 0) ∧ p x ≠ 0
  rw [hf, units_iff_inK_ne_zero, inK_mul_residueRV, mul_ne_zero_iff, residueRV_ne_zero]
  change ((ValuedModelMap.inK c ∨ p x = 0) ∧ c ≠ 0 ∧ p x ≠ 0) ↔
    (ValuedModelMap.inK c ∧ c ≠ 0) ∧ p x ≠ 0
  tauto

theorem absolute_residue (x : ModelResidue M) :
    RVOperations.absoluteHom (residueRV x) = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · rw [hx, residueRV_zero, map_zero, if_pos rfl]
  · rw [if_neg hx]
    apply (RVOperations.units_iff_absolute_one _ ((residueRV_ne_zero x).mpr hx)).mp
    exact (CanonicalResidue.toRV_units_iff _ _ x).mpr hx

theorem Scaled.le {f g : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : Scaled f) (hg : Scaled g) : PureDef {x | iLe (f x).val (g x).val} := by
  obtain ⟨c, p, hp, hf⟩ := hf
  obtain ⟨d, q, hq, hg⟩ := hg
  let ac := RVOperations.absoluteHom c
  let ad := RVOperations.absoluteHom d
  have h := pure_zero_cases hp
    (pure_zero_cases hq (pure_proposition (0 ≤ (0 * ac))) (pure_proposition (ad ≤ (0 * ac))))
    (pure_zero_cases hq (pure_proposition (0 ≤ ac)) (pure_proposition (ad ≤ ac)))
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
