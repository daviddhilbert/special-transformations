module

public import Section4.ResidueCoefficientContext

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {ι : Type}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- The parameter-controlled version of the fixed-coefficient form. Its
residue function uses exactly the displayed actual coefficient subfield. -/
def ScaledOver (C : CoefficientContext M)
    (f : (ι → ModelResidue M) → CanonicalRV.RVSort M) : Prop :=
  ∃ c ∈ C.coefficients, ∃ g : (ι → ModelResidue M) → ModelResidue M,
    Relative.Fun C.field g ∧ ∀ x, f x = c * residueRV (g x)

variable {C : CoefficientContext M}

theorem scaledOver_const (c : CanonicalRV.RVSort M) (hc : c ∈ C.coefficients) :
    ScaledOver C (fun _ : ι → ModelResidue M => c) :=
  ⟨c, hc, fun _ => 1, Relative.constant 1 C.field.one_mem, fun _ => by simp⟩

theorem scaledOver_coordinate (c : CanonicalRV.RVSort M) (hc : c ∈ C.coefficients) (i : ι) :
    ScaledOver C (fun x : ι → ModelResidue M => c * residueRV (x i)) :=
  ⟨c, hc, fun x => x i, Relative.projection i, fun _ => rfl⟩

theorem ScaledOver.mul {f g : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : ScaledOver C f) (hg : ScaledOver C g) : ScaledOver C (fun x => f x * g x) := by
  obtain ⟨c, hc, p, hp, hf⟩ := hf
  obtain ⟨d, hd, q, hq, hg⟩ := hg
  refine ⟨c * d, C.mul_mem hc hd, fun x => p x * q x, hp.mul hq, ?_⟩
  intro x
  change f x * g x = c * d * residueRV (p x * q x)
  rw [hf, hg, residueRV_mul]
  ac_rfl

theorem ScaledOver.inv {f : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : ScaledOver C f) : ScaledOver C (fun x => (f x)⁻¹) := by
  obtain ⟨c, hc, p, hp, hf⟩ := hf
  refine ⟨c⁻¹, C.inv_mem hc, fun x => (p x)⁻¹, hp.inv, ?_⟩
  intro x
  change (f x)⁻¹ = c⁻¹ * residueRV ((p x)⁻¹)
  rw [hf, mul_inv, residueRV_inv]

theorem relative_residue_condition (c : CanonicalRV.RVSort M)
    {p : (ι → ModelResidue M) → ModelResidue M} (hp : Relative.Fun C.field p) :
    Relative.Def C.field {x | ValuedModelMap.inK c ∨ p x = 0} :=
  (Relative.proposition C.field (ValuedModelMap.inK c)).union (hp.eq_const 0 C.field.zero_mem)

theorem ScaledOver.addK {f g : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : ScaledOver C f) (hg : ScaledOver C g) :
    ScaledOver C (fun x => ValuedModelMap.addK (f x) (g x)) := by
  obtain ⟨c, hc, p, hp, hf⟩ := hf
  obtain ⟨d, hd, q, hq, hg⟩ := hg
  let P (x : ι → ModelResidue M) :=
    (ValuedModelMap.inK c ∨ p x = 0) ∧ (ValuedModelMap.inK d ∨ q x = 0)
  let r (x : ι → ModelResidue M) :=
    if P x then residuePart c * p x + residuePart d * q x else 0
  have hr : Relative.Fun C.field r :=
    Relative.Fun.ite ((relative_residue_condition c hp).inter (relative_residue_condition d hq))
      (((Relative.constant (residuePart c) (C.residuePart_mem hc)).mul hp).add
        ((Relative.constant (residuePart d) (C.residuePart_mem hd)).mul hq))
      (Relative.constant 0 C.field.zero_mem)
  refine ⟨1, C.one_mem, r, hr, ?_⟩
  intro x
  change ValuedModelMap.addK (f x) (g x) = 1 * residueRV (r x)
  rw [hf, hg, one_mul]
  by_cases hP : P x
  · change ValuedModelMap.addK _ _ = residueRV (if P x then _ else _)
    rw [if_pos hP, residueRV_add, residueRV_part_mul c (p x) hP.1,
      residueRV_part_mul d (q x) hP.2]
  · have hj : ¬ValuedModelMap.inK (c * residueRV (p x)) ∨
        ¬ValuedModelMap.inK (d * residueRV (q x)) := by
      simpa only [inK_mul_residueRV, P, not_and_or] using hP
    rw [ValuedModelMap.addK_junk _ _ hj]
    change (ValuedModelMap.zeroRV : CanonicalRV.RVSort M) = residueRV (if P x then _ else _)
    rw [if_neg hP, residueRV_zero]
    exact RVOperations.zeroRV_eq

theorem ScaledOver.negK {f : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : ScaledOver C f) : ScaledOver C (fun x => ValuedModelMap.negK (f x)) := by
  obtain ⟨c, hc, p, hp, hf⟩ := hf
  let P (x : ι → ModelResidue M) := ValuedModelMap.inK c ∨ p x = 0
  let r (x : ι → ModelResidue M) := if P x then -(residuePart c * p x) else 0
  have hr : Relative.Fun C.field r := Relative.Fun.ite (relative_residue_condition c hp)
    (((Relative.constant (residuePart c) (C.residuePart_mem hc)).mul hp).neg)
    (Relative.constant 0 C.field.zero_mem)
  refine ⟨1, C.one_mem, r, hr, ?_⟩
  intro x
  change ValuedModelMap.negK (f x) = 1 * residueRV (r x)
  rw [hf, one_mul]
  by_cases hP : P x
  · change ValuedModelMap.negK _ = residueRV (if P x then _ else _)
    rw [if_pos hP, residueRV_neg, residueRV_part_mul c (p x) hP]
  · have hj : ¬ValuedModelMap.inK (c * residueRV (p x)) := by
      simpa only [inK_mul_residueRV, P] using hP
    rw [ValuedModelMap.negK_junk _ hj]
    change (ValuedModelMap.zeroRV : CanonicalRV.RVSort M) = residueRV (if P x then _ else _)
    rw [if_neg hP, residueRV_zero]
    exact RVOperations.zeroRV_eq

end SpecialTransformations.Section4.ResiduePurity

end
