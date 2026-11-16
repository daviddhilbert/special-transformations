module

public import Section4.ResiduePureFunctions
public import Section3.RVOperations

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open ResidueTranscendentalTransport

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev ModelResidue (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] :=
  Residue (Values.presentationValuation (M := M))

def residueRV (x : ModelResidue M) : CanonicalRV.RVSort M :=
  CanonicalResidue.toRV Values.presentationValuation Values.presentation_compatible x

theorem residueRV_injective : Function.Injective (residueRV (M := M)) :=
  CanonicalResidue.toRV_injective Values.presentationValuation Values.presentation_compatible

@[simp] theorem residueRV_zero : residueRV (0 : ModelResidue M) = 0 :=
  (CanonicalResidue.toRV_zero _ _).trans RVOperations.zeroRV_eq

@[simp] theorem residueRV_one : residueRV (1 : ModelResidue M) = 1 :=
  (CanonicalResidue.toRV_one _ _).trans RVOperations.oneRV_eq

@[simp] theorem residueRV_mul (x y : ModelResidue M) :
    residueRV (x * y) = residueRV x * residueRV y :=
  (CanonicalResidue.toRV_mul _ _ x y).trans (RVOperations.mulRV_eq _ _)

def residueRVHom : ModelResidue M →*₀ CanonicalRV.RVSort M where
  toFun := residueRV
  map_zero' := residueRV_zero
  map_one' := residueRV_one
  map_mul' := residueRV_mul

@[simp] theorem residueRV_inv (x : ModelResidue M) : residueRV x⁻¹ = (residueRV x)⁻¹ :=
  map_inv₀ residueRVHom x

theorem residueRV_add (x y : ModelResidue M) :
    residueRV (x + y) = ValuedModelMap.addK (residueRV x) (residueRV y) :=
  CanonicalResidue.toRV_add _ _ x y

theorem residueRV_neg (x : ModelResidue M) :
    residueRV (-x) = ValuedModelMap.negK (residueRV x) :=
  CanonicalResidue.toRV_neg _ _ x

theorem residueRV_inK (x : ModelResidue M) : ValuedModelMap.inK (residueRV x) :=
  (CanonicalResidue.equiv Values.presentationValuation Values.presentation_compatible x).property

theorem exists_residueRV {c : CanonicalRV.RVSort M} (hc : ValuedModelMap.inK c) :
    ∃ a : ModelResidue M, residueRV a = c := by
  obtain ⟨a, ha⟩ := (CanonicalResidue.equiv
    Values.presentationValuation Values.presentation_compatible).surjective ⟨c, hc⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem residueRV_ne_zero (x : ModelResidue M) : residueRV x ≠ 0 ↔ x ≠ 0 := by
  rw [← residueRV_zero, residueRV_injective.ne_iff]

@[simp] theorem residueRV_eq_zero (x : ModelResidue M) : residueRV x = 0 ↔ x = 0 := by
  rw [← residueRV_zero, residueRV_injective.eq_iff]

/-- Multiplication by a nonzero residue element cannot bring a genuinely
nonresidue RV coefficient into the residue field. -/
theorem inK_mul_residueRV (c : CanonicalRV.RVSort M) (x : ModelResidue M) :
    ValuedModelMap.inK (c * residueRV x) ↔ ValuedModelMap.inK c ∨ x = 0 := by
  by_cases hx : x = 0
  · simp only [hx, residueRV_zero, mul_zero, or_true, iff_true]
    exact residueRV_zero (M := M) ▸ residueRV_inK (0 : ModelResidue M)
  · constructor
    · intro hc
      obtain ⟨a, ha⟩ := exists_residueRV hc
      left
      have he : residueRV (a * x⁻¹) = c := by
        rw [residueRV_mul, residueRV_inv, ha, mul_inv_cancel_right₀
          ((residueRV_ne_zero x).mpr hx)]
      exact he ▸ residueRV_inK (a * x⁻¹)
    · rintro (hc | hzero)
      · obtain ⟨a, rfl⟩ := exists_residueRV hc
        rw [← residueRV_mul]
        exact residueRV_inK (a * x)
      · exact (hx hzero).elim

def residuePart (c : CanonicalRV.RVSort M) : ModelResidue M :=
  if hc : ValuedModelMap.inK c then Classical.choose (exists_residueRV hc) else 0

theorem residueRV_part {c : CanonicalRV.RVSort M} (hc : ValuedModelMap.inK c) :
    residueRV (residuePart c) = c := by
  rw [residuePart, dif_pos hc]
  exact Classical.choose_spec (exists_residueRV hc)

theorem residueRV_part_mul (c : CanonicalRV.RVSort M) (x : ModelResidue M)
    (h : ValuedModelMap.inK c ∨ x = 0) :
    residueRV (residuePart c * x) = c * residueRV x := by
  rcases h with hc | rfl
  · rw [residueRV_mul, residueRV_part hc]
  · simp

variable {ι : Type}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- An RV function on residue tuples has one fixed RV coefficient and
a function definable in the pure residue-field language. -/
def Scaled (f : (ι → ModelResidue M) → CanonicalRV.RVSort M) : Prop :=
  ∃ c : CanonicalRV.RVSort M, ∃ g : (ι → ModelResidue M) → ModelResidue M,
    PureFun g ∧ ∀ x, f x = c * residueRV (g x)

theorem scaled_const (c : CanonicalRV.RVSort M) : Scaled (fun _ : ι → ModelResidue M => c) :=
  ⟨c, fun _ => 1, pure_const 1, fun _ => by simp⟩

theorem scaled_coordinate (c : CanonicalRV.RVSort M) (i : ι) :
    Scaled (fun x : ι → ModelResidue M => c * residueRV (x i)) :=
  ⟨c, fun x => x i, pure_proj i, fun _ => rfl⟩

theorem Scaled.mul {f g : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : Scaled f) (hg : Scaled g) : Scaled (fun x => f x * g x) := by
  obtain ⟨c, p, hp, hf⟩ := hf
  obtain ⟨d, q, hq, hg⟩ := hg
  refine ⟨c * d, fun x => p x * q x, hp.mul hq, ?_⟩
  intro x
  change f x * g x = c * d * residueRV (p x * q x)
  rw [hf, hg, residueRV_mul]
  ac_rfl

theorem Scaled.inv {f : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : Scaled f) : Scaled (fun x => (f x)⁻¹) := by
  obtain ⟨c, p, hp, hf⟩ := hf
  refine ⟨c⁻¹, fun x => (p x)⁻¹, hp.inv, ?_⟩
  intro x
  change (f x)⁻¹ = c⁻¹ * residueRV ((p x)⁻¹)
  rw [hf, mul_inv, residueRV_inv]

theorem pure_residue_condition (c : CanonicalRV.RVSort M)
    {p : (ι → ModelResidue M) → ModelResidue M} (hp : PureFun p) :
    PureDef {x | ValuedModelMap.inK c ∨ p x = 0} :=
  (pure_proposition (ValuedModelMap.inK c)).union (hp.eq_const 0)

theorem Scaled.addK {f g : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : Scaled f) (hg : Scaled g) : Scaled (fun x => ValuedModelMap.addK (f x) (g x)) := by
  obtain ⟨c, p, hp, hf⟩ := hf
  obtain ⟨d, q, hq, hg⟩ := hg
  let P (x : ι → ModelResidue M) :=
    (ValuedModelMap.inK c ∨ p x = 0) ∧ (ValuedModelMap.inK d ∨ q x = 0)
  let r (x : ι → ModelResidue M) :=
    if P x then residuePart c * p x + residuePart d * q x else 0
  have hr : PureFun r :=
    PureFun.ite ((pure_residue_condition c hp).inter (pure_residue_condition d hq))
      (((pure_const (residuePart c)).mul hp).add ((pure_const (residuePart d)).mul hq))
      (pure_const 0)
  refine ⟨1, r, hr, ?_⟩
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

theorem Scaled.negK {f : (ι → ModelResidue M) → CanonicalRV.RVSort M}
    (hf : Scaled f) : Scaled (fun x => ValuedModelMap.negK (f x)) := by
  obtain ⟨c, p, hp, hf⟩ := hf
  let P (x : ι → ModelResidue M) := ValuedModelMap.inK c ∨ p x = 0
  let r (x : ι → ModelResidue M) := if P x then -(residuePart c * p x) else 0
  have hr : PureFun r := PureFun.ite (pure_residue_condition c hp)
    (((pure_const (residuePart c)).mul hp).neg) (pure_const 0)
  refine ⟨1, r, hr, ?_⟩
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
