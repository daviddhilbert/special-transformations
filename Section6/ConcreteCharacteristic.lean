import Section6.ConcreteLogic
import Section6.HenselSchemeSemantics

/-! Field operations, characteristic zero, and canonical sorting for the concrete model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)
local instance characteristicStructure : LRV.Structure (Carrier v) := nativeStructure v

def fieldInterpretation : HenselianTheory.FieldInterpretation (M := Carrier v) v where
  pack := Sum.inl
  injective := Sum.inl_injective
  sort z := ⟨fun h => by
    obtain ⟨x, hx⟩ := of_vf v z h
    exact ⟨x, hx.symm⟩, by rintro ⟨x, rfl⟩; exact vf_inl v x⟩
  zero := (vfZero_eq v).symm
  one := (vfOne_eq v).symm
  add x y := (vfAdd_eq v x y).symm
  neg x := (vfNeg_eq v x).symm
  mul x y := (vfMul_eq v x y).symm
  rvOne := by
    rw [rvMap_eq, rvOne_eq]
    simp [RVCalc.rv, Units.mk0_one]
  compare x y := by rw [rvMap_eq, rvMap_eq, le_inr, RVCalc.vrv_rv, RVCalc.vrv_rv]

theorem charZeroVF_realize [CharZero K] (k : ℕ) : Carrier v ⊨ Axioms.charZeroVF k := by
  change ¬ (pEq (tVFNumeral (k + 1) : Tm 0) tVFZero).Realize
    (@default (Empty → Carrier v) Unique.instInhabited)
    (@default (Fin 0 → Carrier v) Unique.instInhabited)
  rw [pEq, BoundedFormula.realize_bdEqual, HenselianTheory.realize_numeral (fieldInterpretation v),
    realize_tVFZero, vfZero_eq]
  change (Sum.inl ((k + 1 : ℕ) : K) : Carrier v) ≠ Sum.inl 0
  exact fun h => Nat.succ_ne_zero k (Nat.cast_eq_zero.mp (Sum.inl.inj h))

theorem residueCharZero_realize [CharZero (ConcreteRV.Residue v)] {p : ℕ}
    (hp : p.Prime) : Carrier v ⊨ Axioms.residueCharZero p := by
  change ¬ (HenselianTheory.inMaximalIdeal (tVFNumeral p : Tm 0)).Realize
    (@default (Empty → Carrier v) Unique.instInhabited)
    (@default (Fin 0 → Carrier v) Unique.instInhabited)
  rw [HenselianTheory.realize_inMaximalIdeal (fieldInterpretation v) _ _ _
    (HenselianTheory.realize_numeral (fieldInterpretation v) _ p)]
  let z : v.valuationSubring := p
  have hz : (z : K) = p := map_natCast v.valuationSubring.subtype p
  intro h
  have hsmall : v (z : K) < 1 := hz.symm ▸ h
  have hz0 := (IsLocalRing.residue_eq_zero_iff z).mpr
    ((Valuation.mem_maximalIdeal_iff K v).mpr hsmall)
  rw [show z = (p : v.valuationSubring) from rfl, map_natCast] at hz0
  exact hp.ne_zero (Nat.cast_eq_zero.mp hz0)

theorem model_canonicalNative : Carrier v ⊨ HenselianTheory.canonicalNative := by
  constructor
  intro σ hσ
  rcases hσ with (⟨n, f, rfl⟩ | ⟨n, r, rfl⟩)
  · change Carrier v ⊨ CanonicalTheory.functionAxiom f
    exact (CanonicalTheory.functionAxiom_realize f).mpr ((canonical v).1 f)
  · simp only [HenselianTheory.nativeRelationSort, Sentence.Realize,
      BoundedFormula.realize_alls, BoundedFormula.realize_imp, sortedHyps_realize]
    intro z hz
    change Structure.RelMap (L := LRV) r z at hz
    cases r with
    | memVF => intro i; fin_cases i; exact hz
    | memRV => intro i; fin_cases i; exact hz
    | memUnits => intro i; fin_cases i; exact hz.1
    | rvLe => exact hz.1

end SpecialTransformations.Section6.ConcreteValued
