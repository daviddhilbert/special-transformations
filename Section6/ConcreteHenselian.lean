import Section6.ConcreteRVAxioms
import Section6.ConcreteCharacteristic
import Section6.HenselianValuationRing

/-! The concrete leading-term model of an ordinary henselian valued field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)
local instance henselianStructure : LRV.Structure (Carrier v) := nativeStructure v

theorem model_canonicalHen00 [CharZero K] [CharZero (ConcreteRV.Residue v)]
    [HenselianLocalRing v.valuationSubring] (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) :
    Carrier v ⊨ HenselianTheory.canonicalHen00 := by
  constructor
  intro σ hσ
  rcases hσ with ((((h | ⟨n, rfl⟩) | ⟨k, rfl⟩) | ⟨p, hp, rfl⟩) | h)
  · exact sentence_realize (model_valuedField v hnt) h
  · exact (HenselianTheory.henselScheme_realize (fieldInterpretation v) n).mpr
      (HenselianTheory.simpleRootLiftAt v n)
  · exact charZeroVF_realize v k
  · exact residueCharZero_realize v hp
  · exact sentence_realize (model_canonicalNative v) h

end SpecialTransformations.Section6.ConcreteValued
