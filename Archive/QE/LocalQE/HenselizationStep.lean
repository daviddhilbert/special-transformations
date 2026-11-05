import ImmediateRVTransport
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian

/-! The authorized henselization quotation, separated from its proved RV
consequence. Only an actual henselization is required to extend a map.
-/

namespace HenselizationStep

open ImmediateRVTransport

/-- Engler--Prestel, Valued Fields, Theorems 5.2.2 and 5.2.5:
henselization inside a fixed algebraic closure, its universal property and
immediacy. This is the specialization to algebraically closed target fields.

The hypothesis is generic valuation theory. It says nothing about QE, LRV
substructure embeddings or a prescribed RV map. In particular it does not
assert that every immediate henselian extension has the universal property.
-/
def EnglerPrestelHenselization : Prop :=
  ∀ (K Γ : Type) [Field K] [IsAlgClosed K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (F : Subfield K),
    ∃ (E : Subfield K) (hI : Immediate v F E),
      HenselianLocalRing ((v.comap E.subtype).valuationSubring) ∧
      ∀ (L Δ : Type) [Field L] [IsAlgClosed L] [LinearOrderedCommGroupWithZero Δ]
        (w : Valuation L Δ) (σ : F →+* L),
        (∀ x y : F, v (x : K) ≤ v (y : K) ↔ w (σ x) ≤ w (σ y)) →
        ∃ τ : E →+* L,
          (∀ x y : E, v (x : K) ≤ v (y : K) ↔ w (τ x) ≤ w (τ y)) ∧
          ∀ a : F, τ ⟨(a : K), hI.base_le a.2⟩ = σ a

/-- The paper's henselization step with its prescribed RV compatibility
proved, rather than included in the quotation. -/
theorem exists_compatible_henselian_extension
    (hEP : EnglerPrestelHenselization)
    {K L Γ Δ : Type} [Field K] [IsAlgClosed K] [Field L] [IsAlgClosed L]
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    (v : Valuation K Γ) (w : Valuation L Δ) (F : Subfield K) (σ : F →+* L)
    (hσ : ∀ x y : F, v (x : K) ≤ v (y : K) ↔ w (σ x) ≤ w (σ y))
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a))) :
    ∃ (E : Subfield K) (hI : Immediate v F E) (τ : E →+* L),
      HenselianLocalRing ((v.comap E.subtype).valuationSubring) ∧
      (∀ x y : E, v (x : K) ≤ v (y : K) ↔ w (τ x) ≤ w (τ y)) ∧
      (∀ a : F, τ ⟨(a : K), hI.base_le a.2⟩ = σ a) ∧
      ∀ x : E, R (RVCalc.rv v (x : K)) (RVCalc.rv w (τ x)) := by
  obtain ⟨E, hI, hH, hU⟩ := hEP K Γ v F
  obtain ⟨τ, hτ, hext⟩ := hU L Δ w σ hσ
  exact ⟨E, hI, τ, hH, hτ, hext,
    relation_of_immediate v w F E hI σ τ hτ hext R hbase⟩

end HenselizationStep

#print axioms HenselizationStep.exists_compatible_henselian_extension
