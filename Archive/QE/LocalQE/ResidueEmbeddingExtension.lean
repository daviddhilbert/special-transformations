import ResidueReduct
import VFAlgClosed

/-! The ordinary algebraically closed residue-field extension step.

The two explicit standard-book inputs concern arbitrary valued fields and
arbitrary algebraically closed fields, respectively. Neither mentions the
tagged language, RV graphs, preparation, or the desired QE theorem. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalResidue ResidueTranscendentalTransport

namespace ResidueEmbeddingExtension

/-- **Authorized standard valued-field input:** the residue field of a valuation
on an algebraically closed field is algebraically closed. This is stated in
actual algebraic types; no model-theoretic or RV extension assertion is included.
Reference: Engler–Prestel, *Valued Fields*, algebraically closed valued fields.
No unverified theorem number is asserted here. -/
def EPAlgebraicallyClosedResidue : Prop :=
  ∀ (K Γ : Type) [Field K] [IsAlgClosed K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ), IsAlgClosed (Residue v)

/-- **Authorized standard model-theoretic input:** the saturated embedding
extension corollary of Marker, *Model Theory: An Introduction* (2002),
Theorem 3.2.2 (ACF quantifier elimination, p. 85) and Proposition 4.3.28
(the saturated embedding criterion, p. 148).

Any embedding of a subfield of an algebraically closed field into a sufficiently
saturated algebraically closed field extends to the whole field. The language
is Mathlib's ordinary ring language with its usual compatible interpretations.
An existing subfield embedding already ensures matching characteristics.

Source: https://ebooks.karbust.me/Mathematics/David%20Marker%20-%20Model%20Theory%20(2002)%20%5B978-0-387-22734-4%5D.pdf
-/
def MarkerACFSaturatedEmbeddingExtension : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]
    [FirstOrder.Ring.CompatibleRing K] [FirstOrder.Ring.CompatibleRing L],
    MarkerBridge.SatAt Language.ring L (Order.succ (Cardinal.mk K)) →
    ∀ (A : Subfield K) (σ : A →+* L),
      ∃ ρ : K →+* L, ∀ a : A, ρ a.1 = σ a

section Application

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
  (hw : ∀ a b : VFType (M := N), VFValued.predV a b ↔ w a ≤ w b)

include hv hw

/-- Tagged saturation suffices for the usual full residue-field extension.
The interpreted residue field has cardinality at most that of the source
tagged model, by the proved injective residue encoding. -/
theorem exists_residue_embedding
    (hEP : EPAlgebraicallyClosedResidue)
    (hACF : MarkerACFSaturatedEmbeddingExtension)
    (hSat : MarkerBridge.SatAt LRV N (Order.succ (Cardinal.mk M)))
    (A : Subfield (Residue v)) (σ : A →+* Residue w) :
    ∃ ρ : Residue v →+* Residue w, ∀ a : A, ρ a.1 = σ a := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (VFType (M := N)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (Residue v) := hEP (VFType (M := M)) Γ v
  letI : IsAlgClosed (Residue w) := hEP (VFType (M := N)) Δ w
  letI : FirstOrder.Ring.CompatibleRing (Residue v) :=
    FirstOrder.Ring.compatibleRingOfRing (Residue v)
  letI : FirstOrder.Ring.CompatibleRing (Residue w) :=
    FirstOrder.Ring.compatibleRingOfRing (Residue w)
  have hsize : Cardinal.mk (Residue v) ≤ Cardinal.mk M :=
    Cardinal.mk_le_of_injective (encodeResidue_injective v hv)
  have hSatFull : MarkerBridge.SatAt Language.ring (Residue w)
      (Order.succ (Cardinal.mk M)) := ResidueReduct.satAt_residue w hw hSat
  have hSatSmall : MarkerBridge.SatAt Language.ring (Residue w)
      (Order.succ (Cardinal.mk (Residue v))) := by
    intro B g hB p hp
    exact hSatFull B g (lt_of_lt_of_le hB (Order.succ_le_succ hsize)) p hp
  exact hACF (Residue v) (Residue w) hSatSmall A σ

end Application
end ResidueEmbeddingExtension

#print axioms ResidueEmbeddingExtension.exists_residue_embedding
