import Section6.HenselianModel
import Section5.Geometry

/-! Package the independent earlier/standard data used by the checked
Lemma 6.2 for a substructure. The constructor contains an actual
henselian valuation ring and an actual elementary algebraic envelope.
It contains no functional-closure, definable-closure or elimination field.
This is not a definition of saturation.
-/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]

inductive HenselianInputs (X : LRV.Substructure C) : Prop
  | of_envelope {N : Type} [sN : LRV.Structure N] [hN : N ⊨ Axioms.ACVF]
      (Y : LRV.Substructure N)
      (j : @ElementaryEmbedding LRV N C
        (CanonicalStructure.normalize (M := N)) (CanonicalStructure.normalize (M := C)))
      (himage : j '' (Y : Set N) = (X : Set C))
      {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
      (v : Valuation (VFType (M := N)) Γ)
      (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
      (K : Subfield (VFType (M := N))) [IsGalois K (VFType (M := N))]
      (hK : ∀ a : VFType (M := N), a ∈ K ↔ a.val ∈ Y)
      (hRV : ∀ t ∈ Y, iRV t → ∃ a : K, iRv a.val.val = t)
      (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
      (hEP : HenselianAutomorphismInvariance v K)
      (hCenters : DefinableRVLifting (Y : Set N))
      (hsurj : ∀ t : Section5.RV (M := C), t.val ∈ X →
        ∃ a : Section5.VF (M := C), a.val ∈ X ∧ Section5.rv a = t) :
      HenselianInputs X

theorem HenselianInputs.dclClosed {X : LRV.Substructure C} (h : HenselianInputs X) :
    NormalizedDclClosed (X : Set C) := by
  cases h with
  | of_envelope Y j himage v hv K hK hRV hH hEP hCenters hsurj =>
    exact @dclClosed_of_functionallyClosed LRV C (CanonicalStructure.normalize (M := C))
      (X : Set C) (lemma_6_2 X Y j himage v hv K hK hRV hH hEP hCenters)

theorem HenselianInputs.rv_surjective {X : LRV.Substructure C} (h : HenselianInputs X) :
    ∀ t : Section5.RV (M := C), t.val ∈ X →
      ∃ a : Section5.VF (M := C), a.val ∈ X ∧ Section5.rv a = t := by
  cases h with
  | of_envelope Y j himage v hv K hK hRV hH hEP hCenters hsurj => exact hsurj

end SpecialTransformations.Section6
