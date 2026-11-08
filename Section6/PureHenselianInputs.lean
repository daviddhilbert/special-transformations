import Section6.HenselianRVClosure
import Section6.HenselianInputs

/-! The pure characteristic zero algebraic envelope supplies its own RV
representatives for the henselian closure input. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section6

theorem HenselianInputs.of_pure_algebraic_envelope
    {N C : Type} [sN : LRV.Structure N] [LRV.Structure C]
    [N ⊨ Axioms.ACVF] [C ⊨ Axioms.ACVF]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : N ⊨ Axioms.ACVF00)
    (X : LRV.Substructure C) (Y : LRV.Substructure N)
    (j : @ElementaryEmbedding LRV N C
      (CanonicalStructure.normalize (M := N)) (CanonicalStructure.normalize (M := C)))
    (himage : j '' (Y : Set N) = (X : Set C))
    (v : Valuation (VFType (M := N)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (K : Subfield (VFType (M := N))) [IsGalois K (VFType (M := N))]
    (hK : ∀ a : VFType (M := N), a ∈ K ↔ a.val ∈ Y)
    (hRV : ∀ t ∈ Y, iRV t → ∃ a : K, iRv a.val.val = t)
    (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
    (hEP : HenselianAutomorphismInvariance v K)
    (hsurj : ∀ t : Section5.RV (M := C), t.val ∈ X →
      ∃ a : Section5.VF (M := C), a.val ∈ X ∧ Section5.rv a = t) : HenselianInputs X := by
  refine HenselianInputs.of_envelope Y j himage v hv K hK hRV hH hEP ?_ hsurj
  intro t ht hd
  have hrv (a : VFType (M := N)) (ha : a.val ∈ Y) : iRv a.val ∈ Y :=
    Y.fun_mem Fn.rvMap ![a.val] (by intro i; fin_cases i; exact ha)
  have htY := henselian_rv_dcl_of_algebraic_envelope v hv h00 K (Y : Set N) hK hRV hrv hH hEP t ht hd
  obtain ⟨a, ha⟩ := hRV t htY ht
  have haY := (hK a.val).mp a.property
  refine ⟨a.val, ha, ?_⟩
  letI : LRV.Structure N := @CanonicalStructure.normalize N sN
  exact Set.Definable.singleton_of_mem LRV haY

end SpecialTransformations.Section6
