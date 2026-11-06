import Section6.HenselianClosure
import Section6.ElementaryTransfer

/-! Lemma 6.2 for an actual substructure of the ambient model.
The elementary algebraic envelope is the accepted earlier-section input,
with its exact comparison to the original substructure retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6

section NamedBase

variable {L : Language} {C : Type} [L.Structure C]

/-- The literal original-base form of Definition 6.1. The named base S is
kept separate from the carrier X of the substructure. -/
def FunctionallyClosedOver (S X : Set C) : Prop :=
  ∀ (ι κ : Type) [Finite ι] [Finite κ] (A : Set (ι → C)) (f : A → κ → C),
    S.Definable L A → S.Definable L (partialGraph A f) →
    ∀ a : A, (∀ i, a.val i ∈ X) → ∀ j, f a j ∈ X

/-- The parameter-closed form proved by the fixed-field argument implies
the paper's form over every named base contained in the substructure. -/
theorem FunctionallyClosed.over {S X : Set C}
    (hX : FunctionallyClosed (L := L) X) (hSX : S ⊆ X) :
    FunctionallyClosedOver (L := L) S X := by
  intro ι κ _ _ A f hA hf
  exact hX ι κ A f (hA.mono hSX) (hf.mono hSX)

end NamedBase

variable {N M : Type} [sN : LRV.Structure N] [sM : LRV.Structure M]
  [hN : N ⊨ Axioms.ACVF] [hM : M ⊨ Axioms.ACVF]
  {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

/-- Lemma 6.2, using Corollary 3.14's elementary algebraic envelope and
Lemma 3.13's centre theorem as given. There is no assumed Section 6
closure statement. The henselian input is the ordinary valuation-ring
property, together with the explicitly permitted standard uniqueness
theorem. Surjectivity includes the sole absorbing RV element. -/
theorem lemma_6_2
    (X : LRV.Substructure M) (Y : LRV.Substructure N)
    (j : @ElementaryEmbedding LRV N M
      (CanonicalStructure.normalize (M := N)) (CanonicalStructure.normalize (M := M)))
    (himage : j '' (Y : Set N) = (X : Set M))
    (v : Valuation (VFType (M := N)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (K : Subfield (VFType (M := N))) [IsGalois K (VFType (M := N))]
    (hK : ∀ a : VFType (M := N), a ∈ K ↔ a.val ∈ Y)
    (hRV : ∀ t ∈ Y, iRV t → ∃ a : K, iRv a.val.val = t)
    (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
    (hEP : HenselianAutomorphismInvariance v K)
    (hCenters : DefinableRVLifting (Y : Set N)) :
    NormalizedFunctionallyClosed (X : Set M) := by
  have hrv : ∀ a : VFType (M := N), a.val ∈ Y → iRv a.val ∈ Y := by
    intro a ha
    exact Y.fun_mem Fn.rvMap ![a.val] (by intro i; fin_cases i; exact ha)
  have hY := lemma_6_2_in_algebraic_envelope v hv K (Y : Set N) hK hRV hrv hH hEP hCenters
  have hI := @FunctionallyClosed.image LRV N M
    (CanonicalStructure.normalize (M := N)) (CanonicalStructure.normalize (M := M))
    (Y : Set N) hY j
  exact himage ▸ hI

end SpecialTransformations.Section6
