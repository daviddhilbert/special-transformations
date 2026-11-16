module

public import Section4.VFDimension
public import Section4.RVDimension

@[expose] public section

/-! The dimension in the exceptional-set condition is the dimension of
the indicated sort. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def AlmostEverywhereVF (Δ : Space LRV M) {Q : Space LRV M} (A : DefSet Q S)
    (P : Q.Carrier → Prop) : Prop :=
  ∃ B : DefSet Q S, B.carrier ⊆ A.carrier ∧ vfDim Δ B < vfDim Δ A ∧
    ∀ x ∈ A.carrier \ B.carrier, P x

def AlmostEverywhereRV {m : ℕ} (A : DefSet (rawRVSpace (M := M) m) S)
    (P : (rawRVSpace (M := M) m).Carrier → Prop) : Prop :=
  ∃ B : DefSet (rawRVSpace (M := M) m) S, B.carrier ⊆ A.carrier ∧ rvDim B < rvDim A ∧
    ∀ x ∈ A.carrier \ B.carrier, P x

end SpecialTransformations.Section8
