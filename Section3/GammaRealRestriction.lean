module

public import Section3.GammaParameters

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Combine an imaginary-parameter relation with a real-base definable
relation, after projecting the real output coordinates. -/
def Relation.interRealPreimage {S : Set M} {k n m : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (sm : Fin m → SortTag) (G : Set (Fin m → M))
    (hG : SpecialTransformations.Section3.DefinableOver S sm G) (π : Fin n → Fin m) :
    Relation S k m sm where
  carrier := {p | (p.1,p.2 ∘ π) ∈ Q.carrier ∧ p.2 ∈ G}
  definable := by
    have hg := (definableOver_iff_normalized_raw S sm G).mp hG
    have hq := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      (Fin k ⊕ Fin n) (Fin k ⊕ Fin m) (Sum.map id π) _ Q.definable
    have hg' := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      (Fin m) (Fin k ⊕ Fin m) Sum.inr G hg.1
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    convert hq.inter hg' using 1
    ext z
    rfl
  proper := by
    intro p hp
    exact ⟨(Q.proper _ hp.1).1,((definableOver_iff_normalized_raw S sm G).mp hG).2 p.2 hp.2⟩
  invariant := by
    intro t u htu b
    exact and_congr (Q.invariant t u htu (b ∘ π)) Iff.rfl

theorem DefinableWith.inter_real_preimage {S : Set M} {k n m : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : DefinableWith S γ sn A) (sm : Fin m → SortTag) (G : Set (Fin m → M))
    (hG : SpecialTransformations.Section3.DefinableOver S sm G) (π : Fin n → Fin m) :
    DefinableWith S γ sm {z | z ∘ π ∈ A ∧ z ∈ G} := by
  obtain ⟨Q,hQA⟩ := hA
  refine ⟨Q.interRealPreimage sm G hG π,?_⟩
  ext z
  change (z ∘ π ∈ Q.fibre γ ∧ z ∈ G) ↔ (z ∘ π ∈ A ∧ z ∈ G)
  rw [hQA]

theorem DefinableOverBase.inter_real_preimage {B : Base (M := M)} {n m : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A)
    (sm : Fin m → SortTag) (G : Set (Fin m → M))
    (hG : SpecialTransformations.Section3.DefinableOver B.real sm G) (π : Fin n → Fin m) :
    DefinableOverBase B sm {z | z ∘ π ∈ A ∧ z ∈ G} := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  exact ⟨k,γ,hγ,hA.inter_real_preimage sm G hG π⟩

end SpecialTransformations.Section3.GammaParameters
