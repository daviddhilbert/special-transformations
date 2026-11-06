import Section3.GammaBaseTools

/- Component: GammaRealMap -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Pull a full invariant Gamma relation back along a map definable in
the normalized real structure. Input sorts are guarded explicitly. -/
def Relation.preimageRealMap {S : Set M} {k n m : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (sm : Fin m → SortTag)
    (F : (Fin m → M) → (Fin n → M))
    (hF : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin m) (Fin n) S F) : Relation S k m sm where
  carrier := {p | (p.1,F p.2) ∈ Q.carrier ∧ p.2 ∈ sortedUniverse sm}
  definable := by
    have hQ := Q.definable
    have hs := ((definableOver_iff_normalized_raw S sm _).mp
      (sortedUniverse_definable S sm)).1
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    let G : (Fin k ⊕ Fin m → M) → (Fin k ⊕ Fin n → M) :=
      fun z => Sum.elim (z ∘ Sum.inl) (F (z ∘ Sum.inr))
    have hG : S.DefinableMap LRV G := by
      intro i
      cases i with
      | inl i => exact Set.DefinableFun.proj LRV
      | inr i => exact (hF i).comp (fun _ => Set.DefinableFun.proj LRV)
    exact (hQ.preimage_map hG).inter (hs.preimage_comp Sum.inr)
  proper := fun p hp => ⟨(Q.proper _ hp.1).1,hp.2⟩
  invariant := fun t u htu b => and_congr (Q.invariant t u htu (F b)) Iff.rfl

theorem DefinableWith.preimage_real_map {S : Set M} {k n m : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {sn : Fin n → SortTag}
    {A : Set (Fin n → M)} (hA : DefinableWith S γ sn A)
    (sm : Fin m → SortTag) (F : (Fin m → M) → (Fin n → M))
    (hF : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin m) (Fin n) S F) :
    DefinableWith S γ sm {z | F z ∈ A ∧ z ∈ sortedUniverse sm} := by
  obtain ⟨Q,hQA⟩ := hA
  refine ⟨Q.preimageRealMap sm F hF,?_⟩
  ext z
  change ((F z ∈ Q.fibre γ) ∧ z ∈ sortedUniverse sm) ↔ _
  rw [hQA]
  rfl

theorem DefinableOverBase.preimage_real_map {B : Base (M := M)} {n m : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : DefinableOverBase B sn A) (sm : Fin m → SortTag)
    (F : (Fin m → M) → (Fin n → M))
    (hF : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin m) (Fin n) B.real F) :
    DefinableOverBase B sm {z | F z ∈ A ∧ z ∈ sortedUniverse sm} := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  exact ⟨k,γ,hγ,hA.preimage_real_map sm F hF⟩

end SpecialTransformations.Section3.GammaParameters
