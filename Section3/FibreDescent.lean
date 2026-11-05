import Section3.ClosureBridge

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def tupleRVFibre {n : ℕ} (t : Fin n → M) : Set (Fin n → M) :=
  {a | ∀ i, iVF (a i) ∧ iRv (a i) = t i}

/-- VF-to-RV half of Corollary 3.2, with full tuple arities and explicit
nonemptiness. The proof uses the stronger tuple-family descent theorem;
the fibre inclusion itself is not needed for this implication. -/
theorem corollary_3_2_vf (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) {n : ℕ} (t : Fin n → M)
    (hsmall : Cardinal.mk ↥(S ∪ Set.range t) < κ)
    (A : Set (Fin n → M)) (b : M) (σ : SortTag)
    (hA : DefinableOver (S ∪ Set.range t) (fun _ => .vf) A) (hne : A.Nonempty)
    (_hfibre : A ⊆ tupleRVFibre t)
    (hb : ∀ a ∈ A, AlgebraicAt (S ∪ Set.range a) σ b) :
    AlgebraicAt (S ∪ Set.range t) σ b := by
  apply lemma_3_1 hc hκ hs (S ∪ Set.range t) hsmall (fun _ => .vf) A b σ hA hne
  intro a ha
  apply (hb a ha).mono
  intro x hx
  rcases hx with hxS | hxa
  · exact Or.inl (Or.inl hxS)
  · exact Or.inr hxa

end SpecialTransformations.Section3
