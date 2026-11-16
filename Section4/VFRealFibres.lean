module

public import Section4.MapParameters
public import Section4.RVCoordinates
public import Section3.SortedTuples

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n r : ℕ}

theorem vfValues_decode (c : (rawVFSpace (M := M) n).domain) :
    vfValues ((rawVFSpace (M := M) n).decode c) = c.val :=
  Space.ofEmbedding_decode vfValues vfValues_injective (rawVFSpace n).domain_definable c

theorem decode_vfValues (a : Fin n → VFType (M := M)) :
    (rawVFSpace (M := M) n).decode ⟨vfValues a, ⟨a, rfl⟩⟩ = a :=
  vfValues_injective (vfValues_decode _)

def fixedRVFibre (A : DefSet (rawMixedSpace (M := M) n r) S)
    (t : Fin r → CanonicalRV.RVSort M) :
    DefSet (rawVFSpace (M := M) n) (S ∪ Set.range (rvValues t)) where
  carrier := {a | (a, t) ∈ A.carrier}
  definable := by
    let B := S ∪ Set.range (rvValues t)
    let P := rawMixedSpace (M := M) n r
    let F (z : Fin n → M) : Fin n ⊕ Fin r → M := Sum.elim z (rvValues t)
    have hF : B.DefinableMap LRV F := by
      intro i
      cases i with
      | inl i => exact Set.DefinableFun.proj LRV
      | inr i => exact LRV.definableFun_const (Fin n) (Or.inr (Set.mem_range_self i))
    have hA : B.Definable LRV (P.preimage A.carrier) := A.definable.mono P Set.subset_union_left
    have h := hA.preimage_map hF
    have hdom (z : Fin n → M) (hz : z ∈ (rawVFSpace (M := M) n).domain) : F z ∈ P.domain :=
      ⟨hz, ⟨t, rfl⟩⟩
    have hdecode (z : Fin n → M) (hz : F z ∈ P.domain) :
        P.decode ⟨F z, hz⟩ = ((rawVFSpace n).decode ⟨z, hz.1⟩, t) := by
      apply Prod.ext
      · rfl
      · exact decode_rvValues t
    have he : (rawVFSpace (M := M) n).preimage {a | (a, t) ∈ A.carrier} =
        F ⁻¹' P.preimage A.carrier := by
      ext z
      constructor
      · rintro ⟨hz, hmem⟩
        refine ⟨hdom z hz, ?_⟩
        rw [hdecode]
        exact hmem
      · rintro ⟨hz, hmem⟩
        refine ⟨hz.1, ?_⟩
        rw [hdecode] at hmem
        exact hmem
    change B.Definable LRV ((rawVFSpace (M := M) n).preimage {a | (a, t) ∈ A.carrier})
    rw [he]
    exact h

def rawFixedRVFibre (A : DefSet (rawMixedSpace (M := M) n r) S)
    (t : Fin r → CanonicalRV.RVSort M) : Set (Fin n → M) :=
  (rawVFSpace n).preimage (fixedRVFibre A t).carrier

theorem mem_rawFixedRVFibre (A : DefSet (rawMixedSpace (M := M) n r) S)
    (t : Fin r → CanonicalRV.RVSort M) (a : Fin n → VFType (M := M)) :
    vfValues a ∈ rawFixedRVFibre A t ↔ (a, t) ∈ A.carrier := by
  have h := (rawVFSpace (M := M) n).preimage_decode (fixedRVFibre A t).carrier
    ⟨vfValues a, ⟨a, rfl⟩⟩
  simpa only [rawFixedRVFibre, fixedRVFibre, decode_vfValues, Set.mem_setOf_eq] using h

variable [hM : M ⊨ Axioms.ACVF]

theorem rawFixedRVFibre_sorted (hcan : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) (t : Fin r → CanonicalRV.RVSort M) :
    DefinableOver (S ∪ Set.range (rvValues t)) (fun _ => .vf) (rawFixedRVFibre A t) := by
  apply raw_definableOver_sorted hcan _ _ _ (fixedRVFibre A t).definable
  rintro z ⟨hz, _⟩ i
  obtain ⟨a, ha⟩ := hz
  exact (congrFun ha i) ▸ (a i).property

end SpecialTransformations.Section4

end
