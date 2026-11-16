module

public import Section4.ResidueRVSet
public import Section9.ResidueChartArithmetic

@[expose] public section

/-! Interpret the arithmetic tests on arbitrary finite index types in
the actual residue field of the VF/RV structure. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "k" => ModelResidue M
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def rawResidueImage {ι : Type} (A : Set (ι → k)) : Set (ι → M) :=
  {z | ∃ x ∈ A, (fun i => residueRaw (x i)) = z}

theorem residueFieldImage_indexed_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {ι : Type} [Finite ι] (E : Subfield k) (S : Set M) (hE : E ≤ residueDefinableField S)
    (A : Set (ι → k)) (hA : Relative.Def E A) :
    S.Definable LRV (rawResidueImage A) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  let D := {x : Fin (Fintype.card ι) → k | x ∘ e.symm ∈ A}
  have hD : Relative.Def E D := hA.preimage_comp e.symm
  have h := (residueFieldImage_definable_of_definable_names hc E S
    (fun c => hE c.property) D hD).raw_definable.preimage_comp e
  convert h using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x ∘ e, ?_, rfl⟩
    change x ∘ e ∘ e.symm ∈ A
    simpa only [Function.comp_assoc, e.self_comp_symm, Function.comp_id] using hx
  · rintro ⟨x, hx, h⟩
    refine ⟨x ∘ e.symm, hx, ?_⟩
    funext i
    have he := congrFun h (e.symm i)
    change residueRaw (x (e.symm i)) = z (e (e.symm i)) at he
    change residueRaw (x (e.symm i)) = z i
    simpa only [e.apply_symm_apply] using he

theorem mem_rawResidueImage_iff {ι : Type} (A : Set (ι → k)) (x : ι → k) :
    (fun i => residueRaw (x i)) ∈ rawResidueImage A ↔ x ∈ A := by
  constructor
  · rintro ⟨y, hy, h⟩
    have he : y = x := funext fun i => residueRaw_injective (congrFun h i)
    exact he ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

theorem relative_graph_on_sum {K : Type} [Field K] {ι : Type} [Finite ι] (E : Subfield K)
    (f : (ι → K) → K) (hf : Relative.Fun E f) :
    Relative.Def E {z : ι ⊕ Unit → K | f (z ∘ Sum.inl) = z (.inr ())} :=
  (hf.comp (fun i => Relative.projection (E := E) (Sum.inl i))).ofPred_eq
    (Relative.projection (E := E) (Sum.inr ()))

end SpecialTransformations.Section9
