module

public import Section3.NearestRootDefinability
public import Section3.SortedBoolean

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.NearestRootSyntax
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The pair relation is real-base definable independently of the set A
whose nearest roots will be selected. Geometry is in the normalized model. -/
def normalizedPairs (R : Set M) : Set (Fin 2 → M) :=
  {z | z 0 ∈ R ∧ iVF (z 1) ∧ ∀ s ∈ R,
    @distanceLe M (CanonicalStructure.normalize (M := M)) (z 0) (z 1) s}

theorem normalizedPairs_definable (S R : Set M) (hR : DefinableAt S .vf R) :
    DefinableOver S (fun _ : Fin 2 => .vf) (normalizedPairs R) := by
  have hRN := (definableAt_iff_normalized_raw S .vf R).mp hR
  apply (definableOver_iff_normalized_raw S (fun _ => .vf) _).mpr
  constructor
  · let N := CanonicalStructure.normalize (M := M)
    letI := N
    let idx : Fin 3 → Fin 2 ⊕ Fin 1 := ![.inl 0,.inl 1,.inr 0]
    have hp := (distanceLe_definable S).preimage_comp idx
    have hr := hRN.1.preimage_comp (Sum.inr : Fin 1 → Fin 2 ⊕ Fin 1)
    have hall := (hr.himp hp).forall_of_finite
    have hi : S.Definable LRV {z : Fin 2 → M | ∀ s ∈ R, distanceLe (z 0) (z 1) s} := by
      convert hall using 1
      ext z
      change (∀ s ∈ R, distanceLe (z 0) (z 1) s) ↔
        ∀ u : Fin 1 → M, u 0 ∈ R → distanceLe (z 0) (z 1) (u 0)
      exact ⟨fun h u => h (u 0),fun h s => h (fun _ => s)⟩
    have hr0 := hRN.1.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
    have ha1 := (definableAt_sort S .vf).raw_definable.preimage_comp
      (fun _ : Fin 1 => (1 : Fin 2))
    convert hr0.inter (ha1.inter hi) using 1
    ext z
    rfl
  · intro z hz i
    fin_cases i
    · exact hR.2 hz.1
    · exact hz.2.1

end SpecialTransformations.Section3.NearestRootSyntax
