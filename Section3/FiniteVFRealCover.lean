import Section3.FiniteAlgebraicCover
import Section3.FiniteCoding
import Section3.RVIndependence
import Section3.GammaSpecialization
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A finite VF tuple set defined after adjoining RV names has a finite
cover defined over the original base. This is a cover, not parameter
elimination from the original set or from an arbitrary choice function. -/
theorem finite_vf_tuple_cover (S T : Set M) (hT : ∀ t ∈ T, iRV t) {n : ℕ}
    (A : Set (Fin n → VFType (M := M))) (hfin : A.Finite)
    (hA : DefinableOver (S ∪ T) (fun _ => .vf) (FiniteCoding.values '' A)) :
    ∃ C : Set (Fin n → VFType (M := M)), C.Finite ∧ A ⊆ C ∧
      DefinableOver S (fun _ => .vf) (FiniteCoding.values '' C) := by
  have hAN := (definableOver_iff_normalized_raw (S ∪ T) (fun _ => .vf) _).mp hA
  have hcoord (a : Fin n → VFType (M := M)) (ha : a ∈ A) (i : Fin n) :
      AlgebraicAt S .vf (a i).val := by
    let P : Set M := {x | ∃ b ∈ A, (b i).val = x}
    have hP : DefinableAt (S ∪ T) .vf P := by
      apply (definableAt_iff_normalized_raw (S ∪ T) .vf P).mpr
      constructor
      · exact @FiniteCoding.projection_definable M (CanonicalStructure.normalize (M := M)) (S ∪ T) n A hAN.1 i
      · rintro x ⟨b,hb,he⟩
        rw [← he]
        exact (b i).property
    have hPf : P.Finite := by
      convert hfin.image (fun b : Fin n → VFType (M := M) => (b i).val) using 1
      ext x
      rfl
    exact (algebraicAt_vf_union_rv_iff S T hT (a i)).mp ⟨P,hP,hPf,a,ha,rfl⟩
  let D : Set M := ⋃ a ∈ A, Set.range (fun i => (a i).val)
  have hD : D.Finite := hfin.biUnion (fun a _ => Set.finite_range (fun i => (a i).val))
  have hDacl : ∀ x ∈ D, AlgebraicAt S .vf x := by
    rintro x hx
    obtain ⟨a,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ha,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i,rfl⟩ := hx
    exact hcoord a ha i
  obtain ⟨E,hEd,hEf,hDE⟩ := finite_definable_cover hD hDacl
  let U : Set (Fin n → M) := {z | ∀ i, z i ∈ E}
  have hUf : U.Finite := Set.Finite.pi' (fun _ => hEf)
  have hUs : ∀ z ∈ U, ∀ i, iVF (z i) := fun z hz i => hEd.2 (hz i)
  have hUd : DefinableOver S (fun _ => .vf) U := by
    apply (definableOver_iff_normalized_raw S (fun _ => .vf) U).mpr
    constructor
    · have hEN := (definableAt_iff_normalized_raw S .vf E).mp hEd
      let N := CanonicalStructure.normalize (M := M)
      letI := N
      have hh := Set.definable_iInter_of_finite
        (fun i : Fin n => hEN.1.preimage_comp (fun _ : Fin 1 => i))
      convert hh using 1
      ext z
      simp only [U,Set.mem_iInter,Set.mem_preimage,Set.mem_ofPred_eq,Function.comp_apply]
    · exact hUs
  let C : Set (Fin n → VFType (M := M)) := {a | FiniteCoding.values a ∈ U}
  have hCf : C.Finite := hUf.preimage FiniteCoding.values_injective.injOn
  have hCU : FiniteCoding.values '' C = U := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hz
      let a : Fin n → VFType (M := M) := fun i => ⟨z i,hUs z hz i⟩
      exact ⟨a,hz,rfl⟩
  refine ⟨C,hCf,?_,hCU.symm ▸ hUd⟩
  intro a ha i
  apply hDE
  exact Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨ha,Set.mem_range_self i⟩⟩

namespace GammaParameters

theorem finite_vf_tuple_cover_gamma_base (B : Base (M := M)) {n : ℕ}
    (A : Set (Fin n → VFType (M := M))) (hfin : A.Finite)
    (hA : DefinableOverBase B (fun _ => .vf) (FiniteCoding.values '' A)) :
    ∃ C : Set (Fin n → VFType (M := M)), C.Finite ∧ A ⊆ C ∧
      DefinableOver B.real (fun _ => .vf) (FiniteCoding.values '' C) := by
  obtain ⟨k,t,hAd⟩ := hA.specialize
  apply finite_vf_tuple_cover B.real (Set.range (rawTuple t)) ?_ A hfin hAd
  rintro x ⟨i,rfl⟩
  exact raw_rv (t i)

end GammaParameters
end SpecialTransformations.Section3
