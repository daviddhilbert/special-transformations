import Section3.GammaParameterBridge
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Every representative gives a defining real formula. The extra RV
parameters are explicit in the conclusion; this is not their elimination. -/
theorem DefinableWith.specialize {S : Set M} {k n : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : DefinableWith S γ sn A) (t : Fin k → Code (M := M)) (ht : values t = γ) :
    SpecialTransformations.Section3.DefinableOver (S ∪ Set.range (rawTuple t)) sn A := by
  obtain ⟨R,hRA⟩ := hA
  let U := R.carrier
  let a := rawTuple t
  let B := S ∪ Set.range a
  have hrow : {x | (a,x) ∈ U} = A := (R.row_eq_fibre t γ ht).trans hRA
  have hsort : ∀ x ∈ A, ∀ i, sortEval (sn i) (x i) := DefinableWith.proper ⟨R,hRA⟩
  have hRN := R.definable
  apply (definableOver_iff_normalized_raw B sn A).mpr
  constructor
  · let N := CanonicalStructure.normalize (M := M)
    letI := N
    have hr : B.Definable LRV {z : Fin k ⊕ Fin n → M | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ U} :=
      hRN.mono Set.subset_union_left
    have hF : B.DefinableMap LRV (fun x : Fin n → M => Sum.elim a x) := by
      intro i
      cases i with
      | inl j => exact LRV.definableFun_const (Fin n) (Or.inr (Set.mem_range_self j))
      | inr j => exact Set.DefinableFun.proj LRV
    have h := hr.preimage_map hF
    convert h using 1
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,Sum.elim_comp_inl,Sum.elim_comp_inr]
    exact (Set.ext_iff.mp hrow x).symm
  · exact hsort

theorem DefinableOverBase.specialize {B : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A) :
    ∃ k, ∃ t : Fin k → Code (M := M),
      SpecialTransformations.Section3.DefinableOver (B.real ∪ Set.range (rawTuple t)) sn A := by
  obtain ⟨k,γ,_,hA⟩ := hA
  exact ⟨k,representatives γ,hA.specialize (representatives γ) (representatives_values γ)⟩

theorem DefinableAtBase.specialize {B : Base (M := M)} {σ : SortTag} {A : Set M}
    (hA : DefinableAtBase B σ A) :
    ∃ k, ∃ t : Fin k → Code (M := M),
      SpecialTransformations.Section3.DefinableAt (B.real ∪ Set.range (rawTuple t)) σ A := by
  obtain ⟨k,t,hT⟩ := DefinableOverBase.specialize hA
  refine ⟨k,t,hT,?_⟩
  intro a ha
  exact ((definableOver_iff_normalized_raw _ (fun _ : Fin 1 => σ) _).mp hT).2 ![a] ha 0

theorem real_definableOverBase (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hA : SpecialTransformations.Section3.DefinableOver B.real sn A) : DefinableOverBase B sn A :=
  ⟨0,Fin.elim0,(fun i => i.elim0),(with_zero_iff B.real Fin.elim0 sn A).mpr hA⟩

theorem real_definableAtBase (B : Base (M := M)) (σ : SortTag) (A : Set M)
    (hA : SpecialTransformations.Section3.DefinableAt B.real σ A) : DefinableAtBase B σ A :=
  real_definableOverBase B (fun _ : Fin 1 => σ) {z | z 0 ∈ A} hA.1

end SpecialTransformations.Section3.GammaParameters
