import Section8.ContinuityFormula

/-! A generic-point continuity result gives the closed exceptional set
in 8.7 by closing the definable discontinuity locus. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem continuityException_properties_of_generic_continuity (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded) (hn : 0 < n)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfGraph f))
    (hgeneric : ∀ a : Fin n → VFType (M := M), AlgebraicIndependent (vfParameterField S) a → ContinuousAt f a) :
    let B := continuityExceptionRaw (vfGraph f)
    B ⊆ vfRawUniverse n ∧ IsClosed {a | vfValues a ∈ B} ∧
      vfDim Δ (vfObjectOfRaw (continuityExceptionRaw_definable hf)) < n ∧
      ContinuousOn f {a | vfValues a ∉ B} := by
  let A := vfRawUniverse n \ continuousInputs (vfGraph f)
  have hA : S.Definable LRV A := (vfRawUniverse_definable S n).inter (continuousInputs_definable hf).compl
  have hDim : vfDim Δ (vfObjectOfRaw hA) < n := by
    apply vfDim_lt_of_no_independent hc hs hsmall Δ hΔ hn
    intro a ha hind
    exact ha.2 ((mem_continuousInputs_iff hv f a).mpr (hgeneric a hind))
  let B := vfRawClosure A
  have he : {a | vfValues a ∈ B} = closure {a | vfValues a ∈ A} :=
    Set.ext (fun a => mem_vfRawClosure_iff hv A a)
  refine ⟨fun _ ha => ha.1, ?_, vfRawClosure_dim_lt_arity hc hs hsmall Δ hΔ hn hv hA hDim, ?_⟩
  · change IsClosed {a | vfValues a ∈ B}
    rw [he]
    exact isClosed_closure
  · intro a ha
    apply ContinuousAt.continuousWithinAt
    apply (mem_continuousInputs_iff hv f a).mp
    by_contra hnot
    have hA' : a ∈ {a | vfValues a ∈ A} := ⟨fun i => (a i).property, hnot⟩
    exact ha ((mem_vfRawClosure_iff hv A a).mpr (subset_closure hA'))

theorem closed_exception_of_generic_continuity (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded) (hn : 0 < n)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfGraph f))
    (hgeneric : ∀ a : Fin n → VFType (M := M), AlgebraicIndependent (vfParameterField S) a → ContinuousAt f a) :
    ∃ B : Set (Fin n → M), ∃ hB : S.Definable LRV B,
      B ⊆ vfRawUniverse n ∧ IsClosed {a | vfValues a ∈ B} ∧
      vfDim Δ (vfObjectOfRaw hB) < n ∧ ContinuousOn f {a | vfValues a ∉ B} :=
  ⟨continuityExceptionRaw (vfGraph f), continuityExceptionRaw_definable hf,
    continuityException_properties_of_generic_continuity hc hs hsmall Δ hΔ hn hv f hf hgeneric⟩

end SpecialTransformations.Section8
