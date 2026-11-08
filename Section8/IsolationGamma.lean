import Section8.IsolationFamilies
import Section3.GammaSpecialization
import Section3.NormalizationSaturation
import Section3.SmallFiniteParameters

/-! The exceptional locus is definable over the original Gamma base.
The full representative relation is invariant in every Gamma coordinate. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem rvUniformBall_normalize (a : Fin n → M) (t : M) :
    @rvUniformBall M (CanonicalStructure.normalize (M := M)) n a t = rvUniformBall a t := by
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  ext x
  change (@GammaParameters.NonzeroRV M N t ∧
      ∃ r, iVF r ∧ @iRv M N r = t ∧ x ∈ @uniformBall M N n a r) ↔
    (GammaParameters.NonzeroRV t ∧ ∃ r, iVF r ∧ iRv r = t ∧ x ∈ uniformBall a r)
  rw [GammaParameters.nonzero_rv_normalize]
  refine and_congr Iff.rfl (exists_congr (fun r => and_congr_right (fun hr => ?_)))
  have he : @iRv M N r = iRv r :=
    CanonicalStructure.normalize_fun Fn.rvMap ![r] (by
      intro j
      fin_cases j
      exact hr)
  rw [he, uniformBall_normalize]

theorem isolatedInputs_normalize (G : Set (Fin n ⊕ Fin m → M)) :
    @isolatedInputs M (CanonicalStructure.normalize (M := M)) n m G = isolatedInputs G := by
  have he : @graphIsolation M (CanonicalStructure.normalize (M := M)) n m G = graphIsolation G := by
    ext z
    simp only [graphIsolation, Set.mem_ofPred_eq, GammaParameters.nonzero_rv_normalize,
      rvUniformBall_normalize]
  simp only [isolatedInputs, inputIsolation, he]

private def isolationRelation {S : Set M} {k : ℕ}
    (Q : GammaParameters.Relation S k (n + m) (fun _ => .vf)) :
    GammaParameters.Relation S k n (fun _ => .vf) where
  carrier := {p | p.2 ∈ isolatedInputs
    {w | (p.1, w ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm) ∈ Q.carrier}}
  definable := by
    let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
    let N := @CanonicalStructure.normalize M sM
    letI := sM
    have hnorm (G : Set (Fin n ⊕ Fin m → M)) : @isolatedInputs M N n m G = isolatedInputs G :=
      isolatedInputs_normalize G
    have hQN := Q.definable
    letI := N
    have hG := @Set.Definable.preimage_comp M S LRV N
      (Fin k ⊕ Fin (n + m)) (Fin k ⊕ (Fin n ⊕ Fin m)) (Sum.map id e.symm) _ hQN
    have hd := @isolatedInputsFamily_definable M N (Fin k) n m inferInstance S _ hG
    convert hd using 1
    ext z
    change _ ↔ (z ∘ Sum.inr) ∈ @isolatedInputs M N n m _
    rw [hnorm] <;> rfl
  proper := by
    rintro p ⟨t, ht⟩
    obtain ⟨y, hy⟩ := (mem_inputIsolation_iff p.2 t).mp ht
    obtain ⟨hp, hs⟩ := Q.proper _ hy.1
    refine ⟨hp, fun i => ?_⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using
      hs ((finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) (.inl i))
  invariant := by
    intro t u htu a
    have he : {w : Fin n ⊕ Fin m → M |
        (GammaParameters.rawTuple t, w ∘ finSumFinEquiv.symm) ∈ Q.carrier} =
      {w : Fin n ⊕ Fin m → M |
        (GammaParameters.rawTuple u, w ∘ finSumFinEquiv.symm) ∈ Q.carrier} :=
      Set.ext (fun w => Q.invariant t u htu (w ∘ finSumFinEquiv.symm))
    change a ∈ isolatedInputs _ ↔ a ∈ isolatedInputs _
    rw [he]

theorem isolatedInputs_gamma_definable {B : GammaParameters.Base (M := M)}
    {G : Set (Fin n ⊕ Fin m → M)}
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin (n + m) => .vf)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ G}) :
    GammaParameters.DefinableOverBase B (fun _ => .vf) (isolatedInputs G) := by
  obtain ⟨k, γ, hγ, Q, hQ⟩ := hG
  refine ⟨k, γ, hγ, isolationRelation Q, ?_⟩
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  have he : {w : Fin n ⊕ Fin m → M | w ∘ e.symm ∈ Q.fibre γ} = G := by
    rw [hQ]
    ext w
    change (w ∘ e.symm) ∘ e ∈ G ↔ w ∈ G
    have hw : (w ∘ e.symm) ∘ e = w := funext (fun i => congrArg w (e.symm_apply_apply i))
    rw [hw]
  change isolatedInputs {w : Fin n ⊕ Fin m → M | w ∘ e.symm ∈ Q.fibre γ} = _
  rw [he]

private theorem normalizedGraph_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : DefinableOver S (fun _ : Fin (n + m) => .vf)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ G}) :
    @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin n ⊕ Fin m) G := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have h := (definableOver_iff_normalized_raw S (fun _ => .vf) _).mp hG
  letI := N
  convert h.1.preimage_comp e.symm using 1
  ext z
  change z ∈ G ↔ (z ∘ e.symm) ∘ e ∈ G
  have he : (z ∘ e.symm) ∘ e = z := funext (fun i => congrArg z (e.symm_apply_apply i))
  rw [he]

/-- Lemma 8.2 for a real parameter base and the actual Gamma presentation.
The dimension object uses the same original base after normalization. -/
theorem lemma_8_2_actual_gamma {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : DefinableOver S (fun _ : Fin (n + m) => .vf)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ vfGraph f}) :
    let N := @CanonicalStructure.normalize M sM
    let Δ : @Space LRV M N := @gammaSpace M sM hM
    let hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
    letI := N
    letI : M ⊨ Axioms.ACVF := hN
    vfDim Δ (isolatedInputsObject (normalizedGraph_definable (sM := sM) hf)) < n := by
  dsimp only
  let N := @CanonicalStructure.normalize M sM
  let Δ : @Space LRV M N := @gammaSpace M sM hM
  have hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
  have hcan : @CanonicalStructure.IsCanonical M N := @CanonicalStructure.normalize_isCanonical M sM
  have hΔ : @Space.RVCoded M N Δ := @gammaSpace_rvCoded M sM hM
  have hsN : @Saturated M N κ := @Saturated.normalize M sM κ hs
  letI := N
  letI : M ⊨ Axioms.ACVF := hN
  exact lemma_8_2 hcan hsN hsmall Δ hΔ hn f (normalizedGraph_definable (sM := sM) hf)

/-- The original Gamma base defines the exceptional locus, and a finite
representative presentation computes its dimension below the input arity. -/
theorem lemma_8_2_gamma_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) {B : GammaParameters.Base (M := M)}
    (hsmall : Cardinal.mk ↥B.real < κ) (hn : 0 < n)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : GammaParameters.DefinableOverBase B (fun _ : Fin (n + m) => .vf)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ vfGraph f}) :
    GammaParameters.DefinableOverBase B (fun _ => .vf) (isolatedInputs (vfGraph f)) ∧
      ∃ k, ∃ t : Fin k → GammaParameters.Code (M := M),
        ∃ hG : DefinableOver (B.real ∪ Set.range (GammaParameters.rawTuple t))
          (fun _ : Fin (n + m) => .vf)
          {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ vfGraph f},
        let N := @CanonicalStructure.normalize M sM
        let Δ : @Space LRV M N := @gammaSpace M sM hM
        let hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
        letI := N
        letI : M ⊨ Axioms.ACVF := hN
        vfDim Δ (isolatedInputsObject (normalizedGraph_definable (sM := sM) hG)) < n := by
  obtain ⟨k, t, ht⟩ := GammaParameters.DefinableOverBase.specialize hf
  exact ⟨isolatedInputs_gamma_definable hf, k, t, ht,
    lemma_8_2_actual_gamma hs (small_union_range hκ B.real hsmall _) hn f ht⟩

end SpecialTransformations.Section8
