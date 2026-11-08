import Section8.RVFibreGeneric
import Section3.GammaSpecialization
import Section3.NormalizationSaturation
import Section3.SmallFiniteParameters

/-! The local-constancy locus descends to the original Gamma base.
The same Gamma parameters remain fixed when the VF centre varies. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

private def localConstancyRelation {S : Set M} {k : ℕ}
    (Q : GammaParameters.Relation S k (n + m) (MixedLocal.tupleSort n m)) :
    GammaParameters.Relation S k n (fun _ => .vf) where
  carrier := {p | GammaParameters.Proper p.1 ∧ p.2 ∈ rvConstantRaw
    {w | (p.1, w ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm) ∈ Q.carrier}}
  definable := by
    let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
    let N := @CanonicalStructure.normalize M sM
    letI := sM
    have hnorm (G : Set (Fin n ⊕ Fin m → M)) : @rvConstantRaw M N n m G = rvConstantRaw G :=
      rvConstantRaw_normalize G
    have hp : @Set.Definable M S LRV N (Fin k) {t | GammaParameters.Proper t} := by
      letI := N
      change S.Definable LRV {t : Fin k → M | ∀ i, GammaParameters.NonzeroRV (t i)}
      rw [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite (fun i => (GammaParameters.nonzero_rv_definable S).preimage_comp
        (fun _ : Fin 1 => i))
    have hQN := Q.definable
    letI := N
    have hG := @Set.Definable.preimage_comp M S LRV N
      (Fin k ⊕ Fin (n + m)) (Fin k ⊕ (Fin n ⊕ Fin m)) (Sum.map id e.symm) _ hQN
    have h := (hp.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin n)).inter
      (rvConstantFamilyRaw_definable hG)
    convert h using 1
    ext z
    change _ ↔ _ ∧ (z ∘ Sum.inr) ∈ @rvConstantRaw M N n m _
    rw [hnorm]
    rfl
  proper := fun _ hp => ⟨hp.1, hp.2.1⟩
  invariant := by
    intro t u htu a
    have he : {w : Fin n ⊕ Fin m → M |
        (GammaParameters.rawTuple t, w ∘ finSumFinEquiv.symm) ∈ Q.carrier} =
      {w : Fin n ⊕ Fin m → M |
        (GammaParameters.rawTuple u, w ∘ finSumFinEquiv.symm) ∈ Q.carrier} :=
      Set.ext (fun w => Q.invariant t u htu (w ∘ finSumFinEquiv.symm))
    change GammaParameters.Proper (GammaParameters.rawTuple t) ∧ a ∈ rvConstantRaw _ ↔
      GammaParameters.Proper (GammaParameters.rawTuple u) ∧ a ∈ rvConstantRaw _
    rw [he]
    exact and_congr (iff_of_true (fun i => ⟨(t i).val.property, (t i).property⟩)
      (fun i => ⟨(u i).val.property, (u i).property⟩)) Iff.rfl

theorem rvConstantRaw_gamma_definable {B : GammaParameters.Base (M := M)}
    {G : Set (Fin n ⊕ Fin m → M)}
    (hG : GammaParameters.DefinableOverBase B (MixedLocal.tupleSort n m)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ G}) :
    GammaParameters.DefinableOverBase B (fun _ => .vf) (rvConstantRaw G) := by
  obtain ⟨k, γ, hγ, Q, hQ⟩ := hG
  refine ⟨k, γ, hγ, localConstancyRelation Q, ?_⟩
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  have he : {w : Fin n ⊕ Fin m → M | w ∘ e.symm ∈ Q.fibre γ} = G := by
    rw [hQ]
    ext w
    change (w ∘ e.symm) ∘ e ∈ G ↔ w ∈ G
    have hw : (w ∘ e.symm) ∘ e = w := funext (fun i => congrArg w (e.symm_apply_apply i))
    rw [hw]
  ext a
  change GammaParameters.Proper (GammaParameters.rawTuple (GammaParameters.representatives γ)) ∧
    a ∈ rvConstantRaw {w | w ∘ e.symm ∈ Q.fibre γ} ↔ a ∈ rvConstantRaw G
  rw [he]
  exact and_iff_right (fun i => ⟨(GammaParameters.representatives γ i).val.property,
    (GammaParameters.representatives γ i).property⟩)

private theorem normalizedRVFamily_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : DefinableOver S (MixedLocal.tupleSort n m)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ G}) :
    @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin n ⊕ Fin m) G := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have h := (definableOver_iff_normalized_raw S (MixedLocal.tupleSort n m) _).mp hG
  letI := N
  convert h.1.preimage_comp e.symm using 1
  ext z
  change z ∈ G ↔ (z ∘ e.symm) ∘ e ∈ G
  have he : (z ∘ e.symm) ∘ e = z := funext (fun i => congrArg z (e.symm_apply_apply i))
  rw [he]

theorem lemma_8_9_gamma_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : GammaParameters.Base (M := M)} (hsmall : Cardinal.mk ↥B.real < κ) (hn : 0 < n)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {G : Set (Fin n ⊕ Fin m → M)}
    (hG : GammaParameters.DefinableOverBase B (MixedLocal.tupleSort n m)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ G}) :
    GammaParameters.DefinableOverBase B (fun _ => .vf) (rvConstantRaw G) ∧
      rvLocallyConstantOn (rvFibre G) {a | vfValues a ∈ rvConstantRaw G} ∧
      ∃ k, ∃ t : Fin k → GammaParameters.Code (M := M),
        ∃ hR : DefinableOver (B.real ∪ Set.range (GammaParameters.rawTuple t)) (MixedLocal.tupleSort n m)
          {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ G},
        let N := @CanonicalStructure.normalize M sM
        let Δ : @Space LRV M N := @gammaSpace M sM hM
        let hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
        letI := N
        letI : M ⊨ Axioms.ACVF := hN
        vfDim Δ (rvFibreBadObject (normalizedRVFamily_definable (sM := sM) hR)) < n := by
  refine ⟨rvConstantRaw_gamma_definable hG, ?_, ?_⟩
  · have he : {a | vfValues a ∈ rvConstantRaw G} = {a | rvLocallyConstantAt (rvFibre G) a} :=
      Set.ext (fun a => mem_rvConstantRaw_iff hv G a)
    rw [he]
    exact ⟨isOpen_rvLocallyConstantAt (rvFibre G), fun _ h => h⟩
  · obtain ⟨k, t, ht⟩ := GammaParameters.DefinableOverBase.specialize hG
    have hSmall := small_union_range hκ B.real hsmall (GammaParameters.rawTuple t)
    refine ⟨k, t, ht, ?_⟩
    dsimp only
    let N := @CanonicalStructure.normalize M sM
    let Δ : @Space LRV M N := @gammaSpace M sM hM
    have hcan : @CanonicalStructure.IsCanonical M N := @CanonicalStructure.normalize_isCanonical M sM
    have hΔ : @Space.RVCoded M N Δ := @gammaSpace_rvCoded M sM hM
    have hsN : @Saturated M N κ := @Saturated.normalize M sM κ hs
    letI := N
    letI : M ⊨ Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
    let v := Values.presentationValuation (M := M)
    letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' v
    exact rvFibreBad_dim_lt hcan hsN hSmall hn
      Values.presentation_compatible Δ hΔ (normalizedRVFamily_definable (sM := sM) ht)

end SpecialTransformations.Section8
