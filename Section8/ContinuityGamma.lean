import Section8.ContinuityFamilies
import Section8.GenericOutputBall
import Section3.GammaSpecialization
import Section3.NormalizationSaturation
import Section3.SmallFiniteParameters

/-! The closed exception in Lemma 8.7 is defined over the original
Gamma base. Dimension and continuity use the released normalized model. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def normalizedContinuityException (G : Set (Fin n ⊕ Fin m → M)) : Set (Fin n → M) :=
  @continuityExceptionRaw M (@CanonicalStructure.normalize M sM) n m G

private def continuityExceptionRelation {S : Set M} {k : ℕ}
    (Q : GammaParameters.Relation S k (n + m) (fun _ => .vf)) :
    GammaParameters.Relation S k n (fun _ => .vf) where
  carrier := {p | GammaParameters.Proper p.1 ∧ p.2 ∈ normalizedContinuityException
    {w | (p.1, w ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm) ∈ Q.carrier}}
  definable := by
    let N := @CanonicalStructure.normalize M sM
    let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
    letI := sM
    have hQ := Q.definable
    have hProper (t : Fin k → M) : @GammaParameters.Proper M N k t ↔ @GammaParameters.Proper M sM k t := by
      change (∀ i, @GammaParameters.NonzeroRV M N (t i)) ↔
        (∀ i, @GammaParameters.NonzeroRV M sM (t i))
      exact forall_congr' (fun i => @GammaParameters.nonzero_rv_normalize M sM hM (t i))
    letI := N
    letI : M ⊨ Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
    have hP : S.Definable LRV {t : Fin k → M | @GammaParameters.Proper M sM k t} := by
      have hp : S.Definable LRV {t : Fin k → M | ∀ i, GammaParameters.NonzeroRV (t i)} := by
        rw [Set.ofPred_forall]
        exact Set.definable_iInter_of_finite (fun i =>
          (GammaParameters.nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => i))
      convert hp using 1
      ext t
      exact (hProper t).symm
    have hG := @Set.Definable.preimage_comp M S LRV N
      (Fin k ⊕ Fin (n + m)) (Fin k ⊕ (Fin n ⊕ Fin m)) (Sum.map id e.symm) _ hQ
    convert (hP.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin n)).inter
      (continuityExceptionFamily_definable hG) using 1
    ext z
    rfl
  proper := by
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  invariant := by
    intro t u htu a
    have he : {w : Fin n ⊕ Fin m → M |
        (GammaParameters.rawTuple t, w ∘ finSumFinEquiv.symm) ∈ Q.carrier} =
      {w : Fin n ⊕ Fin m → M |
        (GammaParameters.rawTuple u, w ∘ finSumFinEquiv.symm) ∈ Q.carrier} :=
      Set.ext (fun w => Q.invariant t u htu (w ∘ finSumFinEquiv.symm))
    change GammaParameters.Proper (GammaParameters.rawTuple t) ∧ a ∈ normalizedContinuityException _ ↔
      GammaParameters.Proper (GammaParameters.rawTuple u) ∧ a ∈ normalizedContinuityException _
    rw [he]
    exact and_congr (iff_of_true (GammaParameters.rawTuple_proper t) (GammaParameters.rawTuple_proper u)) Iff.rfl

theorem normalizedContinuityException_gamma_definable {B : GammaParameters.Base (M := M)}
    {G : Set (Fin n ⊕ Fin m → M)}
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin (n + m) => .vf)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ G}) :
    GammaParameters.DefinableOverBase B (fun _ => .vf) (normalizedContinuityException G) := by
  obtain ⟨k, γ, hγ, Q, hQ⟩ := hG
  refine ⟨k, γ, hγ, continuityExceptionRelation Q, ?_⟩
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  have he : {w : Fin n ⊕ Fin m → M | w ∘ e.symm ∈ Q.fibre γ} = G := by
    rw [hQ]
    ext w
    change (w ∘ e.symm) ∘ e ∈ G ↔ w ∈ G
    have hw : (w ∘ e.symm) ∘ e = w := funext (fun i => congrArg w (e.symm_apply_apply i))
    rw [hw]
  ext a
  change GammaParameters.Proper (GammaParameters.rawTuple (GammaParameters.representatives γ)) ∧
    a ∈ normalizedContinuityException {w | w ∘ e.symm ∈ Q.fibre γ} ↔
      a ∈ normalizedContinuityException G
  rw [he]
  exact and_iff_right (GammaParameters.rawTuple_proper _)

private theorem normalizedContinuityGraph_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : DefinableOver S (fun _ : Fin (n + m) => .vf)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ G}) :
    @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin n ⊕ Fin m) G := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have h := (definableOver_iff_normalized_raw S (fun _ : Fin (n + m) => .vf) _).mp hG
  letI := N
  convert h.1.preimage_comp e.symm using 1
  ext z
  change z ∈ G ↔ (z ∘ e.symm) ∘ e ∈ G
  have he : (z ∘ e.symm) ∘ e = z := funext (fun i => congrArg z (e.symm_apply_apply i))
  rw [he]

theorem lemma_8_7_gamma_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : GammaParameters.Base (M := M)} (hsmall : Cardinal.mk ↥B.real < κ) (hn : 0 < n)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : GammaParameters.DefinableOverBase B (fun _ : Fin (n + m) => .vf)
      {z | z ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) ∈ vfGraph f}) :
    GammaParameters.DefinableOverBase B (fun _ => .vf) (normalizedContinuityException (vfGraph f)) ∧
      ∃ k, ∃ t : Fin k → GammaParameters.Code (M := M),
        ∃ hG : DefinableOver (B.real ∪ Set.range (GammaParameters.rawTuple t))
          (fun _ : Fin (n + m) => .vf) {z | z ∘ finSumFinEquiv ∈ vfGraph f},
        let N := @CanonicalStructure.normalize M sM
        let Δ : @Space LRV M N := @gammaSpace M sM hM
        let hN : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
        letI := N
        letI : M ⊨ Axioms.ACVF := hN
        letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
          Valued.mk' Values.presentationValuation
        vfDim Δ (vfObjectOfRaw (continuityExceptionRaw_definable
          (@normalizedContinuityGraph_definable M sM hM n m _ _ hG))) < n ∧
          IsClosed {a | vfValues a ∈ continuityExceptionRaw (@vfGraph M N n m f)} ∧
          ContinuousOn (show (Fin n → @VFType M N) → Fin m → @VFType M N from f)
            {a | vfValues a ∉ continuityExceptionRaw (@vfGraph M N n m f)} := by
  refine ⟨normalizedContinuityException_gamma_definable hf, ?_⟩
  obtain ⟨k, t, hG⟩ := GammaParameters.DefinableOverBase.specialize hf
  have hSmall := small_union_range hκ B.real hsmall (GammaParameters.rawTuple t)
  refine ⟨k, t, hG, ?_⟩
  dsimp only
  let N := @CanonicalStructure.normalize M sM
  let Δ : @Space LRV M N := @gammaSpace M sM hM
  have hcan : @CanonicalStructure.IsCanonical M N := @CanonicalStructure.normalize_isCanonical M sM
  have hΔ : @Space.RVCoded M N Δ := @gammaSpace_rvCoded M sM hM
  have hsN : @Saturated M N κ := @Saturated.normalize M sM κ hs
  letI := N
  letI : M ⊨ Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' Values.presentationValuation
  have hF := @normalizedContinuityGraph_definable M sM hM n m _ _ hG
  obtain ⟨_, hclosed, hdim, hcont⟩ := continuityException_properties_of_generic_continuity
    hcan hsN hSmall Δ hΔ hn Values.presentation_compatible f hF
    (continuousAt_of_independent hcan hκ hsN hSmall Values.presentation_compatible f hF)
  exact ⟨hdim, hclosed, hcont⟩

end SpecialTransformations.Section8
