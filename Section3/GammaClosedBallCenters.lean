import Section3.ClosedBallCenterCover
import Section3.ClosedCentersFromFiniteSet
import Section3.GammaRealRestriction
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
open ClosedBallCodes
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem coded_centers_gamma_base (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (A : Set (ClosedBallCodes.ClosedBall M)) (hA : A.Finite)
    (hdef : DefinableOverBase B (fun _ => .vf) (pullback A)) :
    ∃ f : pullback A → M, (∀ t, f t ∈ rawBall t.val) ∧
      DefinableOverBase B (fun _ => .vf) (centerGraph (pullback A) f) ∧
      ∀ t u : pullback A, rawBall t.val = rawBall u.val → f t = f u := by
  obtain ⟨k,t,hAd⟩ := hdef.specialize
  have ht : ∀ x ∈ Set.range (rawTuple t), iRV x := by
    rintro x ⟨i,rfl⟩
    exact raw_rv (t i)
  obtain ⟨R,hRd,hhit⟩ := finite_hitting_set_over_real_base h00 B.real
    (Set.range (rawTuple t)) ht A hA hAd
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hRN := (definableAt_normalize_iff B.real .vf
    (Subtype.val '' (R : Set (VFType (M := M))))).mpr hRd
  let D : (Fin 3 → M) → Set (VFType (M := M)) := @ClosedBallCodes.ball M N
  have hD (q : Fin 3 → M) : D q = ball q := by
    ext x
    exact Set.ext_iff.mp (rawBall_normalize q) x.val
  have hsort (q : Fin 3 → M) (hq : q ∈ pullback A) : ∀ i, @iVF M N (q i) := by
    obtain ⟨hs,_⟩ := hq
    exact hs
  obtain ⟨Γ,hΓ,v,hv⟩ := @VFValued.exists_valuation_predV M N hN
  letI := hΓ
  have hclosed (q : Fin 3 → M) (hq : q ∈ pullback A) : ClosedBallRoots.IsClosedBall v (D q) := by
    by_cases hz : q 2 = @iVFZero M N
    · exact Or.inl (@ball_eq_univ M N hN q (hsort q hq) hz)
    · exact Or.inr ⟨⟨q 0,hsort q hq 0⟩,⟨q 1,hsort q hq 1⟩,
        @ball_eq_closed M N hN Γ hΓ v hv q (hsort q hq) hz⟩
  have hhitN (q : Fin 3 → M) (hq : q ∈ pullback A) : ∃ x ∈ R, x ∈ D q := by
    obtain ⟨hqs,hqA⟩ := hq
    let q' : ClosedBallCodes.Code M := ⟨q,hqs⟩
    let a : A := ⟨Quotient.mk _ q',hqA⟩
    obtain ⟨x,hxR,hxB⟩ := hhit a
    refine ⟨x,hxR,?_⟩
    rw [hD]
    exact hxB
  obtain ⟨g,hg,hgmem,hgeq⟩ := @BallFamilies.centers_of_finite_hitting_set M N hN 3 Γ hΓ
    v hv h00N B.real (pullback A) D (@ClosedBallCodes.relation_definable M N B.real)
    R hRN hhitN hclosed
  let H : Set (Fin 4 → M) := {z | (∀ i, iVF (z i)) ∧ (g (Fin.init z)).val = z (Fin.last 3)}
  let S : Set M := B.real
  have hHd : SpecialTransformations.Section3.DefinableOver S (fun _ => .vf) H := by
    apply (definableOver_iff_normalized_raw S (fun _ => .vf) H).mpr
    constructor
    · letI := N
      have hi : S.DefinableMap LRV (Fin.init : (Fin 4 → M) → (Fin 3 → M)) :=
        fun _ => Set.DefinableFun.proj LRV
      have he := (hg.comp hi).ofPred_eq
        (Set.DefinableFun.proj (L := LRV) (A := S) (i := Fin.last 3))
      have hs := Set.definable_iInter_of_finite (fun i : Fin 4 =>
        (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => i))
      convert hs.inter he using 1
      ext z
      simp only [H,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage,
        Function.comp_apply]
      rfl
    · exact fun z hz => hz.1
  let f (q : pullback A) := (g q.val).val
  have hfmem (q : pullback A) : f q ∈ rawBall q.val := by
    have hh := hgmem q.val q.property
    rw [hD] at hh
    exact hh
  have he : centerGraph (pullback A) f = {z : Fin 4 → M | Fin.init z ∈ pullback A ∧ z ∈ H} := by
    ext z
    constructor
    · rintro ⟨q,hq,hf⟩
      have hC : Fin.init z ∈ pullback A := hq ▸ q.property
      have heq : (g (Fin.init z)).val = z (Fin.last 3) := by rw [← hq]; exact hf
      refine ⟨hC,?_,heq⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact heq ▸ (g (Fin.init z)).property
      · exact hsort (Fin.init z) hC j
    · rintro ⟨hC,_,heq⟩
      exact ⟨⟨Fin.init z,hC⟩,rfl,heq⟩
  have hgraph : DefinableOverBase B (fun _ => .vf) (centerGraph (pullback A) f) := by
    rw [he]
    exact hdef.inter_real_preimage (fun _ => .vf) H hHd Fin.castSucc
  refine ⟨f,hfmem,hgraph,?_⟩
  intro q u heq
  apply congrArg Subtype.val
  apply hgeq
  rw [hD,hD]
  exact congrArg (fun P : Set M => {x : VFType (M := M) | x.val ∈ P}) heq


/-- Lemma3.10 over genuine Gamma-named bases, on the actual closed-ball
quotient with its complete full-code graph over exactly the same base. -/
theorem lemma_3_10_gamma_base (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (A : Set (ClosedBallCodes.ClosedBall M)) (hA : A.Finite)
    (hdef : DefinableOverBase B (fun _ => .vf) (pullback A)) :
    ∃ f : A → M, (∀ D, f D ∈ underlying D.val) ∧
      DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A f) := by
  obtain ⟨f,hfmem,hfgraph,hfinv⟩ := coded_centers_gamma_base h00 B A hA hdef
  let rep (B : A) : ClosedBallCodes.Code M := Classical.choose (Quotient.exists_rep B.val)
  have hrep (B : A) : Quotient.mk _ (rep B) = B.val :=
    Classical.choose_spec (Quotient.exists_rep B.val)
  let repC (B : A) : pullback A := ⟨(rep B).val, (rep B).property, (hrep B).symm ▸ B.property⟩
  let F (B : A) : M := f (repC B)
  have hFc (t : ClosedBallCodes.Code M) (ht : Quotient.mk _ t ∈ A) (B : A)
      (he : Quotient.mk _ t = B.val) : F B = f ⟨t.val, t.property, ht⟩ := by
    apply hfinv
    exact congrArg underlying ((hrep B).trans he.symm)
  refine ⟨F, ?_, ?_⟩
  · intro B
    have hh := hfmem (repC B)
    have he : rawBall (rep B).val = underlying B.val := congrArg underlying (hrep B)
    exact he ▸ hh
  · have hgraph : quotientCenterGraph A F = centerGraph (pullback A) f := by
      ext z
      constructor
      · rintro ⟨t, ht, B, he, hF⟩
        have htA : Quotient.mk _ t ∈ A := he.symm ▸ B.property
        exact ⟨⟨t.val, t.property, htA⟩, ht, (hFc t htA B he).symm.trans hF⟩
      · rintro ⟨t, ht, hf⟩
        obtain ⟨hcode, htA⟩ := t.property
        let c : ClosedBallCodes.Code M := ⟨t.val, hcode⟩
        let B : A := ⟨Quotient.mk _ c, htA⟩
        exact ⟨c, ht, B, rfl, (hFc c htA B rfl).trans hf⟩
    rw [hgraph]
    exact hfgraph

end SpecialTransformations.Section3.GammaParameters
