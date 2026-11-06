import Section3.ClosedClassCodes
import Section3.GammaBaseTools
import Section3.GammaProjection
import Section3.OpenBallCodes

/- Component: OpenBallFamilyHulls -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.OpenBallCodes
variable {M : Type} [sM : LRV.Structure M]

/-- The complete equality kernel of real closed-ball codes, with no
representative parameters. This is the same quantified-membership scheme
as the checked ClosedClassCodes.eq_class_definable theorem. -/
theorem closed_kernel_raw_definable (S : Set M) :
    S.Definable LRV {z : Fin 3 ⊕ Fin 3 → M |
      ClosedBallCodes.rawBall (z ∘ Sum.inl) = ClosedBallCodes.rawBall (z ∘ Sum.inr)} := by
  let ι := Fin 3 ⊕ Fin 3
  let il : Fin 3 ⊕ Fin 1 → ι ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let ir : Fin 3 ⊕ Fin 1 → ι ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inr i)) Sum.inr
  have hl := (ClosedClassCodes.rawBall_definable S).preimage_comp il
  have hr := (ClosedClassCodes.rawBall_definable S).preimage_comp ir
  have hh := ((hl.himp hr).inter (hr.himp hl)).forall_of_finite
  convert hh using 1
  ext z
  change ClosedBallCodes.rawBall (z ∘ Sum.inl) = ClosedBallCodes.rawBall (z ∘ Sum.inr) ↔
    ∀ u : Fin 1 → M,
      ((u 0 ∈ ClosedBallCodes.rawBall (z ∘ Sum.inl) → u 0 ∈ ClosedBallCodes.rawBall (z ∘ Sum.inr)) ∧
       (u 0 ∈ ClosedBallCodes.rawBall (z ∘ Sum.inr) → u 0 ∈ ClosedBallCodes.rawBall (z ∘ Sum.inl)))
  constructor
  · intro he u
    exact ⟨fun h => he ▸ h,fun h => he.symm ▸ h⟩
  · intro h
    exact Set.ext (fun x => ⟨(h ![x]).1,(h ![x]).2⟩)

def hullIndex : Fin 2 ⊕ Fin 3 ≃ Fin 5 := finSumFinEquiv

def hullGraph : Set (Fin 5 → M) :=
  {z | (∀ i, iVF (z i)) ∧ z (hullIndex (Sum.inl (1 : Fin 2))) ≠ iVFZero ∧
    ClosedBallCodes.rawBall (hullCode (fun i => z (hullIndex (Sum.inl i)))) =
      ClosedBallCodes.rawBall (fun i => z (hullIndex (Sum.inr i)))}

theorem hullGraph_raw_definable (S : Set M) : S.Definable LRV (hullGraph (M := M)) := by
  let e : Fin 2 ⊕ Fin 3 ≃ Fin 5 := hullIndex
  let F : (Fin 5 → M) → (Fin 3 ⊕ Fin 3 → M) := fun z =>
    Sum.elim (hullCode (fun i => z (e (.inl i)))) (fun i => z (e (.inr i)))
  have hF : S.DefinableMap LRV F := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · exact Set.DefinableFun.proj LRV
      · exact Set.DefinableFun.proj LRV
      · exact DefinableConstants.constant (DefinableConstants.function_symbol
          (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
    | inr i => exact Set.DefinableFun.proj LRV
  have hk := (closed_kernel_raw_definable S).preimage_map hF
  have hs := Set.definable_iInter_of_finite (fun i : Fin 5 =>
    (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => i))
  have hzero : S.DefinableFun LRV (fun _ : Fin 5 → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hn := ((Set.DefinableFun.proj (L := LRV) (A := S) (i := e (.inl 1))).ofPred_eq hzero).compl
  convert (hs.inter hn).inter hk using 1
  ext z
  simp only [hullGraph,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage,
    Set.mem_compl_iff,Function.comp_apply]
  exact and_assoc.symm

variable [hM : M ⊨ Axioms.ACVF]

theorem hullCode_normalize (q : Fin 2 → M) :
    @hullCode M (CanonicalStructure.normalize (M := M)) q = hullCode q := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact CanonicalStructure.normalize_fun Fn.vfOne Fin.elim0 (fun i => i.elim0)

theorem hullGraph_normalize :
    @hullGraph M (CanonicalStructure.normalize (M := M)) = hullGraph (M := M) := by
  ext z
  have hz : @iVFZero M (CanonicalStructure.normalize (M := M)) = iVFZero :=
    CanonicalStructure.sortZero_normalize .vf
  simp only [hullGraph,Set.mem_ofPred_eq,ClosedBallCodes.rawBall_normalize,hullCode_normalize,hz] <;> rfl

theorem hullGraph_definable (S : Set M) :
    DefinableOver S (fun _ : Fin 5 => .vf) (hullGraph (M := M)) := by
  apply (definableOver_iff_normalized_raw S (fun _ : Fin 5 => .vf) _).mpr
  refine ⟨?_,fun z hz => hz.1⟩
  have h := @hullGraph_raw_definable M (CanonicalStructure.normalize (M := M)) S
  exact @hullGraph_normalize M sM hM ▸ h

/-- The full closed-code preimage of the hull family is the projection
of the original open family intersected with the complete hull graph. -/
theorem hull_family_definable_base (B : GammaParameters.Base (M := M))
    (A : Set (OpenBall M))
    (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) (pullback A)) :
    GammaParameters.DefinableOverBase B (fun _ => .vf)
      (ClosedBallCodes.pullback (hull '' A)) := by
  let e : Fin 2 ⊕ Fin 3 ≃ Fin 5 := hullIndex
  let iq : Fin 2 → Fin 5 := fun i => e (.inl i)
  let ic : Fin 3 → Fin 5 := fun i => e (.inr i)
  have hDom := hA.preimage_real (fun _ : Fin 5 => .vf) iq
  have hGr := GammaParameters.real_definableOverBase B _ _ (hullGraph_definable B.real)
  have hProj := (hGr.inter hDom).image_real ic
  convert hProj using 1
  all_goals try rfl
  ext c
  constructor
  · rintro ⟨hc,D,hD,he⟩
    obtain ⟨q,hq⟩ := Quotient.exists_rep D
    have hqA : Quotient.mk _ q ∈ A := hq.symm ▸ hD
    let z := Sum.elim q.val c ∘ e.symm
    have hzq : z ∘ iq = q.val := by
      funext i
      simp only [z,iq,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
    have hzc : z ∘ ic = c := by
      funext i
      simp only [z,ic,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    have hzs : ∀ i, iVF (z i) := by
      intro i
      change iVF (Sum.elim q.val c (e.symm i))
      cases e.symm i with
      | inl j => exact q.property.1 j
      | inr j => exact hc j
    have hraw : ClosedBallCodes.rawBall (hullCode q.val) = ClosedBallCodes.rawBall c := by
      have hh := congrArg ClosedBallCodes.underlying he
      rw [← hq] at hh
      exact hh
    have hzG : z ∈ hullGraph := by
      refine ⟨hzs,?_,?_⟩
      · change (z ∘ iq) 1 ≠ iVFZero
        rw [hzq]
        exact q.property.2
      · change ClosedBallCodes.rawBall (hullCode (z ∘ iq)) = ClosedBallCodes.rawBall (z ∘ ic)
        rw [hzq,hzc]
        exact hraw
    refine ⟨z,⟨hzG,?_,hzs⟩,hzc⟩
    rw [hzq]
    exact ⟨q.property,hqA⟩
  · rintro ⟨z,⟨hzG,hzA,_⟩,hzc⟩
    change z ∘ ic = c at hzc
    obtain ⟨hq,hqA⟩ := hzA
    let q : Code M := ⟨z ∘ iq,hq⟩
    have hc : ∀ i, iVF (c i) := by
      intro i
      rw [← congrFun hzc i]
      exact hzG.1 (ic i)
    refine ⟨hc,Quotient.mk _ q,hqA,?_⟩
    apply Quotient.sound
    have he := hzG.2.2
    change ClosedBallCodes.rawBall (hullCode (z ∘ iq)) = ClosedBallCodes.rawBall (z ∘ ic) at he
    rwa [hzc] at he

end SpecialTransformations.Section3.OpenBallCodes
