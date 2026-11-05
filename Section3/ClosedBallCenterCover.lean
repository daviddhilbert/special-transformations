import Section3.ClosedBallQuotient
import Section3.FiniteAlgebraicCover
import Section3.RVIndependence
import Section3.GammaSpecialization
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedBallCodes
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Temporary RV names do not obstruct a finite real-base definable hitting
set for a finite family of closed-ball imaginaries. A finite cover of the
chosen center image, rather than the chosen centers, descends to S. -/
theorem finite_hitting_set_over_real_base (h00 : M ⊨ Axioms.ACVF00)
    (S T : Set M) (hT : ∀ t ∈ T, iRV t) (A : Set (ClosedBall M))
    (hA : A.Finite) (hdef : FamilyDefinable (S ∪ T) A) :
    ∃ R : Finset (VFType (M := M)),
      DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M)))) ∧
      ∀ B : A, ∃ r ∈ R, r.val ∈ underlying B.val := by
  obtain ⟨f,hmem,hgraph⟩ := lemma_3_10 h00 (S ∪ T) A hA hdef
  haveI : Finite A := hA.to_subtype
  let F := Set.range f
  let G := quotientCenterGraph A f
  have hFf : F.Finite := Set.finite_range f
  have hfVF (B : A) : iVF (f B) := by
    obtain ⟨t,ht⟩ := Quotient.exists_rep B.val
    have hb := hmem B
    rw [← ht] at hb
    change f B ∈ rawBall t.val at hb
    exact hb.2.1
  have hFd : DefinableAt (S ∪ T) .vf F := by
    have hGN := (definableOver_iff_normalized_raw (S ∪ T) (fun _ => .vf) G).mp hgraph
    apply (definableAt_iff_normalized_raw (S ∪ T) .vf F).mpr
    constructor
    · let N := CanonicalStructure.normalize (M := M)
      letI := N
      change (S ∪ T).Definable LRV {w : Fin 1 → M | w 0 ∈ F}
      have hh := hGN.1.image_comp (fun _ : Fin 1 => Fin.last 3)
      convert hh using 1
      ext w
      change (∃ B : A, f B = w 0) ↔
        ∃ z ∈ G, z ∘ (fun _ : Fin 1 => Fin.last 3) = w
      constructor
      · rintro ⟨B,hB⟩
        obtain ⟨t,ht⟩ := Quotient.exists_rep B.val
        let z : Fin 4 → M := Fin.snoc t.val (f B)
        refine ⟨z,?_,?_⟩
        · refine ⟨t,?_,B,ht,?_⟩
          · simp only [z,Fin.init_snoc]
          · simp only [z,Fin.snoc_last]
        · funext i
          fin_cases i
          change z (Fin.last 3) = w 0
          simpa only [z,Fin.snoc_last] using hB
      · rintro ⟨z,⟨t,ht,B,hBt,hf⟩,he⟩
        exact ⟨B,hf.trans (congrFun he 0)⟩
    · rintro x ⟨B,rfl⟩
      exact hfVF B
  have hAcl : ∀ x ∈ F, AlgebraicAt S .vf x := by
    rintro x ⟨B,rfl⟩
    exact (algebraicAt_vf_union_rv_iff S T hT (⟨f B,hfVF B⟩ : VFType (M := M))).mp
      ⟨F,hFd,hFf,Set.mem_range_self B⟩
  obtain ⟨E,hEd,hEf,hFE⟩ := finite_definable_cover hFf hAcl
  let E' : Set (VFType (M := M)) := Subtype.val ⁻¹' E
  have hEf' : E'.Finite := hEf.preimage Subtype.val_injective.injOn
  let R := hEf'.toFinset
  have hRE : Subtype.val '' (R : Set (VFType (M := M))) = E := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact (hEf'.mem_toFinset).mp hr
    · intro hx
      let r : VFType (M := M) := ⟨x,hEd.2 hx⟩
      exact ⟨r,hEf'.mem_toFinset.mpr hx,rfl⟩
  refine ⟨R,hRE.symm ▸ hEd,?_⟩
  intro B
  let r : VFType (M := M) := ⟨f B,hfVF B⟩
  exact ⟨r,hEf'.mem_toFinset.mpr (hFE (Set.mem_range_self B)),hmem B⟩

end SpecialTransformations.Section3.ClosedBallCodes
