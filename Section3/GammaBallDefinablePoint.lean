import Section3.GammaNearestRoots
import Section3.GammaFiniteMeans
import Section3.BallDefinablePoint
import Section3.RVIndependence
import Section3.FiniteAlgebraicCover
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
open Barycentre
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma3.11 over a genuine Gamma-named base. The containing ball is not
required to be definable. Nonempty proper containment is explicit. -/
theorem lemma_3_11_gamma_base (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (A C : Set M) (hA : DefinableAtBase B .vf A) (hne : A.Nonempty)
    (hC : IsBall C) (hproper : A ⊂ C) :
    ∃ b ∈ C, DefinableClosureAtBase B .vf b := by
  let S := B.real
  obtain ⟨k,t,hAd⟩ := hA.specialize
  let T := Set.range (rawTuple t)
  have hT : ∀ x ∈ T, iRV x := by
    rintro x ⟨i,rfl⟩
    exact raw_rv (t i)
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hAN : @DefinableAt M N (S ∪ T) .vf A :=
    (definableAt_normalize_iff (S ∪ T) .vf A).mpr hAd
  have hCN : @IsBall M N C := isBall_normalize C hC
  have hDefBack (E : Set M) : @DefinableAt M N S .vf E → DefinableAt S .vf E :=
    (definableAt_normalize_iff S .vf E).mp
  let fmean : Finset (VFType (M := M)) → M := normalizedMean
  have hex : ∃ E : Set M, DefinableAt S .vf E ∧
      ∃ F : Finset (VFType (M := M)),
        Subtype.val '' (F : Set (VFType (M := M))) = @NearestRootSyntax.nearest M N E A ∧
        F.Nonempty ∧ fmean F ∈ C := by
    letI := N
    letI := hN
    obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨R₀,hR₀,hR₀d,hO,hCl⟩ := finite_definable_obstacles_both v hv (S ∪ T) A hAN
    let D : Set M := Subtype.val '' (R₀ : Set (VFType (M := M)))
    have hDf : D.Finite := R₀.finite_toSet.image Subtype.val
    have hAcl : ∀ x ∈ D, AlgebraicAt S .vf x := by
      rintro x ⟨r,hr,rfl⟩
      exact (@algebraicAt_vf_union_rv_iff M N hN S T (fun x hx => hT x hx) r).mp
        ⟨D,hR₀d,hDf,r,hr,rfl⟩
    obtain ⟨E,hEd,hEf,hDE⟩ := finite_definable_cover hDf hAcl
    let E' : Set (VFType (M := M)) := Subtype.val ⁻¹' E
    have hEf' : E'.Finite := hEf.preimage Subtype.val_injective.injOn
    let R := hEf'.toFinset
    have hRE : Subtype.val '' (R : Set (VFType (M := M))) = E := by
      ext x
      constructor
      · rintro ⟨r,hr,rfl⟩
        exact hEf'.mem_toFinset.mp hr
      · intro hx
        let r : VFType (M := M) := ⟨x,hEd.2 hx⟩
        exact ⟨r,hEf'.mem_toFinset.mpr hx,rfl⟩
    have hR₀R : R₀ ⊆ R := by
      intro r hr
      exact hEf'.mem_toFinset.mpr (hDE ⟨r,hr,rfl⟩)
    have hR : R.Nonempty := by
      obtain ⟨r,hr⟩ := hR₀
      exact ⟨r,hR₀R hr⟩
    let U : Set (VFType (M := M)) := {a | a.val ∈ A}
    let V : Set (VFType (M := M)) := {c | c.val ∈ C}
    have hU : U.Nonempty := by
      obtain ⟨a,ha⟩ := hne
      exact ⟨⟨a,hAN.2 ha⟩,ha⟩
    have hdisc : ∃ a, (∃ ρ : Balls.OpenRadius Γ, V = Balls.openDisc v a ρ) ∨
      (∃ ρ : Balls.Radius Γ, V = Balls.closedDisc v a ρ) :=
      encodedBall_disc v hv C hCN
    have hsub : ∀ a ∈ U, a ∈ V := fun a ha => hproper.1 ha
    have hprop : ∃ b ∈ V, b.val ∉ A := by
      obtain ⟨b,hb,hbA⟩ := Set.exists_of_ssubset hproper
      exact ⟨⟨b,isBall_subset_vf C hCN hb⟩,hb,hbA⟩
    have hTR : ∃ r ∈ R, r ∈ V := by
      by_contra hnot
      have hmiss : ∀ r ∈ R, r ∉ V := by simpa only [not_exists,not_and] using hnot
      have hmiss₀ : ∀ r ∈ R₀, r ∉ V := fun r hr => hmiss r (hR₀R hr)
      obtain ⟨a,ha⟩ := hU
      obtain ⟨b,hb,hbA⟩ := hprop
      obtain ⟨c, ⟨ρ, he⟩ | ⟨ρ, he⟩⟩ := hdisc
      · exact hbA ((hO c ρ (he ▸ hmiss₀) a (he ▸ hsub a ha) b (he ▸ hb)).mp ha)
      · exact hbA ((hCl c ρ (he ▸ hmiss₀) a (he ▸ hsub a ha) b (he ▸ hb)).mp ha)
    let F := Balls.nearestRoots v R U
    have hF : F.Nonempty := Balls.nearestRoots_nonempty v R hR U hU
    have hFV : ∀ x ∈ F, x ∈ V := by
      obtain ⟨c, ⟨ρ, he⟩ | ⟨ρ, he⟩⟩ := hdisc
      · rw [he]
        exact Balls.nearestRoots_mem_openDisc v R U c ρ
          (fun x hx => he ▸ hsub x hx) (he ▸ hTR)
      · rw [he]
        exact Balls.nearestRoots_mem_closedDisc v R U c ρ
          (fun x hx => he ▸ hsub x hx) (he ▸ hTR)
    have hmV : mean F ∈ V := by
      obtain ⟨c, ⟨ρ, he⟩ | ⟨ρ, he⟩⟩ := hdisc
      · rw [he]
        exact mean_mem_openDisc v hv h00N F hF c ρ (he ▸ hFV)
      · rw [he]
        exact mean_mem_closedDisc v hv h00N F hF c ρ (he ▸ hFV)
    have hFE : Subtype.val '' (F : Set (VFType (M := M))) = NearestRootSyntax.nearest E A := by
      have hh := NearestRootSyntax.nearest_eq_image v hv R A hAN.2
      rw [hRE] at hh
      exact hh.symm
    refine ⟨E,hDefBack E hEd,F,hFE,hF,?_⟩
    change (mean F).val ∈ C
    exact hmV
  obtain ⟨E,hEd,F,hFE,_,hmC⟩ := hex
  have hFd : DefinableAtBase B .vf (Subtype.val '' (F : Set (VFType (M := M)))) := by
    rw [hFE]
    exact nearest_definable_gamma_base B E A hEd hA
  exact ⟨fmean F,hmC,finite_mean_definable_base h00 B F hFd⟩

end SpecialTransformations.Section3.GammaParameters
