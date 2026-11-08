import Section8.SeparatedSets
import Section3.GammaSpecialization
import Section3.GammaValueLaws

/-! Lemma 8.1 over a genuinely imaginary Gamma base and with a radius
in the actual value-group quotient. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private def gammaDiscMem (a x : VFType (M := M)) (γ : Values.Gamma (M := M)) : Prop :=
  γ.val < Values.vfValueHom (x - a)

/-- An ordinary paper radius in the actual Gamma sort, with the paper's
strict inequality. The centre and member coordinates are all VF. -/
def gammaUniformBall {n : ℕ} (a : Fin n → M) (γ : Values.Gamma (M := M)) :
    Set (Fin n → M) :=
  {x | ∀ i, ∃ ha : iVF (a i), ∃ hx : iVF (x i),
    gammaDiscMem ⟨a i, ha⟩ ⟨x i, hx⟩ γ}

private theorem mem_rawOpenBall_iff_value (a r x : VFType (M := M)) (hr : r ≠ 0) :
    x.val ∈ rawOpenBall a.val r.val ↔ Values.vfValueHom r < Values.vfValueHom (x - a) :=
  (mem_rawOpenBall_iff Values.presentationValuation Values.presentation_compatible a r x hr).trans
    (lt_iff_not_ge.trans
      ((not_congr ((Values.presentation_compatible r (x - a)).symm.trans
        (Values.vf_pred_iff_gamma_le r (x - a)))).trans lt_iff_not_ge.symm))

/-- The choice of nonzero VF representative affects neither the ball nor
the separation condition. This uses equality of values, not RV classes. -/
theorem gammaUniformBall_eq_uniformBall {n : ℕ} (a : Fin n → M)
    (γ : Values.Gamma (M := M)) (r : VFType (M := M)) (hr : r ≠ 0)
    (hval : Values.vfValueHom r = γ.val) :
    gammaUniformBall a γ = uniformBall a r.val := by
  ext x
  constructor
  · intro hx i
    obtain ⟨ha, hxi, hi⟩ := hx i
    apply (mem_rawOpenBall_iff_value ⟨a i, ha⟩ r ⟨x i, hxi⟩ hr).mpr
    simpa only [gammaDiscMem, hval] using hi
  · intro hx i
    have hi := hx i
    refine ⟨hi.1.1 0, hi.2.1, ?_⟩
    simpa only [gammaDiscMem, hval] using
      (mem_rawOpenBall_iff_value ⟨a i, hi.1.1 0⟩ r ⟨x i, hi.2.1⟩ hr).mp hi

theorem lemma_8_1_gamma {B : GammaParameters.Base (M := M)} {n : ℕ}
    (A : Set (Fin n → M)) (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) A)
    (hsep : ∃ γ : Values.Gamma (M := M),
      A.Pairwise (fun a b => Disjoint (gammaUniformBall a γ) (gammaUniformBall b γ))) :
    A.Finite := by
  obtain ⟨γ, hγ⟩ := hsep
  obtain ⟨t, ht0, htγ⟩ := Values.gamma_has_nonzero_representative γ
  obtain ⟨r, hrt⟩ := CanonicalRV.encodedRv_surjective t
  have hr0 : r ≠ 0 := by
    intro hz
    exact ht0 ((congrArg Subtype.val hrt).symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr hz))
  have hv : Values.vfValueHom r = γ.val := (congrArg Values.vrv hrt).trans htγ
  obtain ⟨k, codes, hAr⟩ := GammaParameters.DefinableOverBase.specialize hA
  apply lemma_8_1 A hAr
  refine ⟨r.val, r.property, fun h => hr0 (Subtype.ext h), ?_⟩
  intro x hx y hy hne
  rw [← gammaUniformBall_eq_uniformBall x γ r hr0 hv, ← gammaUniformBall_eq_uniformBall y γ r hr0 hv]
  exact hγ hx hy hne

end SpecialTransformations.Section8
