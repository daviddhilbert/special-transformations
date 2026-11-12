module

public import Section4.FullDimension
public import Section4.CoordinateMaps
public import Section4.RVCategories
public import Section4.VFCategories
public import Section4.CanonicalLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

/-- An actual RV-polydisc with fixed RV tail has VF dimension equal to
the number of nonabsorbing coordinates. The definable set and its parameter
base are explicit; no definability of the labels over that base is presumed. -/
theorem vfDim_rv_polydisc (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S)
    (t : Fin n → CanonicalRV.RVSort M) (s : Fin r → CanonicalRV.RVSort M)
    (hA : ∀ p, p ∈ A.carrier ↔ tupleRV p.1 = t ∧ p.2 = s) :
    vfDim Δ A = rvWeight t := by
  classical
  let I := {i : Fin n // (t i).val ≠ iRVZero}
  let d := Fintype.card I
  let e : Fin d ≃ I := (Fintype.equivFin I).symm
  let v : Fin d → Fin n := fun i => (e i).val
  have hd : d = rvWeight t := by
    rw [rvWeight_eq_card]
    exact Fintype.card_subtype _
  let f := vfSelect v A
  have hzero (a : A) (j : Fin n) (hj : (t j).val = iRVZero) : a.val.1 j = 0 := by
    apply (CanonicalRV.encodedRv_zero_iff _).mp
    exact (congrArg Subtype.val (congrFun ((hA a.val).mp a.property).1 j)).trans hj
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases hj : (t j).val ≠ iRVZero
      · let i := e.symm ⟨j, hj⟩
        have hvi : v i = j := congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)
        have h := congrArg (fun y => y.val.1 i) he
        change a.val.1 (v i) = b.val.1 (v i) at h
        simpa only [hvi] using h
      · rw [hzero a j (not_ne_iff.mp hj), hzero b j (not_ne_iff.mp hj)]
    · exact ((hA a.val).mp a.property).2.trans ((hA b.val).mp b.property).2.symm
  have hupper : vfDim Δ A ≤ d :=
    (vfDim_le_of_finite_map Δ f (Map.finiteFibres_of_injective hinj)).trans
      (vfDim_le_arity Δ (DefSet.univ (rawMixedSpace d r) S))
  obtain ⟨c, hc⟩ := tupleRV_surjective (t ∘ v)
  have hc0 (i : Fin d) : c i ≠ 0 := by
    intro hz
    apply (e i).property
    exact (congrArg Subtype.val (congrFun hc i)).symm.trans
      ((CanonicalRV.encodedRv_zero_iff _).mpr hz)
  let D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) d := ⟨c, c, hc0⟩
  have hrv (x : Fin d → VFType (M := M)) (hx : x ∈ D.carrier) : tupleRV x = t ∘ v := by
    have he : tupleRV x = tupleRV c := by
      funext i
      apply Subtype.ext
      apply (CanonicalRV.encoded_eq_iff_close (x i).property (c i).property
        (fun h => hc0 i (Subtype.ext h))).mpr
      change ¬ VFValued.predV (c i) (x i - c i)
      rw [hv, not_le]
      exact hx i
    exact he.trans hc
  let fill (x : Fin d → VFType (M := M)) (j : Fin n) : VFType (M := M) :=
    if hj : (t j).val ≠ iRVZero then x (e.symm ⟨j, hj⟩) else 0
  have hfill (x : Fin d → VFType (M := M)) : fill x ∘ v = x := by
    funext i
    simp only [Function.comp_apply, fill, v, dif_pos (e i).property]
    exact congrArg x (e.symm_apply_apply i)
  have hfillrv (x : Fin d → VFType (M := M)) (hx : tupleRV x = t ∘ v) :
      tupleRV (fill x) = t := by
    funext j
    apply Subtype.ext
    by_cases hj : (t j).val ≠ iRVZero
    · simp only [tupleRV, fill, dif_pos hj]
      have h := congrArg Subtype.val (congrFun hx (e.symm ⟨j, hj⟩))
      simpa only [tupleRV, Function.comp_apply, v, e.apply_symm_apply] using h
    · simp only [tupleRV, fill, dif_neg hj]
      exact ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl).trans
        (not_ne_iff.mp hj).symm
  have hdisc : ∀ x ∈ D.carrier, (x, s) ∈ f.image.carrier := by
    intro x hx
    let a : A := ⟨(fill x, s), (hA _).mpr ⟨hfillrv x (hrv x hx), rfl⟩⟩
    refine ⟨a, ?_⟩
    exact Prod.ext (hfill x) rfl
  have hdim : vfDim Δ f.image = d :=
    vfDim_eq_arity_of_contains_polydisc hcan hs hsmall Δ hΔ hv f.image s D hdisc
  have hlower : d ≤ vfDim Δ A := by
    rw [← hdim]
    exact vfDim_image_le hcan hs hsmall Δ hΔ f
  exact (hupper.antisymm hlower).trans hd

end SpecialTransformations.Section4

end
