import Section4.FullDimension
import Section4.CoordinateMaps
import Section4.CanonicalLift

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def zeroPrefix (n : ℕ) {k : ℕ} (a : Fin k → VFType (M := M)) :
    Fin (n + k) → VFType (M := M) := Fin.addCases (fun _ => 0) a

theorem zeroPrefix_tail (n : ℕ) {k : ℕ} (a : Fin k → VFType (M := M)) :
    zeroPrefix n a ∘ Fin.natAdd n = a := by
  funext i
  simp only [zeroPrefix, Function.comp_apply, Fin.addCases_right]

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

/-- Corollary 4.7 in its zero-prefix form. The fixed RV tuples need not be
named in S: the definable coordinate image is formed over S, and the
polydisc lower bound is applied to that image. -/
theorem corollary_4_7 (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n k r : ℕ} (A : DefSet (rawMixedSpace (M := M) (n + k) r) S)
    (t : Fin k → CanonicalRV.RVSort M) (ht : ∀ i, (t i).val ≠ iRVZero)
    (s : Fin r → CanonicalRV.RVSort M)
    (hcontains : ∀ a : Fin k → VFType (M := M), tupleRV a = t →
      (zeroPrefix n a, s) ∈ A.carrier) : k ≤ vfDim Δ A := by
  obtain ⟨c, hc⟩ := tupleRV_surjective t
  have hc0 (i : Fin k) : c i ≠ 0 := by
    intro hz
    apply ht i
    exact (congrArg Subtype.val (congrFun hc i)).symm.trans
      ((CanonicalRV.encodedRv_zero_iff (c i)).mpr hz)
  let D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) k := ⟨c, c, hc0⟩
  have hRV (x : Fin k → VFType (M := M)) (hx : x ∈ D.carrier) : tupleRV x = t := by
    have he : tupleRV x = tupleRV c := by
      funext i
      apply Subtype.ext
      apply (CanonicalRV.encoded_eq_iff_close (x i).property (c i).property
        (fun h => hc0 i (Subtype.ext h))).mpr
      change ¬ VFValued.predV (c i) (x i - c i)
      rw [hv, not_le]
      exact hx i
    exact he.trans hc
  let f := vfSelect (Fin.natAdd n) A
  let B := f.image
  have hdisc : ∀ x ∈ D.carrier, (x, s) ∈ B.carrier := by
    intro x hx
    let a : A := ⟨(zeroPrefix n x, s), hcontains x (hRV x hx)⟩
    refine ⟨a, ?_⟩
    change (zeroPrefix n x ∘ Fin.natAdd n, s) = (x, s)
    exact Prod.ext (zeroPrefix_tail n x) rfl
  have hd : vfDim Δ B = k :=
    vfDim_eq_arity_of_contains_polydisc hcan hs hsmall Δ hΔ hv B s D hdisc
  have hle : vfDim Δ B ≤ vfDim Δ A := vfDim_image_le hcan hs hsmall Δ hΔ f
  rwa [hd] at hle

end SpecialTransformations.Section4

end
