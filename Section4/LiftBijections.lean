import Section4.LiftFibres
import Section4.RVWeightDimension
import Section4.MapCorestrict
import Section3.SmallFiniteParameters

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ} {U V : RVObject (M := M) S k}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

/-- An injective definable commuting lift already forces the weight
inequality required of an RV morphism. -/
theorem lift_injective_volumetric (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : Map U.domain V.domain) (G : Map (rvLift U) (rvLift V))
    (hcomm : LiftCommutes F G) (hinj : Function.Injective G) (u : U.domain) :
    rvWeight (U.value u) ≤ rvWeight (V.value (F u)) := by
  let T := (S ∪ Set.range (rvValues u.val)) ∪ Set.range (rvValues (F u).val)
  have hT : Cardinal.mk T < κ := small_union_range hκ _
    (small_union_range hκ S hsmall (rvValues u.val)) (rvValues (F u).val)
  have hST : S ⊆ T := fun _ h => Or.inl (Or.inl h)
  have hVT : S ∪ Set.range (rvValues (F u).val) ⊆ T := by
    rintro x (hx | hx)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  let A := (liftFibre U u).extend (show S ∪ Set.range (rvValues u.val) ⊆ T from Set.subset_union_left)
  let B := (liftFibre V (F u)).extend hVT
  have hA (p : (rawMixedSpace (M := M) k U.arity).Carrier) :
      p ∈ A.carrier ↔ tupleRV p.1 = U.value u ∧ p.2 = u.val := mem_liftFibre U u p
  have hB (p : (rawMixedSpace (M := M) k V.arity).Carrier) :
      p ∈ B.carrier ↔ tupleRV p.1 = V.value (F u) ∧ p.2 = (F u).val := mem_liftFibre V (F u) p
  have hsub : A.carrier ⊆ ((rvLift U).extend hST).carrier := by
    intro p hp
    exact (mem_tailFibre (rvLift U) u.val p).mp hp |>.1
  let H := (G.extend hST).restrict hsub
  have htarget (a : A) : (H a).val ∈ B.carrier := by
    apply (hB _).mpr
    have h := hcomm ⟨a.val, hsub a.property⟩ u ((hA _).mp a.property).2
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  let J : Map A B := H.corestrict htarget
  have hJ : Function.Injective J := by
    intro a b he
    apply Subtype.ext
    have he' : G ⟨a.val, hsub a.property⟩ = G ⟨b.val, hsub b.property⟩ :=
      Subtype.ext (congrArg (fun y : B => y.val) he)
    exact congrArg (fun y : rvLift U => y.val) (hinj he')
  have hdA := vfDim_rv_polydisc hcan hs hT Δ hΔ hv A (U.value u) u.val hA
  have hdB := vfDim_rv_polydisc hcan hs hT Δ hΔ hv B (V.value (F u)) (F u).val hB
  rw [← hdA, ← hdB]
  exact vfDim_le_of_finite_map Δ J (Map.finiteFibres_of_injective hJ)

/-- Lemma 4.20; the stronger injectivity premise for G suffices for the
morphism conclusion, so in particular a definable bijective lift suffices. -/
theorem lemma_4_20 (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : Map U.domain V.domain) (G : Map (rvLift U) (rvLift V))
    (hcomm : LiftCommutes F G) (hinj : Function.Injective G) :
    ∃ H : RVHom U V, H.map = F :=
  lemma_4_19 hcan hκ hs hsmall F G hcomm
    (lift_injective_volumetric hcan hκ hs hsmall Δ hΔ hv F G hcomm hinj)

end SpecialTransformations.Section4

end
