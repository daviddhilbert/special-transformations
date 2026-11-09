import Section9.RVFiniteHead
import Section9.LiftLabelRepresentatives

/-! The lift over a fixed head point is precisely the polydisc
specified by the complementary coordinates of the same RV label. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k m : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)

theorem rvLift_product_mem_iff_tail (U : RVFiniteObject (M := M) S (k + m))
    (h : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (p : rvLift (rvFiniteHead U (productLeft k m) h).obj) (z : Fin m → VF) :
    (productTuple p.val.1 z, p.val.2) ∈ (rvLift U.obj).carrier ↔
      tupleRV z = U.obj.value (liftLabelMap (rvFiniteHead U (productLeft k m) h).obj p) ∘ productRight k m := by
  let V := (rvFiniteHead U (productLeft k m) h).obj
  let u : U.obj.domain := liftLabelMap V p
  have hu : u.val = p.val.2 := rfl
  have hhead : U.obj.value u ∘ productLeft k m = tupleRV p.val.1 := by
    obtain ⟨u', hu', hval⟩ := p.property
    have he : u' = u := Subtype.ext (hu'.trans hu.symm)
    exact he ▸ hval
  constructor
  · rintro ⟨u', hu', hval⟩
    have he : u' = u := Subtype.ext (hu'.trans hu.symm)
    funext i
    have hi := congrFun (he ▸ hval : U.obj.value u = tupleRV (productTuple p.val.1 z)) (productRight k m i)
    simpa only [tupleRV, productTuple_right, Function.comp_apply] using hi.symm
  · intro hz
    refine ⟨u, hu, ?_⟩
    apply productTuple_ext
    · intro i
      simpa only [tupleRV, productTuple_left, Function.comp_apply] using congrFun hhead i
    · intro i
      simpa only [tupleRV, productTuple_right, Function.comp_apply, u, V] using (congrFun hz i).symm

theorem rvLift_head_tail_reconstruct (U : RVFiniteObject (M := M) S (k + m))
    (h : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres) (p : rvLift U.obj) :
    productTuple (rvLiftHeadSelect U (productLeft k m) h p).val.1 (p.val.1 ∘ productRight k m) = p.val.1 := by
  apply productTuple_ext
  · intro i
    rw [productTuple_left, rvLiftHeadSelect_apply]
    rfl
  · exact productTuple_right _ _

theorem tupleRV_tail_of_mem_rvLift (U : RVFiniteObject (M := M) S (k + m))
    (h : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres) (p : rvLift U.obj) :
    tupleRV (p.val.1 ∘ productRight k m) =
      U.obj.value (liftLabelMap (rvFiniteHead U (productLeft k m) h).obj
        (rvLiftHeadSelect U (productLeft k m) h p)) ∘ productRight k m := by
  apply (rvLift_product_mem_iff_tail U h _ _).mp
  rw [rvLift_head_tail_reconstruct]
  exact p.property

end SpecialTransformations.Section9
