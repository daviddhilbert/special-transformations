module

public import Section9.AffineTailJacobian
public import Section9.LiftHeadDecomposition
public import Section9.MixedJacobian

@[expose] public section

/-! Pass from the chart determinant calculation to the affine lift
with fixed RV labels. The tail parameters need only depend on the
head and its label. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k m : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)
local notation "X" => Fin k → VF
local notation "Y" => Fin m → VF
local notation "Z" => Fin (k + m) → VF

theorem det_affineLift_of_mixed_derivatives
    (U V : RVFiniteObject (M := M) S (k + m))
    (hU : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (hV : (rvHeadVolume V.obj (productLeft k m)).FiniteFibres)
    (F : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (rvLift (rvFiniteHead V (productLeft k m) hV).obj))
    (G : Map (rvLift U.obj) (rvLift V.obj))
    (a b c : rvLift (rvFiniteHead U (productLeft k m) hU).obj → Y)
    (hG : ∀ p : rvLift U.obj,
      let x := rvLiftHeadSelect U (productLeft k m) hU p
      (G p).val.1 = productTuple (F x).val.1 (affineTail (a x) (b x) (c x) (p.val.1 ∘ productRight k m)))
    (p : rvLift U.obj) (D : X →ₗ[VF] X) (L : Z →ₗ[VF] Z)
    (hD : HasMixedVFDerivativeAt F (rvLiftHeadSelect U (productLeft k m) hU p) D)
    (hL : HasMixedVFDerivativeAt G p L) :
    (LinearMap.toMatrix' L).det = (LinearMap.toMatrix' D).det *
      ∏ i, c (rvLiftHeadSelect U (productLeft k m) hU p) i := by
  classical
  let H := rvLiftHeadSelect U (productLeft k m) hU
  let W := rvLift (rvFiniteHead U (productLeft k m) hU).obj
  let x := (H p).val.1
  let t := (H p).val.2
  let y := p.val.1 ∘ productRight k m
  let J (u : X) : W := if hu : (u,t) ∈ W.carrier then ⟨(u,t),hu⟩ else H p
  have hJ : J x = H p := by
    rw [show J x = ⟨(x,t), (H p).property⟩ from dif_pos (H p).property]
    exact Subtype.ext rfl
  have hp : productTuple x y = p.val.1 := rvLift_head_tail_reconstruct U hU p
  obtain ⟨F₀, ⟨ρ, hρ⟩, hF₀⟩ := hD
  obtain ⟨G₀, ⟨σ, hσ⟩, hG₀⟩ := hL
  have he : Set.EqOn (liftWithAffineTail F₀ (a ∘ J) (b ∘ J) (c ∘ J)) G₀
      (vfBall (productTuple x y) (max ρ σ)) := by
    intro z hz
    rw [hp] at hz
    have hnear : z ∘ productLeft k m ∈ vfBall x ρ := by
      intro i
      exact (vfBall_anti (le_max_left ρ σ) hz) (productLeft k m i)
    obtain ⟨hzH, hF⟩ := hρ _ hnear
    obtain ⟨hzG, hG'⟩ := hσ _ (vfBall_anti (le_max_right ρ σ) hz)
    let q : rvLift U.obj := ⟨(z, p.val.2), hzG⟩
    have hq : H q = J (z ∘ productLeft k m) := by
      rw [show J (z ∘ productLeft k m) = ⟨(z ∘ productLeft k m,t),hzH⟩ from dif_pos hzH]
      exact Subtype.ext rfl
    have hF' : (F (H q)).val.1 = F₀ (z ∘ productLeft k m) := by
      rw [hq, show J (z ∘ productLeft k m) = ⟨(z ∘ productLeft k m,t),hzH⟩ from dif_pos hzH]
      exact congrArg Prod.fst hF
    change liftWithAffineTail F₀ (a ∘ J) (b ∘ J) (c ∘ J) z = G₀ z
    have heG := congrArg Prod.fst hG'
    change (G q).val.1 = G₀ z at heG
    rw [← heG, hG q, hF', hq]
    rfl
  have h := det_liftWithAffineTail G₀ F₀ (a ∘ J) (b ∘ J) (c ∘ J) x y L D
    (hp.symm ▸ hG₀) hF₀ (max ρ σ) he
  simpa only [Function.comp_apply, hJ] using h

end SpecialTransformations.Section9
