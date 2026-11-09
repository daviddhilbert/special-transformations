import Section9.AffineTailMaps
import Section9.AppendTailMap
import Section9.LiftHeadDecomposition
import Section4.CoordinateMaps

/-! Extend the actual same-base head lift by the guarded affine tail.
The construction retains the labels and is a bijection on the whole
source, including heads on the derivative exception. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {k m : ℕ}
local notation "VF" => VFType (M := M)

theorem exists_affineLift_of_headLift
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {S : Set M} (U V : RVFiniteObject (M := M) S (k + m))
    (hU : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (hV : (rvHeadVolume V.obj (productLeft k m)).FiniteFibres)
    (F : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (rvLift (rvFiniteHead V (productLeft k m) hV).obj)) (hF : Function.Bijective F)
    (a b : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) m) S))
    (D c : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) 1) S)) (j : Fin m)
    (ha : ∀ p i, (a p).val i ≠ 0) (hb : ∀ p i, (b p).val i ≠ 0)
    (haRV : ∀ p, tupleRV (a p).val = U.obj.value
      (liftLabelMap (rvFiniteHead U (productLeft k m) hU).obj p) ∘ productRight k m)
    (hbRV : ∀ p, tupleRV (b p).val = V.obj.value
      (liftLabelMap (rvFiniteHead V (productLeft k m) hV).obj (F p)) ∘ productRight k m) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧
      ∀ p : rvLift U.obj,
        let x := rvLiftHeadSelect U (productLeft k m) hU p
        (G p).val = (productTuple (F x).val.1
          (affineTail (a x).val (b x).val
            (affineTailSlopesForHead v (a x).val (b x).val j ((D x).val 0) ((c x).val 0))
            (p.val.1 ∘ productRight k m)), (F x).val.2) := by
  let l := productLeft k m
  let r := productRight k m
  let U₁ := (rvFiniteHead U l hU).obj
  let V₁ := (rvFiniteHead V l hV).obj
  let H := rvLiftHeadSelect U l hU
  let H' := rvLiftHeadSelect V l hV
  let X := rvLift U.obj
  let Y := rvLift V.obj
  let Q := rawVFSpace (M := M) (k + m)
  let q := Map.fst Q (rawRVSpace U.obj.arity) S X
  let tail : Map X (DefSet.univ (rawVFSpace (M := M) m) S) := by
    let W := rawVFSpace (M := M) m
    let f : Q.Carrier → W.Carrier := fun z => z ∘ r
    have hcode (z : Q.domain) : vfValues (f (Q.decode z)) = z.val ∘ r := by
      funext i
      exact congrFun (vfValues_decode z) (r i)
    let P := Map.ofCodes (DefSet.univ Q S) f (fun z => z ∘ r)
      (fun _ => Set.DefinableFun.proj LRV) (fun z => ⟨f (Q.decode z), hcode z⟩)
      (fun z => vfValues_injective ((vfValues_decode _).trans (hcode z).symm))
    exact P.comp q
  have htail (p : X) : (tail p).val = p.val.1 ∘ r := rfl
  obtain ⟨L, hL⟩ := exists_affineTailMap v hv (a.comp H) (b.comp H) tail (D.comp H) (c.comp H) j
    (fun p => ha (H p)) (fun p => hb (H p))
  let B (p : rvLift U₁) := affineTail (a p).val (b p).val
    (affineTailSlopesForHead v (a p).val (b p).val j ((D p).val 0) ((c p).val 0))
  let W (p : rvLift U₁) := {z : Fin m → VF | tupleRV z = U.obj.value (liftLabelMap U₁ p) ∘ r}
  let W' (p : rvLift V₁) := {z : Fin m → VF | tupleRV z = V.obj.value (liftLabelMap V₁ p) ∘ r}
  have hB (p : rvLift U₁) : Set.BijOn (B p) (W p) (W' (F p)) := by
    have hfibre (z : Fin m → VF) :
        RVFibre v (fun i => RVCalc.rv v (z i)) = {w | tupleRV w = tupleRV z} := by
      ext w
      constructor
      · intro h
        funext i
        exact ((CanonicalRV.equiv_rv v hv (w i)).symm.trans
          (congrArg (CanonicalRV.equiv v hv) (h i))).trans (CanonicalRV.equiv_rv v hv (z i))
      · intro h i
        apply (CanonicalRV.equiv v hv).injective
        rw [CanonicalRV.equiv_rv, CanonicalRV.equiv_rv]
        exact congrFun h i
    have hh := (affineTailSlopesForHead_spec v (a p).val (b p).val j ((D p).val 0) ((c p).val 0)
      (ha p) (hb p)).1
    rw [hfibre, hfibre, haRV p, hbRV p] at hh
    exact hh
  let G₀ := appendTailMap (F.comp H) L
  have hG₀ (p : X) : (G₀ p).val = (productTuple (F (H p)).val.1 (B (H p) (p.val.1 ∘ r)), (F (H p)).val.2) := by
    rw [appendTailMap_apply, hL p, htail p]
    rfl
  have hGY (p : X) : (G₀ p).val ∈ Y.carrier := by
    rw [hG₀]
    exact (rvLift_product_mem_iff_tail V hV _ _).mpr
      ((hB (H p)).mapsTo (tupleRV_tail_of_mem_rvLift U hU p))
  let G := G₀.corestrict hGY
  have hG (p : X) : (G p).val = (productTuple (F (H p)).val.1 (B (H p) (p.val.1 ∘ r)), (F (H p)).val.2) := hG₀ p
  have hHead (p : X) : H' (G p) = F (H p) := by
    apply Subtype.ext
    rw [rvLiftHeadSelect_apply, hG]
    exact Prod.ext (funext (productTuple_left _ _)) rfl
  have hTail (p : X) : (G p).val.1 ∘ r = B (H p) (p.val.1 ∘ r) := by
    rw [hG]
    exact funext (productTuple_right _ _)
  refine ⟨G, ⟨?_, ?_⟩, hG⟩
  · intro p p' he
    have hh : H p = H p' := hF.injective ((hHead p).symm.trans (he ▸ hHead p'))
    have ht : p.val.1 ∘ r = p'.val.1 ∘ r := by
      apply (hB (H p)).injOn (tupleRV_tail_of_mem_rvLift U hU p)
      · rw [hh]
        exact tupleRV_tail_of_mem_rvLift U hU p'
      · calc
          _ = (G p).val.1 ∘ r := (hTail p).symm
          _ = (G p').val.1 ∘ r := congrArg (fun q : Y => q.val.1 ∘ r) he
          _ = _ := hh.symm ▸ hTail p'
    apply Subtype.ext
    apply Prod.ext
    · rw [← rvLift_head_tail_reconstruct U hU p, ← rvLift_head_tail_reconstruct U hU p', hh, ht]
    · exact congrArg (fun z : rvLift U₁ => z.val.2) hh
  · intro y
    obtain ⟨x, hx⟩ := hF.surjective (H' y)
    have hy : y.val.1 ∘ r ∈ W' (F x) := by
      rw [hx]
      exact tupleRV_tail_of_mem_rvLift V hV y
    obtain ⟨z, hz, hzy⟩ := (hB x).surjOn hy
    let p : X := ⟨(productTuple x.val.1 z, x.val.2), (rvLift_product_mem_iff_tail U hU x z).mpr hz⟩
    have hp : H p = x := by
      apply Subtype.ext
      rw [rvLiftHeadSelect_apply]
      exact Prod.ext (funext (productTuple_left _ _)) rfl
    have hpz : p.val.1 ∘ r = z := funext (productTuple_right _ _)
    refine ⟨p, Subtype.ext ?_⟩
    rw [hG, hp, hpz, hx, hzy, rvLift_head_tail_reconstruct V hV y]
    rfl

end SpecialTransformations.Section9
