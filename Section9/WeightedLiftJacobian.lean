module

public import Section9.WeightedLiftDomains
public import Section9.ImplicitJacobianIdentification
public import Section9.MixedGenericDifferentiation
public import Section7.LiftedIsomorphism

@[expose] public section

/-! The weighted lift of an essential RV isomorphism has the required
Gamma Jacobian at independent VF points. In the lower-dimensional case
of 9.16 this applies to the projected head. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF

private theorem lift_tupleRV_eq_of_sameTag {S : Set M} (U : RVObject (M := M) S n)
    (p q : rvLift U) (h : p.val.2 = q.val.2) : tupleRV p.val.1 = tupleRV q.val.1 := by
  obtain ⟨u, hu, ht⟩ := p.property
  obtain ⟨u', hu', ht'⟩ := q.property
  have he : u = u' := Subtype.ext (hu.trans (h.trans hu'.symm))
  exact ht.symm.trans (he ▸ ht')

theorem exists_weighted_liftMap_of_rvIso [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsat : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B)
    {G : Type} [LinearOrderedCommGroupWithZero G] (w : Valuation VF G)
    (hw : ∀ x y : VF, VFValued.predV x y ↔ w x ≤ w y)
    {U U' : RVObject (M := M) B.real n} (e : U ≅ U')
    (hU : ∀ u : U.domain, ∀ i, (U.value u i).val ≠ iRVZero)
    (hU' : ∀ u : U'.domain, ∀ i, (U'.value u i).val ≠ iRVZero) :
    ∃ f : Map (rvLift U) (rvLift U'), Function.Bijective f ∧
      (∀ p : rvLift U, e.hom.map.graph p.val.2 (f p).val.2) ∧
      ∀ p : rvLift U, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
        ∃ J : VF, HasMixedVFJacobianAt f p J ∧
          w J = (∏ i, w ((f p).val.1 i)) / ∏ i, w (p.val.1 i) := by
  let C := rawVolumeCorrespondence e.hom.map
  have hC₀ : ∀ z ∈ C, ∀ i, z i ≠ iRVZero := by
    rintro _ ⟨u, rfl⟩ i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      change productTuple _ _ (productLeft n n j) ≠ iRVZero
      rw [productTuple_left]
      exact hU u j
    | inr j =>
      change productTuple _ _ (productRight n n j) ≠ iRVZero
      rw [productTuple_right]
      exact hU' (e.hom.map u) j
  obtain ⟨A, hA, hGood, hWeighted⟩ := exists_lift_with_weighted_blocks w hw hκ hsat h00 B hsmall hB
    C (rawVolumeCorrespondence_definableOverBase hc B e.hom.map) hC₀
    (rawVolumeCorrespondence_left_finite e) (rawVolumeCorrespondence_right_finite e.hom)
  obtain ⟨f, hf, hGraph⟩ := exists_liftMap_of_volume_lift e A hA hGood
  refine ⟨f, hf, fun p => (hGraph p).2.2.1, ?_⟩
  intro p hp
  let a : V := p.val.1
  let b : V := (f p).val.1
  let r (x : V) : Fin n → _root_.RVCalc.RV w := fun i => _root_.RVCalc.rv w (x i)
  let t := r a
  let s := r b
  have hcode (x : V) : rawRV w hw (r x) = rvValues (tupleRV x) := by
    funext i
    change (CanonicalRV.equiv w hw (_root_.RVCalc.rv w (x i))).val = _
    exact congrArg Subtype.val (CanonicalRV.equiv_rv w hw (x i))
  have hpair : productTuple (rawRV w hw t) (rawRV w hw s) ∈ C := by
    obtain ⟨u, hu, ht⟩ := p.property
    obtain ⟨u', hu', hs⟩ := (f p).property
    obtain ⟨u₀, hu₀, hu₀'⟩ := (hGraph p).2.2.1
    have he : u₀ = u := Subtype.ext (hu₀.trans hu.symm)
    have he' : e.hom.map u₀ = u' := Subtype.ext (hu₀'.trans hu'.symm)
    change productTuple (rawRV w hw (r a)) (rawRV w hw (r b)) ∈ C
    rw [hcode, hcode, ← ht, ← hs, ← he, ← he']
    exact rawVolumeCorrespondence_mem e.hom.map u₀
  obtain ⟨H, hH⟩ := hWeighted t s hpair
  let E := vfDefinableClosureFieldBase B
  let P : Fin n → MvPolynomial (Fin (n + n)) VF := fun i => (H i).map E.subtype
  letI : Valued VF G := Valued.mk' w
  obtain ⟨L, F, hChart, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hsat hsmall hw f p hp
  have hCenter : F a = b := hChart.center
  obtain ⟨ρ, hρ⟩ := hChart
  have hFibre (x y : V) (h : tupleRV x = tupleRV y) : x ∈ RVFibre w (r y) := by
    intro i
    apply (CanonicalRV.equiv w hw).injective
    rw [CanonicalRV.equiv_rv, CanonicalRV.equiv_rv]
    exact congrFun h i
  have hLocal (x : V) (hx : x ∈ vfBall a ρ) :
      x ∈ RVFibre w t ∧ F x ∈ RVFibre w s ∧ productTuple (rawVF x) (rawVF (F x)) ∈ A := by
    obtain ⟨hxU, he⟩ := hρ x hx
    let q : rvLift U := ⟨(x, p.val.2), hxU⟩
    have hq : (f q).val = (F x, (f p).val.2) := he
    have hqx : tupleRV x = tupleRV a := lift_tupleRV_eq_of_sameTag U q p rfl
    have hqy : tupleRV (F x) = tupleRV b := by
      have htag := congrArg (fun z : V × (Fin U'.arity → CanonicalRV.RVSort M) => z.2) hq
      have ht := lift_tupleRV_eq_of_sameTag U' (f q) (f p) htag
      have hfibre := congrArg (fun z : V × (Fin U'.arity → CanonicalRV.RVSort M) => tupleRV z.1) hq
      exact hfibre.symm.trans ht
    refine ⟨hFibre x a hqx, hFibre (F x) b hqy, ?_⟩
    have ht := (hGraph q).2.2.2
    rw [hq] at ht
    exact ht
  have heq : ∀ x ∈ vfBall a ρ, ∀ i, (P i).eval (productTuple x (F x)) = 0 := by
    intro x hx
    obtain ⟨hxt, hxs, hxa⟩ := hLocal x hx
    exact (hH x hxt (F x) hxs).1.mp hxa
  obtain ⟨hat, has, haA⟩ := hLocal a (mem_vfBall_self a ρ)
  have hblocks := (hH a hat (F a) has).2 haA
  have ha₀ (i : Fin n) : a i ≠ 0 := by
    obtain ⟨u, _, htu⟩ := p.property
    intro hi
    have he := congrArg Subtype.val (congrFun htu i)
    change (U.value u i).val = (CanonicalRV.encodedRv (a i)).val at he
    rw [hi] at he
    exact hU u i (he.trans (RVCalc.rv_zero_eq ‹M ⊨ Axioms.ACVF›))
  refine ⟨(LinearMap.toMatrix' L).det, ⟨F, ⟨ρ, hρ⟩, hL.hasJacobianAt⟩, ?_⟩
  exact (vfJacobian_value_of_blocks w P F a L hL ρ heq ha₀ hblocks).trans
    (congrArg (fun y : V => (∏ i, w (y i)) / ∏ i, w (a i)) hCenter)

end SpecialTransformations.Section9
