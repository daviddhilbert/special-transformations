import Section9.SpecialJacobian
import Section9.MixedGenericDifferentiation
import Section5.PullbackLift
import Section8.GammaRadiusBase

/-! The derivative calculation along an actual Section 5 special chain.
The map is recoded on the raw mixed presentation to apply the
independent-point theorem without changing its underlying function. -/

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawMixedSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF

noncomputable def rawSpecialSet (hc : CanonicalStructure.IsCanonical (M := M))
    (A : Section5.DefSet (M := M) S n r) : DefSet (rawMixedSpace (M := M) n r) S := by
  let N := CanonicalStructure.normalize (M := M)
  letI : LRV.Structure M := sM
  let P := Section5.rawPointSpace (M := M) n r
  let D := Section5.Map.image (Section5.rawPointMap A)
  let C : Set (Section5.Point (M := M) n r) := Section5.carrier A
  let U := (rawMixedSpace (M := M) n r).preimage C
  have hEq : Section5.carrier D = C := by
    ext p
    exact ⟨fun ⟨a, h⟩ => h ▸ a.property, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
  have hD' : Section5.SetDefinable P S C :=
    Eq.mp (congrArg (Section5.SetDefinable P S) hEq) (Section5.setDefinable D)
  have hD : @Set.Definable M S LRV N (Fin n ⊕ Fin r) U := hD'
  exact ⟨C, Eq.mp (congrArg (fun T : LRV.Structure M =>
    @Set.Definable M S LRV T (Fin n ⊕ Fin r) U) (normalize_eq_of_isCanonical hc)) hD⟩

noncomputable def rawSpecialMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : Section5.DefSet (M := M) S n r} {B : Section5.DefSet (M := M) S n s}
    (f : Section5.Map A B) : Map (rawSpecialSet hc A) (rawSpecialSet hc B) := by
  let a := Section5.Map.toImage (Section5.rawPointMap A)
  let b := Section5.Map.toImage (Section5.rawPointMap B)
  have ha : Function.Bijective a := by
    constructor
    · intro x y h
      have he := congrArg Subtype.val h
      exact Subtype.ext he
    · rintro ⟨p, x, rfl⟩
      exact ⟨x, rfl⟩
  let q := Section5.Map.comp b (Section5.Map.comp f (Section5.Map.inverse a ha))
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n s
  let R (x : P.Carrier) (y : Q.Carrier) := ∃ u : A, u.val = x ∧ (f u).val = y
  let N := CanonicalStructure.normalize (M := M)
  letI : LRV.Structure M := sM
  let RN (x : P.Carrier) (y : Q.Carrier) := ∃ u, u.val = x ∧ (q u).val = y
  let H := P.relation Q R
  let HN := @Space.relation LRV M N
    (Section5.rawPointSpace (M := M) n r) (Section5.rawPointSpace (M := M) n s) RN
  have he : H = HN := by
    ext z
    change (∃ hx : z ∘ Sum.inl ∈ P.domain, ∃ hy : z ∘ Sum.inr ∈ Q.domain,
      R (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode ⟨z ∘ Sum.inr, hy⟩)) ↔
      (∃ hx : z ∘ Sum.inl ∈ P.domain, ∃ hy : z ∘ Sum.inr ∈ Q.domain,
        RN (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode ⟨z ∘ Sum.inr, hy⟩))
    refine exists_congr (fun hx => exists_congr fun hy => ?_)
    constructor
    · rintro ⟨p, hp, hf⟩
      refine ⟨a p, hp, ?_⟩
      have hq : (q (a p)).val = (f p).val := by
        change (f (Section5.Map.inverse a ha (a p))).val = (f p).val
        rw [Section5.Map.inverse_apply]
      exact hq.trans hf
    · rintro ⟨p, hp, hf⟩
      let p' := Section5.Map.inverse a ha p
      have hp' : p'.val = p.val := congrArg Subtype.val (Section5.Map.apply_inverse a ha p)
      exact ⟨p', hp'.trans hp, hf⟩
  have h : @Set.Definable M S LRV N ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) H := by
    rw [he]
    exact Section5.Map.graph_definable q
  refine ⟨fun p => f (show A from p), ?_⟩
  exact Eq.mp (congrArg (fun T : LRV.Structure M =>
    @Set.Definable M S LRV T ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) H)
      (normalize_eq_of_isCanonical hc)) h

private theorem det_eq_one_of_preservesVF
    {A : Set ((Fin n → VF) × (Fin r → CanonicalRV.RVSort M))}
    {B : Set ((Fin n → VF) × (Fin s → CanonicalRV.RVSort M))}
    (f : A → B) (p : A) {L : V →ₗ[VF] V}
    (hL : HasMixedVFDerivativeAt f p L) (h : ∀ p, (f p).val.1 = p.val.1) :
    (LinearMap.toMatrix' L).det = 1 := by
  obtain ⟨F, ⟨ρ, hρ⟩, hF⟩ := hL
  have he : Set.EqOn F id (vfBall p.val.1 ρ) := by
    intro x hx
    obtain ⟨hp, hFx⟩ := hρ x hx
    exact (congrArg Prod.fst hFx).symm.trans (h ⟨(x, p.val.2), hp⟩)
  have hId : HasVFDerivativeAt id p.val.1 LinearMap.id := by
    change HasVFDerivativeAt (fun x : V => x) p.val.1 LinearMap.id
    simpa only [LinearMap.id_apply, add_zero] using
      hasVFDerivativeAt_affine (LinearMap.id : V →ₗ[VF] V) 0 p.val.1
  rw [(hF.congr_on_vfBall he).unique hId, LinearMap.toMatrix'_id, Matrix.det_one]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VFType (M := M)) G]

/-- The forward special chain has determinant one on VF-independent
points. This proof uses the actual primitive transformations of Section 5. -/
theorem specialChain_det_one_of_independent [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Section5.DefSet (M := M) S n r} {B : Section5.DefSet (M := M) S n s}
    (c : Section5.Chain S n A B) (p : A)
    (hp : AlgebraicIndependent (vfParameterField S) (show V from p.val.1)) :
    ∃ L : V →ₗ[VF] V, HasMixedVFDerivativeAt c.toMap p L ∧ (LinearMap.toMatrix' L).det = 1 := by
  revert p
  induction c with
  | nil A =>
    intro p hp
    obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv
      (rawSpecialMap hc (Section5.Map.id A)) p hp
    exact ⟨L, hL, det_eq_one_of_preservesVF _ _ hL (fun _ => rfl)⟩
  | cons f tail ih =>
    intro p hp
    let f' := rawSpecialMap hc f.toMap
    obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f' p hp
    have hdet : (LinearMap.toMatrix' L).det = 1 := by
      cases f with
      | canonical _ => exact det_eq_one_of_preservesVF _ _ hL (fun _ => rfl)
      | centripetal D => exact centripetal_det_eq_one D p hL
    have h' := independent_map_of_finiteFibres hc f'
      (Map.finiteFibres_of_injective f.bijective.1) p hp
    obtain ⟨D, hD, hd⟩ := ih (f.toMap p) h'
    obtain ⟨F, hF, hf⟩ := hL
    obtain ⟨H, hH, hg⟩ := hD
    have hchain : HasVFDerivativeAt H (F p.val.1) D := hF.center.symm ▸ hg
    refine ⟨D.comp L, ⟨H ∘ F, hF.comp hH hf, hchain.comp hf⟩, ?_⟩
    rw [LinearMap.toMatrix'_comp, Matrix.det_mul, hd, hdet, mul_one]

/-- The inverse special bijection has determinant one at VF-independent
points of its target. -/
theorem specialInverse_det_one_of_independent [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Section5.DefSet (M := M) S n r} {B : Section5.DefSet (M := M) S n s}
    (T : Section5.SpecialBijection A B) (p : B)
    (hp : AlgebraicIndependent (vfParameterField S) (show V from p.val.1)) :
    ∃ L : V →ₗ[VF] V, HasMixedVFDerivativeAt T.inverseMap p L ∧ (LinearMap.toMatrix' L).det = 1 := by
  let g := rawSpecialMap hc T.inverseMap
  have hg_inj : Function.Injective g := by
    intro x y h
    change T.inverseMap x = T.inverseMap y at h
    have he := congrArg (fun a : A => T.toMap a) h
    simpa only [Section5.SpecialBijection.apply_inverse] using he
  have hq := independent_map_of_finiteFibres hc g (Map.finiteFibres_of_injective hg_inj) p hp
  obtain ⟨D, F, hF, hf⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv g p hp
  obtain ⟨L, ⟨H, hH, hh⟩, hL⟩ := specialChain_det_one_of_independent hc hκ hs hsmall hv
    T.chain (T.inverseMap p) hq
  have hH' : HasVFDerivativeAt H (F p.val.1) L := hF.center.symm ▸ hh
  have he : T.toMap ∘ T.inverseMap = id := funext T.apply_inverse
  have hcomp : HasMixedVFDerivativeAt (T.toMap ∘ T.inverseMap) p (L.comp D) :=
    ⟨H ∘ F, hF.comp hH hf, hH'.comp hf⟩
  have hd := det_eq_one_of_preservesVF _ p hcomp (fun x => congrArg
    (fun b : B => b.val.1) (congrFun he x))
  rw [LinearMap.toMatrix'_comp, Matrix.det_mul, hL, one_mul] at hd
  exact ⟨D, ⟨F, hF, hf⟩, hd⟩

end SpecialTransformations.Section9
