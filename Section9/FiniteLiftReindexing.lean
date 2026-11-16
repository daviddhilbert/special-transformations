module

public import Section4.RVReindexing
public import Section4.RVFiniteScissors
public import Section4.CoordinateMaps
public import Section4.CanonicalLift
public import Section9.MixedGenericDifferentiation

@[expose] public section

/-! Reindex a finite-volume object and its actual lift. The VF
determinant of the coordinate change is the permutation sign. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF

noncomputable def rvFiniteReindexVolume (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    RVFiniteObject (M := M) S n :=
  ⟨U.obj.reindexVolume e, (Map.finiteFibres_of_injective (rvReindexMap_bijective S e).injective).comp U.property⟩

noncomputable def rvFiniteReindexIso (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    U ≅ rvFiniteReindexVolume U e := rvFiniteIsoOfAmbient (rvReindexVolumeIso U.obj e)

noncomputable def rvLiftReindexMap (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    Map (rvLift U.obj) (rvLift (rvFiniteReindexVolume U e).obj) :=
  (vfSelect e (rvLift U.obj)).corestrict (fun p => by
    obtain ⟨u, hu, ht⟩ := p.property
    exact ⟨u, hu, congrArg (fun z => z ∘ e) ht⟩)

@[simp] theorem rvLiftReindexMap_apply (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n))
    (p : rvLift U.obj) : (rvLiftReindexMap U e p).val = (p.val.1 ∘ e, p.val.2) := rfl

theorem rvLiftReindexMap_bijective (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    Function.Bijective (rvLiftReindexMap U e) := by
  constructor
  · intro p q he
    have h : (p.val.1 ∘ e, p.val.2) = (q.val.1 ∘ e, q.val.2) :=
      congrArg Subtype.val he
    have hlabel := congrArg (fun z : V × (Fin U.obj.arity → CanonicalRV.RVSort M) => z.2) h
    apply Subtype.ext
    apply Prod.ext
    · funext i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact congrFun (congrArg Prod.fst h) j
    · exact hlabel
  · intro q
    obtain ⟨u, hu, ht⟩ := q.property
    have hq : U.obj.value u ∘ e = tupleRV q.val.1 := ht
    let p : rvLift U.obj := ⟨(q.val.1 ∘ e.symm, q.val.2), u, hu, by
      funext i
      have he := congrFun hq (e.symm i)
      change U.obj.value u (e (e.symm i)) = CanonicalRV.encodedRv (q.val.1 (e.symm i)) at he
      change U.obj.value u i = CanonicalRV.encodedRv (q.val.1 (e.symm i))
      simpa only [e.apply_symm_apply] using he⟩
    refine ⟨p, Subtype.ext (Prod.ext ?_ rfl)⟩
    funext i
    change q.val.1 (e.symm (e i)) = q.val.1 i
    rw [e.symm_apply_apply]

noncomputable def rvLiftUnreindexMap (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n)) :=
  (rvLiftReindexMap U e).inverse (rvLiftReindexMap_bijective U e)

@[simp] theorem rvLiftUnreindexMap_apply (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n))
    (p : rvLift (rvFiniteReindexVolume U e).obj) :
    (rvLiftUnreindexMap U e p).val = (p.val.1 ∘ e.symm, p.val.2) := by
  have hp := congrArg Subtype.val (Map.apply_inverse (rvLiftReindexMap U e)
    (rvLiftReindexMap_bijective U e) p)
  change (rvLiftReindexMap U e (rvLiftUnreindexMap U e p)).val = p.val at hp
  rw [rvLiftReindexMap_apply] at hp
  have hlabel := congrArg (fun z : V × (Fin U.obj.arity → CanonicalRV.RVSort M) => z.2) hp
  refine Prod.ext (funext fun i => ?_) hlabel
  have h := congrFun (congrArg Prod.fst hp) (e.symm i)
  change (rvLiftUnreindexMap U e p).val.1 (e (e.symm i)) = p.val.1 (e.symm i) at h
  rwa [e.apply_symm_apply] at h

theorem rvLiftUnreindexMap_bijective (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    Function.Bijective (rvLiftUnreindexMap U e) :=
  (Equiv.ofBijective (rvLiftReindexMap U e) (rvLiftReindexMap_bijective U e)).symm.bijective

noncomputable def vfReindexLinear (e : Equiv.Perm (Fin n)) : V →ₗ[VF] V :=
  LinearMap.pi fun i => LinearMap.proj (e i)

theorem det_vfReindexLinear (e : Equiv.Perm (Fin n)) :
    (LinearMap.toMatrix' (vfReindexLinear (M := M) e)).det = (Equiv.Perm.sign e : VF) := by
  classical
  have hM : LinearMap.toMatrix' (vfReindexLinear (M := M) e) =
      (1 : Matrix (Fin n) (Fin n) VF).submatrix e id := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change (Pi.single j (1 : VF) : V) (e i) = (1 : Matrix (Fin n) (Fin n) VF) (e i) j
    simp only [Pi.single_apply, Matrix.one_apply]
  rw [hM, Matrix.det_permute, Matrix.det_one, mul_one]

theorem hasMixedVFDerivativeAt_liftReindex_of_independent [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued VF Γ]
    (hv : ∀ a b : VF, VFValued.predV a b ↔ Valued.v a ≤ Valued.v b)
    (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n)) (p : rvLift U.obj)
    (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
    HasMixedVFDerivativeAt (rvLiftReindexMap U e) p (vfReindexLinear e) := by
  obtain ⟨_, _, ⟨ρ, hρ⟩, _⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv (rvLiftReindexMap U e) p hp
  refine ⟨fun x => x ∘ e, ⟨ρ, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨h, _⟩ := hρ x hx
    exact ⟨h, rfl⟩
  · change HasVFDerivativeAt (fun x => vfReindexLinear e x) p.val.1 (vfReindexLinear e)
    simpa only [add_zero] using hasVFDerivativeAt_affine (vfReindexLinear e) 0 p.val.1

theorem hasMixedVFDerivativeAt_liftUnreindex_of_independent [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued VF Γ]
    (hv : ∀ a b : VF, VFValued.predV a b ↔ Valued.v a ≤ Valued.v b)
    (U : RVFiniteObject (M := M) S n) (e : Equiv.Perm (Fin n))
    (p : rvLift (rvFiniteReindexVolume U e).obj)
    (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
    HasMixedVFDerivativeAt (rvLiftUnreindexMap U e) p (vfReindexLinear e.symm) := by
  obtain ⟨_, _, ⟨ρ, hρ⟩, _⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv (rvLiftUnreindexMap U e) p hp
  refine ⟨fun x => vfReindexLinear e.symm x, ⟨ρ, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨h, _⟩ := hρ x hx
    refine ⟨h, ?_⟩
    rw [rvLiftUnreindexMap_apply, rvLiftUnreindexMap_apply]
    rfl
  · simpa only [add_zero] using hasVFDerivativeAt_affine (vfReindexLinear e.symm) 0 p.val.1

end SpecialTransformations.Section9
