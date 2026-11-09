import Section4.RVFiniteScissors
import Section7.LiftedIsomorphism
import Section9.MixedJacobian

/-! Restrict an RV isomorphism along a source-label cut and its image.
The fixed-label Jacobian of a map on the restricted lift is unchanged
by gluing it with maps on other labels. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {U V : RVObject (M := M) S n}

theorem rvLabelImage_subset (e : U ≅ V)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    (e.hom.map.restrict hA).image.carrier ⊆ V.domain.carrier := by
  rintro z ⟨a, ha⟩
  rw [← ha]
  exact (e.hom.map.restrict hA a).property

noncomputable def rvIsoRestrict (e : U ≅ V)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    U.restrict A hA ≅
      V.restrict (e.hom.map.restrict hA).image (rvLabelImage_subset e A hA) where
  hom := e.hom.restrict A hA _ _ (fun a => Set.mem_range_self a)
  inv := e.inv.restrict _ _ A hA (by
    rintro ⟨v, a, rfl⟩
    change (e.inv.map (e.hom.map ⟨a.val, hA a.property⟩)).val ∈ A.carrier
    rw [rvIso_inv_apply]
    exact a.property)
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro a
    apply Subtype.ext
    change (e.inv.map (e.hom.map ⟨a.val, hA a.property⟩)).val = a.val
    rw [rvIso_inv_apply]
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro v
    apply Subtype.ext
    change (e.hom.map (e.inv.map ⟨v.val, _⟩)).val = v.val
    rw [rvIso_apply_inv]

theorem HasMixedVFJacobianAt.of_label_restriction
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)
    {B : DefSet (rawMixedSpace (M := M) n V.arity) S}
    (f : Map (rvLift (U.restrict A hA)) B)
    (g : Map (rvLift U) (rvLift V))
    (p : rvLift (U.restrict A hA)) (q : rvLift U) (hpq : p.val = q.val)
    (hagree : ∀ (p' : rvLift (U.restrict A hA)) (q' : rvLift U), p'.val = q'.val →
      (f p').val = (g q').val)
    {J} (hJ : HasMixedVFJacobianAt f p J) : HasMixedVFJacobianAt g q J := by
  obtain ⟨F, ⟨ρ, hρ⟩, hJ⟩ := hJ
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  refine ⟨F, ⟨ρ, fun x hx => ?_⟩, h₁ ▸ hJ⟩
  obtain ⟨hxA, hxF⟩ := hρ x (h₁.symm ▸ hx)
  let a : rvLift (U.restrict A hA) := ⟨(x, p.val.2), hxA⟩
  have hxU : (x, q.val.2) ∈ (rvLift U).carrier :=
    h₂ ▸ ((rvLift_restrict_mem_iff U A hA _).mp hxA).1
  let b : rvLift U := ⟨(x, q.val.2), hxU⟩
  have hab := hagree a b (Prod.ext rfl h₂)
  have he := hagree p q hpq
  refine ⟨hxU, ?_⟩
  change (g b).val = _
  rw [← hab, hxF, congrArg Prod.snd he]

end SpecialTransformations.Section9
