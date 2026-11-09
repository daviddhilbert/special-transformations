import Section9.LiftRestriction
import Section9.LiftLabelRepresentatives

/-! A bijection lifting an RV isomorphism restricts to a bijection
between the corresponding label cuts. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {U V : RVObject (M := M) S n}

theorem exists_restricted_actual_lift
    (e : U ≅ V) (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)
    (f : Map (rvLift U) (rvLift V)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U, e.hom.map.graph p.val.2 (f p).val.2) :
    let B := (e.hom.map.restrict hA).image
    let hB := rvLabelImage_subset e A hA
    ∃ g : Map (rvLift (U.restrict A hA)) (rvLift (V.restrict B hB)), Function.Bijective g ∧
      ∀ (p : rvLift (U.restrict A hA)) (q : rvLift U), p.val = q.val → (g p).val = (f q).val := by
  let B := (e.hom.map.restrict hA).image
  let hB := rvLabelImage_subset e A hA
  let hdom : (rvLift (U.restrict A hA)).carrier ⊆ (rvLift U).carrier :=
    fun p hp => ((rvLift_restrict_mem_iff U A hA p).mp hp).1
  let i (p : rvLift (U.restrict A hA)) : rvLift U := ⟨p.val, hdom p.property⟩
  have hlabel' (p : rvLift U) :
      (e.hom.map (liftLabelMap U p)).val = (f p).val.2 := (e.hom.map.graph_apply _ _).mp (hlabel p)
  have hcod (p : rvLift (U.restrict A hA)) : (f.restrict hdom p).val ∈ (rvLift (V.restrict B hB)).carrier := by
    have hlabel_mem := ((rvLift_restrict_mem_iff U A hA p.val).mp p.property).2
    let u : A := ⟨p.val.2, hlabel_mem⟩
    exact (rvLift_restrict_mem_iff V B hB _).mpr ⟨(f (i p)).property, u, hlabel' (i p)⟩
  let g := (f.restrict hdom).corestrict hcod
  have hval (p : rvLift (U.restrict A hA)) : (g p).val = (f (i p)).val := rfl
  refine ⟨g, ⟨?_, ?_⟩, fun p q hpq => ?_⟩
  · intro p q h
    have he := congrArg Subtype.val h
    have he' : f (i p) = f (i q) := Subtype.ext ((hval p).symm.trans (he.trans (hval q)))
    have hpq := congrArg Subtype.val (hf.injective he')
    exact Subtype.ext hpq
  · intro q
    have hq := (rvLift_restrict_mem_iff V B hB q.val).mp q.property
    let q' : rvLift V := ⟨q.val, hq.1⟩
    obtain ⟨p, hp⟩ := hf.surjective q'
    obtain ⟨u, hu⟩ := hq.2
    have he : e.hom.map (liftLabelMap U p) = e.hom.map ⟨u.val, hA u.property⟩ := by
      apply Subtype.ext
      rw [hlabel' p, hp]
      exact hu.symm
    have hpU : p.val.2 = u.val := by
      have h := congrArg e.inv.map he
      rw [rvIso_inv_apply, rvIso_inv_apply] at h
      exact congrArg Subtype.val h
    let a : rvLift (U.restrict A hA) :=
      ⟨p.val, (rvLift_restrict_mem_iff U A hA _).mpr ⟨p.property, hpU.symm ▸ u.property⟩⟩
    have he := congrArg Subtype.val hp
    exact ⟨a, Subtype.ext ((hval a).trans he)⟩
  · exact (hval p).trans (congrArg (fun a => (f a).val) (Subtype.ext hpq))

end SpecialTransformations.Section9
