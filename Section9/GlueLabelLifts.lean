import Section9.LiftRestriction
import Section9.LiftLabelRepresentatives

/-! Glue a finite family of lifts along a disjoint partition of the
source labels. The target partition is the image under the given
label isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {U V : RVObject (M := M) S n}

theorem exists_glued_label_lift {I : Type} [Finite I]
    (e : U ≅ V) (P : I → DefSet (rawRVSpace (M := M) U.arity) S)
    (hP : ∀ i, (P i).carrier ⊆ U.domain.carrier)
    (hcover : ∀ u : U.domain, ∃ i, u.val ∈ (P i).carrier)
    (hdisj : ∀ i j z, z ∈ (P i).carrier → z ∈ (P j).carrier → i = j)
    (F : ∀ i, Map (rvLift (U.restrict (P i) (hP i)))
      (rvLift (V.restrict (e.hom.map.restrict (hP i)).image
        (rvLabelImage_subset e (P i) (hP i)))))
    (hF : ∀ i, Function.Bijective (F i))
    (hlabel : ∀ i (p : rvLift (U.restrict (P i) (hP i))),
      e.hom.map.graph p.val.2 (F i p).val.2) :
    ∃ G : Map (rvLift U) (rvLift V), Function.Bijective G ∧
      (∀ p : rvLift U, e.hom.map.graph p.val.2 (G p).val.2) ∧
      ∀ i (p : rvLift (U.restrict (P i) (hP i))) (q : rvLift U), p.val = q.val →
        (F i p).val = (G q).val := by
  let X := rawMixedSpace (M := M) n U.arity
  let Y := rawMixedSpace (M := M) n V.arity
  let R (x : X.Carrier) (y : Y.Carrier) := ∃ i, (F i).graph x y
  have hR : X.RelationDefinable Y S R := by
    change S.Definable LRV (X.relation Y R)
    have he : X.relation Y R = ⋃ i, X.relation Y (F i).graph := by
      ext z
      simp only [Space.relation, Set.mem_ofPred_eq, Set.mem_iUnion, R]
      aesop
    rw [he]
    exact Set.definable_iUnion_of_finite (fun i => (F i).graph_definable)
  have hdom (x y) (h : R x y) : x ∈ (rvLift U).carrier ∧ y ∈ (rvLift V).carrier := by
    obtain ⟨i, a, rfl, rfl⟩ := h
    exact ⟨((rvLift_restrict_mem_iff U (P i) (hP i) _).mp a.property).1,
      ((rvLift_restrict_mem_iff V _ _ _).mp (F i a).property).1⟩
  have htotal (p : rvLift U) : ∃ y, R p.val y := by
    let u := liftLabelMap U p
    obtain ⟨i, hi⟩ := hcover u
    let a : rvLift (U.restrict (P i) (hP i)) :=
      ⟨p.val, (rvLift_restrict_mem_iff U (P i) (hP i) _).mpr ⟨p.property, hi⟩⟩
    exact ⟨(F i a).val, i, a, rfl, rfl⟩
  have hunique (x y z) (hy : R x y) (hz : R x z) : y = z := by
    obtain ⟨i, a, ha, rfl⟩ := hy
    obtain ⟨j, b, hb, rfl⟩ := hz
    have hai := ((rvLift_restrict_mem_iff U (P i) (hP i) _).mp a.property).2
    have hbj := ((rvLift_restrict_mem_iff U (P j) (hP j) _).mp b.property).2
    have he := hdisj i j x.2 (congrArg Prod.snd ha ▸ hai) (congrArg Prod.snd hb ▸ hbj)
    subst j
    exact congrArg (fun c => (F i c).val) (Subtype.ext (ha.trans hb.symm))
  let G : Map (rvLift U) (rvLift V) := Map.ofFunctionalRelation hR hdom htotal hunique
  have hG (p : rvLift U) : R p.val (G p).val :=
    Map.ofFunctionalRelation_graph hR hdom htotal hunique p
  have hGlab (p : rvLift U) : e.hom.map.graph p.val.2 (G p).val.2 := by
    obtain ⟨i, a, ha, hb⟩ := hG p
    rw [← ha, ← hb]
    exact hlabel i a
  have hGlocal (i) (p : rvLift (U.restrict (P i) (hP i))) (q : rvLift U)
      (hpq : p.val = q.val) : (F i p).val = (G q).val :=
    hunique _ _ _ ⟨i, p, hpq, rfl⟩ (hG q)
  refine ⟨G, ⟨?_, ?_⟩, hGlab, hGlocal⟩
  · intro p q hpq
    have he : p.val.2 = q.val.2 := by
      obtain ⟨u, hu, hfu⟩ := hGlab p
      obtain ⟨w, hw, hfw⟩ := hGlab q
      have h' : e.hom.map u = e.hom.map w :=
        Subtype.ext (hfu.trans ((congrArg (fun p => p.val.2) hpq).trans hfw.symm))
      have h'' : u = w := by
        have h := congrArg e.inv.map h'
        rwa [rvIso_inv_apply, rvIso_inv_apply] at h
      exact hu.symm.trans (h'' ▸ hw)
    obtain ⟨i, a, ha, hb⟩ := hG p
    have hai := ((rvLift_restrict_mem_iff U (P i) (hP i) _).mp a.property).2
    have hqi : q.val.2 ∈ (P i).carrier := (congrArg Prod.snd ha |>.trans he) ▸ hai
    let b : rvLift (U.restrict (P i) (hP i)) :=
      ⟨q.val, (rvLift_restrict_mem_iff U (P i) (hP i) _).mpr ⟨q.property, hqi⟩⟩
    have hab : a = b := (hF i).injective (Subtype.ext
      (hb.trans ((congrArg Subtype.val hpq).trans (hGlocal i b q rfl).symm)))
    exact Subtype.ext (ha.symm.trans (congrArg Subtype.val hab))
  · intro q
    let v := liftLabelMap V q
    obtain ⟨i, hi⟩ := hcover (e.inv.map v)
    let a : P i := ⟨(e.inv.map v).val, hi⟩
    let B := (e.hom.map.restrict (hP i)).image
    let hB := rvLabelImage_subset e (P i) (hP i)
    have hv : q.val.2 ∈ B.carrier :=
      ⟨a, congrArg Subtype.val (rvIso_apply_inv e v)⟩
    let b : rvLift (V.restrict B hB) :=
      ⟨q.val, (rvLift_restrict_mem_iff V B hB _).mpr ⟨q.property, hv⟩⟩
    obtain ⟨p, hp⟩ := (hF i).surjective b
    let p' : rvLift U := ⟨p.val, ((rvLift_restrict_mem_iff U (P i) (hP i) _).mp p.property).1⟩
    exact ⟨p', Subtype.ext ((hGlocal i p p' rfl).symm.trans (congrArg Subtype.val hp))⟩

end SpecialTransformations.Section9
