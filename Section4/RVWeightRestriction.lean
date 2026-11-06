import Section4.RVCompression

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

theorem rvIso_inv_apply {U V : RVObject (M := M) S k} (e : U ≅ V) (u : U.domain) :
    e.inv.map (e.hom.map u) = u :=
  congrArg (fun f : RVHom U U => f.map u) e.hom_inv_id

theorem rvIso_weight {U V : RVObject (M := M) S k} (e : U ≅ V) (u : U.domain) :
    rvWeight (U.value u) = rvWeight (V.value (e.hom.map u)) := by
  apply (e.hom.volumetric u).antisymm
  have h := e.inv.volumetric (e.hom.map u)
  rwa [rvIso_inv_apply] at h

def rvLowDomain (U : RVObject (M := M) S (k + 1)) :
    DefSet (rawRVSpace (M := M) U.arity) S where
  carrier := {x | ∃ u : U.domain, u.val = x ∧ U.value u ∈ (lowZeroLabels S k).carrier}
  definable := U.volume.definable_preimage (lowZeroLabels S k).definable

theorem rvLowDomain_subset (U : RVObject (M := M) S (k + 1)) :
    (rvLowDomain U).carrier ⊆ U.domain.carrier := by
  rintro x ⟨u, rfl, _⟩
  exact u.property

theorem mem_rvLowDomain (U : RVObject (M := M) S (k + 1)) (u : U.domain) :
    u.val ∈ (rvLowDomain U).carrier ↔ rvWeight (U.value u) ≤ k := by
  constructor
  · rintro ⟨v, hv, hzero⟩
    have he : v = u := Subtype.ext hv
    subst v
    exact (rvWeight_le_pred_iff_zero _).mpr hzero
  · intro h
    exact ⟨u, rfl, (rvWeight_le_pred_iff_zero _).mp h⟩

def rvLowRestriction (U : RVObject (M := M) S (k + 1)) : RVObject (M := M) S (k + 1) :=
  U.restrict (rvLowDomain U) (rvLowDomain_subset U)

theorem rvLowRestriction_weight (U : RVObject (M := M) S (k + 1)) :
    rvLowWeightProperty S k (rvLowRestriction U) := by
  intro u
  exact (mem_rvLowDomain U ⟨u.val, rvLowDomain_subset U u.property⟩).mp u.property

def rvLowRestrictionIso {U V : RVObject (M := M) S (k + 1)} (e : U ≅ V) :
    rvLowRestriction U ≅ rvLowRestriction V where
  hom := e.hom.restrict _ (rvLowDomain_subset U) _ (rvLowDomain_subset V) (by
    intro u
    apply (mem_rvLowDomain V _).mpr
    exact (rvIso_weight e ⟨u.val, rvLowDomain_subset U u.property⟩).symm.le.trans
      ((mem_rvLowDomain U ⟨u.val, rvLowDomain_subset U u.property⟩).mp u.property))
  inv := e.inv.restrict _ (rvLowDomain_subset V) _ (rvLowDomain_subset U) (by
    intro u
    apply (mem_rvLowDomain U _).mpr
    exact (rvIso_weight e.symm ⟨u.val, rvLowDomain_subset V u.property⟩).symm.le.trans
      ((mem_rvLowDomain V ⟨u.val, rvLowDomain_subset V u.property⟩).mp u.property))
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro u
    apply Subtype.ext
    change (e.inv.map (e.hom.map ⟨u.val, rvLowDomain_subset U u.property⟩)).val = u.val
    exact congrArg (fun x : U.domain => x.val)
      (rvIso_inv_apply e ⟨u.val, rvLowDomain_subset U u.property⟩)
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro u
    apply Subtype.ext
    change (e.hom.map (e.inv.map ⟨u.val, rvLowDomain_subset V u.property⟩)).val = u.val
    exact congrArg (fun x : V.domain => x.val)
      (rvIso_inv_apply e.symm ⟨u.val, rvLowDomain_subset V u.property⟩)

def rvCompressIso {U V : RVObject (M := M) S (k + 1)}
    (hU : rvLowWeightProperty S k U) (hV : rvLowWeightProperty S k V) (e : U ≅ V) :
    rvCompressObject U hU ≅ rvCompressObject V hV where
  hom := rvCompressHom hU hV e.hom
  inv := rvCompressHom hV hU e.inv
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro u
    exact rvIso_inv_apply e u
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro v
    exact rvIso_inv_apply e.symm v

/-- Restrict to weight at most k and then compress the labels. -/
def rvWeightProjection (U : RVObject (M := M) S (k + 1)) : RVObject (M := M) S k :=
  rvCompressObject (rvLowRestriction U) (rvLowRestriction_weight U)

def rvWeightProjectionIso {U V : RVObject (M := M) S (k + 1)} (e : U ≅ V) :
    rvWeightProjection U ≅ rvWeightProjection V :=
  rvCompressIso _ _ (rvLowRestrictionIso e)

end SpecialTransformations.Section4

end
