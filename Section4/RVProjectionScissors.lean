import Section4.RVWeightRestriction
import Section4.RVIsoTools
import Section4.RVScissorPresentation
import Mathlib.Tactic.Tauto

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

theorem rvLowDomain_restrict_carrier (U : RVObject (M := M) S (k + 1))
    (X : DefSet (rawRVSpace (M := M) U.arity) S) (hX : X.carrier ⊆ U.domain.carrier) :
    (rvLowDomain (U.restrict X hX)).carrier = X.carrier ∩ (rvLowDomain U).carrier := by
  ext x
  constructor
  · intro hx
    have hxX := rvLowDomain_subset (U.restrict X hX) hx
    have hw := (mem_rvLowDomain (U.restrict X hX) ⟨x, hxX⟩).mp hx
    exact ⟨hxX, (mem_rvLowDomain U ⟨x, hX hxX⟩).mpr hw⟩
  · rintro ⟨hxX, hxU⟩
    have hw := (mem_rvLowDomain U ⟨x, hX hxX⟩).mp hxU
    exact (mem_rvLowDomain (U.restrict X hX) ⟨x, hxX⟩).mpr hw

def rvWeightProjection_restrict_iso (U : RVObject (M := M) S (k + 1))
    (X : DefSet (rawRVSpace (M := M) U.arity) S) (hX : X.carrier ⊆ U.domain.carrier) :
    rvWeightProjection (U.restrict X hX) ≅
      (rvWeightProjection U).restrict (X.inter (rvLowDomain U)) (fun _ h => h.2) :=
  rvIsoOfCarrierEq _ _ _ _ (rvLowDomain_restrict_carrier U X hX) (fun _ => rfl)

theorem rvWeightProjection_scissor {A B C D : RVObject (M := M) S (k + 1)}
    (h : RVScissor A B C D) :
    rvClass (rvWeightProjection A) + rvClass (rvWeightProjection B) =
      rvClass (rvWeightProjection C) + rvClass (rvWeightProjection D) := by
  obtain ⟨U, X, Y, hX, hY, rfl, rfl, rfl, rfl⟩ := h
  let W := rvWeightProjection U
  let L := rvLowDomain U
  let X' := X.inter L
  let Y' := Y.inter L
  have hX' : X'.carrier ⊆ W.domain.carrier := fun _ hx => hx.2
  have hY' : Y'.carrier ⊆ W.domain.carrier := fun _ hy => hy.2
  have hUnion : W.restrict ((X.union Y).inter L) (fun _ h => h.2) =
      W.restrict (X'.union Y') (fun _ h => h.elim (fun hx => hX' hx) (fun hy => hY' hy)) := by
    apply RVObject.restrict_eq_of_carrier_eq
    ext x
    simp only [X', Y', DefSet.inter, DefSet.union, Set.mem_inter_iff, Set.mem_union]
    tauto
  have hInter : W.restrict ((X.inter Y).inter L) (fun _ h => h.2) =
      W.restrict (X'.inter Y') (fun _ h => hX' h.1) := by
    apply RVObject.restrict_eq_of_carrier_eq
    ext x
    simp only [X', Y', DefSet.inter, Set.mem_inter_iff]
    tauto
  rw [rvClass_iso (rvWeightProjection_restrict_iso U X hX),
    rvClass_iso (rvWeightProjection_restrict_iso U Y hY),
    rvClass_iso (rvWeightProjection_restrict_iso U (X.union Y) _),
    rvClass_iso (rvWeightProjection_restrict_iso U (X.inter Y) _)]
  change rvClass (W.restrict X' hX') + rvClass (W.restrict Y' hY') =
    rvClass (W.restrict ((X.union Y).inter L) _) + rvClass (W.restrict ((X.inter Y).inter L) _)
  rw [hUnion, hInter]
  exact rvClass_scissor ⟨W, X', Y', hX', hY', rfl, rfl, rfl, rfl⟩

def rvWeightProjection_empty_iso :
    rvWeightProjection (RVObject.empty (M := M) S (k + 1)) ≅ RVObject.empty S k := by
  have hcarrier : (rvWeightProjection (RVObject.empty (M := M) S (k + 1))).domain.carrier =
      (RVObject.empty (M := M) S k).domain.carrier := by
    ext x
    constructor
    · rintro ⟨u, _, _⟩
      exact False.elim u.property
    · exact False.elim
  apply rvIsoOfCarrierEq _ _ _ _ hcarrier
  intro a
  obtain ⟨u, _, _⟩ := a.property
  exact False.elim u.property

def rvWeightProjectionInvariant :
    PositiveAdditiveGrothendieck.Invariant (rvScissorPresentation (M := M) S (k + 1))
      (A := RVKPlus (M := M) S k) where
  toFun U := rvClass (rvWeightProjection U)
  iso h := by
    obtain ⟨e⟩ := h
    exact rvClass_iso (rvWeightProjectionIso e)
  empty := by
    change rvClass (rvWeightProjection (RVObject.empty S (k + 1))) = 0
    exact (rvClass_iso rvWeightProjection_empty_iso).trans rvClass_empty
  scissor := rvWeightProjection_scissor

def rvWeightProjectionKPlus : RVKPlus (M := M) S (k + 1) →+ RVKPlus (M := M) S k :=
  PositiveAdditiveGrothendieck.lift (rvScissorPresentation S (k + 1)) rvWeightProjectionInvariant

@[simp] theorem rvWeightProjectionKPlus_class (U : RVObject (M := M) S (k + 1)) :
    rvWeightProjectionKPlus (rvClass U) = rvClass (rvWeightProjection U) :=
  PositiveAdditiveGrothendieck.lift_of (rvScissorPresentation S (k + 1)) rvWeightProjectionInvariant U

end SpecialTransformations.Section4

end
