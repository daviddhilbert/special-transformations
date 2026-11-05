import SubstructureRVGroup
import SubstructureRVCompatibility
import RVGroupGraph

set_option backward.isDefEq.respectTransparency false

/-! Translate containment of the extracted old RV group map into the precise
old-RV and generated-VF compatibility clauses used by the preparation argument. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SubstructureRVGraph

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
  {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
  (hw : ∀ a b : VFType (M := N), VFValued.predV a b ↔ w a ≤ w b)
  (S : LRV.Substructure M) (f : S ↪[LRV] N)

theorem oldRV_of_contains_group
    (R : _root_.RVCalc.RV v → _root_.RVCalc.RV w → Prop)
    (hzero : R none none)
    (hgroup : ∀ t : SubstructureRVGroup.group v hv S,
      R (some (t : _root_.RVCalc.RVUnit v)) (some (SubstructureRVGroup.map v w hv hw S f t))) :
    SubstructureRVCompatibility.OldRVRepresentatives v w S f R := by
  intro x hx
  by_cases hx0 : (x : M) = iRVZero
  · have hfx : f x = iRVZero := by
      have he : x = (⟨iRVZero, SubstructureRVGroup.rvZero_mem S⟩ : S) := Subtype.ext hx0
      rw [he, SubstructureRVGroup.map_rvZero]
    refine ⟨0, 0, (RVCalc.rv_zero_eq hM).trans hx0.symm,
      (RVCalc.rv_zero_eq hN).trans hfx.symm, ?_⟩
    change R (_root_.RVCalc.rv v (0 : VFType (M := M)))
      (_root_.RVCalc.rv w (0 : VFType (M := N)))
    rw [_root_.RVCalc.rv_zero (v := v), _root_.RVCalc.rv_zero (v := w)]
    exact hzero
  · obtain ⟨t, ht, hft⟩ := SubstructureRVGroup.exists_group_element v w hv hw S f x hx hx0
    obtain ⟨c, hc⟩ := CanonicalRV.rv_surjective v (some (t : _root_.RVCalc.RVUnit v))
    obtain ⟨d, hd⟩ := CanonicalRV.rv_surjective w (some (SubstructureRVGroup.map v w hv hw S f t))
    have hce := congrArg Subtype.val (CanonicalRV.equiv_rv v hv c)
    have hde := congrArg Subtype.val (CanonicalRV.equiv_rv w hw d)
    rw [hc] at hce
    rw [hd] at hde
    refine ⟨c, d, hce.symm.trans ht, hde.symm.trans hft, ?_⟩
    rw [hc, hd]
    exact hgroup t

noncomputable def graph : _root_.RVCalc.RV v → _root_.RVCalc.RV w → Prop :=
  RVGroupGraph.Graph v w (SubstructureRVGroup.group v hv S) (SubstructureRVGroup.map v w hv hw S f)

theorem oldRV : SubstructureRVCompatibility.OldRVRepresentatives v w S f (graph v w hv hw S f) :=
  oldRV_of_contains_group v w hv hw S f (graph v w hv hw S f)
    (Or.inl ⟨rfl, rfl⟩) (fun t => Or.inr ⟨t, rfl, rfl⟩)

theorem field_compat (a : SubstructureField.generatedField S) :
    graph v w hv hw S f (_root_.RVCalc.rv v a.1)
      (_root_.RVCalc.rv w (SubstructureField.fieldMap S f a)) :=
  SubstructureRVCompatibility.field_compat v w hv hw S f (graph v w hv hw S f)
    (RVGroupGraph.mul v w _ _) (RVGroupGraph.inv v w _ _) (oldRV v w hv hw S f) a

end SubstructureRVGraph

#print axioms SubstructureRVGraph.oldRV_of_contains_group
#print axioms SubstructureRVGraph.oldRV
#print axioms SubstructureRVGraph.field_compat
