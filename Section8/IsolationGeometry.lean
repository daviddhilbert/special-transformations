import Section8.IsolationFibres
import Section8.SeparatedSets
import Section4.FullDimension

/-! A generic VF input cannot be isolated in a product of two balls
on a definable graph. The fixed-radius image of a neighbourhood
would contradict the finiteness theorem in Lemma 8.1. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]
variable (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {n m : ℕ}

private theorem polydisc_infinite (hnt : ∃ e : VFType (M := M), e ≠ 0 ∧ Valued.v e < 1)
    (D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) n) (i : Fin n) :
    D.carrier.Infinite := by
  classical
  let g (b : VFType (M := M)) (j : Fin n) := if j = i then b else D.centre j
  have hinj : Function.Injective g := by
    intro b c he
    simpa only [g, if_pos rfl] using congrFun he i
  apply ((D.side_infinite hnt i).image hinj.injOn).mono
  rintro _ ⟨b, hb, rfl⟩ j
  by_cases hji : j = i
  · subst j
    change Valued.v (b - D.centre i) < Valued.v (D.step i) at hb
    simpa only [g, if_pos rfl] using hb
  · change Valued.v (g b j - D.centre j) < Valued.v (D.step j)
    simp only [g, if_neg hji, sub_self, map_zero]
    exact pos_iff_ne_zero.mpr (Valued.v.ne_zero_iff.mpr (D.step_ne_zero j))

include hv in
private theorem polydisc_graph_image_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    {f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (vfGraph f))
    (D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) n) :
    DefinableOver ((S ∪ Set.range (vfValues D.centre)) ∪ Set.range (vfValues D.step))
      (fun _ => .vf) ((fun a => vfValues (f a)) '' D.carrier) := by
  let T := (S ∪ Set.range (vfValues D.centre)) ∪ Set.range (vfValues D.step)
  let X : Set (Fin n → M) := {a | ∀ i, a i ∈ rawOpenBall (vfValues D.centre i) (vfValues D.step i)}
  have hX : T.Definable LRV X := by
    change T.Definable LRV {a : Fin n → M | ∀ i, a i ∈ rawOpenBall (vfValues D.centre i) (vfValues D.step i)}
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i =>
      (rawOpenBall_definable (S := T) (Or.inl (Or.inr (Set.mem_range_self i)))
        (Or.inr (Set.mem_range_self i))).preimage_comp (fun _ : Fin 1 => i))
  have hXiff (a : Fin n → VFType (M := M)) : vfValues a ∈ X ↔ a ∈ D.carrier :=
    forall_congr' (fun i => mem_rawOpenBall_iff Valued.v hv (D.centre i) (D.step i) (a i) (D.step_ne_zero i))
  have hS : S ⊆ T := Set.subset_union_left.trans Set.subset_union_left
  have hImg := ((hf.mono hS).inter (hX.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin m))).image_comp Sum.inr
  apply raw_definableOver_sorted hc T (fun _ => .vf)
  · convert hImg using 1
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Sum.elim (vfValues a) (vfValues (f a)), ⟨⟨a, rfl⟩, (hXiff a).mpr ha⟩, rfl⟩
    · rintro ⟨_, ⟨⟨a, rfl⟩, ha⟩, rfl⟩
      exact ⟨a, (hXiff a).mp ha, rfl⟩
  · rintro _ ⟨a, _, rfl⟩ i
    exact (f a i).property

include hv in
theorem independent_not_isolated (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (vfGraph f)) (hn : 0 < n)
    (a : Fin n → VFType (M := M)) (ha : AlgebraicIndependent (vfParameterField S) a)
    (t : Fin 2 → M) : vfValues a ∉ fixedIsolation (vfGraph f) t := by
  intro h
  have ht := ((mem_fixedIsolation_vfGraph_iff f a t).mp h).2.1
  obtain ⟨r, hrt⟩ := CanonicalRV.encodedRv_surjective ⟨t 0, (ht 0).1⟩
  obtain ⟨s, hst⟩ := CanonicalRV.encodedRv_surjective ⟨t 1, (ht 1).1⟩
  have hr' : iRv r.val = t 0 := congrArg Subtype.val hrt
  have hs' : iRv s.val = t 1 := congrArg Subtype.val hst
  have hr : r ≠ 0 := fun h0 => (ht 0).2 (hr'.symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr h0))
  have hs : s ≠ 0 := fun h0 => (ht 1).2 (hs'.symm.trans ((CanonicalRV.encodedRv_zero_iff s).mpr h0))
  have ht' : ![iRv r.val, iRv s.val] = t := by
    funext i
    fin_cases i
    · exact hr'
    · exact hs'
  have hInd : AlgebraicIndependent (vfParameterField (S ∪ Set.range t)) a := by
    rw [vfParameterField_union_rv S _ (by rintro _ ⟨i, rfl⟩; exact (ht i).1)]
    exact ha
  have hF := independent_definable_mem_nhds hv _ _ (fixedIsolation_sorted hc hf t) a hInd h
  let E : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) n :=
    ⟨a, fun _ => r, fun _ => hr⟩
  have hE : {x | vfValues x ∈ uniformBall (vfValues a) r.val} ∈ 𝓝 a := by
    rw [nhds_pi, Filter.mem_pi']
    refine ⟨Finset.univ, E.side, E.side_mem_nhds, ?_⟩
    intro x hx
    apply (mem_uniformBall_iff Valued.v hv a x r hr).mpr
    exact (E.mem_carrier_iff x).mpr (fun i hi => hx i (Finset.mem_univ i))
  obtain ⟨D, _, hD⟩ := exists_polydisc_subset_of_mem_nhds a (Filter.inter_mem hF hE)
  have huniq (x y : Fin n → VFType (M := M)) (hx : x ∈ D.carrier) (hy : y ∈ D.carrier)
      (hfy : vfValues (f y) ∈ uniformBall (vfValues (f x)) s.val) : y = x := by
    have hxT : vfValues x ∈ fixedIsolation (vfGraph f) t := (hD hx).1
    rw [← ht'] at hxT
    apply (mem_fixedIsolation_iff_unique f x r s hr hs).mp hxT y _ hfy
    intro i
    exact rawOpenBall_recentre Valued.v hv ((hD hx).2 i) ((hD hy).2 i)
  let C := (fun x => vfValues (f x)) '' D.carrier
  have hC : C.Finite := by
    apply lemma_8_1 C (polydisc_graph_image_definable hv hc hf D)
    refine ⟨s.val, s.property, fun h0 => hs (Subtype.ext h0), ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    apply (disjoint_uniformBall_iff Valued.v hv (fun i => (f x i).property)
      (fun i => (f y i).property) s.property (fun h0 => hs (Subtype.ext h0))).mpr
    exact fun hxy => hne (congrArg (fun z => vfValues (f z)) (huniq x y hx hy hxy).symm)
  apply polydisc_infinite (model_valuation_nontrivial hv) D ⟨0, hn⟩
  apply hC.of_finite_image
  intro x hx y hy he
  apply (huniq x y hx hy ?_).symm
  change vfValues (f x) = vfValues (f y) at he
  have hself : vfValues (f x) ∈ uniformBall (vfValues (f x)) s.val :=
    fun i => rawOpenBall_self Valued.v hv (f x i).property s.property (fun h0 => hs (Subtype.ext h0))
  exact Eq.mp (congrArg (fun z => z ∈ uniformBall (vfValues (f x)) s.val) he) hself

end SpecialTransformations.Section8
