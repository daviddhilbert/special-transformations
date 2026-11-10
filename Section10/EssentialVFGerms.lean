import Section10.EssentialVFMap
import Section4.MapCorestrict

/-! Cofull definable domains and the induced bijections on independent VF
tuples. Independence is relative to the original parameter set. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10.EssentialVFMap

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t : ℕ}
local notation "Δ" => rawRVSpace (M := M) 1

variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S}

/-- The independent points of a definable set in its given VF coordinates. -/
def Generic (A : DefSet (rawMixedSpace (M := M) n r) S) :=
  {a : A // AlgebraicIndependent (vfParameterField S) a.val.1}

theorem independent_not_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) n r) S) (hE : vfDim Δ E < n)
    (a : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))
    (ha : AlgebraicIndependent (vfParameterField S) a.1) :
    a ∉ E.carrier := by
  intro hm
  have hr : vfTupleTrdeg S a.1 = n := (tupleField_trdeg_eq_arity_iff (vfParameterField S) a.1).mpr ha
  have hle := vfTupleTrdeg_le_vfDim hc Δ (rawRVSpace_rvCoded 1) E ⟨a, hm⟩
  change vfTupleTrdeg S a.1 ≤ _ at hle
  rw [hr] at hle
  exact (not_le_of_gt hE) (by exact_mod_cast hle)

theorem mem_of_small_complement (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) n r) S) (hE : vfDim Δ (A.sdiff E) < n)
    (a : Generic A) : a.val.val ∈ E.carrier := by
  by_contra hn
  exact independent_not_mem hc (A.sdiff E) hE a.val.val a.property ⟨a.val.property, hn⟩

theorem small_complement_of_generic (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ) (hn : 0 < n)
    (E : DefSet (rawMixedSpace (M := M) n r) S) (hE : ∀ a : Generic A, a.val.val ∈ E.carrier) :
    vfDim Δ (A.sdiff E) < n := by
  apply mixed_vfDim_lt_of_no_independent hc hs hS Δ (rawRVSpace_rvCoded 1) hn
  intro a ha
  exact a.property.2 (hE ⟨⟨a.val, a.property.1⟩, ha⟩)

def id (A : DefSet (rawMixedSpace (M := M) n r) S) (hn : 0 < n) : EssentialVFMap A A := by
  have h : A.sdiff A = DefSet.empty _ S := DefSet.eq_of_carrier_eq Set.sdiff_self
  have hd : vfDim Δ (A.sdiff A) < n := by
    rw [h]
    have hz : vfDim Δ (DefSet.empty (rawMixedSpace (M := M) n r) S) = 0 :=
      Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space Δ) (.rv r)
    rwa [hz]
  exact ⟨A, A, fun _ h => h, fun _ h => h, hd, hd, Map.id A, Function.bijective_id⟩

def symm (f : EssentialVFMap A B) : EssentialVFMap B A :=
  ⟨f.target, f.source, f.target_subset, f.source_subset, f.target_small, f.source_small,
    f.map.inverse f.bijective, (Equiv.ofBijective f.map f.bijective).symm.bijective⟩

def genericFun (hc : CanonicalStructure.IsCanonical (M := M)) (f : EssentialVFMap A B)
    (a : Generic A) : Generic B := by
  let p : f.source := ⟨a.val.val, mem_of_small_complement hc f.source f.source_small a⟩
  exact ⟨⟨(f.map p).val, f.target_subset (f.map p).property⟩,
    independent_map_of_finiteFibres hc f.map (Map.finiteFibres_of_injective f.bijective.injective) p a.property⟩

def genericEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (f : EssentialVFMap A B) :
    Generic A ≃ Generic B where
  toFun := f.genericFun hc
  invFun := f.symm.genericFun hc
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    change (f.map.inverse f.bijective (f.map _)).val = _
    rw [Map.inverse_apply]
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    change (f.map (f.map.inverse f.bijective _)).val = _
    rw [Map.apply_inverse]

/-- Two representatives agree away from a definable set of smaller VF
dimension exactly when they induce the same map on independent points. -/
theorem genericEquiv_eq_iff (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ) (hn : 0 < n)
    (f g : EssentialVFMap A B) : f.genericEquiv hc = g.genericEquiv hc ↔
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, vfDim Δ (A.sdiff E) < n ∧
      ∀ x ∈ E.carrier, ∃ (p : f.source) (q : g.source),
        p.val = x ∧ q.val = x ∧ (f.map p).val = (g.map q).val := by
  constructor
  · intro he
    let P := rawMixedSpace (M := M) n r
    let Q := rawMixedSpace (M := M) n s
    let E : DefSet P S := ⟨{x | ∃ y, f.map.graph x y ∧ g.map.graph x y},
      ((f.map.graph_definable).inter P Q g.map.graph_definable).exists_right P Q⟩
    refine ⟨E, small_complement_of_generic hc hs hS hn E ?_, ?_⟩
    · intro a
      let p : f.source := ⟨a.val.val, mem_of_small_complement hc f.source f.source_small a⟩
      let q : g.source := ⟨a.val.val, mem_of_small_complement hc g.source g.source_small a⟩
      have hv : (f.map p).val = (g.map q).val := congrArg (fun e : Generic A ≃ Generic B => (e a).val.val) he
      exact ⟨_, ⟨p, rfl, rfl⟩, ⟨q, rfl, hv.symm⟩⟩
    · rintro x ⟨y, ⟨p, hp, hf⟩, ⟨q, hq, hg⟩⟩
      exact ⟨p, q, hp, hq, hf.trans hg.symm⟩
  · rintro ⟨E, hE, he⟩
    apply Equiv.ext
    intro a
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨p, q, hp, hq, h⟩ := he a.val.val (mem_of_small_complement hc E hE a)
    exact (congrArg (fun p : f.source => (f.map p).val) (Subtype.ext hp.symm)).trans
      (h.trans (congrArg (fun q : g.source => (g.map q).val) (Subtype.ext hq)))

def compSource (f : EssentialVFMap A B) (g : EssentialVFMap B C) :
    DefSet (rawMixedSpace (M := M) n r) S :=
  ⟨{x | ∃ p : f.source, p.val = x ∧ (f.map p).val ∈ g.source.carrier},
    f.map.definable_preimage g.source.definable⟩

omit [M ⊨ Axioms.ACVF] in
theorem compSource_subset (f : EssentialVFMap A B) (g : EssentialVFMap B C) :
    (f.compSource g).carrier ⊆ f.source.carrier := by
  rintro x ⟨p, rfl, _⟩
  exact p.property

def compMiddle (f : EssentialVFMap A B) (g : EssentialVFMap B C) :
    Map (f.compSource g) g.source :=
  (f.map.restrict (f.compSource_subset g)).corestrict (by
    rintro ⟨x, p, rfl, hp⟩
    exact hp)

omit [M ⊨ Axioms.ACVF] in
theorem compMiddle_injective (f : EssentialVFMap A B) (g : EssentialVFMap B C) :
    Function.Injective (f.compMiddle g) := by
  intro p q he
  apply Subtype.ext
  have he' : (f.map ⟨p.val, f.compSource_subset g p.property⟩).val =
      (f.map ⟨q.val, f.compSource_subset g q.property⟩).val := congrArg (fun x : g.source => x.val) he
  exact congrArg (fun x : f.source => x.val) (f.bijective.injective (Subtype.ext he'))

/-- The actual overlap of the middle sets gives an essential composite. -/
def comp (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ) (hn : 0 < n)
    (f : EssentialVFMap A B) (g : EssentialVFMap B C) : EssentialVFMap A C := by
  let E := f.compSource g
  let j := f.compMiddle g
  let h := g.map.comp j
  refine ⟨E, h.image, (f.compSource_subset g).trans f.source_subset, ?_, ?_, ?_, h.toImage, ?_⟩
  · rintro y ⟨p, rfl⟩
    exact g.target_subset (h p).property
  · apply small_complement_of_generic hc hs hS hn E
    intro a
    let p : f.source := ⟨a.val.val, mem_of_small_complement hc f.source f.source_small a⟩
    exact ⟨p, rfl, mem_of_small_complement hc g.source g.source_small (f.genericFun hc a)⟩
  · apply small_complement_of_generic hc hs hS hn h.image
    intro c
    let y : g.target := ⟨c.val.val, mem_of_small_complement hc g.target g.target_small c⟩
    let b := g.symm.genericFun hc c
    let z : f.target := ⟨b.val.val, mem_of_small_complement hc f.target f.target_small b⟩
    let a := f.map.inverse f.bijective z
    have ha : (f.map a).val ∈ g.source.carrier := by
      rw [Map.apply_inverse]
      exact (g.map.inverse g.bijective y).property
    let p : E := ⟨a.val, a, rfl, ha⟩
    have he : j p = g.map.inverse g.bijective y := by
      apply Subtype.ext
      exact congrArg (fun q : f.target => q.val) (Map.apply_inverse f.map f.bijective z)
    exact ⟨p, by change (g.map (j p)).val = _; rw [he, Map.apply_inverse]⟩
  · constructor
    · intro p q he
      exact f.compMiddle_injective g (g.bijective.injective
        (Subtype.ext (congrArg (fun y : h.image => y.val) he)))
    · rintro ⟨y, p, rfl⟩
      exact ⟨p, rfl⟩

@[simp] theorem genericEquiv_comp (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ) (hn : 0 < n)
    (f : EssentialVFMap A B) (g : EssentialVFMap B C) :
    (comp hc hs hS hn f g).genericEquiv hc = (f.genericEquiv hc).trans (g.genericEquiv hc) := by
  apply Equiv.ext
  intro a
  rfl

@[simp] theorem genericEquiv_symm (hc : CanonicalStructure.IsCanonical (M := M))
    (f : EssentialVFMap A B) : f.symm.genericEquiv hc = (f.genericEquiv hc).symm := by
  apply Equiv.ext
  intro a
  rfl

end SpecialTransformations.Section10.EssentialVFMap
