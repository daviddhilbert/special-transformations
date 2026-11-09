import Section4.CoordinateMaps
import Section4.FiniteGluing
import Section4.RVFiniteScissors
import Section4.RVWeightRestriction
import Section7.LiftedIsomorphism

/-! The essential restriction of Definition 9.13. The positive degree is
written `k + 1` so the discarded lifts have VF dimension at most `k`. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def rvEssentialLabels (U : RVObject (M := M) S (k + 1)) :
    DefSet (rawRVSpace (M := M) U.arity) S :=
  U.domain.sdiff (rvLowDomain U)

theorem rvEssentialLabels_subset (U : RVObject (M := M) S (k + 1)) :
    (rvEssentialLabels U).carrier ⊆ U.domain.carrier := fun _ h => h.1

theorem mem_rvEssentialLabels (U : RVObject (M := M) S (k + 1)) (u : U.domain) :
    u.val ∈ (rvEssentialLabels U).carrier ↔ ∀ i, (U.value u i).val ≠ iRVZero := by
  change (u.val ∈ U.domain.carrier ∧ u.val ∉ (rvLowDomain U).carrier) ↔ _
  rw [mem_rvLowDomain, rvWeight_le_pred_iff_zero, not_exists]
  exact and_iff_right u.property

/-- Definition 9.13's restriction to volume labels with no zero coordinate. -/
def rvEssential (U : RVObject (M := M) S (k + 1)) : RVObject (M := M) S (k + 1) :=
  U.restrict (rvEssentialLabels U) (rvEssentialLabels_subset U)

theorem rvEssential_value_nonzero (U : RVObject (M := M) S (k + 1))
    (u : (rvEssential U).domain) : ∀ i, ((rvEssential U).value u i).val ≠ iRVZero :=
  (mem_rvEssentialLabels U ⟨u.val, rvEssentialLabels_subset U u.property⟩).mp u.property

/-- Essential restriction stays in the full finite-volume subcategory. -/
def rvFiniteEssential (U : RVFiniteObject (M := M) S (k + 1)) :
    RVFiniteObject (M := M) S (k + 1) :=
  ⟨rvEssential U.obj, U.obj.restrict_finite_volume U.property _ (rvEssentialLabels_subset U.obj)⟩

/-- Essential part in arbitrary degree. The nondegeneracy condition is
vacuous for the empty volume tuple. -/
def rvFiniteEssentialPart {n : ℕ} (U : RVFiniteObject (M := M) S n) :
    RVFiniteObject (M := M) S n :=
  match n with
  | 0 => U
  | _ + 1 => rvFiniteEssential U

/-- Definition 9.13 in the finite-volume category. This also allows an
isomorphism given only on the essential parts. -/
abbrev RVFiniteEssentialIso {n : ℕ} (U V : RVFiniteObject (M := M) S n) :=
  rvFiniteEssentialPart U ≅ rvFiniteEssentialPart V

private theorem rvIso_preserves_essential {U V : RVObject (M := M) S (k + 1)}
    (e : U ≅ V) (u : U.domain) :
    u.val ∈ (rvEssentialLabels U).carrier ↔ (e.hom.map u).val ∈ (rvEssentialLabels V).carrier := by
  change (u.val ∈ U.domain.carrier ∧ u.val ∉ (rvLowDomain U).carrier) ↔
    ((e.hom.map u).val ∈ V.domain.carrier ∧ (e.hom.map u).val ∉ (rvLowDomain V).carrier)
  rw [mem_rvLowDomain U u, mem_rvLowDomain V (e.hom.map u), rvIso_weight e u]
  exact (and_iff_right u.property).trans (and_iff_right (e.hom.map u).property).symm

/-- An ambient isomorphism restricts to an essential isomorphism. -/
def rvEssentialIso {U V : RVObject (M := M) S (k + 1)} (e : U ≅ V) :
    rvEssential U ≅ rvEssential V where
  hom := e.hom.restrict _ (rvEssentialLabels_subset U) _ (rvEssentialLabels_subset V)
    (fun u => (rvIso_preserves_essential e ⟨u.val, rvEssentialLabels_subset U u.property⟩).mp
      u.property)
  inv := e.inv.restrict _ (rvEssentialLabels_subset V) _ (rvEssentialLabels_subset U)
    (fun v => (rvIso_preserves_essential e.symm ⟨v.val, rvEssentialLabels_subset V v.property⟩).mp
      v.property)
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro u
    apply Subtype.ext
    change (e.inv.map (e.hom.map ⟨u.val, rvEssentialLabels_subset U u.property⟩)).val = u.val
    exact congrArg Subtype.val (rvIso_inv_apply e ⟨u.val, rvEssentialLabels_subset U u.property⟩)
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro v
    apply Subtype.ext
    change (e.hom.map (e.inv.map ⟨v.val, rvEssentialLabels_subset V v.property⟩)).val = v.val
    exact congrArg Subtype.val (rvIso_inv_apply e.symm ⟨v.val, rvEssentialLabels_subset V v.property⟩)

def rvFiniteEssentialIso {U V : RVFiniteObject (M := M) S (k + 1)} (e : U ≅ V) :
    rvFiniteEssential U ≅ rvFiniteEssential V :=
  rvFiniteIsoOfAmbient (rvEssentialIso ((finiteVolumeProperty S (k + 1)).ι.mapIso e))

variable [M ⊨ Axioms.ACVF]

theorem mem_rvEssentialLift (U : RVObject (M := M) S (k + 1))
    (p : (rawMixedSpace (M := M) (k + 1) U.arity).Carrier) :
    p ∈ (rvLift (rvEssential U)).carrier ↔
      p ∈ (rvLift U).carrier ∧ ∀ i, p.1 i ≠ 0 := by
  change p ∈ (rvLift (U.restrict (rvEssentialLabels U) (rvEssentialLabels_subset U))).carrier ↔ _
  rw [SpecialTransformations.Section7.rvLift_restrict_mem_iff]
  constructor
  · rintro ⟨⟨u, hu, hv⟩, he⟩
    refine ⟨⟨u, hu, hv⟩, ?_⟩
    have hn := (mem_rvEssentialLabels U u).mp (hu ▸ he : u.val ∈ (rvEssentialLabels U).carrier)
    intro i hi
    exact hn i ((congrArg Subtype.val (congrFun hv i)).trans
      ((CanonicalRV.encodedRv_zero_iff _).mpr hi))
  · rintro ⟨⟨u, hu, hv⟩, hn⟩
    refine ⟨⟨u, hu, hv⟩, hu ▸ (mem_rvEssentialLabels U u).mpr ?_⟩
    intro i hi
    exact hn i ((CanonicalRV.encodedRv_zero_iff _).mp
      ((congrArg Subtype.val (congrFun hv i)).symm.trans hi))

/-- The lift of the low-weight restriction is precisely the omitted locus. -/
theorem rvLowLift_eq_complement (U : RVObject (M := M) S (k + 1)) :
    rvLift (rvLowRestriction U) = (rvLift U).sdiff (rvLift (rvEssential U)) := by
  apply DefSet.eq_of_carrier_eq
  ext p
  change p ∈ (rvLift (U.restrict (rvLowDomain U) (rvLowDomain_subset U))).carrier ↔
    p ∈ (rvLift U).carrier ∧
      p ∉ (rvLift (U.restrict (rvEssentialLabels U) (rvEssentialLabels_subset U))).carrier
  rw [SpecialTransformations.Section7.rvLift_restrict_mem_iff U (rvLowDomain U),
    SpecialTransformations.Section7.rvLift_restrict_mem_iff U (rvEssentialLabels U)]
  constructor
  · rintro ⟨hp, hl⟩
    exact ⟨hp, fun he => he.2.2 hl⟩
  · rintro ⟨hp, he⟩
    refine ⟨hp, ?_⟩
    by_contra h
    obtain ⟨u, hu, hv⟩ := hp
    exact he ⟨⟨u, hu, hv⟩, ⟨hu ▸ u.property, h⟩⟩

private def rvZeroDomainAt (U : RVObject (M := M) S (k + 1)) (i : Fin (k + 1)) :
    DefSet (rawRVSpace (M := M) U.arity) S where
  carrier := {x | ∃ u : U.domain, u.val = x ∧ U.value u ∈ (zeroLabelsAt S i).carrier}
  definable := U.volume.definable_preimage (zeroLabelsAt S i).definable

omit [M ⊨ Axioms.ACVF] in
private theorem rvZeroDomainAt_subset (U : RVObject (M := M) S (k + 1)) (i : Fin (k + 1)) :
    (rvZeroDomainAt U i).carrier ⊆ U.domain.carrier := by
  rintro x ⟨u, rfl, _⟩
  exact u.property

/-- The omitted VF locus has dimension below the ambient degree. Deleting
the known zero coordinate is injective on each of finitely many pieces. -/
theorem rvLowLift_vfDim_le (Δ : Space LRV M) (U : RVObject (M := M) S (k + 1)) :
    vfDim Δ (rvLift (rvLowRestriction U)) ≤ k := by
  let A (i : Fin (k + 1)) := rvLift (U.restrict (rvZeroDomainAt U i) (rvZeroDomainAt_subset U i))
  let D := DefSet.univ (rawMixedSpace (M := M) k U.arity) S
  let f (i : Fin (k + 1)) : Map (A i) D := vfSelect i.succAbove (A i)
  have hzero (i : Fin (k + 1)) (p : A i) : p.val.1 i = 0 := by
    obtain ⟨⟨u, hu, hv⟩, v, hvl, hz⟩ :=
      (SpecialTransformations.Section7.rvLift_restrict_mem_iff _ _ _ _).mp p.property
    have huv : v = u := Subtype.ext (hvl.trans hu.symm)
    subst v
    apply (CanonicalRV.encodedRv_zero_iff _).mp
    exact (congrArg Subtype.val (congrFun hv i)).symm.trans hz
  have hfin (i : Fin (k + 1)) : (f i).FiniteFibres := by
    apply Map.finiteFibres_of_injective
    intro p q h
    have he : (p.val.1 ∘ i.succAbove, p.val.2) = (q.val.1 ∘ i.succAbove, q.val.2) :=
      congrArg Subtype.val h
    have hRV : p.val.2 = q.val.2 := congrArg (fun z : (rawMixedSpace (M := M) k U.arity).Carrier => z.2) he
    apply Subtype.ext
    refine Prod.ext ?_ hRV
    funext j
    by_cases hj : j = i
    · subst j
      rw [hzero i p, hzero i q]
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
      exact congrFun (congrArg Prod.fst he) l
  have hcov (p : rvLift (rvLowRestriction U)) : ∃ i, p.val ∈ (A i).carrier := by
    obtain ⟨hp, hlow⟩ :=
      (SpecialTransformations.Section7.rvLift_restrict_mem_iff U _ _ p.val).mp p.property
    obtain ⟨u, hu, hz⟩ := hlow
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, (SpecialTransformations.Section7.rvLift_restrict_mem_iff U _ _ p.val).mpr
      ⟨hp, u, hu, hi⟩⟩
  obtain ⟨g, hg⟩ := finite_cover_finite_map (rvLift (rvLowRestriction U)) D A f hfin hcov
  exact (vfDim_le_iff Δ _ k).mpr ⟨k, le_rfl, .rv U.arity, g, hg⟩

theorem rvEssentialLift_complement_dim_lt (Δ : Space LRV M)
    (U : RVObject (M := M) S (k + 1)) :
    vfDim Δ ((rvLift U).sdiff (rvLift (rvEssential U))) < k + 1 := by
  rw [← rvLowLift_eq_complement]
  exact Nat.lt_succ_of_le (rvLowLift_vfDim_le Δ U)

end SpecialTransformations.Section9

end
