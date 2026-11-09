import Section4.RVFinitaryImages
import Section4.RVRestrictions

/-! A finite-to-one map to its volume image preserves RV dimension.
Use the checked finitary-image inequality for the reverse bound. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m n : ℕ} {S : Set M}

theorem rvDim_mapImage_eq_of_finiteFibres
    (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {A : DefSet (rawRVSpace (M := M) m) S} {B : DefSet (rawRVSpace (M := M) n) S}
    (f : Map A B) (hf : f.FiniteFibres) : rvDim f.image = rvDim A := by
  let G : RVFinitaryFunction A n :=
    { values := fun x => {y | f.graph x y}
      definable := f.graph_definable
      finite := fun a => by
        convert Set.finite_singleton (f a).val using 1
        ext y
        exact (f.graph_apply a y).trans eq_comm }
  have he : G.image = f.image := by
    apply DefSet.eq_of_carrier_eq
    ext y
    change (∃ a : A, f.graph a.val y) ↔ _
    simp only [Map.graph_apply, Map.image, Set.mem_range]
  have hf' : f.toImage.FiniteFibres := by
    intro b
    obtain ⟨a, ha⟩ := b.property
    let y := f a
    apply (hf y).subset
    intro a' ha'
    apply Subtype.ext
    exact (congrArg Subtype.val ha').trans ha.symm
  exact (he ▸ G.dimension_image_le hc hex hs hsmall).antisymm (rvDim_le_of_finite_map _ hf')

theorem rvDim_sdiff_eq_of_lt
    (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A B : DefSet (rawRVSpace (M := M) n) S) (h : rvDim B < rvDim A) :
    rvDim (A.sdiff B) = rvDim A := by
  have hA : A.carrier.Nonempty := by
    by_contra hn
    have hf : A.carrier.Finite := by rw [Set.not_nonempty_iff_eq_empty.mp hn]; exact Set.finite_empty
    rw [(rvDim_eq_zero_iff_finite A).mpr hf] at h
    exact (Nat.not_lt_zero _) h
  obtain ⟨a, ha⟩ := exists_point_of_maximum_rv_rank hc hex hs hsmall A hA
  have hn : a.val ∉ B.carrier := by
    intro hab
    have hb := rvTupleRank_le_rvDim hc hex B ⟨a.val, hab⟩
    change rvTupleRank hc hex S a.val ≤ rvDim B at hb
    exact (not_le_of_gt h) (ha ▸ hb)
  let a' : A.sdiff B := ⟨a.val, a.property, hn⟩
  have h' := rvTupleRank_le_rvDim hc hex (A.sdiff B) a'
  change rvTupleRank hc hex S a.val ≤ rvDim (A.sdiff B) at h'
  rw [ha] at h'
  let i : Map (A.sdiff B) A := Map.inclusion Set.sdiff_subset
  have hi : Function.Injective i := by
    intro a b h
    have he := congrArg Subtype.val h
    exact Subtype.ext he
  exact (rvDim_le_of_finite_map i (Map.finiteFibres_of_injective hi)).antisymm h'

theorem rvDim_union_le_max
    (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A B : DefSet (rawRVSpace (M := M) n) S) :
    rvDim (A.union B) ≤ max (rvDim A) (rvDim B) := by
  apply rvDim_le_of_point_rank hc hex hs hsmall
  rintro ⟨a, ha | hb⟩
  · exact (rvTupleRank_le_rvDim hc hex A ⟨a, ha⟩).trans (le_max_left _ _)
  · exact (rvTupleRank_le_rvDim hc hex B ⟨a, hb⟩).trans (le_max_right _ _)

end SpecialTransformations.Section9
