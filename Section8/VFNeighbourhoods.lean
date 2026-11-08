import Section8.UniformBalls

/-! A single realized radius gives a neighbourhood basis for finite VF
tuples in the valuation topology. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem uniformBall_mem_nhds
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VFType (M := M)) (r : VFType (M := M)) (hr : r ≠ 0) :
    {x | vfValues x ∈ uniformBall (vfValues a) r.val} ∈ 𝓝 a := by
  let D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) n :=
    ⟨a, fun _ => r, fun _ => hr⟩
  have hs (i : Fin n) : {x : Fin n → VFType (M := M) | x i ∈ D.side i} ∈ 𝓝 a :=
    (continuous_apply i).continuousAt.preimage_mem_nhds (D.side_mem_nhds i)
  filter_upwards [Filter.eventually_all.mpr hs] with x hx
  exact (mem_uniformBall_iff Valued.v hv a x r hr).mpr hx

theorem exists_uniformBall_subset_of_mem_nhds
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VFType (M := M)) {A : Set (Fin n → VFType (M := M))} (hA : A ∈ 𝓝 a) :
    ∃ r : VFType (M := M), r ≠ 0 ∧ {x | vfValues x ∈ uniformBall (vfValues a) r.val} ⊆ A := by
  classical
  obtain ⟨D, hcentre, hD⟩ := exists_polydisc_subset_of_mem_nhds a hA
  let T := insert (1 : VFType (M := M)) (Finset.univ.image D.step)
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image T Valued.v ⟨1, Finset.mem_insert_self _ _⟩
  have hr0 : r ≠ 0 := by
    rcases Finset.mem_insert.mp hr with he | he
    · exact he.symm ▸ one_ne_zero
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      exact D.step_ne_zero i
  refine ⟨r, hr0, fun x hx => hD ?_⟩
  have h := (mem_uniformBall_iff Valued.v hv a x r hr0).mp hx
  intro i
  rw [hcentre]
  exact (h i).trans_le (hmin (D.step i) (Finset.mem_insert.mpr
    (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))))

end SpecialTransformations.Section8
