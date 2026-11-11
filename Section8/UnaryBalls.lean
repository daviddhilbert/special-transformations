import Section8.UniformBalls
import Section3.RootFreeConstancy
import Section3.ClosureBridge
import ValuedFieldExtension

/-! An infinite definable unary VF set contains an arbitrarily small open
ball. We use the stronger checked finite-obstacle form of unary locality. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]
variable (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

private theorem strictBall_mem_nhds (a r : VFType (M := M)) (hr : r ≠ 0) :
    {x : VFType (M := M) | Valued.v (x - a) < Valued.v r} ∈ 𝓝 a :=
  Section4.ValuedPolydisc.side_mem_nhds
    (⟨fun _ => a, fun _ => r, fun _ => hr⟩ :
      Section4.ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) 1) 0

include hv in
theorem rawOpenBall_infinite {a r : M} (ha : iVF a) (hr : iVF r) (hr0 : r ≠ iVFZero) :
    (rawOpenBall a r).Infinite := by
  let a' : VFType (M := M) := ⟨a, ha⟩
  let r' : VFType (M := M) := ⟨r, hr⟩
  have hr' : r' ≠ 0 := fun h => hr0 (congrArg Subtype.val h)
  obtain ⟨ε, hε0, hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  have hnt : ∃ ε : VFType (M := M), ε ≠ 0 ∧ Valued.v ε < 1 := by
    refine ⟨ε, hε0, lt_of_not_ge (fun h => hε ((hv 1 ε).mpr ?_))⟩
    simpa only [map_one] using h
  have hInf := infinite_valued_neighbourhood hnt a' (strictBall_mem_nhds a' r' hr')
  apply (hInf.image Subtype.val_injective.injOn).mono
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_rawOpenBall_iff Valued.v hv a' r' x hr').mpr hx

include hv in
theorem infinite_definable_contains_small_ball {S A : Set M}
    (hA : DefinableAt S .vf A) (hInf : A.Infinite)
    {r : M} (hr : iVF r) (hr0 : r ≠ iVFZero) :
    ∃ a ∈ A, ∃ s : M, iVF s ∧ s ≠ iVFZero ∧
      rawOpenBall a s ⊆ A ∩ rawOpenBall a r := by
  classical
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  obtain ⟨R, _, _, hlocal⟩ := finite_definable_obstacles v hv S A hA
  obtain ⟨a, haA, haR⟩ := Set.not_subset.mp
    (show ¬ A ⊆ Subtype.val '' (R : Set (VFType (M := M))) from
      fun h => hInf ((R.finite_toSet.image _).subset h))
  let a' : VFType (M := M) := ⟨a, hA.2 haA⟩
  let r' : VFType (M := M) := ⟨r, hr⟩
  have hr' : r' ≠ 0 := fun h => hr0 (congrArg Subtype.val h)
  have hR : a' ∈ (R : Set (VFType (M := M)))ᶜ := fun h => haR ⟨a', h, rfl⟩
  have hU := Filter.inter_mem (strictBall_mem_nhds a' r' hr')
    (R.finite_toSet.isClosed.isOpen_compl.mem_nhds hR)
  obtain ⟨s, hs0, hs⟩ := Section4.exists_nonzero_ball_subset a' hU
  let ρ : Balls.OpenRadius Γ := Balls.openRadius (v s) (v.ne_zero_iff.mpr hs0)
  have hdisc (x : VFType (M := M)) : x ∈ Balls.openDisc v a' ρ ↔ v (x - a') < v s := by
    rfl
  have havoid : ∀ c ∈ R, c ∉ Balls.openDisc v a' ρ := by
    intro c hc hcd
    exact (hs ((hdisc c).mp hcd)).2 hc
  refine ⟨a, haA, s.val, s.property, fun he => hs0 (Subtype.ext he), ?_⟩
  intro x hx
  let x' : VFType (M := M) := ⟨x, hx.2.1⟩
  have hxs := (mem_rawOpenBall_iff v hv a' s x' hs0).mp hx
  exact ⟨(hlocal a' ρ havoid a' (Balls.centre_mem_openDisc v a' ρ)
    x' ((hdisc x').mpr hxs)).mp haA,
    (mem_rawOpenBall_iff v hv a' r' x' hr').mpr (hs hxs).1⟩

end SpecialTransformations.Section8
