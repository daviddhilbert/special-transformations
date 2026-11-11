import Section4.MultivariateLocal
import Section3.QuantifierFree
import Section3.BallGeometry
import Section3.ValuedNeighbourhood
import Section3.VFAclField

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- Finite open polydiscs with realized nonzero radii. The displayed strict
inequality uses Mathlib's multiplicative valuation order. The corresponding
paper radius is OrderDual.toDual (v (step i)); no second RV point is added. -/
structure ValuedPolydisc (v : Valuation K Γ) (n : ℕ) where
  centre : Fin n → K
  step : Fin n → K
  step_ne_zero : ∀ i, step i ≠ 0

def ValuedPolydisc.carrier {v : Valuation K Γ} {n : ℕ} (D : ValuedPolydisc v n) :
    Set (Fin n → K) := {x | ∀ i, v (x i - D.centre i) < v (D.step i)}

def ValuedPolydisc.side {v : Valuation K Γ} {n : ℕ} (D : ValuedPolydisc v n) (i : Fin n) :
    Set K := {x | v (x - D.centre i) < v (D.step i)}

theorem ValuedPolydisc.mem_carrier_iff {v : Valuation K Γ} {n : ℕ}
    (D : ValuedPolydisc v n) (x : Fin n → K) :
    x ∈ D.carrier ↔ x ∈ Set.pi Set.univ D.side := by
  simp only [carrier, side, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]

theorem ValuedPolydisc.side_mem_nhds [Valued K Γ] {n : ℕ}
    (D : ValuedPolydisc (Valued.v : Valuation K Γ) n) (i : Fin n) :
    D.side i ∈ 𝓝 (D.centre i) := by
  let v : Valuation K Γ := Valued.v
  apply Valued.mem_nhds.mpr
  refine ⟨Units.mk0 (v.restrict (D.step i))
    (v.restrict.ne_zero_iff.mpr (D.step_ne_zero i)), ?_⟩
  intro x hx
  exact v.restrict_lt_iff.mp hx

theorem ValuedPolydisc.side_infinite [Valued K Γ]
    (hnt : ∃ ε : K, ε ≠ 0 ∧ Valued.v ε < 1) {n : ℕ}
    (D : ValuedPolydisc (Valued.v : Valuation K Γ) n) (i : Fin n) : (D.side i).Infinite :=
  infinite_valued_neighbourhood hnt (D.centre i) (D.side_mem_nhds i)

theorem ValuedPolydisc.carrier_eq_paper_balls {v : Valuation K Γ} {n : ℕ}
    (D : ValuedPolydisc v n) :
    D.carrier = {x | ∀ i, x i ∈ Balls.openDisc v (D.centre i)
      (Balls.openRadius (v (D.step i)) (v.ne_zero_iff.mpr (D.step_ne_zero i)))} := by
  rfl

theorem exists_nonzero_ball_subset [Valued K Γ] (a : K) {s : Set K} (hs : s ∈ 𝓝 a) :
    ∃ r : K, r ≠ 0 ∧ {x | Valued.v (x - a) < Valued.v r} ⊆ s := by
  let v : Valuation K Γ := Valued.v
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  obtain ⟨r, hr⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass v) γ.val
  have hr' : v.restrict r = γ.val := hr
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hr'
    exact γ.ne_zero hr'.symm
  refine ⟨r, hr0, ?_⟩
  intro x hx
  apply hγ
  rw [← hr']
  exact v.restrict_lt_iff.mpr hx

theorem exists_polydisc_subset_of_mem_nhds [Valued K Γ] {n : ℕ}
    (a : Fin n → K) {s : Set (Fin n → K)} (hs : s ∈ 𝓝 a) :
    ∃ D : ValuedPolydisc (Valued.v : Valuation K Γ) n, D.centre = a ∧ D.carrier ⊆ s := by
  rw [nhds_pi, Filter.mem_pi'] at hs
  obtain ⟨I, t, ht, hsub⟩ := hs
  choose r hr0 hrsub using fun i => exists_nonzero_ball_subset (a i) (ht i)
  refine ⟨⟨a, r, hr0⟩, rfl, ?_⟩
  intro x hx
  apply hsub
  intro i hi
  exact hrsub i (hx i)

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable [Valued (VFType (M := M)) Γ]

/-- Released QE and the finite-tuple local-polynomial argument give a
neighbourhood at an algebraically independent point of a definable VF set. -/
theorem independent_definable_mem_nhds
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) {n : ℕ} (X : Set (Fin n → M))
    (hX : DefinableOver S (fun _ => .vf) X) (a : Fin n → VFType (M := M))
    (ha : AlgebraicIndependent (vfParameterField S) a) (haX : vfValues a ∈ X) :
    {x : Fin n → VFType (M := M) | vfValues x ∈ X} ∈ 𝓝 a := by
  obtain ⟨p, φ, hqf, hws, heq⟩ := hX.quantifier_free hM
  let E := vfParameterField S
  have hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E :=
    fun i h => Subfield.subset_closure (p.mem_base i)
  have hφ (x : Fin n → VFType (M := M)) :
      vfValues x ∈ X ↔ φ.Realize p.values (vfValues x) :=
    (Set.ext_iff.mp heq (vfValues x)).trans (and_iff_right (fun i => (x i).property))
  filter_upwards [MultivariateLocal.qf_local p E hp hv a ha φ hqf hws] with x hx
  exact (hφ x).mpr (hx.mpr ((hφ a).mp haX))

theorem independent_definable_contains_polydisc
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) {n : ℕ} (X : Set (Fin n → M))
    (hX : DefinableOver S (fun _ => .vf) X) (a : Fin n → VFType (M := M))
    (ha : AlgebraicIndependent (vfParameterField S) a) (haX : vfValues a ∈ X) :
    ∃ D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) n,
      D.centre = a ∧ ∀ x ∈ D.carrier, vfValues x ∈ X :=
  exists_polydisc_subset_of_mem_nhds a (independent_definable_mem_nhds hv S X hX a ha haX)

end SpecialTransformations.Section4

end
