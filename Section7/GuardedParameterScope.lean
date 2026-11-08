import Section7.GeneratedRVRepresentatives
import Section3.GuardedRationalNormalForm

/-!
# Original-base coefficient assignments for all-RV formulas

The VF slots in an all-RV input formula can only be parameter slots.
Their values and representatives of the named RV parameters therefore
lie in the original generated base's VF field. The assignments below do
not depend on a choice of representatives of the free RV coordinates.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GuardedRVNormalForm

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def allRVVariableEquiv (n : ℕ) : RVVariableSlot (fun _ : Fin n => SortTag.rv) ≃ Fin n where
  toFun := Subtype.val
  invFun i := ⟨i, rfl⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

theorem originalBase_guarded_parameters {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (p : Parameters B.real) (n : ℕ) :
    let sn := fun _ : Fin n => SortTag.rv
    let E := vfDefinableClosureFieldBase B
    ∃ (a : VFSlot p.sorts sn → E) (r : RVParameterSlot p.sorts → E),
      (∀ x : Fin n → M, ∀ hx : ∀ i, iRV (x i),
        SourceAssignment.vfValues p.sorts sn p.values x p.sorted hx =
          fun i => (a i : VFType (M := M))) ∧
      SourceAssignment.rvParameters p.sorts p.values p.sorted =
        fun i => CanonicalRV.encodedRv (r i : VFType (M := M)) := by
  classical
  let sn := fun _ : Fin n => SortTag.rv
  let E := vfDefinableClosureFieldBase B
  let x₀ : Fin n → M := fun _ => iRVZero
  have hx₀ (i : Fin n) : iRV (x₀ i) := rv_zero_mem hM
  let a₀ := SourceAssignment.vfValues p.sorts sn p.values x₀ p.sorted hx₀
  have hslot (i : VFSlot p.sorts sn) : ∃ j : Fin p.length, i.val = Sum.inl j := by
    rcases he : i.val with j | j
    · exact ⟨j, rfl⟩
    · have h := i.property
      change Sum.elim p.sorts sn i.val = .vf at h
      rw [he] at h
      exact SortTag.noConfusion h
  have ha₀ (i : VFSlot p.sorts sn) : a₀ i ∈ E := by
    apply (mem_generatedBase_vfField B hB (a₀ i)).mpr
    obtain ⟨j, hj⟩ := hslot i
    change Sum.elim p.values x₀ i.val ∈ B.real
    rw [hj]
    exact p.mem_base j
  let a : VFSlot p.sorts sn → E := fun i => ⟨a₀ i, ha₀ i⟩
  have hr (i : RVParameterSlot p.sorts) :
      ∃ r : E, CanonicalRV.encodedRv (r : VFType (M := M)) =
        SourceAssignment.rvParameters p.sorts p.values p.sorted i := by
    let t := SourceAssignment.rvParameters p.sorts p.values p.sorted i
    have htB : t.val ∈ B.real := p.mem_base i.val
    by_cases ht : t = 0
    · exact ⟨0, RVOperations.rv_zero.trans ht.symm⟩
    · obtain ⟨u, hu, hr⟩ := generatedBase_rv_representative hκ hs h00 B hsmall hB t htB ht
      exact ⟨⟨u, (mem_generatedBase_vfField B hB u).mpr hu⟩, hr⟩
  choose r hr using hr
  refine ⟨a, r, ?_, funext (fun i => (hr i).symm)⟩
  intro x hx
  funext i
  apply Subtype.ext
  obtain ⟨j, hj⟩ := hslot i
  change Sum.elim p.values x i.val = Sum.elim p.values x₀ i.val
  simp only [hj, Sum.elim_inl]

end SpecialTransformations.Section7
