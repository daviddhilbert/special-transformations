module

public import Section9.FinitePointLimits
public import Section8.VFNeighbourhoods
public import Section8.IsolationRadius

@[expose] public section

/-! The closure used in Lemma 9.2 agrees with topological closure for
every compatible presentation of the valuation. -/

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VFType (M := M)) G]

theorem vfClosure_eq_closure
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (L : Set (Fin m → VFType (M := M))) : vfClosure L = closure L := by
  ext b
  rw [mem_closure_iff_nhds]
  have ball_eq (ε : Values.Gamma (M := M)) (r : VFType (M := M)) (hr : r ≠ 0)
      (hval : Values.vfValueHom r = ε.val) :
      vfBall b ε = {x | vfValues x ∈ uniformBall (vfValues b) r.val} := by
    ext x
    rw [mem_vfBall_iff_gammaUniformBall, gammaUniformBall_eq_uniformBall _ ε r hr hval]
    rfl
  constructor
  · intro hb U hU
    obtain ⟨r, hr, hsub⟩ := exists_uniformBall_subset_of_mem_nhds hv b hU
    let ε := Values.gammaOf (CanonicalRV.encodedRv r)
      (fun h => hr ((CanonicalRV.encodedRv_zero_iff r).mp h))
    obtain ⟨x, hx, hxB⟩ := hb ε
    rw [ball_eq ε r hr rfl] at hxB
    exact ⟨x, hsub hxB, hx⟩
  · intro hb ε
    obtain ⟨r, hr, hval⟩ := gamma_has_vf_representative ε
    obtain ⟨x, hxB, hx⟩ := hb _ (uniformBall_mem_nhds hv b r hr)
    rw [← ball_eq ε r hr hval] at hxB
    exact ⟨x, hx, hxB⟩

/-- Lemma 9.2 stated directly in the valuation topology. -/
theorem lemma_9_2_topological {n : ℕ}
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L₁ L₂ : Set (Fin m → VFType (M := M))}
    (h₁ : IsMinimalVFLimitSet A a f L₁) (h₂ : IsMinimalVFLimitSet A a f L₂) :
    closure L₁ = closure L₂ := by
  rw [← vfClosure_eq_closure hv L₁, ← vfClosure_eq_closure hv L₂]
  exact lemma_9_2 h₁ h₂

end SpecialTransformations.Section9
