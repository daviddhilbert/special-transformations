module

public import Section8.VFNeighbourhoods

@[expose] public section

/-! Definition 8.8 on actual VF and RV tuples. Equality of the fibres
is equality of sets of RV tuples. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

def rvFibre (G : Set (Fin n ⊕ Fin m → M)) (a : Fin n → VFType (M := M)) :
    Set (Fin m → CanonicalRV.RVSort M) :=
  {t | Sum.elim (vfValues a) (rvValues t) ∈ G}

def rvLocallyConstantAt (F : (Fin n → VFType (M := M)) → Set (Fin m → CanonicalRV.RVSort M))
    (a : Fin n → VFType (M := M)) : Prop :=
  ∃ U, IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U, F b = F a

def rvLocallyConstantOn (F : (Fin n → VFType (M := M)) → Set (Fin m → CanonicalRV.RVSort M))
    (A : Set (Fin n → VFType (M := M))) : Prop :=
  IsOpen A ∧ ∀ a ∈ A, rvLocallyConstantAt F a

theorem rvLocallyConstantAt_iff_nhds
    (F : (Fin n → VFType (M := M)) → Set (Fin m → CanonicalRV.RVSort M))
    (a : Fin n → VFType (M := M)) :
    rvLocallyConstantAt F a ↔ {b | F b = F a} ∈ 𝓝 a := by
  constructor
  · rintro ⟨U, hU, ha, hF⟩
    exact Filter.mem_of_superset (hU.mem_nhds ha) hF
  · intro h
    obtain ⟨U, hUF, hU, ha⟩ := mem_nhds_iff.mp h
    exact ⟨U, hU, ha, hUF⟩

theorem rvLocallyConstantAt_iff_uniformBall
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : (Fin n → VFType (M := M)) → Set (Fin m → CanonicalRV.RVSort M))
    (a : Fin n → VFType (M := M)) :
    rvLocallyConstantAt F a ↔ ∃ r : VFType (M := M), r ≠ 0 ∧
      ∀ b, vfValues b ∈ uniformBall (vfValues a) r.val → F b = F a := by
  rw [rvLocallyConstantAt_iff_nhds]
  exact ⟨exists_uniformBall_subset_of_mem_nhds hv a, fun ⟨r, hr, h⟩ =>
    Filter.mem_of_superset (uniformBall_mem_nhds hv a r hr) (fun b hb => h b hb)⟩

theorem isOpen_rvLocallyConstantAt
    (F : (Fin n → VFType (M := M)) → Set (Fin m → CanonicalRV.RVSort M)) :
    IsOpen {a | rvLocallyConstantAt F a} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨U, hU, haU, hF⟩ := ha
  refine Filter.mem_of_superset (hU.mem_nhds haU) (fun b hb => ?_)
  exact ⟨U, hU, hb, fun c hc => (hF c hc).trans (hF b hb).symm⟩

end SpecialTransformations.Section8
