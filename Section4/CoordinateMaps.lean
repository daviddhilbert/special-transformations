module

public import Section4.MapParameters
public import Section4.FiniteCorrespondence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def vfSelect {S : Set M} {n r k : ℕ} (v : Fin k → Fin n)
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) k r) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) k r
  let F (z : P.Index → M) : Q.Index → M :=
    Sum.elim (fun j => z (.inl (v j))) (z ∘ Sum.inr)
  have hcode (c : P.domain) : mixedValues ((P.decode c).1 ∘ v, (P.decode c).2) = F c.val := by
    have hc := mixedValues_decode c
    funext i
    cases i with
    | inl j => exact congrFun hc (.inl (v j))
    | inr j => exact congrFun hc (.inr j)
  have hdom (c : P.domain) : F c.val ∈ Q.domain := by
    rw [← hcode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A (fun a => (a.1 ∘ v, a.2)) F
    (fun i => by cases i <;> exact Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode ⟨F c.val, hdom c⟩).trans (hcode c).symm

@[simp] theorem vfSelect_apply {S : Set M} {n r k : ℕ} (v : Fin k → Fin n)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (a : A) :
    (vfSelect v A a).val = (a.val.1 ∘ v, a.val.2) := rfl

theorem vfDim_image_le (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded) {n r m s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) :
    vfDim Δ f.image ≤ vfDim Δ A := by
  have he : finiteRelationImage A f.graph_definable = f.image := by
    apply DefSet.eq_of_carrier_eq
    ext y
    constructor
    · rintro ⟨a, b, hb, hy⟩
      exact ⟨b, hy⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, a, rfl, ha⟩
  rw [← he]
  exact corollary_4_5 hcan hs hsmall Δ hΔ A f.graph_definable (fun a => f.graph_values_finite a.val)

end SpecialTransformations.Section4

end
