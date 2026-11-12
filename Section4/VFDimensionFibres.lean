module

public import Section4.VFDimensionRank
public import Section3.SmallFiniteParameters

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfTupleTrdeg_union_rv (S T : Set M) (hT : ∀ x ∈ T, iRV x)
    {n : ℕ} (a : Fin n → VFType (M := M)) :
    vfTupleTrdeg (S ∪ T) a = vfTupleTrdeg S a := by
  unfold vfTupleTrdeg
  simp only [vfParameterField_union_rv S T hT]

variable (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    {n r : ℕ} {Q : DefinableGeometry.Space LRV M} (hQ : Q.RVCoded)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet Q S} (f : Map A B)

include hcan hκ hs hsmall hΓ hQ in
theorem vfDim_fibre_le (b : B) (c : Q.domain) (hc : Q.decode c = b.val) :
    vfDim Γ (f.fibre b c hc) ≤ vfDim Γ A := by
  apply vfDim_le_of_point_trdeg hs
    (small_union_finite hκ S hsmall _ (Set.finite_range c.val)) Γ
  rintro ⟨x, a, hax, he⟩
  rw [vfTupleTrdeg_union_rv S _ (fun x hx => by
    obtain ⟨j, rfl⟩ := hx; exact hQ c j)]
  change vfTupleTrdeg S x.1 ≤ (vfDim Γ A : Cardinal)
  rw [← hax]
  exact vfTupleTrdeg_le_vfDim hcan Γ hΓ A a

/-- All real representatives are retained in this index. Different codes of
the same target value give the same fibre over possibly different RV-only
parameter sets, which have the same VF parameter field. -/
abbrev FibreCode := Σ b : B, {c : Q.domain // Q.decode c = b.val}

def codedFibre (p : FibreCode (B := B)) := f.fibre p.1 p.2.val p.2.property

include hcan hκ hs hsmall hΓ hQ in
theorem fibre_dimensions_bounded :
    BddAbove (Set.range (fun p : FibreCode (B := B) => vfDim Γ (codedFibre f p))) := by
  refine ⟨vfDim Γ A, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact vfDim_fibre_le hcan hκ hs hsmall Γ hΓ hQ f p.1 p.2.val p.2.property

include hcan hκ hs hsmall hΓ hQ in
/-- Lemma 4.3 as an equality with the bounded natural supremum of the fibre
dimensions. It is a maximum for nonempty A and has value zero for empty A. -/
theorem lemma_4_3 : vfDim Γ A =
    ⨆ p : FibreCode (B := B), vfDim Γ (codedFibre f p) := by
  apply Nat.le_antisymm
  · apply vfDim_le_of_point_trdeg hs hsmall Γ A
    intro a
    obtain ⟨c, hc⟩ := Q.onto (f a).val
    let p : FibreCode (B := B) := ⟨f a, c, hc⟩
    let a' : codedFibre f p := ⟨a.val, a, rfl, rfl⟩
    have hp := vfTupleTrdeg_le_vfDim hcan Γ hΓ (codedFibre f p) a'
    rw [vfTupleTrdeg_union_rv S _ (fun x hx => by
      obtain ⟨j, rfl⟩ := hx; exact hQ c j)] at hp
    exact hp.trans (by exact_mod_cast
      (le_ciSup (fibre_dimensions_bounded hcan hκ hs hsmall Γ hΓ hQ f) p))
  · apply ciSup_le'
    intro p
    exact vfDim_fibre_le hcan hκ hs hsmall Γ hΓ hQ f p.1 p.2.val p.2.property

include hcan hκ hs hsmall hΓ hQ in
theorem exists_fibre_dimension_eq (hne : A.carrier.Nonempty) :
    ∃ b : B, ∃ c : Q.domain, ∃ hc : Q.decode c = b.val,
      vfDim Γ (f.fibre b c hc) = vfDim Γ A := by
  obtain ⟨a, ha⟩ := hne
  let a' : A := ⟨a, ha⟩
  obtain ⟨c, hc⟩ := Q.onto (f a').val
  let p : FibreCode (B := B) := ⟨f a', c, hc⟩
  have hrange : (Set.range (fun q : FibreCode (B := B) => vfDim Γ (codedFibre f q))).Nonempty :=
    ⟨_, p, rfl⟩
  obtain ⟨q, hq⟩ := Nat.sSup_mem hrange
    (fibre_dimensions_bounded hcan hκ hs hsmall Γ hΓ hQ f)
  exact ⟨q.1, q.2.val, q.2.property,
    hq.trans (lemma_4_3 hcan hκ hs hsmall Γ hΓ hQ f).symm⟩

end SpecialTransformations.Section4

end
