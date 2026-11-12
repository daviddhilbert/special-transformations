module

public import Section9.ResidueIndependentFibre
public import Section9.FiniteVolumeDimension
public import Section9.VolumePairMap

@[expose] public section

/-! A full-dimensional fixed-value family of volume pairs contains
a point with independent normalized source residue coordinates over
any chosen small coefficient extension. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
local notation "RV" => CanonicalRV.RVSort M

theorem exists_generic_projection_on_fixed_value_fibre {d : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hh : StronglyHomogeneous M κ)
    (hS : Cardinal.mk S < κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (hSB : S ⊆ (B : Set M))
    (F : DefSet (rawRVSpace (M := M) d) S) (head : Fin n → Fin d)
    (hf : (rvHeadSelect head F).FiniteFibres) (hd : rvDim F = n)
    (s : F) (hsB : ∀ i, (s.val i).val ∈ B)
    (hval : ∀ t ∈ F.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s.val i)) :
    ∃ p : F, AlgebraicIndependent (residueParameterField B)
      (residueNormalize (s.val ∘ head) (p.val ∘ head)) := by
  let π := rvHeadSelect head F
  let A := π.image
  let t := s.val ∘ head
  have hd' : rvDim A = n := (rvDim_mapImage_eq_of_finiteFibres hc hex hs hS π hf).trans hd
  have ht (a : Fin n → RV) (ha : a ∈ A.carrier) (i : Fin n) :
      Values.vrv (a i) = Values.vrv (t i) := by
    obtain ⟨p, rfl⟩ := ha
    exact hval p.val p.property (head i)
  obtain ⟨x, hx, hInd⟩ := exists_independent_normalized_residue hc hex hκ hs hh hS B hB hSB
    A t (fun i => hsB (head i)) ht ⟨(π s).val, Set.mem_range_self s⟩ hd'
  obtain ⟨⟨p, hp⟩, hz⟩ := hx
  have he : residueNormalize t (p.val ∘ head) = x := by
    change (p.val ∘ head) = residueScale t x at hp
    rw [hp]
    exact residueNormalize_scale t x hz
  exact ⟨p, he.symm ▸ hInd⟩

theorem exists_generic_pair_on_fixed_value_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hh : StronglyHomogeneous M κ)
    (hS : Cardinal.mk S < κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (hSB : S ⊆ (B : Set M))
    (F : DefSet (rawRVSpace (M := M) (n + n)) S)
    (hf : (rvHeadSelect (productLeft n n) F).FiniteFibres) (hd : rvDim F = n)
    (s : F) (hsB : ∀ i, (s.val i).val ∈ B)
    (hval : ∀ t ∈ F.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s.val i)) :
    ∃ p : F, AlgebraicIndependent (residueParameterField B)
      (residueNormalize (s.val ∘ productLeft n n) (p.val ∘ productLeft n n)) :=
  exists_generic_projection_on_fixed_value_fibre hc hex hκ hs hh hS B hB hSB F _ hf hd s hsB hval

end SpecialTransformations.Section9
