module

public import Section4.InjectionRefinement
public import Section4.Dimension
public import Section4.VFPadding

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# VF dimension on definable mixed real tuples

Auxiliary coordinate lists are finite products of RV and Gamma coordinates.
Their parenthesization has no mathematical significance and lets the
finite-to-one refinement append RV coordinates without choosing Gamma
representatives. The Gamma presentation is an explicit parameter.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

inductive AuxiliaryCoordinates where
  | rv (n : ℕ)
  | gamma (n : ℕ)
  | prod (left right : AuxiliaryCoordinates)

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def AuxiliaryCoordinates.space (Γ : DefinableGeometry.Space LRV M) :
    AuxiliaryCoordinates → DefinableGeometry.Space LRV M
  | .rv n => rawRVSpace n
  | .gamma n => Γ.power (Fin n)
  | .prod a b => (a.space Γ).prod (b.space Γ)

def HasVFDimLE (Γ : DefinableGeometry.Space LRV M)
    {P : DefinableGeometry.Space LRV M} {S : Set M} (A : DefSet P S) (k : ℕ) : Prop :=
  Dimension.HasDim rawVFSpace (AuxiliaryCoordinates.space Γ) A k

noncomputable def vfDim (Γ : DefinableGeometry.Space LRV M)
    {P : DefinableGeometry.Space LRV M} {S : Set M} (A : DefSet P S) : ℕ :=
  Dimension.dim rawVFSpace (AuxiliaryCoordinates.space Γ) A

variable (Γ : DefinableGeometry.Space LRV M) {S : Set M} {n r : ℕ}

theorem mixed_has_dimension_bound (A : DefSet (rawMixedSpace (M := M) n r) S) :
    HasVFDimLE Γ A n := by
  refine ⟨n, le_rfl, .rv r, (Map.id A).toUniv, ?_⟩
  exact Map.finiteFibres_of_injective (Map.toUniv_injective Function.injective_id)

theorem vfDim_le_arity (A : DefSet (rawMixedSpace (M := M) n r) S) : vfDim Γ A ≤ n :=
  Nat.sInf_le (mixed_has_dimension_bound Γ A)

theorem vfDim_le_iff (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) :
    vfDim Γ A ≤ k ↔ HasVFDimLE Γ A k :=
  Dimension.dim_le_iff rawVFSpace (AuxiliaryCoordinates.space Γ)
    ⟨n, mixed_has_dimension_bound Γ A⟩ k

theorem vfDim_attained (A : DefSet (rawMixedSpace (M := M) n r) S) :
    ∃ i : AuxiliaryCoordinates, ∃ f : Map A
      (DefSet.univ ((rawVFSpace (vfDim Γ A)).prod (i.space Γ)) S), f.FiniteFibres := by
  obtain ⟨k, hk, i, f, hf⟩ := (vfDim_le_iff Γ A (vfDim Γ A)).mp le_rfl
  have hd : vfDim Γ A ≤ k := Nat.sInf_le
    (show HasVFDimLE Γ A k from ⟨k, le_rfl, i, f, hf⟩)
  have he : k = vfDim Γ A := hk.antisymm hd
  subst k
  exact ⟨i, f, hf⟩

theorem vfDim_le_iff_bounded_injection (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) :
    vfDim Γ A ≤ k ↔
      ∃ k' ≤ k, ∃ i : AuxiliaryCoordinates, ∃ f : Map A
        (DefSet.univ ((rawVFSpace k').prod (i.space Γ)) S), Function.Injective f := by
  constructor
  · intro hd
    obtain ⟨k', hk', i, f, hf⟩ := (vfDim_le_iff Γ A k).mp hd
    obtain ⟨j, h, hinj⟩ := injection_refinement h00 hs hsmall f hf
    let P := rawVFSpace (M := M) k'
    let Q := i.space Γ
    let R := rawRVSpace (M := M) j
    let assoc : Map (DefSet.univ ((P.prod Q).prod R) S)
        (DefSet.univ (P.prod (Q.prod R)) S) :=
      Map.ofCodes _ (fun x => (x.1.1, (x.1.2, x.2)))
        (fun z => Sum.elim (fun u => z (.inl (.inl u)))
          (Sum.elim (fun u => z (.inl (.inr u))) (fun u => z (.inr u))))
        (fun u => by cases u with
          | inl u => exact Set.DefinableFun.proj LRV
          | inr u => cases u <;> exact Set.DefinableFun.proj LRV)
        (fun c => ⟨c.property.1.1, c.property.1.2, c.property.2⟩)
        (fun _ => rfl)
    let g := assoc.comp (f.pair h).toUniv
    refine ⟨k', hk', .prod i (.rv j), g, ?_⟩
    intro a b he
    apply hinj
    apply Subtype.ext
    exact congrArg (fun z => ((z.1, z.2.1), z.2.2)) (congrArg Subtype.val he)
  · rintro ⟨k', hk', i, f, hf⟩
    exact (vfDim_le_iff Γ A k).mpr
      ⟨k', hk', i, f, Map.finiteFibres_of_injective hf⟩

theorem injection_at_vfDim (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    ∃ i : AuxiliaryCoordinates, ∃ f : Map A
      (DefSet.univ ((rawVFSpace (vfDim Γ A)).prod (i.space Γ)) S), Function.Injective f := by
  obtain ⟨k, hk, i, f, hf⟩ :=
    (vfDim_le_iff_bounded_injection Γ h00 hs hsmall A (vfDim Γ A)).mp le_rfl
  have hd : vfDim Γ A ≤ k := (vfDim_le_iff Γ A k).mpr
    ⟨k, le_rfl, i, f, Map.finiteFibres_of_injective hf⟩
  have he : k = vfDim Γ A := hk.antisymm hd
  subst k
  exact ⟨i, f, hf⟩

/-- Lemma 4.2, with an explicitly typed finite list of RV/Gamma factors.
The target has exactly k VF coordinates, also when k exceeds the minimum. -/
theorem lemma_4_2 (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) :
    vfDim Γ A ≤ k ↔ ∃ i : AuxiliaryCoordinates, ∃ f : Map A
      (DefSet.univ ((rawVFSpace k).prod (i.space Γ)) S), Function.Injective f := by
  constructor
  · intro hd
    obtain ⟨k', hk', i, f, hf⟩ :=
      (vfDim_le_iff_bounded_injection Γ h00 hs hsmall A k).mp hd
    exact ⟨i, (vfPadding hk' (i.space Γ) S).comp f,
      (vfPadding_injective hk' (i.space Γ) S).comp hf⟩
  · rintro ⟨i, f, hf⟩
    exact (vfDim_le_iff Γ A k).mpr
      ⟨k, le_rfl, i, f, Map.finiteFibres_of_injective hf⟩

end SpecialTransformations.Section4
