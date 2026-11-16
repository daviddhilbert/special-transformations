module

public import Section4.ResidueFieldInterpretation
public import Section4.ResidueMultivariateFunctions
public import Section4.FiniteCover

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped BigOperators

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem residueFieldValues_injective {n : ℕ} :
    Function.Injective (residueFieldValues (M := M) (n := n)) := by
  intro a b he
  funext i
  exact residueRaw_injective (congrFun he i)

/-- Saturation combines the pointwise polynomial dependence of a fixed
coordinate selection into one nonzero equation over the original residue
parameter field. The finite cover uses actual guarded LRV images. -/
theorem exists_residue_polynomial_vanishing_on_selection
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M)
    (hB : Cardinal.mk B < κ) {n d : ℕ}
    (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def (residueParameterField B) D)
    (v : Fin d → Fin n)
    (hdep : ∀ a ∈ D, ¬ AlgebraicIndependent (residueParameterField B) (a ∘ v)) :
    ∃ p : MvPolynomial (Fin d) (residueParameterField B), p ≠ 0 ∧
      ∀ a ∈ D, p.eval₂ (residueParameterField B).subtype (a ∘ v) = 0 := by
  let E := residueParameterField B
  let Poly := {p : MvPolynomial (Fin d) E // p ≠ 0}
  let Z (p : Poly) : Set (Fin n → M) :=
    residueFieldImage {a : Fin n → ModelResidue M | p.val.eval₂ E.subtype (a ∘ v) = 0}
  have hZ (p : Poly) : (B : Set M).Definable LRV (Z p) :=
    residueFieldImage_raw_definable E (B : Set M) (fun c => c.property) _
      ((mvPolynomial_zeroSet_definable E p.val).preimage_comp v)
  have hW : (B : Set M).Definable LRV (residueFieldImage D) :=
    residueFieldImage_raw_definable E (B : Set M) (fun c => c.property) D hD
  have hcover : ∀ z ∈ residueFieldImage D, ∃ c ∈ Set.range Z, z ∈ c := by
    rintro z ⟨a, ha, he⟩
    have hex : ∃ p : MvPolynomial (Fin d) E,
        p ≠ 0 ∧ p.eval₂ E.subtype (a ∘ v) = 0 := by
      by_contra h
      apply hdep a ha
      apply algebraicIndependent_iff.mpr
      intro p hp
      by_contra hp0
      exact h ⟨p, hp0, hp⟩
    obtain ⟨p, hp, hpa⟩ := hex
    exact ⟨Z ⟨p, hp⟩, Set.mem_range_self _, a, hpa, he⟩
  obtain ⟨C, hC, hsub, hcov⟩ := definable_finite_subcover_index hs (B : Set M) hB
    (residueFieldImage D) hW (Set.range Z)
    (by rintro _ ⟨p, rfl⟩; exact hZ p) hcover
  letI : Fintype C := hC.fintype
  have hchoice (c : C) : ∃ p : Poly, Z p = c.val := hsub c.property
  let p (c : C) : Poly := Classical.choose (hchoice c)
  have hpc (c : C) : Z (p c) = c.val := Classical.choose_spec (hchoice c)
  refine ⟨∏ c : C, (p c).val, Finset.prod_ne_zero_iff.mpr (fun c _ => (p c).property), ?_⟩
  intro a ha
  obtain ⟨c, hc, hac⟩ := hcov (residueFieldValues a) ⟨a, ha, rfl⟩
  let c' : C := ⟨c, hc⟩
  have hz := (Set.ext_iff.mp (hpc c') (residueFieldValues a)).mpr hac
  obtain ⟨a', ha', he⟩ := hz
  have he' : a' = a := residueFieldValues_injective he
  subst a'
  rw [MvPolynomial.eval₂_prod]
  exact Finset.prod_eq_zero_iff.mpr ⟨c', Finset.mem_univ _, ha'⟩

end SpecialTransformations.Section4.ResiduePurity

end
