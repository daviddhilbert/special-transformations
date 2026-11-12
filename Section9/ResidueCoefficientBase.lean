module

public import Section9.GaussEvaluation
public import Section9.SmallValuedCoefficients
public import Section4.ResidueParameterField
public import Section4.ResidueFieldInterpretation

@[expose] public section

/-! Place the residue parameters of a small substructure in the
residue field of a small algebraically closed VF coefficient field. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "VF" => VFType (M := M)
local notation "k" => ModelResidue M
local notation "v" => Values.presentationValuation (M := M)
local notation "O" => Valuation.valuationSubring (Values.presentationValuation (M := M))

noncomputable abbrev residueCoefficientField (E : Subfield VF) : Subfield k :=
  (residueFieldInclusion v E).fieldRange

theorem residueCoefficientField_isAlgClosed (E : Subfield VF) [IsAlgClosed E] :
    IsAlgClosed (residueCoefficientField E) := by
  let w := (v).comap E.subtype
  letI : IsAlgClosed (ResidueField w.valuationSubring) :=
    ValOneEC.Johnson.isAlgClosed_residueField w
  let e := (residueFieldInclusion v E).rangeRestrictFieldEquiv
  constructor
  intro p
  have h := (IsAlgClosed.splits (p.map e.symm.toRingHom)).map e.toRingHom
  have he : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact e.apply_symm_apply (p.coeff i)
  exact he ▸ h

theorem exists_residueCoefficient_extension {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ) :
    ∃ T : Set M, (B : Set M) ⊆ T ∧ Cardinal.mk T < κ ∧
      Cardinal.mk (vfParameterField T) < κ ∧ IsAlgClosed (vfParameterField T) ∧
      residueParameterField B ≤ residueCoefficientField (vfParameterField T) := by
  classical
  let E := residueParameterField B
  have hE : Cardinal.mk E < κ := (Cardinal.mk_le_of_injective
    (f := fun c : E => (⟨residueRaw c.val, c.property⟩ : B))
    (fun a b h => Subtype.ext (residueRaw_injective (congrArg (fun c : B => c.val) h)))).trans_lt hB
  choose x hx using fun c : E => residue_surjective (R := O) (c : k)
  let names (c : E) := (x c : VF).val
  let S := (B : Set M) ∪ Set.range names
  have hS : Cardinal.mk S < κ := (Cardinal.mk_union_le _ _).trans_lt
    (Cardinal.add_lt_of_lt hκ.le hB (Cardinal.mk_range_le.trans_lt hE))
  obtain ⟨T, hST, hT, hField, hclosed, _⟩ :=
    exists_small_algClosed_vfParameter_extension hκ S hS (Fin.elim0 : Fin 0 → VF)
  refine ⟨T, Set.subset_union_left.trans hST, hT, hField, hclosed, ?_⟩
  intro c hc
  let a : E := ⟨c, hc⟩
  let L := vfParameterField T
  have ha : (x a : VF) ∈ L := Subfield.subset_closure (hST (Or.inr (Set.mem_range_self a)))
  let y : ((v).comap L.subtype).valuationSubring := ⟨⟨(x a : VF), ha⟩, (x a).property⟩
  change c ∈ (residueFieldInclusion v L).fieldRange
  refine ⟨residue _ y, ?_⟩
  rw [residueFieldInclusion, ResidueField.map_residue]
  exact hx a

theorem residueCoefficient_eval_injective_of_independent {ι : Type}
    (E : Subfield VF) (x : ι → k) (hx : AlgebraicIndependent (residueCoefficientField E) x) :
    Function.Injective (MvPolynomial.eval₂Hom (residueFieldInclusion v E) x) := by
  let f := residueFieldInclusion v E
  let e := f.rangeRestrictFieldEquiv
  have he : f.fieldRange.subtype.comp e.toRingHom = f := rfl
  intro a b hab
  apply MvPolynomial.map_injective e.toRingHom e.injective
  apply hx
  change MvPolynomial.eval₂ f.fieldRange.subtype x (MvPolynomial.map e.toRingHom a) =
    MvPolynomial.eval₂ f.fieldRange.subtype x (MvPolynomial.map e.toRingHom b)
  rw [MvPolynomial.eval₂_map, MvPolynomial.eval₂_map, he]
  exact hab

end SpecialTransformations.Section9
