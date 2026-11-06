import Section4.TupleBasis

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Classical
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

/-- Maximal transcendence degree of a finite generating tuple is equivalent
to algebraic independence of its original coordinates. -/
theorem tupleField_trdeg_eq_arity_iff {K : Type} [Field K]
    (E : Subfield K) {n : ℕ} (a : Fin n → K) :
    relativeTrdeg E (tupleField E a) (le_tupleField E a) = (n : Cardinal) ↔
      AlgebraicIndependent E a := by
  let F := tupleField E a
  letI := (Subfield.inclusion (le_tupleField E a)).toAlgebra
  letI : FaithfulSMul E F := (faithfulSMul_iff_algebraMap_injective E F).mpr
    (fun x y h => Subtype.ext (congrArg (fun z : F => z.val) h))
  let a' : Fin n → F := fun j => ⟨a j, tuple_mem_tupleField E a j⟩
  let T := IntermediateField.adjoin E (Set.range a')
  have hmap : F ≤ T.toSubfield.map F.subtype := by
    apply sup_le
    · intro x hx
      exact ⟨algebraMap E F ⟨x, hx⟩, T.algebraMap_mem _, rfl⟩
    · apply Subfield.closure_le.mpr
      rintro x ⟨j, rfl⟩
      exact ⟨a' j, IntermediateField.subset_adjoin E _ (Set.mem_range_self j), rfl⟩
  have ht : T = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨y, hy, he⟩ := hmap x.property
    exact (Subtype.ext he : y = x) ▸ hy
  haveI : Algebra.IsAlgebraic (Algebra.adjoin E (Set.range a')) F := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
    change Algebra.IsAlgebraic T F
    rw [ht]
    infer_instance
  let incl : F →ₐ[E] K := { F.subtype with commutes' := fun _ => rfl }
  change Algebra.trdeg E F = (n : Cardinal) ↔ AlgebraicIndependent E a
  constructor
  · intro h
    have hcard : Cardinal.mk (Fin n) ≤ Algebra.trdeg E F := by
      rw [h]
      simp
    have hTB := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite E a' hcard
    exact hTB.1.map' (f := incl) Subtype.val_injective
  · intro h
    have hIF : AlgebraicIndependent E a' := AlgebraicIndependent.of_comp incl h
    have hl : (n : Cardinal) ≤ Algebra.trdeg E F := by
      simpa only [Cardinal.mk_fintype, Fintype.card_fin] using hIF.cardinalMk_le_trdeg
    have hu : Algebra.trdeg E F ≤ (n : Cardinal) := tupleField_trdeg_le E a
    exact hu.antisymm hl

end SpecialTransformations.Section4

end
