import Section4.TupleBasis
import Section4.TupleIndependence

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Classical
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

/-- A tuple of rank k has an algebraically independent selection of k of
its original coordinates. Coordinate selection adds no model parameters. -/
theorem exists_independent_coordinates_of_rank {K : Type} [Field K]
    (E : Subfield K) {n k : ℕ} (a : Fin n → K)
    (hrank : relativeTrdeg E (tupleField E a) (le_tupleField E a) = (k : Cardinal)) :
    ∃ v : Fin k → Fin n, AlgebraicIndependent E (a ∘ v) := by
  let N := AlgebraicIndependent.matroid E K
  obtain ⟨B, hB⟩ := N.exists_isBasis (Set.range a)
  obtain ⟨hBind, hBsub, hBalg⟩ := AlgebraicIndependent.matroid_isBasis_iff.mp hB
  have hBfin : B.Finite := (Set.finite_range a).subset hBsub
  letI : Fintype B := hBfin.fintype
  let F := tupleField E a
  letI := (Subfield.inclusion (le_tupleField E a)).toAlgebra
  let xF : B → F := fun x => ⟨x.val,
    (show Subfield.closure (Set.range a) ≤ F from le_sup_right)
      (Subfield.subset_closure (hBsub x.property))⟩
  let incl : F →ₐ[E] K := { F.subtype with commutes' := fun _ => rfl }
  have hIF : AlgebraicIndependent E xF := AlgebraicIndependent.of_comp incl hBind
  have hcard := hIF.cardinalMk_le_trdeg
  change Cardinal.mk B ≤ relativeTrdeg E F (le_tupleField E a) at hcard
  rw [hrank] at hcard
  let d := Fintype.card B
  have hd : d ≤ k := by
    have hc : (d : Cardinal) ≤ (k : Cardinal) := by
      simpa only [Cardinal.mk_fintype] using hcard
    exact_mod_cast hc
  let e : Fin d ≃ B := (Fintype.equivFin B).symm
  let v : Fin d → Fin n := fun i => Classical.choose (hBsub (e i).property)
  have hv (i : Fin d) : a (v i) = (e i).val := Classical.choose_spec (hBsub (e i).property)
  have hrange : Set.range (a ∘ v) = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change a (v i) ∈ B
      rw [hv i]
      exact (e i).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, (hv i).trans (congrArg Subtype.val hi)⟩
  have halg (j : Fin n) : IsAlgebraic (tupleField E (a ∘ v)) (a j) := by
    have h : IsAlgebraic (Algebra.adjoin E (Set.range (a ∘ v))) (a j) := by
      rw [hrange]
      exact hBalg _ (Set.mem_range_self j)
    have h' := IntermediateField.isAlgebraic_adjoin_iff.mpr h
    change IsAlgebraic (IntermediateField.adjoin E (Set.range (a ∘ v))).toSubfield (a j) at h'
    rwa [← tupleField_eq_adjoin] at h'
  have hk : k ≤ d := by
    have h := tupleField_trdeg_le_of_isAlgebraic E a (a ∘ v) halg
    rw [hrank] at h
    exact_mod_cast h
  have he : d = k := hd.antisymm hk
  have hind : AlgebraicIndependent E (a ∘ v) := by
    have hfun : a ∘ v = ((↑) : B → K) ∘ e := funext hv
    rw [hfun]
    exact hBind.comp e e.injective
  subst k
  exact ⟨v, hind⟩

end SpecialTransformations.Section4

end
