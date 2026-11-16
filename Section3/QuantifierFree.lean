module

public import ACVFQE
public import Section3.Parameters

@[expose] public section

/-!
# The completed QE dependency over the original base

This is the quantifier-free step of the paragraph following Definition 2.4.
It preserves the arbitrary base set and every tuple arity. It does not yet
claim the more specific RV-literal/K-term normal form or C-minimality.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section3

variable {M : Type} [LRV.Structure M]

theorem DefinableOver.quantifier_free (hM : M ⊨ Axioms.ACVF)
    {A : Set M} {n : ℕ} {sn : Fin n → SortTag} {s : Set (Fin n → M)}
    (hs : DefinableOver A sn s) :
    ∃ p : Parameters A, ∃ ψ : LRV.BoundedFormula (Fin p.length) n,
      ψ.IsQF ∧ WellSorted p.sorts sn ψ ∧
      s = {x | (∀ i, sortEval (sn i) (x i)) ∧ ψ.Realize p.values x} := by
  obtain ⟨p, φ, hφ, rfl⟩ := hs
  obtain ⟨ψ, hqf, hws, heq⟩ := theorem_2_3_quantifier_elimination
    (Fin p.length) p.sorts n sn φ hφ
  refine ⟨p, ψ, hqf, hws, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hφx⟩
    exact ⟨hx, (heq M hM p.values x p.sorted hx).mp hφx⟩
  · rintro ⟨hx, hψx⟩
    exact ⟨hx, (heq M hM p.values x p.sorted hx).mpr hψx⟩

end SpecialTransformations.Section3
