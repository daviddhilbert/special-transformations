/-
**No junk elements in models of the frozen `ACVF`.**

The tagged one-carrier encoding has two sorts distinguished by predicates (`iVF`, `iRV`), and the
carriers of `Assembly_val`-style analyses worried about "elements outside both sorts" (junk
elements).  This file proves that cannot happen: the encoding's own sort axioms —

* `Axioms.sdCover`  (`∀ x, x ∈ VF ∨ x ∈ RV`), and
* `Axioms.sdDisjoint` (the two sorts are disjoint),

are *sentences of* `Axioms.ACVF`, so in every model the carrier is exactly the disjoint union of
the two sorts, and every structure that embeds into a model inherits it (an embedding reflects the
sort predicates).  What is junk in this encoding is a property of *terms* — an ill-sorted term such
as `rv (rv x)` has a value no axiom constrains — never of elements.

Proved here, from `Axioms.ACVF` alone, nothing assumed:

* `SortCover.iVF_or_iRV` — the cover half (`eq_top_of_vf_all`'s engine);
* `SortCover.sorted_exclusive` — the full exclusive-or.
-/
import RVCalc
import Assembly_frozen

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0
namespace SortCover

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `sdCover` is a sentence of `ACVF`. -/
theorem mem_ACVF_sdCover : Axioms.sdCover ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Axioms.sortAxioms, Axioms.ofList, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff] at *
  tauto

/-- `sdDisjoint` is a sentence of `ACVF`. -/
theorem mem_ACVF_sdDisjoint : Axioms.sdDisjoint ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Axioms.sortAxioms, Axioms.ofList, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff] at *
  tauto

/-- Realisation of `pVF` at a single element. -/
theorem pVF_realize_at (x : M) :
    (LRV.pVF ((&0 : LRV.Tm 1))).Realize (default : Empty → M) ![x] ↔ iVF x := by
  have := Assembly.real_memVF ![x] (LRV.tv 0 (by decide))
  simpa [Assembly.rho, LRV.tv] using this

/-- Realisation of `pRVsort` at a single element. -/
theorem pRVsort_realize_at (x : M) :
    (LRV.pRVsort ((&0 : LRV.Tm 1))).Realize (default : Empty → M) ![x] ↔ iRV x := by
  have := Assembly.real_memRV ![x] (LRV.tv 0 (by decide))
  simpa [Assembly.rho, LRV.tv] using this

/-- **The cover half**: every element of a model is `VF` or `RV` (`sdCover`). -/
theorem iVF_or_iRV (x : M) : iVF x ∨ iRV x := by
  have hreal : M ⊨ Axioms.sdCover :=
    Theory.realize_sentence_of_mem (T := Axioms.ACVF) mem_ACVF_sdCover
  have hcov : ∀ xs : Fin 1 → M,
      (LRV.pVF ((&0 : LRV.Tm 1)) ⊔ LRV.pRVsort ((&0 : LRV.Tm 1))).Realize
        (default : Empty → M) xs := by
    have h1 : M ⊨ Axioms.sdCover ↔ ∀ xs : Fin 1 → M,
        (LRV.pVF ((&0 : LRV.Tm 1)) ⊔ LRV.pRVsort ((&0 : LRV.Tm 1))).Realize
          (default : Empty → M) xs := by
      simp only [Axioms.sdCover]
      exact FirstOrder.Language.BoundedFormula.realize_alls
    exact h1.mp hreal
  have h := hcov ![x]
  rw [FirstOrder.Language.BoundedFormula.realize_sup] at h
  rcases h with h | h
  · exact Or.inl ((pVF_realize_at x).mp h)
  · exact Or.inr ((pRVsort_realize_at x).mp h)

/-- **The disjointness half**: no element is both (`sdDisjoint`). -/
theorem not_both (x : M) : ¬ (iVF x ∧ iRV x) := by
  have hreal : M ⊨ Axioms.sdDisjoint :=
    Theory.realize_sentence_of_mem (T := Axioms.ACVF) mem_ACVF_sdDisjoint
  have hdis : ∀ xs : Fin 1 → M,
      (∼(LRV.pVF ((&0 : LRV.Tm 1)) ⊓ LRV.pRVsort ((&0 : LRV.Tm 1)))).Realize
        (default : Empty → M) xs := by
    have h1 : M ⊨ Axioms.sdDisjoint ↔ ∀ xs : Fin 1 → M,
        (∼(LRV.pVF ((&0 : LRV.Tm 1)) ⊓ LRV.pRVsort ((&0 : LRV.Tm 1)))).Realize
          (default : Empty → M) xs := by
      simp only [Axioms.sdDisjoint]
      exact FirstOrder.Language.BoundedFormula.realize_alls
    exact h1.mp hreal
  have h := hdis ![x]
  rw [FirstOrder.Language.BoundedFormula.realize_not,
    FirstOrder.Language.BoundedFormula.realize_inf] at h
  intro hc
  exact h ⟨(pVF_realize_at x).mpr hc.1, (pRVsort_realize_at x).mpr hc.2⟩

/-- **No junk elements**: every element of the carrier is in exactly one of the two sorts. -/
theorem sorted_exclusive (x : M) : (iVF x ∧ ¬ iRV x) ∨ (iRV x ∧ ¬ iVF x) := by
  rcases iVF_or_iRV x with h | h
  · exact Or.inl ⟨h, fun h' => not_both x ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => not_both x ⟨h', h⟩⟩

end SortCover
end SpecialTransformations.Milestone0
