import Mathlib

/-!
# Chevalley's lemma, first half: a valuation ring extends to a field extension

Johnson, *Fun with Fields*, §2.2 (Chevalley's lemma, [19, Theorem 3.1.1]) is the algebraic input
to the amalgamation property, which is hypothesis (ii) of his Lemma 2.1.4 for quantifier
elimination. Mathlib supplies the heart of it:

* `ValuationSubring.isMax_toLocalSubring` — a valuation subring is a maximal local subring;
* `LocalSubring.exists_valuationRing_of_isMax` — a maximal local subring is a valuation ring;
* `LocalSubring.exists_le_valuationSubring` — every local subring sits inside a valuation ring.

## What is proved here

`exists_valuationSubring_le_of_algebra`: for a field extension `L/K` and a valuation subring `O`
of `K`, there is a valuation subring `V` of `L` containing the image of `O`. This is the
*containment* half.

## What is not

The *contraction* half — `x ∈ K` and `algebraMap x ∈ V` implies `x ∈ O` — is what makes `V` an
extension of the valuation rather than merely a larger one, and it is the part amalgamation
actually consumes. It is not true for an arbitrary `V ⊇ image O` (a valuation ring can be
properly contained in a finer one on the same field), so the construction has to pin the maximal
ideal: one wants `m_V ∩ image(O) = image(m_O)`, which is Chevalley's Lemma 2.2.1(2) and requires
the localization argument of Johnson §2.2 rather than bare maximality among local subrings.
-/

open Valuation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Chevalley, containment half.** A valuation subring of `K` is contained in a valuation
subring of any field extension `L`, along the structure map. -/
theorem exists_valuationSubring_le_of_algebra (O : ValuationSubring K) :
    ∃ V : ValuationSubring L, ∀ x : K, x ∈ O → algebraMap K L x ∈ V := by
  obtain ⟨V, hV⟩ :=
    LocalSubring.exists_le_valuationSubring ((O.toLocalSubring).map (algebraMap K L))
  exact ⟨V, fun x hx => hV.1 ⟨x, hx, rfl⟩⟩

/-- The same, stated through the local subring of `L` rather than the valuation subring. -/
theorem exists_localSubring_contraction (O : ValuationSubring K) :
    ∃ A : LocalSubring L, ∀ x : K, (algebraMap K L x ∈ A.toSubring ↔ x ∈ O) := by
  refine ⟨(O.toLocalSubring).map (algebraMap K L), fun x => ⟨?_, ?_⟩⟩
  · intro hx
    simp only [LocalSubring.map, Subring.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := (algebraMap K L).injective hyx
    rwa [hyx'] at hy
  · intro hx
    simp only [LocalSubring.map, Subring.mem_map]
    exact ⟨x, hx, rfl⟩
