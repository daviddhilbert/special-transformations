import Section4.RealPresentations
import Section3.AlgebraicFinite

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n : ℕ}

theorem rvValues_decode (c : (rawRVSpace (M := M) n).domain) :
    rvValues ((rawRVSpace (M := M) n).decode c) = c.val :=
  Space.ofEmbedding_decode rvValues rvValues_injective (rawRVSpace n).domain_definable c

theorem decode_rvValues (a : Fin n → CanonicalRV.RVSort M) :
    (rawRVSpace (M := M) n).decode ⟨rvValues a, ⟨a, rfl⟩⟩ = a :=
  rvValues_injective (rvValues_decode _)

def rvCoordinateSet (A : DefSet (rawRVSpace (M := M) n) S) (i : Fin n) : Set M :=
  {x | ∃ a : A, (a.val i).val = x}

theorem rvCoordinateSet_definable (A : DefSet (rawRVSpace (M := M) n) S) (i : Fin n) :
    S.Definable₁ LRV (rvCoordinateSet A i) := by
  have h := A.definable.image_comp (fun _ : Fin 1 => i)
  change S.Definable LRV {x : Fin 1 → M | ∃ a : A, (a.val i).val = x 0}
  convert h using 1
  ext x
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨rvValues a.val, ⟨⟨a.val, rfl⟩, ?_⟩, ?_⟩
    · simpa only [decode_rvValues] using a.property
    · funext j
      fin_cases j
      exact ha
  · rintro ⟨z, ⟨hz, hA⟩, he⟩
    refine ⟨⟨(rawRVSpace (M := M) n).decode ⟨z, hz⟩, hA⟩, ?_⟩
    exact (congrFun (rvValues_decode ⟨z, hz⟩) i).trans (congrFun he 0)

/-- The finite-image step used in 4.19: a definable RV tuple set contained
coordinatewise in algebraic closure of the same small base is finite.
Both definability and the original parameter bound remain explicit. -/
theorem finite_rv_set_of_algebraic {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (A : DefSet (rawRVSpace (M := M) n) S)
    (ha : ∀ a : A, ∀ i, AlgebraicAt S .rv (a.val i).val) : A.carrier.Finite := by
  have hcoord (i : Fin n) : (rvCoordinateSet A i).Finite := by
    apply RawClosure.finite_of_definable_subset_algebraic hs S hsmall _
      (rvCoordinateSet_definable A i)
    rintro x ⟨a, rfl⟩
    exact (ha a i).raw_finite_witness
  apply ((Set.Finite.pi' hcoord).preimage rvValues_injective.injOn).subset
  intro a hA i
  exact ⟨⟨a, hA⟩, rfl⟩

end SpecialTransformations.Section4
