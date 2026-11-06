import Section4.RVDimensionRank
import Section4.RelationFibres

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

/-- A definable finitary function in the paper's terminology: its values
are finite sets. The author confirmed this scope for the image assertion
immediately after Definition 4.9 on November 5, 2026. -/
structure RVFinitaryFunction (A : DefSet (rawRVSpace (M := M) n) S) (m : ℕ) where
  values : (rawRVSpace (M := M) n).Carrier → Set (rawRVSpace (M := M) m).Carrier
  definable : (rawRVSpace n).RelationDefinable (rawRVSpace m) S (fun a b => b ∈ values a)
  finite : ∀ a : A, (values a.val).Finite

namespace RVFinitaryFunction

variable {A : DefSet (rawRVSpace (M := M) n) S} (f : RVFinitaryFunction A m)

/-- The full union of all values, with no selected branch. -/
def image : DefSet (rawRVSpace (M := M) m) S where
  carrier := {b | ∃ a : A, b ∈ f.values a.val}
  definable := by
    let P := rawRVSpace (M := M) n
    let Q := rawRVSpace (M := M) m
    have h : Q.Definable S {b | ∃ a, a ∈ A.carrier ∧ b ∈ f.values a} :=
      ((A.definable.left_relation P Q).inter P Q f.definable).swap P Q |>.exists_right Q P
    convert h using 1
    ext b
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a.val, a.property, ha⟩
    · rintro ⟨a, ha, hab⟩
      exact ⟨⟨a, ha⟩, hab⟩

theorem output_coordinate_algebraic (hcan : CanonicalStructure.IsCanonical (M := M))
    (a : A) (b : (rawRVSpace (M := M) m).Carrier) (hab : b ∈ f.values a.val) (j : Fin m) :
    AlgebraicAt (S ∪ Set.range (rvValues a.val)) .rv (b j).val := by
  let c : (rawRVSpace (M := M) n).domain := ⟨rvValues a.val, ⟨a.val, rfl⟩⟩
  let F := relationFibre f.definable a.val c (decode_rvValues a.val)
  have hfin : F.carrier.Finite := f.finite a
  apply (algebraicAt_iff_raw hcan _ .rv _).mpr
  exact ⟨⟨rvCoordinateSet F j, rvCoordinateSet_definable F j,
    rvCoordinateSet_finite F hfin j, ⟨⟨b, hab⟩, rfl⟩⟩, (b j).property⟩

/-- The unnumbered RV image inequality after Definition 4.9, with the
author-confirmed finitary hypothesis. -/
theorem dimension_image_le (hcan : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : rvDim f.image ≤ rvDim A := by
  apply rvDim_le_of_point_rank hcan hex hs hsmall f.image
  rintro ⟨b, a, hab⟩
  exact (rvTupleRank_le_of_algebraic hcan hex S a.val b
    (f.output_coordinate_algebraic hcan a b hab)).trans
    (rvTupleRank_le_rvDim hcan hex A a)

end RVFinitaryFunction

end SpecialTransformations.Section4

end
