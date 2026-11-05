import Section3.RawAlgebraicity
import Section3.DefinableCompactness
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure
variable {M : Type} [LRV.Structure M]

theorem finite_of_definable_subset_algebraic {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (A : Set M)
    (hA : S.Definable₁ LRV A) (halg : ∀ a ∈ A, AlgebraicOver S a) : A.Finite := by
  classical
  let C : Set (Set M) := {c | S.Definable₁ LRV c ∧ c.Finite}
  have hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨c, hc, hfin, hac⟩ := halg a ha
    exact ⟨c, ⟨hc, hfin⟩, hac⟩
  obtain ⟨C₀, hfin, hsub, hcover⟩ := hs.definable_finite_subcover
    S hsmall A hA C (fun c hc => hc.1) hcov
  exact (hfin.sUnion (fun c hc => (hsub hc).2)).subset
    (by intro a ha; obtain ⟨c, hc, hac⟩ := hcover a ha; exact ⟨c, hc, hac⟩)

end SpecialTransformations.Section3.RawClosure