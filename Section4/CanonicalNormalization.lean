module

public import Section3.CanonicalParameters

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M]

/-- A canonical totalization is literally unchanged by normalization.
This transports raw definability interfaces without changing Gamma's
carrier or any real parameter set. -/
theorem canonical_normalize_eq (hcan : CanonicalStructure.IsCanonical (M := M)) :
    CanonicalStructure.normalize (M := M) = sM := by
  apply FirstOrder.Language.Structure.ext
  · funext n f xs
    change (if ∀ i, sortEval (Fn.argSort f i) (xs i) then
      Structure.funMap (L := LRV) f xs else CanonicalStructure.sortZero (Fn.resSort f)) = _
    by_cases h : ∀ i, sortEval (Fn.argSort f i) (xs i)
    · exact if_pos h
    · rw [if_neg h]
      exact (hcan.1 f xs h).symm
  · funext n r xs
    cases r with
    | memVF => rfl
    | memRV => rfl
    | memUnits => rfl
    | rvLe =>
      apply propext
      change ((∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs) ↔ _
      by_cases h : ∀ i, sortEval .rv (xs i)
      · exact and_iff_right h
      · exact iff_of_false (fun hr => h hr.1) (hcan.2 xs h)

end SpecialTransformations.Section4
