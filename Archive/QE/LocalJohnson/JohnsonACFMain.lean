import JohnsonACFPrime

/-! All-characteristic ACF quantifier elimination from the existing Johnson
argument in QE/ACF_HasQE.lean. The generic criterion and compactness proof are
the same checked declarations used for ordinary valued-field QE. -/

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace JohnsonACF

/-- Bounded quantifier elimination for the theory of all algebraically closed
fields; no characteristic has been fixed. -/
theorem hasQEb : QECriterion.HasQEb (L := Language.ring) ACFValidation.acf :=
  QECriterion.hasQEb_of_QEAllStep (QECriterion.QEAllStep_iff_QEExStep.2
    (BoundedQE.qeExStep_theoryIff (L₀ := Language.ring)
      (HQEDerive.H_of_qfDetermined ACFValidation.field_subset_acf
        JohnsonACFPrime.hasPrimeModels_field_acf
        (fun A B C i j => ACFValidation.amalgamation_field A B C i j)
        (fun M N f hM => ACFValidation.oneEC_field_acf M N f hM))))

end JohnsonACF

#print axioms JohnsonACF.hasQEb
