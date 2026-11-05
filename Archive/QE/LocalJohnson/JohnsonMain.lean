import JohnsonAmalgamation
import JohnsonCriterion

/-!
# Ordinary valued-field quantifier elimination by Johnson's argument

The proof already present in `QE/Assembly_val.lean`, section 21, assembled from
shared local modules. The three inputs to Johnson's criterion are proved in
these modules. No ordinary ACVF QE theorem or other mathematical proposition
is taken as an additional hypothesis.

The language is the ring language with the binary relation `v x ≤ v y`.
The theory is nontrivial ACVF with no characteristic restriction. This is
ordinary valued-field QE; the RV theorem has its separate LocalQE entry point.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
set_option backward.isDefEq.respectTransparency false

/-- Quantifier elimination for nontrivial ACVF in the ordinary valued-field language.
This is the existing theorem from `Assembly_val.lean`, with its inputs imported. -/
theorem hasQE_ACVF_val : QECriterion.HasQE (L := Language.val) ValPM.ACVF_val :=
  HQEDerive.hasQE_of_johnson (L := Language.val) (T₀ := ValPM.valField) (T := ValPM.ACVF_val)
    ValPM.valField_subset_ACVF_val
    ValPM.hasPrimeModels_ACVF_val
    ValOneEC.hasAmalgamation_valField
    ValOneEC.oneECIn_of_modelType

/-- The same result for bounded formulas, retaining arbitrary finite contexts.
This exposes the stronger intermediate result already proved by the criterion. -/
theorem hasQEb_ACVF_val : QECriterion.HasQEb (L := Language.val) ValPM.ACVF_val :=
  QECriterion.hasQEb_of_QEAllStep (QECriterion.QEAllStep_iff_QEExStep.2
    (BoundedQE.qeExStep_theoryIff (L₀ := Language.val)
      (HQEDerive.H_of_qfDetermined ValPM.valField_subset_ACVF_val
        ValPM.hasPrimeModels_ACVF_val
        ValOneEC.hasAmalgamation_valField
        ValOneEC.oneECIn_of_modelType)))

#print axioms hasQE_ACVF_val
#print axioms hasQEb_ACVF_val
