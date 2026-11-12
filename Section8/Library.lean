module

public import Section8.GammaBalls
public import Section8.IsolationGamma
public import Section8.IsolationRadius
public import Section8.UnarySlope
public import Section8.AlmostEverywhere
public import Section8.RVLocalConstancy
public import Section8.VFDefinableTopology
public import Section8.RVFibreGamma
public import Section8.ContinuityGamma
public import Section8.UnaryGamma
public import Section8.CenteredGammaSlope
public import Section8.PairwiseGamma

@[expose] public section

/-! Active Section 8 library. The relocated Sec8* files are historical
snapshots; the active modules use the pinned ACVF-QE language. -/

set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_1
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_1_gamma
set_option pp.universes true in
#check @SpecialTransformations.Section8.mem_uniformBall_iff
set_option pp.universes true in
#check @SpecialTransformations.Section8.gammaUniformBall_eq_uniformBall
set_option pp.universes true in
#check @SpecialTransformations.Section8.infinite_definable_contains_small_ball
set_option pp.universes true in
#check @SpecialTransformations.Section8.independent_not_isolated
set_option pp.universes true in
#check @SpecialTransformations.Section8.isolatedInputsFamily_definable
set_option pp.universes true in
#check @SpecialTransformations.Section8.mem_isolatedInputs_iff
set_option pp.universes true in
#check @SpecialTransformations.Section8.mem_isolatedInputs_iff_gamma
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_2
set_option pp.universes true in
#check @SpecialTransformations.Section8.isolatedInputs_gamma_definable
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_2_actual_gamma
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_2_gamma_base
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_3_canonical
set_option pp.universes true in
#check @SpecialTransformations.Section8.unaryLocalSlope
set_option pp.universes true in
#check @SpecialTransformations.Section8.unary_family_uniform_positive_power_germ
set_option pp.universes true in
#check @SpecialTransformations.Section8.unaryGoodLocus_finite_exception
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_3_gamma_base
set_option pp.universes true in
#check @SpecialTransformations.Section8.unaryLocalSlopeAtBase
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_6_canonical
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_6_gamma_base
set_option pp.universes true in
#check @SpecialTransformations.Section8.uniform_power_estimate_of_independent
set_option pp.universes true in
#check @SpecialTransformations.Section8.estimateRVCodes_gamma_base_definable
set_option pp.universes true in
#check @SpecialTransformations.Section8.gamma_named_unique_shift_radius
#print SpecialTransformations.Section8.powerEstimatePointBase
#print SpecialTransformations.Section8.vfPositivePowerEstimate
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_4_named_gamma_base
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_4_partial
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_4_partial_gamma_base
set_option pp.universes true in
#check @SpecialTransformations.Section8.definable_power_germ_slope_integral
set_option pp.universes true in
#check @SpecialTransformations.Section8.definable_singleton_value_of_immediate_henselian
#print SpecialTransformations.Section8.ImmediateHenselianExtension
#print SpecialTransformations.Section8.centeredGammaSlope
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_5_partial
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_5_partial_gamma_base
set_option pp.universes true in
#check @SpecialTransformations.Section8.rvPairwiseWitnesses_gamma_definable
#print SpecialTransformations.Section8.rvPairwiseGammaLaw
#print SpecialTransformations.Section8.pairwisePointBase
#print SpecialTransformations.Section8.flattenFamilyCentre
#print SpecialTransformations.Section8.unaryLocalSlopeAtBase
set_option pp.universes true in
#check @SpecialTransformations.Section8.AlmostEverywhereVF
set_option pp.universes true in
#check @SpecialTransformations.Section8.AlmostEverywhereRV
set_option pp.universes true in
#check @SpecialTransformations.Section8.rvLocallyConstantAt
set_option pp.universes true in
#check @SpecialTransformations.Section8.rvLocallyConstantOn
set_option pp.universes true in
#check @SpecialTransformations.Section8.rvLocallyConstantAt_iff_uniformBall
set_option pp.universes true in
#check @SpecialTransformations.Section8.mem_vfRawClosure_iff
set_option pp.universes true in
#check @SpecialTransformations.Section8.vfRawClosure_dim_lt_arity
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_7_canonical
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_7_gamma_base
set_option pp.universes true in
#check @SpecialTransformations.Section8.continuousAt_of_independent
set_option pp.universes true in
#check @SpecialTransformations.Section8.normalizedContinuityException_gamma_definable
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_9_canonical
set_option pp.universes true in
#check @SpecialTransformations.Section8.lemma_8_9_gamma_base
set_option pp.universes true in
#check @SpecialTransformations.Section8.rvFibre_locallyConstant_of_independent
set_option pp.universes true in
#check @SpecialTransformations.Section8.rvConstantRaw_gamma_definable

#print axioms SpecialTransformations.Section8.lemma_8_1
#print axioms SpecialTransformations.Section8.lemma_8_1_gamma
#print axioms SpecialTransformations.Section8.mem_uniformBall_iff
#print axioms SpecialTransformations.Section8.gammaUniformBall_eq_uniformBall
#print axioms SpecialTransformations.Section8.infinite_definable_contains_small_ball
#print axioms SpecialTransformations.Section8.independent_not_isolated
#print axioms SpecialTransformations.Section8.isolatedInputsFamily_definable
#print axioms SpecialTransformations.Section8.mem_isolatedInputs_iff
#print axioms SpecialTransformations.Section8.mem_isolatedInputs_iff_gamma
#print axioms SpecialTransformations.Section8.lemma_8_2
#print axioms SpecialTransformations.Section8.isolatedInputs_gamma_definable
#print axioms SpecialTransformations.Section8.lemma_8_2_actual_gamma
#print axioms SpecialTransformations.Section8.lemma_8_2_gamma_base
#print axioms SpecialTransformations.Section8.lemma_8_3_canonical
#print axioms SpecialTransformations.Section8.unaryLocalSlope
#print axioms SpecialTransformations.Section8.unary_family_uniform_positive_power_germ
#print axioms SpecialTransformations.Section8.unaryGoodLocus_finite_exception
#print axioms SpecialTransformations.Section8.lemma_8_3_gamma_base
#print axioms SpecialTransformations.Section8.unaryLocalSlopeAtBase
#print axioms SpecialTransformations.Section8.lemma_8_6_canonical
#print axioms SpecialTransformations.Section8.lemma_8_6_gamma_base
#print axioms SpecialTransformations.Section8.uniform_power_estimate_of_independent
#print axioms SpecialTransformations.Section8.estimateRVCodes_gamma_base_definable
#print axioms SpecialTransformations.Section8.gamma_named_unique_shift_radius
#print axioms SpecialTransformations.Section8.lemma_8_4_named_gamma_base
#print axioms SpecialTransformations.Section8.lemma_8_4_partial
#print axioms SpecialTransformations.Section8.lemma_8_4_partial_gamma_base
#print axioms SpecialTransformations.Section8.definable_power_germ_slope_integral
#print axioms SpecialTransformations.Section8.definable_singleton_value_of_immediate_henselian
#print axioms SpecialTransformations.Section8.lemma_8_5_partial
#print axioms SpecialTransformations.Section8.lemma_8_5_partial_gamma_base
#print axioms SpecialTransformations.Section8.rvPairwiseWitnesses_gamma_definable
#print axioms SpecialTransformations.Section8.AlmostEverywhereVF
#print axioms SpecialTransformations.Section8.AlmostEverywhereRV
#print axioms SpecialTransformations.Section8.rvLocallyConstantAt
#print axioms SpecialTransformations.Section8.rvLocallyConstantOn
#print axioms SpecialTransformations.Section8.rvLocallyConstantAt_iff_uniformBall
#print axioms SpecialTransformations.Section8.mem_vfRawClosure_iff
#print axioms SpecialTransformations.Section8.vfRawClosure_dim_lt_arity
#print axioms SpecialTransformations.Section8.lemma_8_7_canonical
#print axioms SpecialTransformations.Section8.lemma_8_7_gamma_base
#print axioms SpecialTransformations.Section8.continuousAt_of_independent
#print axioms SpecialTransformations.Section8.normalizedContinuityException_gamma_definable
#print axioms SpecialTransformations.Section8.lemma_8_9_canonical
#print axioms SpecialTransformations.Section8.lemma_8_9_gamma_base
#print axioms SpecialTransformations.Section8.rvFibre_locallyConstant_of_independent
#print axioms SpecialTransformations.Section8.rvConstantRaw_gamma_definable
