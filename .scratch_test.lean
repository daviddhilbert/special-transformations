import Mathlib
open FirstOrder FirstOrder.Language
open FirstOrder.Ring
open Polynomial
open scoped FirstOrder
#check @Function.Injective.commRing
#check @Function.Injective.isDomain
#check @IsFractionRing.lift
#check @Ideal.exists_maximal
#check @Ideal.Quotient.field
#check @Algebra.TensorProduct.includeLeft_apply
#check @Algebra.TensorProduct.includeRight_apply
#check @Algebra.TensorProduct.tmul_one_eq_one_tmul
#check @Algebra.TensorProduct.includeLeftRingHom
#check @Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
#check @RingHom.algebraMap_toAlgebra
#check @RingHom.toAlgebra
#check @IsFractionRing.injective
#check @FractionRing
#check @IsFractionRing.liftAlgHom
#check @IsLocalization.lift
#check @IsFractionRing.lift_eq
#check @IsFractionRing.to_map_eq_zero_iff
