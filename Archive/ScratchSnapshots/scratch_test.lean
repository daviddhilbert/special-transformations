module

public import Mathlib

@[expose] public section
open FirstOrder FirstOrder.Language
open FirstOrder.Ring Polynomial
open scoped FirstOrder
#check @RingHom.quotientKerEquivRange
#check @RingHom.ker
#check @Ideal.Quotient.lift
#check @IsLocalization.lift_eq
#check @Ring.termOfFreeCommRing
#check @Ring.realize_termOfFreeCommRing
#check @HomClass.realize_term
#check @IsFractionRing.lift
#check @Subring.mem_closure
#check @RingHom.mem_range
#check @IsFractionRing.injective
#check @Subring.closure
#check @Subring.subtype
#check @RingHom.range
example {K : Type*} [Field K] (R : Subring K) : IsDomain ↥R := inferInstance
