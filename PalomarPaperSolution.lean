module
public import SpecialTransformations
public section
/-!
# Proofs of the independently stated special-transformation results

The compared declarations are imported from the substantive development in
this repository. The independent Challenge must provide their definitions
and complete hypotheses without importing this development. The first submission selects the core deformation results, Theorem 5.5
and Corollary 5.6. Their pure-characteristic-zero model, genuine saturation
and small-parameter hypotheses remain explicit. Jacobian and measured
lifting results are outside this first Comparator configuration.
-/

set_option pp.all true in
#check @SpecialTransformations.Section5.Paper.theorem_5_5
#print axioms SpecialTransformations.Section5.Paper.theorem_5_5

set_option pp.all true in
#check @SpecialTransformations.Section5.Paper.corollary_5_6
#print axioms SpecialTransformations.Section5.Paper.corollary_5_6
