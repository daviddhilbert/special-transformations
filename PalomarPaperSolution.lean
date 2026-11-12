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

open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Section5
set_option backward.isDefEq.respectTransparency false
variable {M : Type} [sM : Milestone0.LRV.Structure M] [hM : M ⊨ Milestone0.Axioms.ACVF]
theorem canonicalMap_value {n m : ℕ} {S : Set M} (A : DefSet (M := M) S n m) (a : A) : ((canonicalMap A).toFun a).val = canonical a.val := rfl
namespace Focus
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
theorem etaMap_value (D : Focus A j k) (a : A) : (D.etaMap.toFun a).val = D.toFocusGeometry.eta a.val := rfl
end Focus
end SpecialTransformations.Section5
#print axioms SpecialTransformations.Section5.canonicalMap_value
#print axioms SpecialTransformations.Section5.Focus.etaMap_value
