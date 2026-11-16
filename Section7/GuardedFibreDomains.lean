module

public import Section3.GuardedRVLiterals

@[expose] public section

/-!
# The constant part of the guarded normal form on a fixed value fibre

The absolute values of ordinary Laurent monomials, all rational pole
conditions, residue membership of individual summands, and order literals
are unchanged when only the RV classes inside their value fibres vary.
Equality comparisons of residue sums are deliberately left to the
polynomial extraction. This is not a claim that the RV classes agree.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GuardedRVNormalForm
open CanonicalRV ValuedModelMap

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M I R V : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (a : I → VFType (M := M)) (r : R → RVSort M)
variable {y z : V → RVSort M}

theorem monomial_absolute_eq_of_values (T : Monomial I R V)
    (h : ∀ i, RVOperations.absoluteHom (y i) = RVOperations.absoluteHom (z i)) :
    RVOperations.absoluteHom (T.rawEval a r y) = RVOperations.absoluteHom (T.rawEval a r z) := by
  simp only [Monomial.rawEval_rational, map_mul, Finsupp.prod, map_prod, map_zpow₀, h]

theorem inResidue_iff_of_absolute_eq {s t : RVSort M}
    (h : RVOperations.absoluteHom s = RVOperations.absoluteHom t) : inK s ↔ inK t := by
  rw [RVOperations.inK_iff, RVOperations.inK_iff,
    ← RVOperations.absolute_eq_zero s, ← RVOperations.absolute_eq_zero t, h]

theorem residuePolynomial_domain_iff_of_values (P : KPolynomial I R V)
    (h : ∀ i, RVOperations.absoluteHom (y i) = RVOperations.absoluteHom (z i)) :
    P.Domain a r y ↔ P.Domain a r z := by
  apply forall_congr'
  intro j
  exact and_congr Iff.rfl
    (inResidue_iff_of_absolute_eq (monomial_absolute_eq_of_values a r (P.terms j) h))

theorem literal_domain_iff_of_values (L : RVLiteral I R V)
    (h : ∀ i, RVOperations.absoluteHom (y i) = RVOperations.absoluteHom (z i)) :
    RVLiteral.Domain a r y L ↔ RVLiteral.Domain a r z L := by
  cases L with
  | order => rfl
  | equality E pos =>
    simp only [RVLiteral.Domain, residuePolynomial_domain_iff_of_values a r E.leftK h,
      residuePolynomial_domain_iff_of_values a r E.rightK h]

theorem orderLiteral_holds_iff_of_values (L : OrderPayload I R V) (pos : Bool)
    (h : ∀ i, RVOperations.absoluteHom (y i) = RVOperations.absoluteHom (z i)) :
    RVLiteral.holds a r y (.order L pos) ↔ RVLiteral.holds a r z (.order L pos) := by
  simp only [RVLiteral.holds, RVLiteral.Domain, RVLiteral.comparison, rvLe_iff_absolute,
    monomial_absolute_eq_of_values a r L.left h, monomial_absolute_eq_of_values a r L.right h]

end SpecialTransformations.Section7
