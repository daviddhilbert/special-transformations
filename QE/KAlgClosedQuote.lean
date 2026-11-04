import ClassicalProps
import KAlgClosed

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.StandingField

namespace KAlgClosedQuote

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- Marker's `ACFExtendsAlgebraicEmbeddings`, as transcribed in `QE/ClassicalProps.lean`, applied
at the residue fields of two models of the frozen `ACVF`. -/
theorem acfExtends_residueK (hacf : ClassicalProps.ACFExtendsAlgebraicEmbeddings)
    {E : Type} [Field E] [Algebra (KOf M) E] [Algebra.IsAlgebraic (KOf M) E]
    (j : KOf M →+* KOf N) :
    ∃ l : E →+* KOf N, ∀ x : KOf M, l (algebraMap (KOf M) E x) = j x :=
  hacf (K := KOf M) (F := KOf N) (E := E)
    (inferInstance : Algebra.IsAlgebraic (KOf M) E) j

/-- The plain corollary: `K(N)` is algebraically closed, from `Axioms.ACVF` alone. -/
theorem isAlgClosed_KOf_residue : IsAlgClosed (KOf N) := KAlgClosed.isAlgClosed_kOf

end KAlgClosedQuote

#print axioms KAlgClosedQuote.acfExtends_residueK
#print axioms KAlgClosedQuote.isAlgClosed_KOf_residue
