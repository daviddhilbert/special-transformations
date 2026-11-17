module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQEFlatLiterals.lean
Original declaration namespaces and notices are retained.
-/
public import Section3.GammaQEFlatResidue
public import Section3.GammaQEValueAlgebra

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Preservation of a true flat literal under a slope-separated RV
perturbation. Residue summands are fixed and value comparisons are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV GuardedRVNormalForm
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {I R : Type}

def literalMonomials : RVLiteral I R (Fin 2) → List (Monomial I R (Fin 2))
  | .equality E _ => [E.left,E.right] ++ List.ofFn E.leftK.terms ++ List.ofFn E.rightK.terms
  | .order E _ => [E.left,E.right]

def ValueComparisonsPreserved (s : List (Monomial I R (Fin 2)))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : Fin 2 → RVSort M) (t : RVSort M) : Prop :=
  ∀ P ∈ s,∀ Q ∈ s,
    (Values.vrv (P.rawEval a r (perturbRV x t)) ≤ Values.vrv (Q.rawEval a r (perturbRV x t)) ↔
      Values.vrv (P.rawEval a r x) ≤ Values.vrv (Q.rawEval a r x))

theorem flat_value_equality_preserved (s : List (Monomial I R (Fin 2)))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : Fin 2 → RVSort M) (t : RVSort M)
    (hv : ValueComparisonsPreserved s a r x t) (P Q : Monomial I R (Fin 2))
    (hP : P ∈ s) (hQ : Q ∈ s) :
    Values.vrv (P.rawEval a r x*t^P.powers 1) = Values.vrv (Q.rawEval a r x*t^Q.powers 1) →
      Values.vrv (P.rawEval a r x) = Values.vrv (Q.rawEval a r x) := by
  intro he
  rw [← flat_rawEval_perturb,← flat_rawEval_perturb] at he
  exact le_antisymm ((hv P hP Q hQ).mp he.le) ((hv Q hQ P hP).mp he.ge)

theorem flat_literal_preserved (s : List (Monomial I R (Fin 2)))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : Fin 2 → RVSort M)
    (h1 : Monomial.one ∈ s) (hs : SlopesSeparated s a r x) (t : RVSort M) (ht : t ≠ 0)
    (hv : ValueComparisonsPreserved s a r x t) (L : RVLiteral I R (Fin 2))
    (hL : ∀ P ∈ literalMonomials L,P ∈ s) (h : L.holds a r x) :
    L.holds a r (perturbRV x t) := by
  cases L with
  | equality E pos =>
    have hEL : E.left ∈ s := hL _ (by simp [literalMonomials])
    have hER : E.right ∈ s := hL _ (by simp [literalMonomials])
    have hKL := flat_residue_polynomial_fixed s a r x h1 hs E.leftK
      (fun i => hL _ (by simp [literalMonomials,List.mem_ofFn])) h.1.2.1 t
    have hKR := flat_residue_polynomial_fixed s a r x h1 hs E.rightK
      (fun i => hL _ (by simp [literalMonomials,List.mem_ofFn])) h.1.2.2.2 t
    refine ⟨⟨h.1.1,hKL.1,h.1.2.2.1,hKR.1⟩,?_⟩
    have he := scaled_residue_equality (E.left.rawEval a r x) (E.right.rawEval a r x)
      (E.leftK.rawEval a r x) (E.rightK.rawEval a r x) t ht
      (flat_polynomial_inK _ a r x) (flat_polynomial_inK _ a r x) _ _
      (hs _ hEL _ hER) (flat_value_equality_preserved s a r x t hv _ _ hEL hER)
    change NFTest.signed pos _
    rw [flat_rawEval_perturb,flat_rawEval_perturb,hKL.2,hKR.2]
    cases pos <;> simp only [NFTest.signed,Bool.false_eq_true,if_false,if_true] at *
    · exact not_congr he |>.mpr h.2
    · exact he.mpr h.2
  | order E pos =>
    refine ⟨h.1,?_⟩
    have hc := hv E.left (hL _ (by simp [literalMonomials]))
      E.right (hL _ (by simp [literalMonomials]))
    have he : iLe (E.left.rawEval a r (perturbRV x t)).val (E.right.rawEval a r (perturbRV x t)).val ↔
        iLe (E.left.rawEval a r x).val (E.right.rawEval a r x).val := by
      simpa only [Values.vrv_le_iff] using hc
    cases pos <;> simp only [RVLiteral.comparison,NFTest.signed,Bool.false_eq_true,if_false,if_true] at *
    · exact not_congr he |>.mpr h.2
    · exact he.mpr h.2

end DiamondIntegral.Section5.GammaQE
