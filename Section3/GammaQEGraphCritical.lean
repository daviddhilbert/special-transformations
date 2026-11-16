/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQEGraphCritical.lean
Original declaration namespaces and notices are retained.
-/
import Section3.GammaQEFlatPerturbation
import Section3.GammaQEParser

/-! A Gamma function graph must meet one of finitely many equal-value
loci with different output slopes. Otherwise a true RV clause survives
a nontrivial perturbation of its output, contradicting uniqueness. -/
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

def dnfMonomials (D : LiteralDNF I R (Fin 2)) : List (Monomial I R (Fin 2)) :=
  Monomial.one :: D.flatten.flatMap literalMonomials

theorem graph_has_critical_pair (a : I → VFType (M := M)) (r : R → RVSort M)
    (D : LiteralDNF I R (Fin 2)) (A : Set (Values.Gamma (M := M)))
    (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hgraph : ∀ (x : Fin 2 → RVSort M) (hx : ∀ i,x i ≠ 0),
      (rvGamma (x 0) (hx 0) ∈ A ∧ f (rvGamma (x 0) (hx 0)) = rvGamma (x 1) (hx 1)) ↔
        PolarityDNF.holds (RVLiteral.holds a r x) D)
    (x : Fin 2 → RVSort M) (hx : ∀ i,x i ≠ 0)
    (h : rvGamma (x 0) (hx 0) ∈ A ∧ f (rvGamma (x 0) (hx 0)) = rvGamma (x 1) (hx 1)) :
    ∃ P ∈ dnfMonomials D,∃ Q ∈ dnfMonomials D,
      P.rawEval a r x ≠ 0 ∧ Q.rawEval a r x ≠ 0 ∧
      Values.vrv (P.rawEval a r x) = Values.vrv (Q.rawEval a r x) ∧ P.powers 1 ≠ Q.powers 1 := by
  by_contra hn
  have hs : SlopesSeparated (dnfMonomials D) a r x := by
    intro P hP Q hQ hP0 hQ0 he
    by_contra hne
    exact hn ⟨P,hP,Q,hQ,hP0,hQ0,he,hne⟩
  obtain ⟨t,ht,he,hv⟩ := flat_finite_perturbation (dnfMonomials D) a r x hs
  have hxt : ∀ i,perturbRV x t i ≠ 0 := by
    intro i
    fin_cases i
    · exact hx 0
    · exact mul_ne_zero (hx 1) ht
  obtain ⟨C,hC,htrue⟩ := (hgraph x hx).mp h
  have hnew : PolarityDNF.holds (RVLiteral.holds a r (perturbRV x t)) D := by
    refine ⟨C,hC,?_⟩
    intro L hL
    apply flat_literal_preserved (dnfMonomials D) a r x (by simp [dnfMonomials]) hs t ht hv L ?_ (htrue L hL)
    intro P hP
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    exact ⟨L,List.mem_flatten.mpr ⟨C,hC,hL⟩,hP⟩
  have hout := ((hgraph (perturbRV x t) hxt).mpr hnew).2
  have hm : rvGamma (x 1) (hx 1) * rvGamma t ht = rvGamma (x 1) (hx 1) := by
    rw [← rvGamma_mul (x 1) t (hx 1) ht]
    exact hout.symm.trans h.2
  have hone : rvGamma t ht = 1 := mul_left_cancel (hm.trans (mul_one _).symm)
  exact (ne_of_gt he) hone

end DiamondIntegral.Section5.GammaQE
