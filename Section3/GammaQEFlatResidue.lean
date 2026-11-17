module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQEFlatResidue.lean
Original declaration namespaces and notices are retained.
-/
public import Section3.GammaQEFlatMonomials

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! At a point where distinct output slopes do not meet, every active
flat residue summand has output slope zero. It is therefore unchanged
under a perturbation of the second RV coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV GuardedRVNormalForm
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {I R : Type}

def SlopesSeparated (s : List (Monomial I R (Fin 2))) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : Fin 2 → RVSort M) : Prop :=
  ∀ P ∈ s,∀ Q ∈ s,P.rawEval a r x ≠ 0 → Q.rawEval a r x ≠ 0 →
    Values.vrv (P.rawEval a r x) = Values.vrv (Q.rawEval a r x) → P.powers 1 = Q.powers 1

theorem flat_residue_term_fixed (s : List (Monomial I R (Fin 2))) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : Fin 2 → RVSort M) (h1 : Monomial.one ∈ s)
    (hs : SlopesSeparated s a r x) (P : Monomial I R (Fin 2)) (hP : P ∈ s)
    (hK : ValuedModelMap.inK (P.rawEval a r x)) (t : RVSort M) :
    P.rawEval a r (perturbRV x t) = P.rawEval a r x := by
  rw [flat_rawEval_perturb]
  by_cases hz : P.rawEval a r x = 0
  · rw [hz,zero_mul]
  · have hv : Values.vrv (P.rawEval a r x) = 1 := (rv_inK_iff _).mp hK |>.resolve_left hz
    have hq := hs P hP Monomial.one h1 hz
      (by rw [Monomial.rawEval_one]; exact one_ne_zero)
      (by rw [Monomial.rawEval_one,RVOperations.vrv_one]; exact hv)
    have hq0 : P.powers 1 = 0 := by simpa only [Monomial.one,Finsupp.zero_apply] using hq
    rw [hq0,zpow_zero,mul_one]

theorem flat_residue_polynomial_fixed (s : List (Monomial I R (Fin 2))) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : Fin 2 → RVSort M) (h1 : Monomial.one ∈ s)
    (hs : SlopesSeparated s a r x) (P : KPolynomial I R (Fin 2))
    (hP : ∀ i,P.terms i ∈ s) (hD : P.Domain a r x) (t : RVSort M) :
    P.Domain a r (perturbRV x t) ∧ P.rawEval a r (perturbRV x t) = P.rawEval a r x := by
  have he (i : Fin P.size) : (P.terms i).rawEval a r (perturbRV x t) = (P.terms i).rawEval a r x :=
    flat_residue_term_fixed s a r x h1 hs (P.terms i) (hP i) (hD i).2 t
  constructor
  · intro i
    exact ⟨(hD i).1,(he i).symm ▸ (hD i).2⟩
  · unfold KPolynomial.rawEval
    rw [funext he]

theorem raw_residue_sum_inK : ∀ {n : ℕ} (f : Fin n → RVSort M),
    ValuedModelMap.inK (KPolynomial.rvSum f) := by
  intro n
  cases n with
  | zero => intro f; exact (rv_inK_iff _).mpr (Or.inl rfl)
  | succ n => intro f; exact RVOperations.addK_inK _ _

theorem flat_polynomial_inK (P : KPolynomial I R (Fin 2)) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : Fin 2 → RVSort M) : ValuedModelMap.inK (P.rawEval a r x) :=
  raw_residue_sum_inK _

end DiamondIntegral.Section5.GammaQE
