module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQEFlatPerturbation.lean
Original declaration namespaces and notices are retained.
-/
public import Section3.GammaQEFlatLiterals
public import HilbertMathlib.Foundation.Euler.GammaFinitePerturbation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A finite slope-separated flat clause admits a nontrivial perturbation
preserving every valuation comparison. -/
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
local instance gammaTopology : TopologicalSpace (Values.Gamma (M := M)) := Preorder.topology _
local instance gammaOrderTopology : OrderTopology (Values.Gamma (M := M)) := ⟨rfl⟩

theorem flat_finite_perturbation (s : List (Monomial I R (Fin 2)))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : Fin 2 → RVSort M)
    (hs : SlopesSeparated s a r x) :
    ∃ t : RVSort M,∃ ht : t ≠ 0,1 < rvGamma t ht ∧ ValueComparisonsPreserved s a r x t := by
  let J := s.toFinset.filter (fun P => P.rawEval a r x ≠ 0)
  let av : Monomial I R (Fin 2) → Values.Gamma (M := M) := fun P =>
    if h : P.rawEval a r x ≠ 0 then rvGamma (P.rawEval a r x) h else 1
  have hsep : ∀ P ∈ J,∀ Q ∈ J,av P = av Q → P.powers 1 = Q.powers 1 := by
    intro P hP Q hQ he
    obtain ⟨hPs,hP0⟩ := Finset.mem_filter.mp hP
    obtain ⟨hQs,hQ0⟩ := Finset.mem_filter.mp hQ
    apply hs P (List.mem_toFinset.mp hPs) Q (List.mem_toFinset.mp hQs) hP0 hQ0
    simpa only [av,dif_pos hP0,dif_pos hQ0,rvGamma_val] using congrArg Subtype.val he
  obtain ⟨e,he,hcomp⟩ := GammaFinitePerturbation.finite_comparisons J av (fun P => P.powers 1) hsep
  obtain ⟨t,ht,hte⟩ := rvGamma_surjective e
  refine ⟨t,ht,hte.symm ▸ he,?_⟩
  intro P hP Q hQ
  by_cases hP0 : P.rawEval a r x = 0
  · rw [flat_rawEval_perturb,flat_rawEval_perturb]
    exact scaled_value_order_zero _ _ t ht _ _ (Or.inl hP0)
  · by_cases hQ0 : Q.rawEval a r x = 0
    · rw [flat_rawEval_perturb,flat_rawEval_perturb]
      exact scaled_value_order_zero _ _ t ht _ _ (Or.inr hQ0)
    · have hPj : P ∈ J := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hP,hP0⟩
      have hQj : Q ∈ J := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hQ,hQ0⟩
      have hc := hcomp P hPj Q hQj
      change ((av P*e^P.powers 1).val ≤ (av Q*e^Q.powers 1).val ↔ (av P).val ≤ (av Q).val) at hc
      simp only [av,dif_pos hP0,dif_pos hQ0,Values.gamma_val_mul,gamma_val_zpow,rvGamma_val] at hc
      rw [← hte,rvGamma_val] at hc
      simpa only [flat_rawEval_perturb,RVOperations.vrv_mul,rv_value_zpow] using hc

end DiamondIntegral.Section5.GammaQE
