import Section3.ValuedCMinimal
open Classical FirstOrder FirstOrder.Language
namespace SpecialTransformations.Section3

/-- The checked valued QE and Johnson geometry preserve an algebraically
closed coefficient field. Its induced valuation may be trivial; only the
ambient valuation must be nontrivial. Every ball center AND radius in the
result belongs to the image of the coefficient field. -/
theorem c_minimal_over_algebraically_closed_base {K N : Type}
    [Field K] [IsAlgClosed K] [Field N] [IsAlgClosed N]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v : Valuation N Γ)
    (hnt : ∃ x : N, x ≠ 0 ∧ v x ≠ 1) (f : K →+* N)
    (φ : Language.val.BoundedFormula K 1) :
    ValOneEC.Good f v {x : N | ValOneEC.Holds v f φ x} := by
  classical
  letI := FirstOrder.valStructure v
  haveI : N ⊨ ValPM.ACVF_val := JohnsonValuedBridge.model_ACVF_val v hnt
  obtain ⟨ψ,hqf,heq⟩ := hasQEb_ACVF_val K 1 φ
  have hgood := ValOneEC.good_solSet (f := f) (w := v)
    ValOneEC.atomGood_of_isAlgClosed ψ hqf
  have hset : {x : N | ValOneEC.Holds v f φ x} =
      {x : N | ValOneEC.Holds v f ψ x} := by
    ext x
    exact Theory.Iff.realize_bd_iff heq
  rw [hset]
  exact hgood

end SpecialTransformations.Section3
