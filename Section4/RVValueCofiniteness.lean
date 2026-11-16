module

public import Section3.AngularPattern
public import Section3.InfiniteValueFibres
public import Section3.FiniteValueFibres
public import Section4.UniformFiniteCofinite

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The given angular-pattern theorem makes every unary definable RV
set finite or cofinite inside each fixed value class. No parameter or
representative used to describe the exceptional set is named in the base. -/
theorem rv_value_finite_or_cofinite (S A : Set M) (hA : DefinableAt S .rv A)
    (γ : Values.GammaTop (M := M)) :
    {t : CanonicalRV.RVSort M | Values.vrv t = γ ∧ t.val ∈ A}.Finite ∨
      {t : CanonicalRV.RVSort M | Values.vrv t = γ ∧ t.val ∉ A}.Finite := by
  obtain ⟨T, hT, hTRV, hpattern⟩ := rv_set_finite_angular_exceptions S A hA
  let T' : Set (CanonicalRV.RVSort M) := {t | t.val ∈ T}
  have hT' : T'.Finite := hT.preimage Subtype.val_injective.injOn
  by_cases hout : ∃ t : CanonicalRV.RVSort M, Values.vrv t = γ ∧ t.val ∈ A ∧ t.val ∉ T
  · obtain ⟨t, htγ, htA, htT⟩ := hout
    right
    apply hT'.subset
    rintro u ⟨huγ, huA⟩
    by_contra huT
    exact huA ((hpattern t u (htγ.trans huγ.symm) htT huT).mp htA)
  · left
    apply hT'.subset
    rintro t ⟨htγ, htA⟩
    by_contra htT
    exact hout ⟨t, htγ, htA, htT⟩

end SpecialTransformations.Section4

end
