module

public import Section4.ResidueRelativeQF
public import Section4.RVDimension
public import Section4.CodeMaps

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {n : ℕ}

def residueScale (s : Fin n → CanonicalRV.RVSort M) (x : Fin n → ModelResidue M) :
    Fin n → CanonicalRV.RVSort M := fun i => s i * residueRV (x i)

def residueZeroPattern (s : Fin n → CanonicalRV.RVSort M) (x : Fin n → ModelResidue M) : Prop :=
  ∀ i, s i = 0 → x i = 0

def normalizedResidueSet {S : Set M} (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) : Set (Fin n → ModelResidue M) :=
  {x | residueScale s x ∈ A.carrier ∧ residueZeroPattern s x}

theorem residueZeroPattern_definable (E : Subfield (ModelResidue M))
    (s : Fin n → CanonicalRV.RVSort M) : Relative.Def E {x | residueZeroPattern s x} := by
  have hi (i : Fin n) : Relative.Def E {x : Fin n → ModelResidue M | s i = 0 → x i = 0} := by
    by_cases hs : s i = 0
    · simpa only [hs, true_implies] using
        (Relative.projection (E := E) i).eq_const 0 E.zero_mem
    · simpa only [hs, false_implies] using (Relative.proposition (ι := Fin n) E True)
  change Relative.Def E {x | ∀ i, s i = 0 → x i = 0}
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite hi

theorem normalizedResidueSet_definable
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    (hE : residueParameterField B ≤ E)
    (A : DefSet (rawRVSpace (M := M) n) (residueExtendedBase B E))
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, s i ∈ extendedCoefficients B E) :
    Relative.Def E (normalizedResidueSet A s) :=
  (Scoped.residue_pullback_definable hcan B E hE A s hs).inter
    (residueZeroPattern_definable E s)

theorem absolute_eq_of_vrv_eq {t s : CanonicalRV.RVSort M}
    (h : Values.vrv t = Values.vrv s) : RVOperations.absoluteHom t = RVOperations.absoluteHom s :=
  congrArg (Values.valueEquiv Values.presentationValuation Values.presentation_compatible) h

theorem eq_zero_of_sameValue_zero {t s : CanonicalRV.RVSort M}
    (h : Values.vrv t = Values.vrv s) (hs : s = 0) : t = 0 := by
  apply (RVOperations.absolute_eq_zero t).mp
  rw [absolute_eq_of_vrv_eq h, hs, map_zero]

theorem residue_ratio_inK {t s : CanonicalRV.RVSort M}
    (h : Values.vrv t = Values.vrv s) : ValuedModelMap.inK (t / s) := by
  apply (RVOperations.inK_iff _).mpr
  by_cases hs : s = 0
  · exact Or.inl (by simp [hs])
  · right
    rw [map_div₀, absolute_eq_of_vrv_eq h]
    exact div_self (fun he => hs ((RVOperations.absolute_eq_zero s).mp he))

theorem residuePart_residueRV (a : ModelResidue M) : residuePart (residueRV a) = a := by
  apply residueRV_injective
  exact residueRV_part (residueRV_inK a)

def residueNormalize (s t : Fin n → CanonicalRV.RVSort M) : Fin n → ModelResidue M :=
  fun i => residuePart (t i / s i)

theorem residueScale_normalize (s t : Fin n → CanonicalRV.RVSort M)
    (h : ∀ i, Values.vrv (t i) = Values.vrv (s i)) :
    residueScale s (residueNormalize s t) = t := by
  funext i
  change s i * residueRV (residuePart (t i / s i)) = t i
  rw [residueRV_part (residue_ratio_inK (h i))]
  by_cases hs : s i = 0
  · rw [hs, eq_zero_of_sameValue_zero (h i) hs, zero_mul]
  · rw [mul_comm, div_mul_cancel₀ _ hs]

theorem residueNormalize_zeroPattern (s t : Fin n → CanonicalRV.RVSort M) :
    residueZeroPattern s (residueNormalize s t) := by
  intro i hs
  change residuePart (t i / s i) = 0
  rw [hs, div_zero, residuePart_zero]

theorem residueNormalize_scale (s : Fin n → CanonicalRV.RVSort M)
    (x : Fin n → ModelResidue M) (hx : residueZeroPattern s x) :
    residueNormalize s (residueScale s x) = x := by
  funext i
  change residuePart ((s i * residueRV (x i)) / s i) = x i
  by_cases hs : s i = 0
  · rw [hs, zero_mul, div_zero, residuePart_zero, hx i hs]
  · rw [mul_div_cancel_left₀ _ hs, residuePart_residueRV]

theorem residueNormalize_mem {S : Set M} (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i))
    (t : A) : residueNormalize s t.val ∈ normalizedResidueSet A s :=
  ⟨(residueScale_normalize s t.val (hval t.val t.property)).symm ▸ t.property,
    residueNormalize_zeroPattern s t.val⟩

theorem residueScale_injective_on_zeroPattern (s : Fin n → CanonicalRV.RVSort M) :
    Set.InjOn (residueScale s) {x | residueZeroPattern s x} := by
  intro x hx y hy he
  calc
    x = residueNormalize s (residueScale s x) := (residueNormalize_scale s x hx).symm
    _ = residueNormalize s (residueScale s y) := congrArg (residueNormalize s) he
    _ = y := residueNormalize_scale s y hy

/-- Normalization is a bijection even when some coordinates are the
single absorbing RV element; those field coordinates are fixed to zero. -/
def residueNormalizationEquiv {S : Set M} (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i)) :
    A ≃ normalizedResidueSet A s where
  toFun t := ⟨residueNormalize s t.val, residueNormalize_mem A s hval t⟩
  invFun x := ⟨residueScale s x.val, x.property.1⟩
  left_inv t := Subtype.ext (residueScale_normalize s t.val (hval _ t.property))
  right_inv x := Subtype.ext (residueNormalize_scale s x.val x.property.2)

end SpecialTransformations.Section4.ResiduePurity

end
