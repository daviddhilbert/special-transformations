module

public import Section3.NormalizationSaturation
public import Section3.CanonicalParameters
public import Section3.ClosureBridge

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma 3.1 in arbitrary ACVF models, with the original small base and
all finite mixed tuple arities. The canonical representation is internal. -/
theorem lemma_3_1 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)) (b : M) (σ : SortTag)
    (hA : DefinableOver S sn A) (hne : A.Nonempty)
    (hb : ∀ a ∈ A, AlgebraicAt (S ∪ Set.range a) σ b) : AlgebraicAt S σ b := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hsat : @Saturated M N κ := hs.normalize
  have hAN : @DefinableOver M N S n sn A := (definableOver_normalize_iff S sn A).mpr hA
  have hbN (a : Fin n → M) (ha : a ∈ A) :
      @AlgebraicAt M N (S ∪ Set.range a) σ b :=
    (algebraicAt_normalize_iff (S ∪ Set.range a) σ b).mpr (hb a ha)
  have hout : @AlgebraicAt M N S σ b :=
    @lemma_3_1_canonical M N hN hcan κ hκ hsat S hsmall n sn A b σ hAN hne hbN
  exact (algebraicAt_normalize_iff S σ b).mp hout

end SpecialTransformations.Section3
