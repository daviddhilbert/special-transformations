import Section3.GammaFamilyIntersection
import Section3.GammaSpecialization
import Section3.AlgebraicUniformCover
import Section3.NormalizationSaturation
import Section3.SmallFiniteParameters
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Algebraicity descends along a nonempty Gamma-definable tuple family.
The finite witness has a globally invariant original-S preimage. Temporary
RV representatives used in compactness do not appear in that relation. -/
theorem descent_with_gamma_parameters {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {k n : ℕ} (γ : Fin k → Values.Gamma (M := M)) (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) (b : M) (σ : SortTag)
    (hA : DefinableWith S γ sn A) (hne : A.Nonempty)
    (hb : ∀ a ∈ A, SpecialTransformations.Section3.AlgebraicAt (S ∪ Set.range a) σ b) :
    AlgebraicAtBase (⟨S,Set.range γ⟩ : Base (M := M)) σ b := by
  obtain ⟨Q,hQA⟩ := hA
  let t := representatives γ
  let B := S ∪ Set.range (rawTuple t)
  have hAN := (definableOver_iff_normalized_raw B sn A).mp
    (DefinableWith.specialize ⟨Q,hQA⟩ t (representatives_values γ))
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hsN : @Saturated M N κ := hs.normalize
  have hbN (a : Fin n → M) (ha : a ∈ A) :
      @RawClosure.AlgebraicOver M N (S ∪ Set.range a) b := by
    have h := (algebraicAt_normalize_iff (S ∪ Set.range a) σ b).mpr (hb a ha)
    exact @AlgebraicAt.raw_finite_witness M N (S ∪ Set.range a) σ b h
  obtain ⟨R,hcov⟩ := @RawClosure.Tuple.uniform_good_relation_cover M N n κ hsN S B
    Set.subset_union_left A b (small_insert hκ B (small_union_range hκ S hsmall (rawTuple t)) b)
    hAN.1 hbN
  let W := intersectionRelation Q σ R.val R.property.1
  let T : Set M := {x | (fun _ : Fin 1 => x) ∈ W.fibre γ}
  have hT : DefinableAtBase (⟨S,Set.range γ⟩ : Base (M := M)) σ T := by
    refine ⟨k,γ,(fun i => Set.mem_range_self i),W,?_⟩
    ext z
    change z ∈ W.fibre γ ↔ (fun _ : Fin 1 => z 0) ∈ W.fibre γ
    have he : (fun _ : Fin 1 => z 0) = z := by funext i; fin_cases i; rfl
    rw [he]
  have hfin : T.Finite := by
    have hneQ : (Q.fibre γ).Nonempty := hQA.symm ▸ hne
    exact intersection_finite Q σ R.val R.property.2 γ hneQ
  have hbσ : sortEval σ b := by
    obtain ⟨a,ha⟩ := hne
    exact (hb a ha).sorted
  refine ⟨T,hT,hfin,?_⟩
  change Proper (rawTuple (representatives γ)) ∧ sortEval σ b ∧
    ∀ a, (rawTuple (representatives γ),a) ∈ Q.carrier → (a,b) ∈ R.val
  refine ⟨rawTuple_proper _,hbσ,?_⟩
  intro a ha
  apply hcov a
  rw [← hQA]
  exact ha

/-- RV-to-Gamma half of Corollary3.2 over any small real base, in all tuple
arities and with nonempty arbitrary Gamma-definable subsets of the fibre.
The output is any element of either released real sort; Gamma outputs and
additional imaginary names in the ambient base are separate extensions. -/
theorem corollary_3_2_rv {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (γ : Fin n → Values.Gamma (M := M))
    (A : Set (Fin n → M)) (b : M) (σ : SortTag)
    (hA : DefinableWith S γ (fun _ => .rv) A) (hne : A.Nonempty)
    (_hfibre : ∀ a ∈ A, ∃ t : Fin n → Code (M := M), rawTuple t = a ∧ values t = γ)
    (hb : ∀ a ∈ A, SpecialTransformations.Section3.AlgebraicAt (S ∪ Set.range a) σ b) :
    AlgebraicAtBase (⟨S,Set.range γ⟩ : Base (M := M)) σ b :=
  descent_with_gamma_parameters hκ hs S hsmall γ (fun _ => .rv) A b σ hA hne hb

end SpecialTransformations.Section3.GammaParameters
