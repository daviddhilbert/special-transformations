module

public import Section3.GammaUniformCover
public import Section3.GammaFamilyIntersection
public import Section3.GammaSpecialization
public import Section3.SmallFiniteParameters
public import Section3.GammaSupport

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Descent with an actual Gamma output. Its finite witness is a finite set
of values, while definability uses its entire invariant RV preimage. -/
theorem gamma_output_descent {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {k n : ℕ} (γ : Fin k → Values.Gamma (M := M)) (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) (δ : Values.Gamma (M := M))
    (hA : DefinableWith S γ sn A) (hne : A.Nonempty)
    (hδ : ∀ a ∈ A, GammaAlgebraicAtBase (⟨S ∪ Set.range a,∅⟩ : Base (M := M)) δ) :
    GammaAlgebraicAtBase (⟨S,Set.range γ⟩ : Base (M := M)) δ := by
  obtain ⟨Q,hQA⟩ := hA
  let t := representatives γ
  let B := S ∪ Set.range (rawTuple t)
  have hAN := (definableOver_iff_normalized_raw B sn A).mp
    (DefinableWith.specialize ⟨Q,hQA⟩ t (representatives_values γ))
  obtain ⟨R,hcov⟩ := uniform_good_gamma_relation_cover hs S B Set.subset_union_left A δ
    (small_insert hκ B (small_union_range hκ S hsmall (rawTuple t)) (raw (representative δ)))
    hAN.1 hδ
  let W := intersectionRelation Q .rv R.carrier R.definable
  let V : Set (Values.Gamma (M := M)) :=
    {ε | (fun _ : Fin 1 => raw (representative ε)) ∈ W.fibre γ}
  obtain ⟨a₀,ha₀⟩ := hne
  have haQ : a₀ ∈ Q.fibre γ := hQA.symm ▸ ha₀
  have hVfin : V.Finite := (R.finite a₀).subset (fun ε hε => hε.2.2 a₀ haQ)
  have hinv (u v : Code (M := M)) (huv : value u = value v) :
      (fun _ : Fin 1 => raw u) ∈ W.fibre γ ↔ (fun _ : Fin 1 => raw v) ∈ W.fibre γ := by
    change (Proper (rawTuple (representatives γ)) ∧ iRV (raw u) ∧
      ∀ a, (rawTuple (representatives γ),a) ∈ Q.carrier → (a,raw u) ∈ R.carrier) ↔
      (Proper (rawTuple (representatives γ)) ∧ iRV (raw v) ∧
      ∀ a, (rawTuple (representatives γ),a) ∈ Q.carrier → (a,raw v) ∈ R.carrier)
    simp only [rawTuple_proper,raw_rv,true_and]
    exact forall_congr' (fun a => imp_congr Iff.rfl (R.invariant a u v huv))
  have hpre : {z : Fin 1 → M | z 0 ∈ Values.gammaPullback V} = W.fibre γ := by
    ext z
    constructor
    · rintro ⟨hr,hz,hV⟩
      let u : Code (M := M) := ⟨⟨z 0,hr⟩,hz⟩
      have hZu := (hinv u (representative (value u)) (representative_value _).symm).mpr hV
      have he : (fun _ : Fin 1 => z 0) = z := by funext i; fin_cases i; rfl
      exact he ▸ hZu
    · intro hz
      have hz0 := R.proper a₀ (z 0) (hz.2.2 a₀ haQ)
      let u : Code (M := M) := ⟨⟨z 0,hz0.1⟩,hz0.2⟩
      refine ⟨hz0.1,hz0.2,?_⟩
      apply (hinv u (representative (value u)) (representative_value _).symm).mp
      have he : (fun _ : Fin 1 => z 0) = z := by funext i; fin_cases i; rfl
      exact he.symm ▸ hz
  have hVdef : GammaDefinableOverBase (⟨S,Set.range γ⟩ : Base (M := M)) V := by
    refine ⟨k,γ,(fun i => Set.mem_range_self i),W,?_⟩
    exact hpre.symm
  refine ⟨V,hVdef,hVfin,?_⟩
  change Proper (rawTuple (representatives γ)) ∧ iRV (raw (representative δ)) ∧
    ∀ a, (rawTuple (representatives γ),a) ∈ Q.carrier → (a,raw (representative δ)) ∈ R.carrier
  refine ⟨rawTuple_proper _,raw_rv _,?_⟩
  intro a ha
  apply hcov a
  rw [← hQA]
  exact ha

theorem lemma_3_1_gamma_output {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)) (δ : Values.Gamma (M := M))
    (hA : SpecialTransformations.Section3.DefinableOver S sn A) (hne : A.Nonempty)
    (hδ : ∀ a ∈ A, GammaAlgebraicAtBase (⟨S ∪ Set.range a,∅⟩ : Base (M := M)) δ) :
    GammaAlgebraicAtBase (⟨S,∅⟩ : Base (M := M)) δ := by
  let γ : Fin 0 → Values.Gamma (M := M) := Fin.elim0
  have hγ : Set.range γ = ∅ := by ext x; simp only [Set.mem_range,Set.mem_empty_iff_false]; exact ⟨fun ⟨i,_⟩ => i.elim0,False.elim⟩
  have hh := gamma_output_descent hκ hs S hsmall γ sn A δ
    ((with_zero_iff S γ sn A).mpr hA) hne hδ
  simpa only [hγ] using hh

theorem corollary_3_2_vf_gamma_output {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (t : Fin n → M) (A : Set (Fin n → M)) (δ : Values.Gamma (M := M))
    (hA : SpecialTransformations.Section3.DefinableOver (S ∪ Set.range t) (fun _ => .vf) A)
    (hne : A.Nonempty)
    (hδ : ∀ a ∈ A, GammaAlgebraicAtBase (⟨S ∪ Set.range a,∅⟩ : Base (M := M)) δ) :
    GammaAlgebraicAtBase (⟨S ∪ Set.range t,∅⟩ : Base (M := M)) δ := by
  apply lemma_3_1_gamma_output hκ hs (S ∪ Set.range t) (small_union_range hκ S hsmall t)
    (fun _ => .vf) A δ hA hne
  intro a ha
  exact (hδ a ha).mono (Set.union_subset_union_left _ Set.subset_union_left) (Set.Subset.refl _)

theorem corollary_3_2_rv_gamma_output {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (γ : Fin n → Values.Gamma (M := M))
    (A : Set (Fin n → M)) (δ : Values.Gamma (M := M))
    (hA : DefinableWith S γ (fun _ => .rv) A) (hne : A.Nonempty)
    (hδ : ∀ a ∈ A, GammaAlgebraicAtBase (⟨S ∪ Set.range a,∅⟩ : Base (M := M)) δ) :
    GammaAlgebraicAtBase (⟨S,Set.range γ⟩ : Base (M := M)) δ :=
  gamma_output_descent hκ hs S hsmall γ (fun _ => .rv) A δ hA hne hδ

end SpecialTransformations.Section3.GammaParameters
