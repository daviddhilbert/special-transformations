import Section3.GammaCodeDefinability
import Section3.FibrePromotion
import Section3.Counting
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters

/-- Generic cardinality argument adapted from Section3.Counting, without
its unused language-structure argument. It applies to the actual imaginary
carrier without putting a fictitious LRV structure on Gamma. -/
theorem no_injection_iff_finite_ncard_le {α : Type*} {A : Set α} {d : ℕ} :
    (¬ ∃ u : Fin (d + 1) → α, Function.Injective u ∧ ∀ i, u i ∈ A) ↔
      A.Finite ∧ A.ncard ≤ d := by
  classical
  have enum {E : Set α} {n : ℕ} (hE : E.Finite) (hc : E.ncard = n) :
      ∃ u : Fin n → α, Function.Injective u ∧ ∀ i, u i ∈ E := by
    have hh : hE.toFinset.card = n := by rw [← hc,Set.ncard_eq_toFinset_card E hE]
    let e : ↥hE.toFinset ≃ Fin n := Finset.equivFinOfCardEq hh
    refine ⟨fun i => (e.symm i).val,?_,?_⟩
    · exact fun i j he => e.symm.injective (Subtype.ext he)
    · exact fun i => hE.mem_toFinset.mp (e.symm i).property
  constructor
  · intro h
    have hf : A.Finite := by
      by_contra hi
      obtain ⟨E,hEA,hEf,hEd⟩ := Set.Infinite.exists_subset_ncard_eq hi (d + 1)
      obtain ⟨u,hu,hm⟩ := enum hEf hEd
      exact h ⟨u,hu,fun i => hEA (hm i)⟩
    refine ⟨hf,?_⟩
    by_contra hn
    have hd : d + 1 ≤ A.ncard := by omega
    obtain ⟨E,hEA,hEd⟩ := Set.exists_subset_card_eq hd
    obtain ⟨u,hu,hm⟩ := enum (hf.subset hEA) hEd
    exact h ⟨u,hu,fun i => hEA (hm i)⟩
  · rintro ⟨hf,hd⟩ ⟨u,hu,hm⟩
    have hh : (Set.univ : Set (Fin (d + 1))).ncard ≤ A.ncard :=
      Set.ncard_le_ncard_of_injOn u (fun i _ => hm i) (fun i _ j _ he => hu he) hf
    rw [Set.ncard_univ] at hh
    simp only [Nat.card_fin] at hh
    omega

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

/-- Count distinct values, rather than the infinitely many RV codes of a
single value. This predicate is first order in the released real language. -/
def HasMoreGamma (R : Set ((Fin n → M) × M)) (d : ℕ) : Set (Fin n → M) :=
  {a | ∃ u : Fin (d + 1) → M, (∀ i, (a,u i) ∈ R) ∧
    ∀ i j, i ≠ j → ¬ SameScalar (u i) (u j)}

theorem hasMoreGamma_definable (S : Set M) (R : Set ((Fin n → M) × M))
    (hR : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) n S R)
    (d : ℕ) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n) (HasMoreGamma R d) := by
  have hSame := @same_scalar_definable M (CanonicalStructure.normalize (M := M)) S
  have hSame' : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      {z | SameScalar (z 0) (z 1)} := by
    convert hSame using 1
    ext z
    exact (same_scalar_normalize (z 0) (z 1)).symm
  let E : M → M → Prop := SameScalar
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  let ι := Fin n ⊕ Fin (d + 1)
  have hr (i : Fin (d + 1)) : S.Definable LRV
      {z : ι → M | (z ∘ Sum.inl,z (.inr i)) ∈ R} :=
    hR.preimage_comp (Sum.map id (fun _ : Fin 1 => i))
  have hn (p : Fin (d + 1) × Fin (d + 1)) : S.Definable LRV
      {z : ι → M | p.1 = p.2 ∨ ¬ E (z (.inr p.1)) (z (.inr p.2))} := by
    by_cases hp : p.1 = p.2
    · simpa [hp] using Set.definable_univ S LRV (α := ι)
    · have hh := (hSame'.preimage_comp (![Sum.inr p.1,Sum.inr p.2] : Fin 2 → ι)).compl
      convert hh using 1
      ext z
      change (p.1 = p.2 ∨ ¬ E (z (.inr p.1)) (z (.inr p.2))) ↔
        ¬ E (z (.inr p.1)) (z (.inr p.2))
      simp only [hp,false_or]
  have hh := ((Set.definable_iInter_of_finite hr).inter
    (Set.definable_iInter_of_finite hn)).exists_of_finite
  convert hh using 1
  ext a
  simp only [HasMoreGamma,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,
    Sum.elim_comp_inl,Sum.elim_inr]
  constructor
  · rintro ⟨u,hu,hn⟩
    exact ⟨u,hu,fun p => or_iff_not_imp_left.mpr (hn p.1 p.2)⟩
  · rintro ⟨u,hu,hn⟩
    exact ⟨u,hu,fun i j hij => (hn (i,j)).resolve_left hij⟩

def gammaRow (R : Set ((Fin n → M) × M)) (a : Fin n → M) : Set (Values.Gamma (M := M)) :=
  {γ | (a,raw (representative γ)) ∈ R}

/-- For a union of full nonzero RV value classes, the first-order count is
exactly the ordinary cardinality count on the actual Gamma quotient. -/
theorem hasMoreGamma_iff (R : Set ((Fin n → M) × M))
    (hproper : ∀ a x, (a,x) ∈ R → NonzeroRV x)
    (hinv : ∀ a (t u : Code (M := M)), value t = value u →
      ((a,raw t) ∈ R ↔ (a,raw u) ∈ R)) (a : Fin n → M) (d : ℕ) :
    a ∈ HasMoreGamma R d ↔
      ∃ v : Fin (d + 1) → Values.Gamma (M := M), Function.Injective v ∧
        ∀ i, v i ∈ gammaRow R a := by
  constructor
  · rintro ⟨u,hu,hn⟩
    let t : Fin (d + 1) → Code (M := M) :=
      fun i => ⟨⟨u i,(hproper a (u i) (hu i)).1⟩,(hproper a (u i) (hu i)).2⟩
    refine ⟨fun i => value (t i),?_,?_⟩
    · intro i j hij
      by_contra hne
      apply hn i j hne
      exact ⟨hproper a (u i) (hu i),hproper a (u j) (hu j),
        (value_eq_iff (t i) (t j)).mp hij⟩
    · intro i
      exact (hinv a (t i) (representative (value (t i)))
        (representative_value _).symm).mp (hu i)
  · rintro ⟨v,hv,hm⟩
    refine ⟨fun i => raw (representative (v i)),hm,?_⟩
    intro i j hij hs
    apply hij
    apply hv
    have he := (value_eq_iff (representative (v i)) (representative (v j))).mpr hs.2.2
    simpa only [representative_value] using he

theorem no_moreGamma_iff (R : Set ((Fin n → M) × M))
    (hproper : ∀ a x, (a,x) ∈ R → NonzeroRV x)
    (hinv : ∀ a (t u : Code (M := M)), value t = value u →
      ((a,raw t) ∈ R ↔ (a,raw u) ∈ R)) (a : Fin n → M) (d : ℕ) :
    a ∉ HasMoreGamma R d ↔ (gammaRow R a).Finite ∧ (gammaRow R a).ncard ≤ d := by
  rw [hasMoreGamma_iff R hproper hinv a d]
  exact no_injection_iff_finite_ncard_le

end SpecialTransformations.Section3.GammaParameters
