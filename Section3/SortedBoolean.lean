import Section3.SortedTuples
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A sorted set is definable exactly when its pullback to canonical
normalization is raw-definable. The raw structure argument is explicit. -/
theorem definableOver_iff_normalized_raw (S : Set M) {n : ℕ} (sn : Fin n → SortTag)
    (s : Set (Fin n → M)) : DefinableOver S sn s ↔
      @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n) s ∧
        ∀ x ∈ s, ∀ i, sortEval (sn i) (x i) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  constructor
  · intro hs
    have hn := (definableOver_normalize_iff S sn s).mpr hs
    refine ⟨@DefinableOver.raw_definable M N S n sn s hn, ?_⟩
    obtain ⟨p, φ, hw, he⟩ := hs
    intro x hx
    exact (he ▸ hx).1
  · rintro ⟨hraw, hsort⟩
    exact (definableOver_normalize_iff S sn s).mp
      (@raw_definableOver_sorted M N hN hcan S n sn s hraw hsort)

theorem definableAt_iff_normalized_raw (S : Set M) (σ : SortTag) (s : Set M) :
    DefinableAt S σ s ↔
      @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M)) s ∧
        s ⊆ {x | sortEval σ x} := by
  constructor
  · intro hs
    exact ⟨((definableOver_iff_normalized_raw S (fun _ => σ) _).mp hs.1).1, hs.2⟩
  · rintro ⟨hraw, hsort⟩
    exact ⟨(definableOver_iff_normalized_raw S (fun _ : Fin 1 => σ) _).mpr
      ⟨hraw, fun x hx i => by fin_cases i; exact hsort hx⟩, hsort⟩

theorem DefinableAt.empty (S : Set M) (σ : SortTag) : DefinableAt S σ ∅ := by
  apply (definableAt_iff_normalized_raw S σ ∅).mpr
  constructor
  · change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1) ∅
    letI := CanonicalStructure.normalize (M := M)
    exact Set.definable_empty
  · exact Set.empty_subset _

theorem DefinableAt.union {S s t : Set M} {σ : SortTag}
    (hs : DefinableAt S σ s) (ht : DefinableAt S σ t) : DefinableAt S σ (s ∪ t) := by
  apply (definableAt_iff_normalized_raw S σ _).mpr
  have hs' := (definableAt_iff_normalized_raw S σ s).mp hs
  have ht' := (definableAt_iff_normalized_raw S σ t).mp ht
  constructor
  · letI := CanonicalStructure.normalize (M := M)
    exact hs'.1.union ht'.1
  · exact Set.union_subset hs.2 ht.2

theorem DefinableAt.inter {S s t : Set M} {σ : SortTag}
    (hs : DefinableAt S σ s) (ht : DefinableAt S σ t) : DefinableAt S σ (s ∩ t) := by
  apply (definableAt_iff_normalized_raw S σ _).mpr
  have hs' := (definableAt_iff_normalized_raw S σ s).mp hs
  have ht' := (definableAt_iff_normalized_raw S σ t).mp ht
  constructor
  · letI := CanonicalStructure.normalize (M := M)
    exact hs'.1.inter ht'.1
  · exact Set.inter_subset_left.trans hs.2

theorem DefinableAt.finite_iUnion {S : Set M} {σ : SortTag} {ι : Type}
    (s : Finset ι) (F : ι → Set M) (hF : ∀ i ∈ s, DefinableAt S σ (F i)) :
    DefinableAt S σ (⋃ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DefinableAt.empty S σ
  | @insert a s ha ih =>
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using
      (hF a (Finset.mem_insert_self a s)).union
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end SpecialTransformations.Section3
