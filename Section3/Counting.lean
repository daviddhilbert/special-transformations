module

public import Section3.Compactness

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure
variable {M : Type} [LRV.Structure M]

theorem definable_equal_coordinates (S : Set M) {ι : Type} (i j : ι) :
    S.Definable LRV {x : ι → M | x i = x j} := by
  exact ⟨(Term.var i).equal (Term.var j), rfl⟩

def HasMore (R : Set (M × M)) (k : ℕ) : Set M :=
  {a | ∃ x : Fin (k + 1) → M, Function.Injective x ∧ ∀ i, (a, x i) ∈ R}

theorem hasMore_definable (S : Set M) (R : Set (M × M))
    (hR : S.Definable₂ LRV R) (k : ℕ) : S.Definable₁ LRV (HasMore R k) := by
  classical
  let ι := Fin 1 ⊕ Fin (k + 1)
  have hrel (i : Fin (k + 1)) : S.Definable LRV
      {x : ι → M | (x (.inl 0), x (.inr i)) ∈ R} := by
    simpa only [Set.Definable₂, Set.preimage_ofPred_eq, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      hR.preimage_comp (![Sum.inl 0, Sum.inr i] : Fin 2 → ι)
  have hne (p : Fin (k + 1) × Fin (k + 1)) : S.Definable LRV
      {x : ι → M | p.1 = p.2 ∨ x (.inr p.1) ≠ x (.inr p.2)} := by
    by_cases h : p.1 = p.2
    · simpa [h] using (Set.definable_univ S LRV (α := ι))
    · simpa [h, Set.compl_ofPred] using
        (definable_equal_coordinates S (.inr p.1 : ι) (.inr p.2)).compl
  have hrelall := Set.definable_iInter_of_finite hrel
  have hneall := Set.definable_iInter_of_finite hne
  have hfull := (hneall.inter hrelall).exists_of_finite
  change S.Definable LRV {x : Fin 1 → M | x 0 ∈ HasMore R k}
  convert hfull using 1
  ext x
  simp only [HasMore, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨u, hu, hRu⟩
    exact ⟨u, fun p => or_iff_not_imp_left.mpr (fun hp => hu.ne hp), hRu⟩
  · rintro ⟨u, hu, hRu⟩
    refine ⟨u, ?_, hRu⟩
    intro i j hij
    exact (hu (i, j)).resolve_right (by simpa using hij)

/- The following finite-cardinality argument is adapted from the audited
   generic part of InfRVDefGam.lean. -/
lemma exists_inj_of_ncard_eq {t : Set M} {n : ℕ} (htfin : t.Finite) (htcard : t.ncard = n) :
    ∃ u : Fin n → M, Function.Injective u ∧ ∀ i, u i ∈ t := by
  classical
  have _ : Fintype ↥t := htfin.fintype
  have hcard : htfin.toFinset.card = n := by
    rw [← htcard, Set.ncard_eq_toFinset_card t htfin]
  let e : ↥htfin.toFinset ≃ Fin n := Finset.equivFinOfCardEq hcard
  refine ⟨fun i => ((e.symm i : ↥htfin.toFinset) : M), ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    exact (Set.Finite.mem_toFinset htfin).mp (e.symm i).2

/-- An infinite set contains `k+1` distinct points. -/
lemma exists_inj_of_infinite {s : Set M} (hs : s.Infinite) (k : ℕ) :
    ∃ u : Fin (k + 1) → M, Function.Injective u ∧ ∀ i, u i ∈ s := by
  obtain ⟨t, hts, htfin, htcard⟩ := hs.exists_subset_ncard_eq (k + 1)
  obtain ⟨u, hinj, hmem⟩ := exists_inj_of_ncard_eq htfin htcard
  exact ⟨u, hinj, fun i => hts (hmem i)⟩

/-- A set of cardinality at least `k+1` contains `k+1` distinct points. -/
lemma exists_inj_of_ncard_le {s : Set M} (hfin : s.Finite) {k : ℕ} (h : k + 1 ≤ s.ncard) :
    ∃ u : Fin (k + 1) → M, Function.Injective u ∧ ∀ i, u i ∈ s := by
  obtain ⟨t, hts, htcard⟩ := Set.exists_subset_card_eq h
  have htfin : t.Finite := hfin.subset hts
  obtain ⟨u, hinj, hmem⟩ := exists_inj_of_ncard_eq htfin htcard
  exact ⟨u, hinj, fun i => hts (hmem i)⟩

open Classical in
/-- **`s` has at most `k` elements iff it contains no `k+1` distinct elements**: the pigeonhole
principle in the form used by the paper's compactness step. -/
theorem no_inj_iff_finite_ncard_le {s : Set M} {k : ℕ} :
    (¬ ∃ u : Fin (k + 1) → M, Function.Injective u ∧ ∀ i, u i ∈ s) ↔
      s.Finite ∧ s.ncard ≤ k := by
  classical
  constructor
  · intro h
    have hfin : s.Finite := by
      by_contra hf
      exact h (exists_inj_of_infinite hf k)
    refine ⟨hfin, ?_⟩
    by_contra hle
    exact h (exists_inj_of_ncard_le hfin (by omega))
  · rintro ⟨hfin, hle⟩ ⟨u, hinj, hmem⟩
    have h1 : (Set.univ : Set (Fin (k + 1))).ncard ≤ s.ncard :=
      Set.ncard_le_ncard_of_injOn u (fun a _ => hmem a) (fun a _ b _ hab => hinj hab) hfin
    rw [Set.ncard_univ] at h1
    simp at h1
    omega


end SpecialTransformations.Section3.RawClosure