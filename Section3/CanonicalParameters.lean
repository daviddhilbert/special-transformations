module

public import Section3.Parameters
public import CanonicalStructure

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem definableOver_normalize_iff (S : Set M) {n : ℕ} (sn : Fin n → SortTag)
    (s : Set (Fin n → M)) :
    @DefinableOver M (CanonicalStructure.normalize (M := M)) S n sn s ↔
      DefinableOver S sn s := by
  constructor
  · rintro ⟨⟨k, vals, ss, hss, hmem⟩, φ, hw, hs⟩
    have hss' : ∀ i, sortEval (ss i) (vals i) :=
      fun i => (CanonicalStructure.sortEval_normalize (ss i) (vals i)).mp (hss i)
    refine ⟨⟨k, vals, ss, hss', hmem⟩, φ, hw, ?_⟩
    rw [hs]
    ext x
    constructor
    · rintro ⟨hx, hφ⟩
      have hx' : ∀ i, sortEval (sn i) (x i) :=
        fun i => (CanonicalStructure.sortEval_normalize (sn i) (x i)).mp (hx i)
      exact ⟨hx', (CanonicalStructure.realize_normalize hM ss vals hss'
        φ sn x hw hx').mp hφ⟩
    · rintro ⟨hx, hφ⟩
      exact ⟨fun i => (CanonicalStructure.sortEval_normalize (sn i) (x i)).mpr (hx i),
        (CanonicalStructure.realize_normalize hM ss vals hss' φ sn x hw hx).mpr hφ⟩
  · rintro ⟨⟨k, vals, ss, hss, hmem⟩, φ, hw, hs⟩
    have hss' : ∀ i, @sortEval M (CanonicalStructure.normalize (M := M)) (ss i) (vals i) :=
      fun i => (CanonicalStructure.sortEval_normalize (ss i) (vals i)).mpr (hss i)
    refine ⟨@Parameters.mk M (CanonicalStructure.normalize (M := M)) S k vals ss hss' hmem, φ, hw, ?_⟩
    rw [hs]
    ext x
    constructor
    · rintro ⟨hx, hφ⟩
      exact ⟨fun i => (CanonicalStructure.sortEval_normalize (sn i) (x i)).mpr (hx i),
        (CanonicalStructure.realize_normalize hM ss vals hss φ sn x hw hx).mpr hφ⟩
    · rintro ⟨hx, hφ⟩
      have hx' : ∀ i, sortEval (sn i) (x i) :=
        fun i => (CanonicalStructure.sortEval_normalize (sn i) (x i)).mp (hx i)
      exact ⟨hx', (CanonicalStructure.realize_normalize hM ss vals hss
        φ sn x hw hx').mp hφ⟩

theorem definableAt_normalize_iff (S : Set M) (σ : SortTag) (s : Set M) :
    @DefinableAt M (CanonicalStructure.normalize (M := M)) S σ s ↔
      DefinableAt S σ s := by
  constructor
  · intro h
    exact ⟨(definableOver_normalize_iff S (fun _ : Fin 1 => σ) _).mp h.1, h.2⟩
  · intro h
    exact ⟨(definableOver_normalize_iff S (fun _ : Fin 1 => σ) _).mpr h.1, h.2⟩

theorem algebraicAt_normalize_iff (S : Set M) (σ : SortTag) (x : M) :
    @AlgebraicAt M (CanonicalStructure.normalize (M := M)) S σ x ↔
      AlgebraicAt S σ x := by
  constructor
  · rintro ⟨s, hs, hf, hx⟩
    exact ⟨s, (definableAt_normalize_iff S σ s).mp hs, hf, hx⟩
  · rintro ⟨s, hs, hf, hx⟩
    exact ⟨s, (definableAt_normalize_iff S σ s).mpr hs, hf, hx⟩

theorem definableClosureAt_normalize_iff (S : Set M) (σ : SortTag) (x : M) :
    @DefinableClosureAt M (CanonicalStructure.normalize (M := M)) S σ x ↔
      DefinableClosureAt S σ x := definableAt_normalize_iff S σ {x}

end SpecialTransformations.Section3
