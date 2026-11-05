import CanonicalQF

/-! Correctly sorted preservation suffices for ordinary embeddings once both
models use canonical totalizations. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open scoped FirstOrder

namespace CanonicalStructure

variable (M N : Type) [sM : LRV.Structure M] [sN : LRV.Structure N]

/-- An injective map preserving the two sorts, functions on correctly sorted
tuples, and relations on correctly sorted tuples. It imposes no condition on
the arbitrary off-sort choices of the original structures. -/
structure SortedEmbedding where
  toFun : M → N
  injective : Function.Injective toFun
  sort_iff : ∀ (s : SortTag) (x : M), sortEval s (toFun x) ↔ sortEval s x
  map_fun : ∀ {k : ℕ} (f : Fn k) (xs : Fin k → M),
    (∀ i, sortEval (Fn.argSort f i) (xs i)) →
    toFun (Structure.funMap (L := LRV) f xs) =
      Structure.funMap (L := LRV) f (toFun ∘ xs)
  map_rel : ∀ {k : ℕ} (r : Rel k) (xs : Fin k → M),
    (∀ i, sortEval (Rel.argSort r i) (xs i)) →
    (Structure.RelMap (L := LRV) r (toFun ∘ xs) ↔ Structure.RelMap (L := LRV) r xs)

variable {M N}

namespace SortedEmbedding

theorem map_nullary (e : SortedEmbedding M N) (f : Fn 0)
    (xs : Fin 0 → M) (ys : Fin 0 → N) :
    e.toFun (Structure.funMap (L := LRV) f xs) = Structure.funMap (L := LRV) f ys := by
  calc
    e.toFun (Structure.funMap (L := LRV) f xs) =
        Structure.funMap (L := LRV) f (e.toFun ∘ xs) :=
      e.map_fun f xs (fun i => i.elim0)
    _ = Structure.funMap (L := LRV) f ys := by
      congr 1
      funext i
      exact i.elim0

theorem map_sortZero (e : SortedEmbedding M N) (s : SortTag) :
    e.toFun (sortZero (M := M) s) = sortZero (M := N) s := by
  cases s with
  | vf => exact e.map_nullary Fn.vfZero _ _
  | rv => exact e.map_nullary Fn.rvZero _ _

/-- On canonical ACVF models the off-sort preservation obligations follow from
the typed ones: off-sort functions are named zeros, and off-sort relations are
false. -/
def toLRVEmbedding (e : SortedEmbedding M N)
    (hM : M ⊨ Axioms.ACVF) (hN : N ⊨ Axioms.ACVF)
    (hcM : IsCanonical (M := M)) (hcN : IsCanonical (M := N)) : M ↪[LRV] N where
  toFun := e.toFun
  inj' := e.injective
  map_fun' f xs := by
    by_cases hs : ∀ i, sortEval (Fn.argSort f i) (xs i)
    · exact e.map_fun f xs hs
    · have hsN : ¬ (∀ i, sortEval (Fn.argSort f i) ((e.toFun ∘ xs) i)) := by
        intro h
        exact hs (fun i => (e.sort_iff _ _).mp (h i))
      rw [hcM.1 f xs hs, hcN.1 f (e.toFun ∘ xs) hsN]
      exact e.map_sortZero _
  map_rel' r xs := by
    by_cases hs : ∀ i, sortEval (Rel.argSort r i) (xs i)
    · exact e.map_rel r xs hs
    · have hsN : ¬ (∀ i, sortEval (Rel.argSort r i) ((e.toFun ∘ xs) i)) := by
        intro h
        exact hs (fun i => (e.sort_iff _ _).mp (h i))
      exact iff_of_false
        (fun h => hsN (relation_sorted hN hcN r _ h))
        (fun h => hs (relation_sorted hM hcM r _ h))

@[simp] theorem toLRVEmbedding_apply (e : SortedEmbedding M N)
    (hM : M ⊨ Axioms.ACVF) (hN : N ⊨ Axioms.ACVF)
    (hcM : IsCanonical (M := M)) (hcN : IsCanonical (M := N)) (x : M) :
    e.toLRVEmbedding hM hN hcM hcN x = e.toFun x := rfl

/-- Canonicalization preserves every typed embedding, without changing its
underlying map. This construction itself needs no model axioms. -/
def normalize (e : SortedEmbedding M N) :
    @SortedEmbedding M N (CanonicalStructure.normalize (M := M))
      (CanonicalStructure.normalize (M := N)) := by
  refine @SortedEmbedding.mk M N (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalize (M := N)) e.toFun e.injective ?_ ?_ ?_
  · intro s x
    simpa only [sortEval_normalize] using e.sort_iff s x
  · intro k f xs hs
    have hsM : ∀ i, sortEval (Fn.argSort f i) (xs i) := by
      simpa only [sortEval_normalize] using hs
    have hsN : ∀ i, sortEval (Fn.argSort f i) ((e.toFun ∘ xs) i) :=
      fun i => (e.sort_iff _ _).mpr (hsM i)
    rw [normalize_fun f xs hsM, normalize_fun f (e.toFun ∘ xs) hsN]
    exact e.map_fun f xs hsM
  · intro k r xs hs
    have hsM : ∀ i, sortEval (Rel.argSort r i) (xs i) := by
      simpa only [sortEval_normalize] using hs
    have hsN : ∀ i, sortEval (Rel.argSort r i) ((e.toFun ∘ xs) i) :=
      fun i => (e.sort_iff _ _).mpr (hsM i)
    exact (normalize_rel r (e.toFun ∘ xs) hsN).trans
      ((e.map_rel r xs hsM).trans (normalize_rel r xs hsM).symm)

/-- The exact bridge needed by a full-language embedding criterion: a typed map
of the original models induces an ordinary embedding of their normalizations. -/
noncomputable def toCanonicalEmbedding (e : SortedEmbedding M N)
    (hM : M ⊨ Axioms.ACVF) (hN : N ⊨ Axioms.ACVF) :
    @FirstOrder.Language.Embedding LRV M N (CanonicalStructure.normalize (M := M))
      (CanonicalStructure.normalize (M := N)) :=
  @toLRVEmbedding M N (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalize (M := N)) (@normalize M N sM sN e)
    (@normalized_model M sM hM) (@normalized_model N sN hN)
    (@normalize_isCanonical M sM) (@normalize_isCanonical N sN)

@[simp] theorem toCanonicalEmbedding_apply (e : SortedEmbedding M N)
    (hM : M ⊨ Axioms.ACVF) (hN : N ⊨ Axioms.ACVF) (x : M) :
    (@FirstOrder.Language.Embedding.toEmbedding LRV M N
      (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalize (M := N))
      (@toCanonicalEmbedding M N sM sN e hM hN)).toFun x = e.toFun x := rfl

end SortedEmbedding
end CanonicalStructure

#print axioms CanonicalStructure.SortedEmbedding.map_sortZero
#print axioms CanonicalStructure.SortedEmbedding.toLRVEmbedding
#print axioms CanonicalStructure.SortedEmbedding.normalize
#print axioms CanonicalStructure.SortedEmbedding.toCanonicalEmbedding
