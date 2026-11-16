module

/-
**A defect in §3's first lemma as frozen: it needs `A ≠ ∅`.**

`QE/Sec3Infra.lean` carries the paper's first §3 lemma as the `Prop`

```
SP.AclConstOfFibres M  :=  ∀ (S : SP M) (sn : Fin 1 → SortTag) (A : Set M) (x : M),
                             DefinableAt S sn A →
                             (∀ a, sortEval (sn 0) a → a ∈ A → acl (S.extendParam (sn 0) a ha) x) →
                             acl S x
```

and derives `acl:VF:transfer:acl:RV` from it; `QE/Sec3_frozen.lean`'s `swl_acl_const_of_fibres` is
its `VF` instance.  Both are **false as stated**: at `A = ∅` the hypothesis is vacuous, so the
statement asserts `acl S x` for an arbitrary element `x`, and `acl S x` contains `iVF x`.  The
paper's lemma is used at a nonempty `A` (its proof applies the hypothesis at some `a ∈ A`, and the
conclusion is `⋂_{a∈A} U_a`), so the missing hypothesis is `A.Nonempty`.

This file machine-checks the refutation and states the corrected forms.  It says nothing about
whether the corrected form is provable: over a non-saturated model it is a genuine compactness
statement, over the monster model it follows from saturation (`Sat.MonsterModel.realizes`).
-/
public import Sec3Infra

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations.Milestone0
open LRV

namespace SP

variable {M : Type*} [LRV.Structure M]

/-- `acl S x` implies `iVF x`, so an element outside the `VF` sort is not in any algebraic
closure.  This is the only property of `acl` the refutation below uses. -/
theorem not_acl_of_not_iVF (S : SP M) {x : M} (hx : ¬ iVF x) : ¬ acl S x :=
  fun h => by
    obtain ⟨φ, -, -, hVF, -⟩ := h
    exact hx hVF

/-- **`SP.AclConstOfFibres` is false** whenever the carrier has an element outside the `VF` sort
(the empty `A` is `S`-definable and makes the hypothesis vacuous).  Such an element always exists in
a model of `ACVF` — `iRVZero` is `RV`-sorted (`Axioms.sdRVZero`) and the two sorts are disjoint
(`Axioms.sdDisjoint`) — so the frozen `Prop` is not merely unproved but refutable. -/
theorem not_aclConstOfFibres (x : M) (hx : ¬ iVF x) : ¬ AclConstOfFibres M := by
  intro hC
  refine not_acl_of_not_iVF (SP.base (M := M)) hx (hC (SP.base (M := M)) (fun _ => SortTag.vf)
    (∅ : Set M) x ?_ ?_)
  · refine ⟨⊥, WellSorted.falsum _, ?_⟩
    ext y
    simp [BoundedFormula.realize_bot]
  · intro a _ ha
    exact absurd ha (Set.notMem_empty a)

/-- The same refutation, in the form of the frozen statement of `QE/Sec3_frozen.lean`
(`swl_acl_const_of_fibres`), at any model of `ACVF`.  The conclusion cannot hold for an element
outside the `VF` sort, and the hypothesis is vacuous at `A = ∅`. -/
theorem not_acl_const_of_fibres_statement [Nonempty M] (_hM : M ⊨ Axioms.ACVF) (x : M)
    (hx : ¬ iVF x) :
    ¬ (∀ (S : SP M) (A : Set M) (s : M), DefinableVF S A →
        (∀ a : M, (ha : iVF a) → a ∈ A → acl (S.extendVFParam a ha) s) → acl S s) := by
  intro h
  refine not_acl_of_not_iVF (SP.base : SP M) hx (h (SP.base : SP M) (∅ : Set M) x ?_ ?_)
  · refine ⟨⊥, WellSorted.falsum _, ?_⟩
    ext y
    simp [BoundedFormula.realize_bot]
  · intro a _ ha
    exact absurd ha (Set.notMem_empty a)

/-- **The corrected form** of §3's first lemma (paper §3, first lemma; quoted sentence: *"Let `A` be
a definable subset and `s` an element such that `s ∈ acl(a)` for every `a ∈ A`, then `s ∈ acl(0)`."*),
with the nonemptiness of `A` made explicit.  The paper's proof applies the hypothesis at an
`a ∈ A`, so this is the shape the compactness argument has; the statement itself is *not* proved
here. -/
def AclConstOfFibresNonempty (M : Type*) [LRV.Structure M] : Prop :=
  ∀ (S : SP M) (sn : Fin 1 → SortTag) (A : Set M) (x : M),
    DefinableAt S sn A → A.Nonempty →
      (∀ a : M, (ha : sortEval (sn 0) a) → a ∈ A →
        acl (S.extendParam (sn 0) a ha) x) →
      acl S x

end SP

end SpecialTransformations.Milestone0
