module

public import Section4.FinitaryClosure
public import Section3.AlgebraicClosure
public import Mathlib.Combinatorics.Matroid.Rank.Finite

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The RV part of the accepted Section 3 exchange principle, uniformly
over actual parameter sets. It is an explicit earlier-section input, not
an assumed Section 4 rank or dimension comparison. -/
def RVExchangeInput : Prop :=
  ∀ (B : Set M) (x y : CanonicalRV.RVSort M),
    AlgebraicAt (insert y.val B) .rv x.val → ¬ AlgebraicAt B .rv x.val →
      AlgebraicAt (insert x.val B) .rv y.val

def rvParameterNames (X : Set (CanonicalRV.RVSort M)) : Set M := Subtype.val '' X

def rvAlgebraicClosure (S : Set M) (X : Set (CanonicalRV.RVSort M)) :
    Set (CanonicalRV.RVSort M) := {t | AlgebraicAt (S ∪ rvParameterNames X) .rv t.val}

theorem rvAlgebraicClosure_extensive (S : Set M) (X : Set (CanonicalRV.RVSort M)) :
    X ⊆ rvAlgebraicClosure S X := by
  intro t ht
  exact (definableClosureAt_of_mem (A := S ∪ rvParameterNames X) (σ := .rv)
    (x := t.val) (Or.inr ⟨t, ht, rfl⟩) t.property).algebraic

theorem rvAlgebraicClosure_mono (S : Set M) {X Y : Set (CanonicalRV.RVSort M)}
    (hXY : X ⊆ Y) : rvAlgebraicClosure S X ⊆ rvAlgebraicClosure S Y := by
  intro t ht
  exact ht.mono (Set.union_subset_union_right S (Set.image_mono hXY))

theorem rvAlgebraicClosure_idempotent (S : Set M) (X : Set (CanonicalRV.RVSort M)) :
    rvAlgebraicClosure S (rvAlgebraicClosure S X) = rvAlgebraicClosure S X := by
  apply Set.Subset.antisymm
  · intro t ht
    apply ht.eliminate_algebraic_params
    rintro b (hb | ⟨u, hu, rfl⟩)
    · exact subset_algebraicClosureSet (S ∪ rvParameterNames X) (Or.inl hb)
    · exact ⟨.rv, hu⟩
  · exact rvAlgebraicClosure_mono S (rvAlgebraicClosure_extensive S X)

def rvClosureOperator (S : Set M) : ClosureOperator (Set (CanonicalRV.RVSort M)) where
  toFun := rvAlgebraicClosure S
  monotone' := fun _ _ h => rvAlgebraicClosure_mono S h
  le_closure' := rvAlgebraicClosure_extensive S
  idempotent' := rvAlgebraicClosure_idempotent S

theorem rvClosureOperator_exchange (hex : RVExchangeInput (M := M)) (S : Set M) :
    FinitaryClosure.Exchange (rvClosureOperator S) := by
  intro I x y hx hnot
  have he (z : CanonicalRV.RVSort M) :
      S ∪ rvParameterNames (insert z I) = insert z.val (S ∪ rvParameterNames I) := by
    simp only [rvParameterNames, Set.image_insert_eq, Set.union_insert]
  change AlgebraicAt (S ∪ rvParameterNames (insert x I)) .rv y.val
  rw [he]
  apply hex (S ∪ rvParameterNames I) x y
  · change AlgebraicAt (S ∪ rvParameterNames (insert y I)) .rv x.val at hx
    rwa [he] at hx
  · exact hnot

theorem rvClosureOperator_finiteCharacter
    (hcan : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    FinitaryClosure.FiniteCharacter (rvClosureOperator S) := by
  intro I t ht
  obtain ⟨U, hU, hUfin, htU⟩ := ht.raw_finite_witness
  obtain ⟨C, hCB, hC⟩ := Set.definable_iff_finitely_definable.mp hU
  let J : Set (CanonicalRV.RVSort M) := {u | u ∈ I ∧ u.val ∈ (C : Set M)}
  have hJI : J ⊆ I := fun _ hu => hu.1
  have hJfin : J.Finite := ((C.finite_toSet).preimage Subtype.val_injective.injOn).subset
    (fun _ hu => hu.2)
  have hparams : (C : Set M) ⊆ S ∪ rvParameterNames J := by
    intro b hb
    rcases hCB hb with hbS | ⟨u, huI, hu⟩
    · exact Or.inl hbS
    · exact Or.inr ⟨u, ⟨huI, hu.symm ▸ hb⟩, hu⟩
  refine ⟨J, hJI, hJfin, ?_⟩
  apply (algebraicAt_iff_raw hcan (S ∪ rvParameterNames J) .rv t.val).mpr
  exact ⟨⟨U, hC.mono hparams, hUfin, htU⟩, t.property⟩

/-- The matroid uses genuine sorted algebraic closure. All closure laws
and finite character are proved; only the accepted Section 3 exchange
principle remains an explicit input. -/
def rvAlgebraicMatroid (hcan : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) : Matroid (CanonicalRV.RVSort M) :=
  FinitaryClosure.matroid (rvClosureOperator S)
    (rvClosureOperator_exchange hex S) (rvClosureOperator_finiteCharacter hcan S)

theorem rvAlgebraicMatroid_closure (hcan : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) (X : Set (CanonicalRV.RVSort M)) :
    (rvAlgebraicMatroid hcan hex S).closure X = rvAlgebraicClosure S X :=
  FinitaryClosure.matroid_closure (rvClosureOperator S)
    (rvClosureOperator_exchange hex S) (rvClosureOperator_finiteCharacter hcan S) X

end SpecialTransformations.Section4

end
