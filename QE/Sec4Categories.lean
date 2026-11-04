/-
**Section 4, the categories `VF[k,·]` and `RV[k,·]`** — from swarm `smw1jgnht` m8, verified here
(compiled: exit 0, 0 errors, no `sorry`; the member's `axcheck.lean` — 38 `#print axioms` — rebuilt
and run here: every footprint is a subset of {propext, Classical.choice, Quot.sound}).

What is here, at statement level and with the paper's sentences in the docstrings: `SP.Definable` for
sorted-tuple sets in the well-sorted fragment, closed under `inf`/`sup`/`compl`/`sdiff`/`biUnion`/
`iUnion_fin`/`biInter`; `VFObj` (definable subsets of `A × VF^k` with finite fibres over `A`) with
`restrict`, `biUnion`, `union` and the `RVFibresFinite` condition; `weight` and `appendInfty` (`E_k`)
with `weight_appendInfty`/`_le`; `RVObj` as a pair `(U, f)` with `companion`, `graph`/`graph_fibre`,
`lift`/`rvImage`, and `rv(𝕃(U,f)) = U_f` in both directions (the reverse under `rv`-surjectivity,
carried as a hypothesis); `FiniteToOne` for `RV[k]`; subobjects via `restrict`/`subUnion`/`subInter`/
`subCompl`; `Volumetric` with `refl`/`trans`; `RVHom`.

**Open, and deliberately not hidden:** pullback along a *general* definable map (only the
definable-predicate case is proved); no `VF`-dimension — the objects use the finite-to-one
characterization instead; `E_k` only at the level of `weight`; and "inclusion is a morphism" is not
proved.  The general pullback needs the graph-composition lemma (`DefinableFun` composed with a
definable function, i.e. renaming free variables by terms), which is the same variable-level
substitution Mathlib lacks and which §3's `exchange` and §4's `dim:RV:fibers` also need — see
`QE-PLAN.md`, "the one wall, three times".

Check with `.scratch2/sec3/` (a compiled `Enc`/`Sec3Frozen`): copy this file there as
`Sec4_categories.lean`, build its olean, then its `axcheck.lean`.
-/
/-
Section 4 of the paper ("Categories of definable subsets", `paper.tex` line 801 ff.), the two
subsections after the dimension theory: the categories `VF[k,·]`, `VF[k]` (Definition
\ref{defn:VF:cat}) and `RV[k,·]`, `RV[k]` (Definition \ref{defn:RV:cat}), their objects, their
morphisms and the elementary closure lemmas of those.

The paper's own sentences, which the definitions below freeze:

* Definition \ref{defn:VF:cat}: *"The objects of the category `VF[k,·]` are the definable subsets
  of `VF`-dimension `≤ k`.  The morphisms in this category are the definable functions between
  the objects.  The category `VF[k]` is the full subcategory of `VF[k,·]` of the definable
  subsets that have `RV`-fiber dimension `0` (that is, all the `RV`-fibers are finite)."*  The
  dimension itself is not needed and is not available here; the paper's own equivalent form
  (same page) is used instead: *"by Lemma \ref{RV:fiber:dim:same}, `A ∈ VF[k]` if and only if
  there is a definable finite-to-one map `A → VF^k`"*.
* Definition \ref{defn:RV:cat}: *"An object of the category `RV[k,·]` is a definable pair `(U,f)`,
  where `U ⊆ RV^m` for some `m` and `f: U → RV^k` is a function ... The companion `U_f` of
  `(U,f)` is the subset `{(f(ū), ū) : ū ∈ U}`.  For any two objects `(U,f), (U',f')` ... and any
  function `F: U → U'`, if `wgt(f(ū)) ≤ wgt((f'∘F)(ū))` for every `ū ∈ U` then we say that `F`
  is *volumetric*.  If `F` is definable, volumetric, and, for every `t̄ ∈ RV^k` the subset
  `(f'∘F)(f^{-1}(t̄))` is finite, then it is a morphism in `mor RV[k,·]`."*  With the paper's
  Definition \ref{defn:weight}: *"the weight of `t̄ = (t_1, …, t_n) ∈ RV` is the number
  `|{i ≤ n : t_i ≠ ∞}|`"*.
* The subobject convention of the same subsection: *"A subobject of an object `A` of a
  `VF`-category is just a definable subset.  A subobject of an object `(U, f)` of an `RV`-category
  is a definable pair `(A, g)` with `A` a subset of `U` and `g = f ↾ A`.  Note that the inclusion
  map is a morphism in both cases."*
* The canonical lift, Definition \ref{def:L}: *"For any `(U,f) ∈ RV[k,·]`, let
  `𝕃_k(U,f) = ⋃{rv^{-1}(f(ū)) × {ū} : ū ∈ U}`."*  Only its shape is recorded here (as a
  definition); the statements proved about it are the elementwise ones of the paper: *"Also note
  that `rv(𝕃(U, f)) = U_f` for `(U,f) ∈ RV[k,·]`"*.

## What is proved, and what is a hypothesis

Everything in this file is stated over an arbitrary `M` with `[LRV.Structure M]` and a parameter
pair `S : SP M` (`QE/Sec3_frozen.lean`).  The definitions and the closure lemmas are *structural*:
they need no axiom of `ACVF` at all (as in the paper, where `VF[k,·]` and `RV[k,·]` are categories
of definable sets of `ACVF_S(0,0)` and the definitions carry no model-theoretic content beyond
definability).  Definability is the encoding's *well-sorted* fragment (`WellSorted`,
`Milestone0/Encoding.lean` Part 2b): the encoding's carrier admits ill-sorted junk terms, so
Mathlib's unrestricted `Set.Definable` would be the wrong notion, exactly as `Milestone0/DECISION.md`
records for C-minimality and QE.

The definable sets are sets of *sorted tuples* `α → M` for an arbitrary index type `α` and sort map
`sα : α → SortTag`, which is what the paper's `A ⊆ VF^n × RV^m` is (take `α = Fin n ⊕ Fin m`).
`SP.DefinableVF` / `SP.DefinableRV` of `QE/Sec3_frozen.lean` are the one-variable case `α = Fin 1`,
`sα = fun _ => .vf` / `.rv`, with the single coordinate a *bound* variable instead of a parameter;
`SP.Definable` records it as a parameter (see its docstring), which is the same notion and needs no
glue lemma here.  (An explicit `↔` would need `BoundedFormula.toFormula` together with preservation
of `WellSorted`, which is the substitution problem recorded two paragraphs below.)

Missing, and stated as an explicit hypothesis where it would be used: the paper's `VF`-dimension
(`dim_VF`, `paper.tex` line 807) and hence the literal objects of `VF[k,·]` as "definable subsets of
`VF`-dimension `≤ k`".  The paper's equivalent characterization *"A ∈ VF[k] iff there is a definable
finite-to-one map A → VF^k"* is what the objects of this file are: an object of `VF[k,A]` is a
definable subset of `A × VF^k` finite-to-one over `A`, i.e. a definable finite-to-one relation
`A ⇀ VF^k`.  (For `l = 0` — objects of `VF[k]` with no `RV`-coordinates in the base — this is
literally the paper's characterization.)

**Not proved, and not assumed anywhere below**: closure of `Definable` under *preimage along a
definable map*, i.e. the paper's implicit `φ(x) ↦ ∃y (θ(x,y) ∧ φ(y))`.  The missing ingredients are
(i) `TmSort`-composition for `Term.subst`/`Term.relabel` — the sort of a substituted term, and
(ii) `WellSorted`-preservation under substitution, which additionally has to preserve the encoding's
guard conditions `GuardsLast` and `GuardTrue` (`Milestone0/Encoding.lean` Part 2b) — plus the
quantifier step, whose body must satisfy `Occurs ... (Fin.last _)` and `GuardTrue` (see the existing
`wellSorted_ex_guarded` for the shape).  Nothing in this file is conditional on it.
What *is* proved for pullback is the case the paper's arguments use, restriction to a definable
subobject — a pullback along a definable predicate: `VFObj.restrict` (with `definable_inf`),
`RVObj.restrict`, `RVObj.subUnion`, `RVObj.subInter` (the fibre product of two subobjects) and
`RVObj.subCompl`.

## Contents

* `SP.Definable` — definability of a sorted tuple set; `definable_inf`/`_sup`/`_compl`/`_sdiff` and
  `definable_biUnion`/`definable_iUnion_fin`/`definable_biInter` — closure under the Boolean
  operations and finite (nonempty) intersections.
* `SP.VFObj` — objects of `VF[k,A]`; `fibre`, `fibre_finite'`, `finite_to_one`, `RVFibresFinite`
  (the `VF[k]` condition), `restrict`, `biUnion`, `union`, `RVFibresFinite.subset`,
  `RVFibresFinite.biUnion`; `SP.VFHom` — morphisms.
* `SP.weight` (Definition \ref{defn:weight}), `appendInfty` (`E_k` on tuples), `weight_appendInfty`,
  `weight_appendInfty_le`.
* `SP.RVObj` — objects of `RV[k,A]`, `companion` (+ `mem_companion`), `lift` and `rvImage` (the
  canonical `RV`-lift, Definition \ref{def:L}) with `rvImage_lift_subset` and
  `companion_subset_rvImage_lift` (`rv(𝕃(U,f)) = U_f`), the `RV[k]` condition `FiniteToOne`
  (+ `FiniteToOne.sub`), and the subobjects `restrict`/`subUnion`/`subInter`/`subCompl` with their
  `_U` simp lemmas and `restrict_mono`.
* `SP.Volumetric` (+ `refl`, `trans`) and `SP.RVObj.RVHom` — morphisms of `RV[k,·]` with the
  volumetric and finite-fibre conditions of Definition \ref{defn:RV:cat}.
-/
import Sec3Frozen

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace SP

variable {M : Type*} [LRV.Structure M]

/-! ## Part 1. Definability of sorted tuples, and its Boolean algebra

The paper works with `A ⊆ VF^n × RV^m` throughout Section 4 (Notation 2.10).  A set of such tuples
is, in the encoding, a set of functions `α → M` for the index type `α = Fin n ⊕ Fin m`, restricted
to the tuples that respect the declared sorts `sα`.  `SP.Definable` is the syntactic definability of
such a set: a well-sorted formula of `L_RV` over the parameters `S`. -/

/-- The tuples of `α → M` that respect the declared sorts `sα`: the paper's `VF^n × RV^m`. -/
def SortedTuple {α : Type} (sα : α → SortTag) (M : Type*) [LRV.Structure M] : Set (α → M) :=
  {x | ∀ i, sortEval (sα i) (x i)}

@[simp]
theorem mem_sortedTuple {α : Type} {sα : α → SortTag} {x : α → M} :
    x ∈ SortedTuple (M := M) sα ↔ ∀ i, sortEval (sα i) (x i) := Iff.rfl

/-- **`s` is `S`-definable**, for `s` a set of sorted tuples: `s` is cut out by a well-sorted
formula of `L_RV` whose parameters are those of the pair `S` (`QE/Sec3_frozen.lean`) together with
the coordinates of the tuple.

This is the paper's "definable subset of `VF^n × RV^m`" (`paper.tex`, Notation 2.10 and Section 4).
The formula is required to be `WellSorted`, i.e. to be a formula of the paper's two-sorted `L_RV`
and not merely of the encoding's one-sorted carrier.

The tuple coordinates are *parameters* of the formula (`BoundedFormula`'s free variables are an
arbitrary type `α`, so a tuple `α → M` is naturally an `α`-indexed family of parameters); this is
the identification `SP.DefinableVF S s ↔ s` definable by a formula in one *bound* variable, used
throughout `QE/Sec3_frozen.lean`, made without loss: `Realize` treats the two identically, and no
quantifier of the paper ever binds a coordinate of `A ⊆ VF^n × RV^m`. -/
def Definable (S : SP M) {α : Type} (sα : α → SortTag) (A : Set (α → M)) : Prop :=
  ∃ φ : LRV.Formula ((Fin S.n ⊕ Fin S.m) ⊕ α),
    WellSorted (Sum.elim S.sortMap sα) (Fin.elim0) φ ∧
      A = {x | (∀ i, sortEval (sα i) (x i)) ∧ φ.Realize (Sum.elim S.toFun x)}

/-- The sorted tuples themselves are definable (`⊤`). -/
theorem definable_sortedTuple (S : SP M) {α : Type} (sα : α → SortTag) :
    Definable S sα (SortedTuple (M := M) sα) := by
  refine ⟨⊤, wellSorted_top _ _, ?_⟩
  ext x
  simp [SortedTuple, Formula.Realize]

/-- The empty set is definable (`⊥`). -/
theorem definable_empty (S : SP M) {α : Type} (sα : α → SortTag) :
    Definable S sα (∅ : Set (α → M)) := by
  refine ⟨⊥, WellSorted.falsum _, ?_⟩
  ext x
  simp

/-- Definable sets are closed under intersection: conjunction of the defining formulas. -/
theorem definable_inf (S : SP M) {α : Type} {sα : α → SortTag} {A B : Set (α → M)}
    (hA : Definable S sα A) (hB : Definable S sα B) : Definable S sα (A ∩ B) := by
  obtain ⟨φ, hφ, rfl⟩ := hA
  obtain ⟨ψ, hψ, rfl⟩ := hB
  refine ⟨φ ⊓ ψ, wellSorted_inf _ _ hφ hψ, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Formula.realize_inf]
  tauto

/-- Definable sets are closed under union: disjunction of the defining formulas. -/
theorem definable_sup (S : SP M) {α : Type} {sα : α → SortTag} {A B : Set (α → M)}
    (hA : Definable S sα A) (hB : Definable S sα B) : Definable S sα (A ∪ B) := by
  obtain ⟨φ, hφ, rfl⟩ := hA
  obtain ⟨ψ, hψ, rfl⟩ := hB
  refine ⟨φ ⊔ ψ, wellSorted_sup _ _ hφ hψ, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq, Formula.realize_sup]
  tauto

/-- Definable sets are closed under complement *inside the sorted tuples*: negation of the defining
formula.  (The complement is taken in `VF^n × RV^m`, not in the encoding's whole carrier: an
ill-sorted tuple is in neither.) -/
theorem definable_compl (S : SP M) {α : Type} {sα : α → SortTag} {A : Set (α → M)}
    (hA : Definable S sα A) : Definable S sα (SortedTuple (M := M) sα \ A) := by
  obtain ⟨φ, hφ, rfl⟩ := hA
  refine ⟨∼φ, wellSorted_not _ _ hφ, ?_⟩
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, mem_sortedTuple, Formula.realize_not]
  tauto

/-- Definable sets are closed under set difference. -/
theorem definable_sdiff (S : SP M) {α : Type} {sα : α → SortTag} {A B : Set (α → M)}
    (hA : Definable S sα A) (hB : Definable S sα B) : Definable S sα (A \ B) := by
  obtain ⟨φ, hφ, rfl⟩ := hA
  obtain ⟨ψ, hψ, rfl⟩ := hB
  refine ⟨φ ⊓ ∼ψ, wellSorted_inf _ _ hφ (wellSorted_not _ _ hψ), ?_⟩
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Formula.realize_inf, Formula.realize_not]
  tauto

/-- Finite unions of definable sets are definable: the paper's definable sets form a Boolean
algebra. -/
theorem definable_biUnion (S : SP M) {α : Type} {sα : α → SortTag} {σ : Type} (s : Finset σ)
    (As : σ → Set (α → M)) (h : ∀ i ∈ s, Definable S sα (As i)) :
    Definable S sα (⋃ i ∈ (s : Set σ), As i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (⋃ i ∈ ((∅ : Finset σ) : Set σ), As i) = (∅ : Set (α → M)) := by
        ext x; simp
      rw [hz]
      exact definable_empty S sα
  | insert a s ha ih =>
      have hstep : (⋃ i ∈ ((insert a s : Finset σ) : Set σ), As i) =
          As a ∪ ⋃ i ∈ (s : Set σ), As i := by
        ext x; simp [exists_prop]
      rw [hstep]
      refine definable_sup S ?_ (ih (fun i hi => h i (by simp [hi])))
      exact h a (by simp)

/-- Finite unions over `Fin n`, the form the paper uses (`⋃_{i ≤ k}`). -/
theorem definable_iUnion_fin (S : SP M) {α : Type} {sα : α → SortTag} {n : ℕ}
    (As : Fin n → Set (α → M)) (h : ∀ i, Definable S sα (As i)) :
    Definable S sα (⋃ i, As i) := by
  obtain ⟨φ, hφ, hset⟩ := definable_biUnion S (Finset.univ : Finset (Fin n)) As (fun i _ => h i)
  refine ⟨φ, hφ, ?_⟩
  have heq : (⋃ i, As i) = ⋃ i ∈ ((Finset.univ : Finset (Fin n)) : Set (Fin n)), As i := by
    ext x; simp
  rw [heq, hset]

/-- Every definable set consists of sorted tuples: definability is definability *inside*
`VF^n × RV^m`, and an ill-sorted tuple lies in no definable set (the encoding's carrier contains
ill-sorted elements, which no axiom of `ACVF` constrains). -/
theorem Definable.subset_sortedTuple (S : SP M) {α : Type} {sα : α → SortTag}
    {A : Set (α → M)} (h : Definable S sα A) : A ⊆ SortedTuple (M := M) sα := by
  obtain ⟨φ, -, rfl⟩ := h
  intro x hx
  exact hx.1

/-- Intersecting with a finite intersection of definable sets keeps definability.  This form
carries the ambient definable set `T` because the intersection over the *empty* index set is the
whole space of tuples, which is not definable (see `Definable.subset_sortedTuple`). -/
theorem definable_inf_biInter (S : SP M) {α : Type} {sα : α → SortTag} {σ : Type}
    (s : Finset σ) (As : σ → Set (α → M)) (h : ∀ i ∈ s, Definable S sα (As i))
    {T : Set (α → M)} (hT : Definable S sα T) :
    Definable S sα (T ∩ ⋂ i ∈ (s : Set σ), As i) := by
  classical
  induction s using Finset.induction_on generalizing T with
  | empty =>
      have hz : T ∩ ⋂ i ∈ ((∅ : Finset σ) : Set σ), As i = T := by
        ext x; simp
      rw [hz]
      exact hT
  | insert a s ha ih =>
      have hstep : T ∩ ⋂ i ∈ ((insert a s : Finset σ) : Set σ), As i =
          (T ∩ As a) ∩ ⋂ i ∈ (s : Set σ), As i := by
        ext x; simp [and_assoc]
      rw [hstep]
      exact ih (fun i hi => h i (by simp [hi])) (definable_inf S hT (h a (by simp)))

/-- Finite intersections of a nonempty family of definable sets are definable. -/
theorem definable_biInter (S : SP M) {α : Type} {sα : α → SortTag} {σ : Type}
    (s : Finset σ) (As : σ → Set (α → M)) (h : ∀ i ∈ s, Definable S sα (As i))
    (hne : s.Nonempty) : Definable S sα (⋂ i ∈ (s : Set σ), As i) := by
  have hT : Definable S sα (SortedTuple (M := M) sα) := definable_sortedTuple S sα
  obtain ⟨a, ha⟩ := hne
  have hsub : (⋂ i ∈ (s : Set σ), As i) ⊆ SortedTuple (M := M) sα := by
    intro x hx
    exact Definable.subset_sortedTuple S (h a ha) (Set.mem_iInter₂.1 hx a ha)
  obtain ⟨φ, hφ, hset⟩ := definable_inf_biInter S s As h hT
  refine ⟨φ, hφ, ?_⟩
  rw [← hset]
  exact (Set.inter_eq_right.2 hsub).symm

/-! ## Part 2. The `VF`-categories `VF[k,·]` and `VF[k]`

The paper's Definition \ref{defn:VF:cat} names the objects of `VF[k,·]` by their `VF`-dimension,
which is not available here; the paper's own equivalent formulation on the same page is used
instead: *"`A ∈ VF[k]` if and only if there is a definable finite-to-one map `A → VF^k`"*.  An
object of `VF[k,A]` below is the graph of such a map: a definable subset of `A × VF^k` whose
fibres over `A` are finite.  The base `A ⊆ VF^n × RV^m` is a definable set of sorted tuples
(`SP.Definable`), and the `k` new coordinates are all at the `VF` sort (hence `vfSort`). -/


/-! ## Part 2. The `VF`-categories `VF[k,·]` and `VF[k]`

The paper's Definition \ref{defn:VF:cat} names the objects of `VF[k,·]` by their `VF`-dimension,
which is not available here; the paper's own equivalent formulation on the same page is used
instead: *"`A ∈ VF[k]` if and only if there is a definable finite-to-one map `A → VF^k`"*.  An
object of `VF[k,A]` below is the graph of such a map: a definable subset of `A × VF^k` whose
fibres over `A` are finite.  The base `A ⊆ VF^n × RV^m` is a definable set of sorted tuples
(`SP.Definable`), and the `k` new coordinates are all at the `VF` sort (hence `vfSort`). -/

section VF

/-- The base coordinates of a tuple in `A × VF^k`: the projection to `A`. -/
def baseProj {β : Type} {ι : Type} (x : (β ⊕ ι) → M) : β → M := fun b => x (Sum.inl b)

/-- The `ι`-coordinates of a tuple in `A × VF^k` (the `VF^k` part when `ι = Fin k`). -/
def secondPart {β : Type} {ι : Type} (x : (β ⊕ ι) → M) : ι → M := fun i => x (Sum.inr i)

/-- The tuple `(a, y) ∈ A × VF^k` from a base point `a` and a fibre point `y`. -/
def tupleJoin {β : Type} {ι : Type} (a : β → M) (y : ι → M) : (β ⊕ ι) → M := Sum.elim a y

@[simp]
theorem baseProj_tupleJoin {β : Type} {ι : Type} (a : β → M) (y : ι → M) :
    baseProj (tupleJoin a y) = a := rfl

@[simp]
theorem secondPart_tupleJoin {β : Type} {ι : Type} (a : β → M) (y : ι → M) :
    secondPart (tupleJoin a y) = y := rfl

theorem tupleJoin_baseProj_secondPart {β : Type} {ι : Type} (x : (β ⊕ ι) → M) :
    tupleJoin (baseProj x) (secondPart x) = x := by
  funext i; cases i <;> rfl

/-- The sort map of `A × VF^k`: the base sorts, then `VF` for every new coordinate. -/
def vfSort {β : Type} (sβ : β → SortTag) (ι : Type) : (β ⊕ ι) → SortTag :=
  Sum.elim sβ fun _ => SortTag.vf

/-- The sort map of `A × RV^k`. -/
def rvSort {β : Type} (sβ : β → SortTag) (ι : Type) : (β ⊕ ι) → SortTag :=
  Sum.elim sβ fun _ => SortTag.rv

variable {β : Type} {sβ : β → SortTag} {A : Set (β → M)} {k : ℕ}

/-- **An object of `VF[k,A]`**: a definable subset of `A × VF^k` that is finite-to-one over `A` —
the graph of a definable finite-to-one relation `A ⇀ VF^k`.  By the paper's characterization quoted
above, these are the objects of `VF[k]` when the base carries no `RV`-coordinates; the family form
`VF[k,A]` is the parametrized version (`A` an arbitrary definable set of sorted tuples), which is
what the paper uses when it speaks of the fibres `fib(A, t̄)` over `RV`-coordinates. -/
structure VFObj (S : SP M) (sβ : β → SortTag) (A : Set (β → M)) (k : ℕ) where
  /-- the definable subset of `A × VF^k` -/
  total : Set ((β ⊕ Fin k) → M)
  /-- the paper's "definable subset": the defining formula is well-sorted -/
  definable : Definable S (vfSort sβ (Fin k)) total
  /-- every point of the object lies over a point of the base `A` -/
  base_mem : ∀ x ∈ total, baseProj x ∈ A
  /-- **finite-to-one over `A`**: every fibre of the projection to `A` is finite -/
  fibre_finite : ∀ a ∈ A, {y : Fin k → M | tupleJoin a y ∈ total}.Finite

namespace VFObj

variable {S : SP M} {β : Type} {sβ : β → SortTag} {A : Set (β → M)} {k : ℕ}
  (T : VFObj S sβ A k)

/-- The fibre of `T` over the base point `a`: the paper's `fib(T, ā)`. -/
def fibre (a : β → M) : Set (Fin k → M) := {y | tupleJoin a y ∈ T.total}

@[simp]
theorem mem_fibre {a : β → M} {y : Fin k → M} : y ∈ T.fibre a ↔ tupleJoin a y ∈ T.total :=
  Iff.rfl

/-- **`T` is finite-to-one over `A`** — the paper's defining property of `VF[k,A]`, at each point
of the base. -/
theorem fibre_finite' {a : β → M} (ha : a ∈ A) : (T.fibre a).Finite := T.fibre_finite a ha

/-- The projection `T.total → A` is finite-to-one — the paper's "definable finite-to-one map
`A → VF^k`" read as a relation (each base point has finitely many values). -/
theorem finite_to_one : ∀ a ∈ A, (T.fibre a).Finite := T.fibre_finite

/-- **`T` carries finite `RV`-fibres with respect to the coordinates `γ` of the base** — the
paper's `RV`-fiber dimension `0`, i.e. the condition defining the full subcategory `VF[k]`:
*"The category `VF[k]` is the full subcategory of `VF[k,·]` of the definable subsets that have
`RV`-fiber dimension `0` (that is, all the `RV`-fibers are finite)."*  `γ ⊆ β` are the base
coordinates that carry `RV`-elements; a fibre is the set of points of `T` with prescribed
`RV`-coordinates. -/
def RVFibresFinite (γ : Set β) : Prop :=
  ∀ t : γ → M, {x : (β ⊕ Fin k) → M | x ∈ T.total ∧ ∀ b : γ, x (Sum.inl b.val) = t b}.Finite

/-- **Subobjects**: the paper's *"A subobject of an object `A` of a `VF`-category is just a
definable subset"*, i.e. `T` restricted to a definable predicate on `A × VF^k`.  This is the
pullback of `T` along the inclusion of a definable subset, and it is the form of pullback the
paper's arguments use. -/
def restrict (B : Set ((β ⊕ Fin k) → M)) (hB : Definable S (vfSort sβ (Fin k)) B) :
    VFObj S sβ A k where
  total := T.total ∩ B
  definable := definable_inf S T.definable hB
  base_mem := fun x hx => T.base_mem x hx.1
  fibre_finite := fun a ha =>
    (T.fibre_finite a ha).subset fun y hy => hy.1

/-- A subobject has the same base and a subset of the points. -/
@[simp]
theorem restrict_total (B : Set ((β ⊕ Fin k) → M)) (hB : Definable S (vfSort sβ (Fin k)) B) :
    (T.restrict B hB).total = T.total ∩ B := rfl

/-- Finite unions of objects: the direction's "closed under finite unions". -/
def biUnion {σ : Type} (s : Finset σ) (Ts : σ → VFObj S sβ A k) : VFObj S sβ A k where
  total := ⋃ i ∈ (s : Set σ), (Ts i).total
  definable := definable_biUnion S s (fun i => (Ts i).total) (fun i _ => (Ts i).definable)
  base_mem := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.1 hx
    exact (Ts i).base_mem x hi
  fibre_finite := by
    intro a ha
    have hfib : {y : Fin k → M | tupleJoin a y ∈ ⋃ i ∈ (s : Set σ), (Ts i).total} =
        ⋃ i ∈ (s : Set σ), (Ts i).fibre a := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_fibre]
    rw [hfib]
    exact Set.Finite.biUnion s.finite_toSet fun i _ => (Ts i).fibre_finite a ha

@[simp]
theorem biUnion_total {σ : Type} (s : Finset σ) (Ts : σ → VFObj S sβ A k) :
    (biUnion s Ts).total = ⋃ i ∈ (s : Set σ), (Ts i).total := rfl

/-- Binary unions of objects of `VF[k,A]`, the form the paper writes. -/
def union (T' : VFObj S sβ A k) : VFObj S sβ A k where
  total := T.total ∪ T'.total
  definable := definable_sup S T.definable T'.definable
  base_mem := fun x hx => hx.elim (fun h => T.base_mem x h) fun h => T'.base_mem x h
  fibre_finite := by
    intro a ha
    have hfib : {y : Fin k → M | tupleJoin a y ∈ T.total ∪ T'.total} =
        T.fibre a ∪ T'.fibre a := by
      ext y; simp [mem_fibre]
    rw [hfib]
    exact (T.fibre_finite a ha).union (T'.fibre_finite a ha)

@[simp]
theorem union_total (T' : VFObj S sβ A k) : (T.union T').total = T.total ∪ T'.total := rfl

/-- Finite `RV`-fibres are preserved by taking subobjects: `VF[k]` is a full subcategory, so its
objects are closed under subobjects. -/
theorem RVFibresFinite.subset (γ : Set β) {T' : VFObj S sβ A k} (h : T.RVFibresFinite γ)
    (hsub : T'.total ⊆ T.total) : T'.RVFibresFinite γ := by
  intro t
  refine (h t).subset ?_
  rintro x ⟨hx, hx'⟩
  exact ⟨hsub hx, hx'⟩

/-- Finite `RV`-fibres are preserved by finite unions: the objects of `VF[k]` are closed under
finite unions, as the paper's dimension `0` condition is. -/
theorem RVFibresFinite.biUnion {σ : Type} (s : Finset σ) (Ts : σ → VFObj S sβ A k) (γ : Set β)
    (h : ∀ i, (Ts i).RVFibresFinite γ) : (biUnion s Ts).RVFibresFinite γ := by
  intro t
  have hset : {x : (β ⊕ Fin k) → M | x ∈ ⋃ i ∈ (s : Set σ), (Ts i).total ∧
      ∀ b : γ, x (Sum.inl b.val) = t b} =
      ⋃ i ∈ (s : Set σ), {x : (β ⊕ Fin k) → M | x ∈ (Ts i).total ∧
        ∀ b : γ, x (Sum.inl b.val) = t b} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    tauto
  rw [biUnion_total, hset]
  exact Set.Finite.biUnion s.finite_toSet fun i _ => h i t

/-- **A morphism of the `VF`-categories** (Definition \ref{defn:VF:cat}): *"The morphisms in this
category are the definable functions between the objects."*  The function is recorded together with
its graph, which must be a definable set of sorted tuples; no further condition (the paper imposes
none for the `VF`-categories — contrast `RVHom`, where `F` must be volumetric with finite fibres). -/
structure VFHom {β' : Type} {sβ' : β' → SortTag} {A' : Set (β' → M)}
    (T : VFObj S sβ A k) (T' : VFObj S sβ' A' k') where
  /-- the paper's definable function `F : T → T'` -/
  F : (β ⊕ Fin k → M) → (β' ⊕ Fin k' → M)
  /-- `F` maps the object `T` into the object `T'` -/
  F_maps : ∀ x ∈ T.total, F x ∈ T'.total
  /-- `F` is definable: its graph is cut out by a well-sorted formula -/
  F_definable : Definable S (Sum.elim (vfSort sβ (Fin k)) (vfSort sβ' (Fin k')))
    {z : ((β ⊕ Fin k) ⊕ (β' ⊕ Fin k')) → M | baseProj z ∈ T.total ∧ secondPart z = F (baseProj z)}

end VFObj

end VF

/-! ## Part 3. The `RV`-categories: weight, objects, companion, volumetric morphisms -/

section RV

/-- **The weight** (Definition \ref{defn:weight}): *"For any tuple `t̄ = (t_1, …, t_n) ∈ RV`, the
weight of `t̄` is the number `|{i ≤ n : t_i ≠ ∞}|`"*.  Written as a sum of indicators, which is
the form the proofs use; `weight_eq_card` connects it to the paper's cardinality. -/
noncomputable def weight {k : ℕ} (t : Fin k → M) : ℕ := by
  classical
  exact ∑ i : Fin k, if t i ≠ iRVZero then 1 else 0

/-- The paper's `E_k` on the value tuple: append `∞` as the last coordinate. -/
def appendInfty {k : ℕ} (t : Fin k → M) : Fin (k + 1) → M := Fin.snoc t iRVZero

/-- `E_k` does not change the weight: *"`E_k : RV[k,·] → RV[k+1,·]` is a functor that is faithful,
full, and injective on objects"* — the paper calls this "obvious"; at the level of the weight the
reason is that the appended coordinate is `∞`. -/
theorem weight_appendInfty {k : ℕ} (t : Fin k → M) : weight (appendInfty t) = weight t := by
  classical
  rw [weight, weight, Fin.sum_univ_castSucc]
  simp [appendInfty]

/-- Hence `E_k` preserves the volumetric inequality: appending `∞` on both sides preserves
`wgt(f(ū)) ≤ wgt((f'∘F)(ū))`. -/
theorem weight_appendInfty_le {k : ℕ} {s t : Fin k → M} (h : weight s ≤ weight t) :
    weight (appendInfty s) ≤ weight (appendInfty t) := by
  rwa [weight_appendInfty, weight_appendInfty]

variable {S : SP M} {β : Type} {sβ : β → SortTag} {A : Set (β → M)} {k : ℕ}

/-- **An object of `RV[k,A]`**: the paper's *"definable pair `(U,f)`, where `U ⊆ RV^m` ... and
`f : U → RV^k` is a function"*, with `U` a definable subset of the base `A` and `f` a definable
function (its graph is a definable set of sorted tuples).  The `RV[k,A]` form is the parametrized
version: `U` ranges over the definable subsets of the base `A`. -/
structure RVObj (S : SP M) (sβ : β → SortTag) (A : Set (β → M)) (k : ℕ) where
  /-- the paper's `U` -/
  U : Set (β → M)
  U_sub : U ⊆ A
  U_definable : Definable S sβ U
  /-- the paper's `f : U → RV^k` -/
  f : (β → M) → Fin k → M
  f_sorted : ∀ u ∈ U, ∀ i, iRV (f u i)
  /-- `f` is a *definable* function: its graph over the base `A` is a definable set of sorted
  tuples.  Taking the graph over `A` rather than over `U` is what makes the subobjects of
  Definition \ref{defn:RV:cat} — *"a definable pair `(A,g)` with `A` a subset of `U` and
  `g = f ↾ A`"* — literally the same function restricted, hence closed under the Boolean
  operations (`RVObj.restrict`, `RVObj.subUnion`, `RVObj.subInter`, `RVObj.subCompl`). -/
  graph_definable : Definable S (rvSort sβ (Fin k))
    {z : (β ⊕ Fin k) → M | baseProj z ∈ A ∧ secondPart z = f (baseProj z)}

namespace RVObj

variable (X : RVObj S sβ A k)

/-- **The companion `U_f`** of `(U,f)`: *"The companion `U_f` of `(U,f)` is the subset
`{(f(ū), ū) : ū ∈ U}`"*. -/
def companion : Set ((Fin k ⊕ β) → M) :=
  {y | (fun b => y (Sum.inr b)) ∈ X.U ∧ ∀ i, y (Sum.inl i) = X.f (fun b => y (Sum.inr b)) i}

/-- The companion is exactly the paper's set `{(f(ū), ū) : ū ∈ U}`. -/
theorem mem_companion (y : (Fin k ⊕ β) → M) :
    y ∈ X.companion ↔ ∃ u : β → M, u ∈ X.U ∧ y = Sum.elim (X.f u) u := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨fun b => y (Sum.inr b), hu, ?_⟩
    funext i
    cases i with
    | inl i => simpa using h i
    | inr b => rfl
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hu, fun i => rfl⟩

/-- The companion is a graph over `U`: its base coordinates are determined by membership. -/
theorem companion_mem_iff (u : β → M) :
    Sum.elim (X.f u) u ∈ X.companion ↔ u ∈ X.U := by
  rw [mem_companion]
  constructor
  · rintro ⟨u', hu', h⟩
    have h' : u = u' := by
      funext b
      exact congrFun h (Sum.inr b)
    rw [h']
    exact hu'
  · intro hu; exact ⟨u, hu, rfl⟩

/-- **The graph of `(U,f)`**: `{(ū, f(ū)) : ū ∈ U} ⊆ U × RV^k`, the definable subset of
`A × RV^k` that the paper's pair `(U,f)` denotes.  This is the `RV`-analogue of an object of
`VF[k,A]`: a definable subset of the base times `RV^k` which is the graph of a function. -/
def graph : Set ((β ⊕ Fin k) → M) :=
  {z | baseProj z ∈ X.U ∧ secondPart z = X.f (baseProj z)}

@[simp]
theorem mem_graph {z : (β ⊕ Fin k) → M} :
    z ∈ X.graph ↔ baseProj z ∈ X.U ∧ secondPart z = X.f (baseProj z) := Iff.rfl

/-- Each point of `U` has exactly one value: the fibre of the graph over `u ∈ U` is `{f(ū)}`. -/
theorem graph_fibre {u : β → M} (hu : u ∈ X.U) :
    {v : Fin k → M | tupleJoin u v ∈ X.graph} = {X.f u} := by
  ext v
  simp [mem_graph, hu]

/-- **The canonical `RV`-lift** `𝕃_k(U,f)` (Definition \ref{def:L}): *"`𝕃_k(U,f) =
⋃{rv^{-1}(f(ū)) × {ū} : ū ∈ U}`"*, the `VF`-part of the lift being the coordinatewise `rv`-fibre.
The coordinates are `Fin k ⊕ β`: the first `k` are `VF`-coordinates mapping to `f(ū)`, the rest are
the base point `ū` itself. -/
def lift : Set ((Fin k ⊕ β) → M) :=
  {z | (∀ i, iVF (z (Sum.inl i))) ∧ (fun b => z (Sum.inr b)) ∈ X.U ∧
    ∀ i, iRv (z (Sum.inl i)) = X.f (fun b => z (Sum.inr b)) i}

/-- The `rv`-image of a set of tuples: coordinatewise `rv` on the `k` first coordinates, identity
on the base coordinates. -/
def rvImage (Y : Set ((Fin k ⊕ β) → M)) : Set ((Fin k ⊕ β) → M) :=
  {y | ∃ z ∈ Y, (∀ i, y (Sum.inl i) = iRv (z (Sum.inl i))) ∧
    ∀ b, y (Sum.inr b) = z (Sum.inr b)}

/-- **`rv(𝕃(U,f)) ⊆ U_f`**: every point of the `rv`-image of the canonical lift is in the
companion. -/
theorem rvImage_lift_subset : rvImage X.lift ⊆ X.companion := by
  rintro y ⟨z, ⟨hVF, hU, hrv⟩, hinl, hinr⟩
  refine ⟨?_, fun i => ?_⟩
  · rw [show (fun b => y (Sum.inr b)) = fun b => z (Sum.inr b) from funext hinr]
    exact hU
  · rw [hinl i, hrv i]
    exact congrArg (fun w => X.f w i) (by funext b; exact (hinr b).symm)

/-- **`rv(𝕃(U,f)) = U_f`** (the paper's *"Also note that `rv(𝕃(U, f)) = U_f`"*), the non-trivial
inclusion.  It needs `rv` to be onto the `RV`-sort, which is axiom (2) of Definition 2.2 as the
paper states it (`rv : VF^× → RV^×` surjective, together with `rv(0) = ∞`); the encoding's
`Axioms.rvSurj` is weaker (`rv` onto the class of `1`), so the needed form is an explicit hypothesis
here. -/
theorem companion_subset_rvImage_lift
    (hsurj : ∀ t : M, iRV t → ∃ x : M, iVF x ∧ iRv x = t) :
    X.companion ⊆ rvImage X.lift := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := (mem_companion X y).1 hy
  choose x hx using fun i => hsurj (X.f u i) (X.f_sorted u hu i)
  exact ⟨Sum.elim (fun i => x i) u, ⟨fun i => (hx i).1, hu, fun i => (hx i).2⟩,
    fun i => ((hx i).2).symm, fun b => rfl⟩

/-- **A subobject of `(U,f)`** (Definition \ref{defn:RV:cat}): *"A subobject of an object `(U, f)`
of an `RV`-category is a definable pair `(A, g)` with `A` a subset of `U` and `g = f ↾ A`."*  Here
`A` is any definable subset of `U`, and the function stays the same. -/
def restrict (B : Set (β → M)) (hB : Definable S sβ B) (hBU : B ⊆ X.U) :
    RVObj S sβ A k where
  U := B
  U_sub := fun u hu => X.U_sub (hBU hu)
  U_definable := hB
  f := X.f
  f_sorted := fun u hu => X.f_sorted u (hBU hu)
  graph_definable := X.graph_definable

@[simp]
theorem restrict_U (B : Set (β → M)) (hB : Definable S sβ B) (hBU : B ⊆ X.U) :
    (X.restrict B hB hBU).U = B := rfl

/-- **`(U,f) ∈ RV[k]`**: *"The category `RV[k]` is the full subcategory of `RV[k,·]` of the pairs
`(U,f)` such that `f : U → RV^k` is finite-to-one."* -/
def FiniteToOne : Prop :=
  ∀ t : Fin k → M, {u : β → M | u ∈ X.U ∧ X.f u = t}.Finite

/-- `RV[k]` is a full subcategory: subobjects of a finite-to-one object are finite-to-one. -/
theorem FiniteToOne.sub {X' : RVObj S sβ A k} (h : X.FiniteToOne) (hU : X'.U ⊆ X.U)
    (hf : X'.f = X.f) : X'.FiniteToOne := by
  intro t
  refine (h t).subset ?_
  rintro u ⟨hu, hfu⟩
  exact ⟨hU hu, by rw [← hf]; exact hfu⟩

/-- Subobjects of `(U,f)` are closed under **finite unions** — the direction's first closure
property, here in the `RV`-categories. -/
def subUnion {σ : Type} (s : Finset σ) (Bs : σ → Set (β → M))
    (hB : ∀ i ∈ s, Definable S sβ (Bs i)) (hBU : ∀ i ∈ s, Bs i ⊆ X.U) : RVObj S sβ A k :=
  X.restrict (⋃ i ∈ (s : Set σ), Bs i) (definable_biUnion S s Bs hB) fun u hu => by
    obtain ⟨i, hi, hui⟩ := Set.mem_iUnion₂.1 hu
    exact hBU i hi hui

/-- Subobjects are closed under **intersection**, which is the pullback (fibre product over
`(U,f)`) of two subobjects. -/
def subInter (B B' : Set (β → M)) (hB : Definable S sβ B) (hB' : Definable S sβ B')
    (hBU : B ⊆ X.U) : RVObj S sβ A k :=
  X.restrict (B ∩ B') (definable_inf S hB hB') fun u hu => hBU hu.1

/-- Subobjects are closed under **complement inside `U`**. -/
def subCompl (B : Set (β → M)) (hB : Definable S sβ B) (hBU : B ⊆ X.U) : RVObj S sβ A k :=
  X.restrict (X.U \ B) (definable_sdiff S X.U_definable hB) fun u hu => hu.1

/-- Subobject inclusion is a preorder: `X ≤ Y` iff `Y.U ⊆ X.U` ... stated directly as monotonicity
of the underlying definable sets. -/
@[simp]
theorem subUnion_U {σ : Type} (s : Finset σ) (Bs : σ → Set (β → M))
    (hB : ∀ i ∈ s, Definable S sβ (Bs i)) (hBU : ∀ i ∈ s, Bs i ⊆ X.U) :
    (X.subUnion s Bs hB hBU).U = ⋃ i ∈ (s : Set σ), Bs i := rfl

@[simp]
theorem subInter_U (B B' : Set (β → M)) (hB : Definable S sβ B) (hB' : Definable S sβ B')
    (hBU : B ⊆ X.U) : (X.subInter B B' hB hB' hBU).U = B ∩ B' := rfl

@[simp]
theorem subCompl_U (B : Set (β → M)) (hB : Definable S sβ B) (hBU : B ⊆ X.U) :
    (X.subCompl B hB hBU).U = X.U \ B := rfl

theorem restrict_mono {B B' : Set (β → M)} (hB : Definable S sβ B) (hB' : Definable S sβ B')
    (hBU : B ⊆ X.U) (hB'U : B' ⊆ X.U) (h : B ⊆ B') :
    (X.restrict B hB hBU).U ⊆ (X.restrict B' hB' hB'U).U := h

end RVObj

/-- **Volumetric** (Definition \ref{defn:RV:cat}): *"if `wgt(f(ū)) ≤ wgt((f'∘F)(ū))` for every
`ū ∈ U` then we say that `F` is volumetric"*. -/
def Volumetric {β' : Type} {sβ' : β' → SortTag} {A' : Set (β' → M)}
    (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k) (F : (β → M) → β' → M) : Prop :=
  ∀ u ∈ X.U, weight (X.f u) ≤ weight (Y.f (F u))

theorem Volumetric.refl (X : RVObj S sβ A k) : Volumetric X X id := fun _ _ => le_rfl

theorem Volumetric.trans {β' β'' : Type} {sβ' : β' → SortTag} {sβ'' : β'' → SortTag}
    {A' : Set (β' → M)} {A'' : Set (β'' → M)}
    {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {Z : RVObj S sβ'' A'' k}
    {F : (β → M) → β' → M} {G : (β' → M) → β'' → M}
    (hmap : ∀ u ∈ X.U, F u ∈ Y.U)
    (hF : Volumetric X Y F) (hG : Volumetric Y Z G) :
    Volumetric X Z (fun u => G (F u)) :=
  fun u hu => le_trans (hF u hu) (hG (F u) (hmap u hu))

/-- **A morphism of `RV[k,·]`** (Definition \ref{defn:RV:cat}): *"If `F` is definable, volumetric,
and, for every `t̄ ∈ RV^k` the subset `(f'∘F)(f^{-1}(t̄))` is finite, then it is a morphism in
`mor RV[k,·]`."* -/
structure RVHom {β' : Type} {sβ' : β' → SortTag} {A' : Set (β' → M)}
    (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k) where
  /-- the paper's `F : U → U'` -/
  F : (β → M) → β' → M
  F_maps : ∀ u ∈ X.U, F u ∈ Y.U
  /-- `F` is definable (its graph is a definable set of sorted tuples) -/
  F_definable : Definable S (Sum.elim sβ sβ')
    {z : (β ⊕ β') → M | baseProj z ∈ X.U ∧ secondPart z = F (baseProj z)}
  /-- `F` is volumetric -/
  volumetric : Volumetric X Y F
  /-- the fibres of `f'∘F` over `RV^k` are finite -/
  finite_fibres : ∀ t : Fin k → M,
    {v : Fin k → M | ∃ u : β → M, u ∈ X.U ∧ X.f u = t ∧ v = Y.f (F u)}.Finite

end RV

end SP

end SpecialTransformations.Milestone0
