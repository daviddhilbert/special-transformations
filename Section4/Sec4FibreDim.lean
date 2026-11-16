module

/-
Section 4 of Yin, "Special transformations in algebraically closed valued fields"
(arXiv:1006.2467), subsection 4.1 "Dimensions" (`paper.tex` lines 803-966): the **fibre layer**
and the **`RV`-side dimension calculus** on top of `QE/Sec4Dim.lean`.

What the paper needs and `QE/Sec4Dim.lean` does not have:

* the splitting of a tuple of `VF^n × RV^m` into its `VF`-part and its `RV`-part, and hence the
  paper's `fib(A, ā) ⊆ RV^m` and `prv(A) ⊆ VF^n` (used in the definition of `dim^fib_RV(A)`, in
  `RV:fiber:dim:same`, and in Definition 4.15's `VF[k]` = "all the `RV`-fibers are finite");
* the fibre `f⁻¹(t̄)` of a definable function `f : A → RV_Γ^l`, which is what `dim:VF:pullback`
  computes the dimension of;
* the `RV`-dimension calculus: monotonicity, a definable-injection bound, and the identification
  `dim_RV(B) = 0 ⟺ B` finite (`RV^0` being the singleton `{∞}`, the paper's `RV[0]` is precisely
  the category of finite sets);
* the paper's *`RV`-fibre dimension* `dim^fib_RV(A) = max {dim_RV(fib(A, ā)) : ā ∈ prv(A)}` with
  its elementary theory: `dim^fib_RV(A) ≤ k` iff every fibre has `dim_RV ≤ k`, the maximum is
  *attained*, it is monotone under inclusion and bounded by `m` for `A ⊆ VF^n × RV^m`, and
  `dim^fib_RV(A) = 0 ⟺ every RV-fibre of A is finite` — the identification Definition 4.15 uses
  verbatim.

**Proved here, unconditionally** (no model theory, no hypothesis; `#print axioms` ⊆
{propext, Classical.choice, Quot.sound} for every one of them):

* Part 1: `vfPart`, `rvPart`, `joinTup` and the splitting `joinTup (vfPart x) (rvPart x) = x`
  (`joinTup_vfPart_rvPart`), the paper's `fibRV`, `pvf`, `fibFun`; `RV^0 = {∞}` as
  `Subsingleton (Tup M 0 0)` with its element `tupZeroZero`, and the constant map into `RV^0` is
  definable (`definableFun_const_zero_zero`).
* Part 2: `dimRV_mono`, `dimRV_le_of_injOn`, **`dimRV_eq_zero_iff_finite`**, `dimVF_le_dimRV`
  (a set of `RV`-tuples has `VF`-dimension at most its `RV`-dimension), `dimVF_eq_zero_of_finite`,
  `dimRV_eq_zero_of_finite`.
* Part 3: `dimFibRV` (the paper's `dim^fib_RV`), `dimFibRV_le_iff`, `dimRV_fibRV_le`,
  `dimFibRV_le_self`, `dimFibRV_mono`, **`dimFibRV_eq_zero_iff`**, and
  `exists_fibRV_dimRV_eq` (the `max` is attained).
* Part 4: **`dim:VF:pullback`** (`paper.tex:832`) in the form
  `dim_VF(A) ≤ k ↔ ∀ t̄, dim_VF(f⁻¹(t̄)) ≤ k`, plus the *unconditional* half
  `dimVF_fibFun_le` (each fibre's dimension is at most `A`'s, "the other direction is trivial"),
  the finite-to-one argument `fibreFinite_pairTup`, and the attainment of the paper's maximum
  (`exists_fibFun_dimVF_eq`).

**The two hypotheses of `dim:VF:pullback`, neither of which is the lemma:**

* `PairWall` — the pairing `x ↦ (g x, h x)` of two `DefinableFun`s is a `DefinableFun`.  This is
  the composition/substitution step that `QE-PLAN.md` records as the one missing piece of the
  encoding (it needs the guarded existential of `Milestone0/Encoding.lean` with
  `QE/ExSortedG.lean`'s `exSortedG_realize`); it is stated for *all* shapes, is used once, and
  says nothing about dimensions.
* `PaperFibreUniform` — the paper's own compactness sentence, *"By compactness, there is a
  definable function `h : A → VF^k × RV_Γ^j` for some `j` such that `h ↾ f^{-1}(t̄)` is injective
  for every `t̄ ∈ ran(f)`"*, with `max{dim_VF(f⁻¹(t̄))} ≤ k` as its premise.

That the second is not a disguised restatement of the conclusion is checked by
`paperFibreUniform_zero`: for an `RV^0`-valued `f` the compactness step is a *theorem* (take
`h = id`), so there `dim:VF:pullback` follows with `PairWall` alone (`dim_VF_pullback_zero`).

Two further honest notes:

* `HasRVdim` is *not* monotone in its bound (the paper's `RV^k` is exact: `RV^k → RV^{k'}` padding
  is not a term-level construction here), unlike `HasDim`, whose `k' ≤ k` is part of the
  definition.  The monotone statement is carried by `dimRV` itself through `dimRV_le_iff`.
* `Tup M 0 l` is not automatically inhabited: `sortEval .rv (iRVZero)` needs the axioms of
  `ACVF`, and this file is stated for an arbitrary `LRV.Structure M`, as `Sec4Dim` is.  This is
  why `exists_fibFun_dimVF_eq` carries `A.Nonempty` (which produces a point of `RV^l`).
-/
public import Sec4Dim

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec4Fibre

open Sec4Dim

variable {M : Type*} [LRV.Structure M]
variable {S : SP M}

/-! ## Part 1. The `VF`/`RV` splitting of a tuple, and the paper's `fib(A, ā)` -/

/-- The `VF`-part of a tuple of `VF^n × RV^m`: the paper's projection `pr_{≤n}`. -/
def vfPart {n m : ℕ} (x : Tup M n m) : Tup M n 0 :=
  ⟨fun i => Sum.elim (fun a => x (Sum.inl a)) (fun b => b.elim0) i, by
    rintro (a | b)
    · exact x.2 (Sum.inl a)
    · exact b.elim0⟩

/-- The `RV`-part of a tuple of `VF^n × RV^m`: the paper's projection `pr_{>n}`. -/
def rvPart {n m : ℕ} (x : Tup M n m) : Tup M 0 m :=
  ⟨fun i => Sum.elim (fun a => a.elim0) (fun b => x (Sum.inr b)) i, by
    rintro (a | b)
    · exact a.elim0
    · exact x.2 (Sum.inr b)⟩

/-- The inverse of the splitting: `(ā, t̄) ↦ (ā, t̄)`. -/
def joinTup {n m : ℕ} (a : Tup M n 0) (t : Tup M 0 m) : Tup M n m :=
  ⟨fun i => Sum.elim (fun p => a (Sum.inl p)) (fun q => t (Sum.inr q)) i, by
    rintro (p | q)
    · exact a.2 (Sum.inl p)
    · exact t.2 (Sum.inr q)⟩

@[simp] theorem vfPart_apply {n m : ℕ} (x : Tup M n m) (p : Fin n) :
    vfPart x (Sum.inl p) = x (Sum.inl p) := rfl

@[simp] theorem rvPart_apply {n m : ℕ} (x : Tup M n m) (q : Fin m) :
    rvPart x (Sum.inr q) = x (Sum.inr q) := rfl

@[simp] theorem joinTup_inl {n m : ℕ} (a : Tup M n 0) (t : Tup M 0 m) (p : Fin n) :
    joinTup a t (Sum.inl p) = a (Sum.inl p) := rfl

@[simp] theorem joinTup_inr {n m : ℕ} (a : Tup M n 0) (t : Tup M 0 m) (q : Fin m) :
    joinTup a t (Sum.inr q) = t (Sum.inr q) := rfl

theorem vfPart_joinTup {n m : ℕ} (a : Tup M n 0) (t : Tup M 0 m) :
    vfPart (joinTup a t) = a := by
  refine Subtype.ext (funext fun i => ?_)
  rcases i with p | q
  · rfl
  · exact q.elim0

theorem rvPart_joinTup {n m : ℕ} (a : Tup M n 0) (t : Tup M 0 m) :
    rvPart (joinTup a t) = t := by
  refine Subtype.ext (funext fun i => ?_)
  rcases i with p | q
  · exact p.elim0
  · rfl

/-- Every tuple is the join of its two parts. -/
theorem joinTup_vfPart_rvPart {n m : ℕ} (x : Tup M n m) :
    joinTup (vfPart x) (rvPart x) = x := by
  refine Subtype.ext (funext fun i => ?_)
  rcases i with p | q <;> rfl

theorem joinTup_inj {n m : ℕ} {a a' : Tup M n 0} {t t' : Tup M 0 m}
    (h : joinTup a t = joinTup a' t') : a = a' ∧ t = t' := by
  constructor
  · rw [← vfPart_joinTup a t, ← vfPart_joinTup a' t', h]
  · rw [← rvPart_joinTup a t, ← rvPart_joinTup a' t', h]

/-- The paper's `fib(A, ā)`: the fibre of `A ⊆ VF^n × RV^m` over a `VF`-tuple `ā`.  It is a subset
of `RV^m`, exactly as in the paper (`fib(A, ā) = {t̄ : (ā, t̄) ∈ A}`). -/
def fibRV {n m : ℕ} (A : Set (Tup M n m)) (a : Tup M n 0) : Set (Tup M 0 m) :=
  {t | joinTup a t ∈ A}

theorem mem_fibRV {n m : ℕ} {A : Set (Tup M n m)} {a : Tup M n 0} {t : Tup M 0 m} :
    t ∈ fibRV A a ↔ joinTup a t ∈ A := Iff.rfl

theorem fibRV_subset_iff {n m : ℕ} {A B : Set (Tup M n m)} (hAB : A ⊆ B)
    (a : Tup M n 0) : fibRV A a ⊆ fibRV B a := fun _ ht => hAB ht

/-- The paper's `prv(A)`: the `VF`-coordinates that occur in `A`. -/
def pvf {n m : ℕ} (A : Set (Tup M n m)) : Set (Tup M n 0) :=
  {a | (fibRV A a).Nonempty}

theorem mem_pvf {n m : ℕ} {A : Set (Tup M n m)} {a : Tup M n 0} :
    a ∈ pvf A ↔ ∃ t : Tup M 0 m, joinTup a t ∈ A := Iff.rfl

theorem pvf_mono {n m : ℕ} {A B : Set (Tup M n m)} (hAB : A ⊆ B) : pvf A ⊆ pvf B := by
  rintro a ⟨t, ht⟩
  exact ⟨t, hAB ht⟩

/-- The paper's `f⁻¹(t̄)` for a function `f` on `A`: the fibre of `f` over `t̄`, as a subset of the
same `VF^n × RV^m` that `A` lives in.  (This is the shape in which `dim:VF:pullback` evaluates
`dim_VF(f⁻¹(t̄))`.) -/
def fibFun {n m l : ℕ} (A : Set (Tup M n m)) (f : Tup M n m → Tup M 0 l)
    (t : Tup M 0 l) : Set (Tup M n m) :=
  {x | x ∈ A ∧ f x = t}

theorem fibFun_subset {n m l : ℕ} (A : Set (Tup M n m)) (f : Tup M n m → Tup M 0 l)
    (t : Tup M 0 l) : fibFun A f t ⊆ A := fun _ hx => hx.1

theorem mem_fibFun {n m l : ℕ} {A : Set (Tup M n m)} {f : Tup M n m → Tup M 0 l}
    {t : Tup M 0 l} {x : Tup M n m} : x ∈ fibFun A f t ↔ x ∈ A ∧ f x = t := Iff.rfl

/-- The paper's `prv(A)` is empty exactly when `A` is: every point of `A` splits into its `VF`-part
and its `RV`-part, and that `VF`-part lies in `prv(A)`. -/
theorem pvf_nonempty_iff {n m : ℕ} {A : Set (Tup M n m)} :
    (pvf A).Nonempty ↔ A.Nonempty := by
  constructor
  · rintro ⟨a, t, ht⟩
    exact ⟨joinTup a t, ht⟩
  · rintro ⟨x, hx⟩
    refine ⟨vfPart x, rvPart x, ?_⟩
    rw [mem_fibRV, joinTup_vfPart_rvPart]
    exact hx

/-- A point outside `prv(A)` has empty fibre. -/
theorem fibRV_eq_empty_of_notMem {n m : ℕ} {A : Set (Tup M n m)} {a : Tup M n 0}
    (ha : a ∉ pvf A) : fibRV A a = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun t ht => ha ⟨t, ht⟩

/-- `RV^0` is the singleton `{∞}` of the paper (Definition 4.16: *"`RV^0` is taken to be the
singleton `{∞}`"*).  The tuple type `Tup M 0 0` has no coordinates at all, hence is a subsingleton;
the next definition exhibits its element. -/
def tupZeroZero : Tup M 0 0 :=
  ⟨fun i => i.elim (fun a => a.elim0) (fun b => b.elim0),
   fun i => i.elim (fun a => a.elim0) (fun b => b.elim0)⟩

instance : Subsingleton (Tup M 0 0) :=
  ⟨fun x y => Subtype.ext (by
    funext i
    rcases i with a | b
    · exact a.elim0
    · exact b.elim0)⟩

/-- The graph of the constant function into `RV^0` is definable by `⊤`. -/
theorem definableFun_const_zero_zero {n m : ℕ} (A : Set (Tup M n m)) :
    DefinableFun S A (fun _ : Tup M n m => tupZeroZero) := by
  refine ⟨⊤, wellSorted_top S.sortMap (Fin.append (fSort n m) (fSort 0 0)), ?_⟩
  intro x _ y
  exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by simp⟩

theorem fibreFinite_const_zero_zero {n m : ℕ} {A : Set (Tup M n m)} (hA : A.Finite) :
    FibreFinite A (fun _ : Tup M n m => tupZeroZero) := by
  intro y
  refine hA.subset ?_
  rintro x hx
  exact hx.1

/-! ## Part 2. The `RV`-dimension: monotonicity, and `dim_RV(B) = 0 ⟺ B` finite

The paper defines the `RV`-dimension right after `VF:dim:tran:deg`: *"Let `B ⊆ RV^m` be a definable
subset.  The `RV`-dimension of `B`, denoted by `dim_RV(B)`, is the smallest number `k` such that
there is a definable finite-to-one function `f : B → RV^k` (`RV^0` is taken to be the singleton
`{∞}`)."* -/

/-- **`dim_RV` is monotone under inclusion**: a finite-to-one defining function for `B'` restricts
to one for `B ⊆ B'`. -/
theorem dimRV_mono {m : ℕ} {B B' : Set (Tup M 0 m)} (hBB' : B ⊆ B') :
    dimRV S B ≤ dimRV S B' := by
  obtain ⟨k', hk', f, hf, hfin⟩ := (dimRV_le_iff S B' (dimRV S B')).1 le_rfl
  exact (dimRV_le_iff S B (dimRV S B')).2 ⟨k', hk', f, hf.mono hBB', hfin.mono hBB'⟩

/-- A definable *injection* of `B` into `RV^k` bounds the `RV`-dimension by `k`. -/
theorem dimRV_le_of_injOn {m k : ℕ} {B : Set (Tup M 0 m)} {f : Tup M 0 m → Tup M 0 k}
    (hf : DefinableFun S B f) (hinj : InjOn B f) : dimRV S B ≤ k :=
  (dimRV_le_iff (S := S) B k).2 ⟨k, le_rfl, f, hf, fibreFinite_of_injOn hinj⟩

/-! **A difference between the two dimensions, worth recording**: `HasDim` is monotone in its bound
because `VF^{k'} → VF^k` (`k' ≤ k`) is definable padding, but `HasRVdim` is *not* — the paper's
`RV^k` is exact, so a finite-to-one map into `RV^k` cannot be padded to one into `RV^{k'}` without a
term-level construction.  The monotone statement is therefore carried by `dimRV` itself, through
`dimRV_le_iff` (`dimRV B ≤ k ↔ ∃ k' ≤ k, HasRVdim S B k'`). -/

/-- Every finite set has `RV`-dimension `0`: its `RV^0`-valued constant map is definable (`⊤`) and
finite-to-one.  (`RV^0 = {∞}` is a singleton, so this is the paper's `RV[0]` being the category of
finite sets.) -/
theorem hasRVdim_zero_of_finite {m : ℕ} {B : Set (Tup M 0 m)} (hB : B.Finite) :
    HasRVdim S B 0 :=
  ⟨fun _ => tupZeroZero, definableFun_const_zero_zero (S := S) B,
    fibreFinite_const_zero_zero hB⟩

/-- Conversely a set of `RV`-dimension `0` is finite: `RV^0` has one point, so a finite-to-one map
into it has a finite domain. -/
theorem finite_of_hasRVdim_zero {m : ℕ} {B : Set (Tup M 0 m)} (h : HasRVdim S B 0) :
    B.Finite := by
  obtain ⟨f, -, hfin⟩ := h
  refine (hfin tupZeroZero).subset ?_
  intro x hx
  exact ⟨hx, Subsingleton.elim _ _⟩

/-- **The paper's `RV[0]` is the category of finite sets**: `dim_RV(B) = 0` if and only if `B` is
finite.  (Definition 4.15 identifies `VF[k]` as the subcategory of finite `RV`-fibres; this is the
`RV`-side statement it rests on.) -/
theorem dimRV_eq_zero_iff_finite (S := S) {m : ℕ} {B : Set (Tup M 0 m)} :
    dimRV S B = 0 ↔ B.Finite := by
  constructor
  · intro h
    have h0 : dimRV S B ≤ 0 := h ▸ le_rfl
    obtain ⟨k', hk', hB⟩ := (dimRV_le_iff S B 0).1 h0
    rw [Nat.eq_zero_of_le_zero hk'] at hB
    exact finite_of_hasRVdim_zero hB
  · intro hB
    exact Nat.le_antisymm ((dimRV_le_iff S B 0).2 ⟨0, le_rfl, hasRVdim_zero_of_finite hB⟩)
      (Nat.zero_le _)

/-- A set of `RV`-tuples has `VF`-dimension at most its `RV`-dimension: a finite-to-one map into
`RV^k = VF^0 × RV^k` is in particular one into `VF^{0} × RV^k`, i.e. witnesses `dim_VF ≤ k`. -/
theorem dimVF_le_dimRV {m : ℕ} {B : Set (Tup M 0 m)} : dimVF S B ≤ dimRV S B := by
  obtain ⟨k', hk', f, hf, hfin⟩ := (dimRV_le_iff S B (dimRV S B)).1 le_rfl
  exact (dimVF_le_iff S B (dimRV S B)).2 ⟨0, Nat.zero_le _, k', f, hf, hfin⟩

/-- Every finite set has `VF`-dimension `0`. -/
theorem dimVF_eq_zero_of_finite {n m : ℕ} {A : Set (Tup M n m)} (hA : A.Finite) :
    dimVF S A = 0 := by
  have h : HasDim S A 0 :=
    ⟨0, le_rfl, 0, fun _ => tupZeroZero, definableFun_const_zero_zero (S := S) A,
      fibreFinite_const_zero_zero hA⟩
  exact Nat.le_antisymm ((dimVF_le_iff S A 0).2 h) (Nat.zero_le _)

theorem dimRV_eq_zero_of_finite {m : ℕ} {B : Set (Tup M 0 m)} (hB : B.Finite) :
    dimRV S B = 0 :=
  dimRV_eq_zero_iff_finite (S := S).2 hB

/-! ## Part 3. The paper's `RV`-fibre dimension `dim^fib_RV(A)`

*"The `RV`-fibre dimension of `A`, denoted by `dim^fib_RV(A)`, is
`max {dim_RV(fib(A, ā)) : ā ∈ prv(A)}`"* (`paper.tex`, before Lemma `RV:fiber:dim:same`).

The maximum is written as the least `k` bounding every fibre, which is the form the paper's proofs
use and which avoids choosing an element of `prv(A)`; `dimFibRV_le_iff` says the two agree. -/

/-- **`dim^fib_RV(A)`**, the paper's `RV`-fibre dimension. -/
noncomputable def dimFibRV (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) : ℕ :=
  sInf {k : ℕ | ∀ a ∈ pvf A, dimRV S (fibRV A a) ≤ k}

theorem dimFibRV_set_nonempty {n m : ℕ} (A : Set (Tup M n m)) :
    {k : ℕ | ∀ a ∈ pvf A, dimRV S (fibRV A a) ≤ k}.Nonempty :=
  ⟨_, fun _ _ => dimRV_le_self S _⟩

/-- `dim^fib_RV(A) ≤ k` iff every `RV`-fibre of `A` has `RV`-dimension at most `k`; i.e.
`dimFibRV` really is the maximum of the fibre dimensions. -/
theorem dimFibRV_le_iff {n m : ℕ} (A : Set (Tup M n m)) (k : ℕ) :
    dimFibRV S A ≤ k ↔ ∀ a ∈ pvf A, dimRV S (fibRV A a) ≤ k := by
  have hne := dimFibRV_set_nonempty (S := S) A
  constructor
  · intro h a ha
    exact (Nat.sInf_mem hne a ha).trans h
  · intro h
    exact Nat.sInf_le h

/-- Each `RV`-fibre has `RV`-dimension at most the `RV`-fibre dimension of the set. -/
theorem dimRV_fibRV_le {n m : ℕ} {A : Set (Tup M n m)} {a : Tup M n 0} (ha : a ∈ pvf A) :
    dimRV S (fibRV A a) ≤ dimFibRV S A :=
  (dimFibRV_le_iff (S := S) A (dimFibRV S A)).1 le_rfl a ha

/-- The empty set has `RV`-fibre dimension `0` (there are no fibres). -/
theorem dimFibRV_empty {n m : ℕ} : dimFibRV S (∅ : Set (Tup M n m)) = 0 := by
  refine Nat.le_antisymm ((dimFibRV_le_iff (S := S) _ 0).2 ?_) (Nat.zero_le _)
  intro a ha
  obtain ⟨t, ht⟩ := ha
  exact absurd ht (Set.notMem_empty t)

/-- A fibre over a point outside `prv(A)` has `RV`-dimension `0`. -/
theorem dimRV_fibRV_eq_zero_of_notMem {n m : ℕ} {A : Set (Tup M n m)} {a : Tup M n 0}
    (ha : a ∉ pvf A) : dimRV S (fibRV A a) = 0 := by
  rw [fibRV_eq_empty_of_notMem ha]
  exact dimRV_eq_zero_of_finite Set.finite_empty

/-- **`dim^fib_RV(A) ≤ m`** for `A ⊆ VF^n × RV^m`: every `RV`-fibre lives in `RV^m`. -/
theorem dimFibRV_le_self {n m : ℕ} (A : Set (Tup M n m)) : dimFibRV S A ≤ m :=
  (dimFibRV_le_iff (S := S) A m).2 fun _ _ => dimRV_le_self S _

/-- **`dim^fib_RV` is monotone under inclusion.** -/
theorem dimFibRV_mono {n m : ℕ} {A A' : Set (Tup M n m)} (hAA' : A ⊆ A') :
    dimFibRV S A ≤ dimFibRV S A' := by
  refine (dimFibRV_le_iff (S := S) A (dimFibRV S A')).2 fun a ha => ?_
  obtain ⟨t, ht⟩ := ha
  exact (dimRV_mono (fibRV_subset_iff hAA' a)).trans (dimRV_fibRV_le ⟨t, hAA' ht⟩)

/-- **`dim^fib_RV(A) = 0` iff every `RV`-fibre of `A` is finite.**  This is the characterization
Definition 4.15 uses verbatim: *"The category `VF[k]` is the full subcategory of `VF[k, ·]` of the
definable subsets that have `RV`-fiber dimension `0` (that is, all the `RV`-fibers are finite)."* -/
theorem dimFibRV_eq_zero_iff {n m : ℕ} (A : Set (Tup M n m)) :
    dimFibRV S A = 0 ↔ ∀ a ∈ pvf A, (fibRV A a).Finite := by
  have hiff : dimFibRV S A = 0 ↔ dimFibRV S A ≤ 0 :=
    ⟨fun h => h ▸ le_rfl, fun h => Nat.le_antisymm h (Nat.zero_le _)⟩
  rw [hiff, dimFibRV_le_iff]
  exact forall₂_congr fun a _ => Nat.le_zero.trans (dimRV_eq_zero_iff_finite (S := S))

/-- **`dim^fib_RV(A)` is a maximum**: if `A` has a point then some `RV`-fibre attains
`dim^fib_RV(A)`.  The paper writes `max {dim_RV(fib(A, ā)) : ā ∈ prv(A)}`, and this is what makes
the word *max* legitimate (`prv(A)` is an infinite type, so the supremum need not be attained a
priori). -/
theorem exists_fibRV_dimRV_eq {n m : ℕ} {A : Set (Tup M n m)} (hA : (pvf A).Nonempty) :
    ∃ a : Tup M n 0, a ∈ pvf A ∧ dimRV S (fibRV A a) = dimFibRV S A := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ a ∈ pvf A, dimRV S (fibRV A a) ≤ dimFibRV S A - 1 := by
    intro a ha
    have h1 := dimRV_fibRV_le (S := S) ha
    have h2 := hcon a ha
    omega
  rcases eq_or_ne (dimFibRV S A) 0 with h0 | h0
  · obtain ⟨a, ha⟩ := hA
    have h1 : dimRV S (fibRV A a) ≤ 0 := by rw [← h0]; exact dimRV_fibRV_le (S := S) ha
    refine hcon a ha ?_
    rw [h0]
    exact le_antisymm h1 (Nat.zero_le _)
  · have hle : dimFibRV S A ≤ dimFibRV S A - 1 := (dimFibRV_le_iff (S := S) A _).2 hlt
    omega

/-! ## Part 4. `dim:VF:pullback` (`paper.tex:832`)

The paper:

> **Lemma `dim:VF:pullback`.** Let `f : A → RV_Γ^l` be a definable function. Then
> `dim_VF(A) = max { dim_VF(f^{-1}(t̄)) : t̄ ∈ RV_Γ^l }`.
>
> *Proof.* Let `max{...} = k`. By Lemma `dim:RV:fibers`, for every `t̄ ∈ ran(f)` there is a
> `t̄`-definable injective function `h_t̄ : f^{-1}(t̄) → VF^k × RV_Γ^j` for some `j`. **By
> compactness, there is a definable function `h : A → VF^k × RV_Γ^j` for some `j` such that
> `h ↾ f^{-1}(t̄)` is injective for every `t̄ ∈ ran(f)`.** Then the function on `A` given by
> `(b̄, s̄) ↦ (h(b̄, s̄), f(b̄, s̄))` is injective and hence `dim_VF(A) ≤ k`. The other direction is
> trivial. -/

/-! Two steps of that proof are not available as theorems of the encoding, and they are exactly the
two hypotheses below.  Neither of them is the lemma: the first is a *closure* property of
`DefinableFun` (the shared wall of `QE-PLAN.md`), the second is the compactness step alone. -/

/-- The paper's pairing `(b̄, s̄) ↦ (h(b̄, s̄), f(b̄, s̄))`: the `RV`-part of the pair is `y`'s,
followed by `z`'s. -/
def pairTupVal {k j l : ℕ} (y : Tup M k j) (z : Tup M 0 l) : Idx k (j + l) → M :=
  fun i => Sum.elim (fun a => y (Sum.inl a))
    (fun b => Sum.elim (fun c => y (Sum.inr c)) (fun c => z (Sum.inr c))
      (finSumFinEquiv.symm b)) i

def pairTup {k j l : ℕ} (y : Tup M k j) (z : Tup M 0 l) : Tup M k (j + l) :=
  ⟨pairTupVal y z, by
    rintro (a | b)
    · exact y.2 (Sum.inl a)
    · have hb : ∀ c : Fin j ⊕ Fin l, sortEval SortTag.rv
          (Sum.elim (fun c : Fin j => y (Sum.inr c)) (fun c : Fin l => z (Sum.inr c)) c) := by
        rintro (c | c)
        · exact y.2 (Sum.inr c)
        · exact z.2 (Sum.inr c)
      exact hb (finSumFinEquiv.symm b)⟩

@[simp] theorem pairTup_vf {k j l : ℕ} (y : Tup M k j) (z : Tup M 0 l) (a : Fin k) :
    pairTup y z (Sum.inl a) = y (Sum.inl a) := rfl

@[simp] theorem pairTup_rv_inl {k j l : ℕ} (y : Tup M k j) (z : Tup M 0 l) (c : Fin j) :
    pairTup y z (Sum.inr (finSumFinEquiv (Sum.inl c))) = y (Sum.inr c) := by
  simp only [pairTup, pairTupVal, Sum.elim_inr, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem pairTup_rv_inr {k j l : ℕ} (y : Tup M k j) (z : Tup M 0 l) (c : Fin l) :
    pairTup y z (Sum.inr (finSumFinEquiv (Sum.inr c))) = z (Sum.inr c) := by
  simp only [pairTup, pairTupVal, Sum.elim_inr, Equiv.symm_apply_apply]

/-- The `VF`-part of the target of `pairTup`. -/
def vfSplit {k j l : ℕ} (w : Tup M k (j + l)) : Tup M k j :=
  ⟨fun i => Sum.elim (fun a => w (Sum.inl a))
      (fun b => w (Sum.inr (finSumFinEquiv (Sum.inl b)))) i, by
    rintro (a | b)
    · exact w.2 (Sum.inl a)
    · exact w.2 (Sum.inr (finSumFinEquiv (Sum.inl b)))⟩

/-- The `RV`-part of the target of `pairTup`, which is the part `f` contributes. -/
def rvSplit {k j l : ℕ} (w : Tup M k (j + l)) : Tup M 0 l :=
  ⟨fun i => Sum.elim (fun a => a.elim0)
      (fun c => w (Sum.inr (finSumFinEquiv (Sum.inr c)))) i, by
    rintro (a | c)
    · exact a.elim0
    · exact w.2 (Sum.inr (finSumFinEquiv (Sum.inr c)))⟩

theorem vfSplit_pairTup {k j l : ℕ} (y : Tup M k j) (z : Tup M 0 l) :
    vfSplit (pairTup y z) = y := by
  refine Subtype.ext (funext fun i => ?_)
  rcases i with a | b
  · rfl
  · exact pairTup_rv_inl y z b

theorem rvSplit_pairTup {k j l : ℕ} (y : Tup M k j) (z : Tup M 0 l) :
    rvSplit (pairTup y z) = z := by
  refine Subtype.ext (funext fun i => ?_)
  rcases i with a | c
  · exact a.elim0
  · exact pairTup_rv_inr y z c

theorem vfSplit_eq_of_pairTup_eq {k j l : ℕ} {y : Tup M k j} {z : Tup M 0 l}
    {w : Tup M k (j + l)} (h : pairTup y z = w) : y = vfSplit w := by
  rw [← h, vfSplit_pairTup]

theorem rvSplit_eq_of_pairTup_eq {k j l : ℕ} {y : Tup M k j} {z : Tup M 0 l}
    {w : Tup M k (j + l)} (h : pairTup y z = w) : z = rvSplit w := by
  rw [← h, rvSplit_pairTup]

/-- **The wall, as the paper uses it**: the pairing `x ↦ (g x, h x)` of two definable functions is
definable.  This is the `DefinableFun` composition/pairing lemma that `QE-PLAN.md` records as the
one missing piece of the encoding (it needs the guarded existentials of `Milestone0/Encoding.lean`
together with `QE/ExSortedG.lean`'s `exSortedG_realize`); it is *not* the statement of
`dim:VF:pullback`, and it is used once, at the end of the proof. -/
def PairWall (S : SP M) : Prop :=
  ∀ {n m k j l : ℕ} (A : Set (Tup M n m)) (g : Tup M n m → Tup M k j)
    (h : Tup M n m → Tup M 0 l),
    DefinableFun S A g → DefinableFun S A h →
      DefinableFun S A (fun x => pairTup (g x) (h x))

/-- **The compactness step of the paper's proof**, as a named hypothesis.  The paper's sentence:

> *"By compactness, there is a definable function `h : A → VF^k × RV_Γ^j` for some `j` such that
> `h ↾ f^{-1}(t̄)` is injective for every `t̄ ∈ ran(f)`."*

The premise is the paper's `max{dim_VF(f^{-1}(t̄))} ≤ k`; the conclusion is the *uniform* `h`.  This
is not the conclusion of `dim:VF:pullback` (`dim_VF(A) ≤ k`): the paper obtains that afterwards,
from the pairing `(h, f)`. -/
def PaperFibreUniform (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) {l : ℕ}
    (f : Tup M n m → Tup M 0 l) (k : ℕ) : Prop :=
  (∀ t : Tup M 0 l, dimVF S (fibFun A f t) ≤ k) →
    ∃ j : ℕ, ∃ h : Tup M n m → Tup M k j,
      DefinableFun S A h ∧ ∀ t : Tup M 0 l, FibreFinite (fibFun A f t) h

/-- **"The other direction is trivial"**: each fibre's `VF`-dimension is at most that of `A`,
because the fibre is a subset of `A` and `dim_VF` is monotone (`dimVF_mono`).  This half is
unconditional. -/
theorem dimVF_fibFun_le {n m l : ℕ} (A : Set (Tup M n m)) (f : Tup M n m → Tup M 0 l)
    (t : Tup M 0 l) : dimVF S (fibFun A f t) ≤ dimVF S A :=
  dimVF_mono S (fibFun_subset A f t)

/-- The paired function is finite-to-one on `A` as soon as `h` is finite-to-one on every fibre of
`f`.  This is the step of the paper's proof that its sentence "then the function on `A` given by
`(b̄, s̄) ↦ (h(b̄, s̄), f(b̄, s̄))` is injective" encodes. -/
theorem fibreFinite_pairTup {n m k j l : ℕ} {A : Set (Tup M n m)}
    {g : Tup M n m → Tup M k j} {h : Tup M n m → Tup M 0 l}
    (hg : ∀ t : Tup M 0 l, FibreFinite (fibFun A h t) g) :
    FibreFinite A (fun x => pairTup (g x) (h x)) := by
  intro w
  refine (hg (rvSplit w) (vfSplit w)).subset ?_
  intro x hx
  exact ⟨⟨hx.1, rvSplit_eq_of_pairTup_eq hx.2⟩, vfSplit_eq_of_pairTup_eq hx.2⟩

/-- `dim_VF(A) ≤ k` from a uniform bound `k` on the `VF`-dimensions of the fibres of a definable
`f : A → RV^l` — the substantive half of `dim:VF:pullback`. -/
theorem dimVF_le_of_fibre_bound {n m l : ℕ} {A : Set (Tup M n m)}
    {f : Tup M n m → Tup M 0 l} {k : ℕ}
    (hW : PairWall S) (hf : DefinableFun S A f) (hU : PaperFibreUniform S A f k)
    (hfib : ∀ t : Tup M 0 l, dimVF S (fibFun A f t) ≤ k) :
    dimVF S A ≤ k := by
  obtain ⟨j, h, hhdef, hhfin⟩ := hU hfib
  refine (dimVF_le_iff (S := S) A k).2
    ⟨k, le_rfl, j + l, fun x => pairTup (h x) (f x), hW A h f hhdef hf, ?_⟩
  exact fibreFinite_pairTup hhfin

/-- **Lemma `dim:VF:pullback`** (`paper.tex:832`): *"Let `f : A → RV_Γ^l` be a definable function.
Then `dim_VF(A) = max { dim_VF(f^{-1}(t̄)) : t̄ ∈ RV_Γ^l }"*, written as the equivalent statement
that a natural number bounds `dim_VF(A)` exactly when it bounds every fibre's `VF`-dimension.

The two hypotheses are the paper's two inputs, and neither is the lemma: `PairWall` is the
composition/pairing lemma for `DefinableFun` (the encoding's missing substitution step), and
`PaperFibreUniform` is the compactness sentence quoted above.  Everything else is proved: the
monotone half is `dimVF_fibFun_le`, and the finite-to-one argument is `fibreFinite_pairTup`. -/
theorem dim_VF_pullback {n m l : ℕ} {A : Set (Tup M n m)} {f : Tup M n m → Tup M 0 l} {k : ℕ}
    (hW : PairWall S) (hf : DefinableFun S A f) (hU : PaperFibreUniform S A f k) :
    dimVF S A ≤ k ↔ ∀ t : Tup M 0 l, dimVF S (fibFun A f t) ≤ k :=
  ⟨fun h t => (dimVF_fibFun_le A f t).trans h, fun hfib => dimVF_le_of_fibre_bound hW hf hU hfib⟩

/-- The paper writes a **maximum** over `RV_Γ^l`; that the maximum is attained is not immediate
(the index type `RV^l` is infinite), so it is proved here from `dim:VF:pullback`: if no fibre
attained `dim_VF(A)` then every fibre would be bounded by `dim_VF(A) - 1`, contradicting the
lemma. -/
theorem exists_fibFun_dimVF_eq {n m l : ℕ} {A : Set (Tup M n m)}
    {f : Tup M n m → Tup M 0 l}
    (hW : PairWall S) (hf : DefinableFun S A f) (hU : ∀ k, PaperFibreUniform S A f k)
    (hA : A.Nonempty) :
    ∃ t : Tup M 0 l, dimVF S (fibFun A f t) = dimVF S A := by
  by_contra hcon
  push Not at hcon
  rcases eq_or_ne (dimVF S A) 0 with h0 | h0
  · obtain ⟨x, hx⟩ := hA
    exact hcon (f x) (le_antisymm (dimVF_fibFun_le (S := S) A f (f x))
      (by rw [h0]; exact Nat.zero_le _))
  · have hlt : ∀ t : Tup M 0 l, dimVF S (fibFun A f t) ≤ dimVF S A - 1 := by
      intro t
      have h1 := dimVF_fibFun_le (S := S) A f t
      have h2 := hcon t
      omega
    have hle : dimVF S A ≤ dimVF S A - 1 :=
      (dim_VF_pullback hW hf (hU (dimVF S A - 1))).2 hlt
    omega

/-! ### Non-vacuity: the `RV^0`-valued case

When `l = 0` the target `RV^0` is the singleton `{∞}`, so there is a single fibre and it is all of
`A`.  There the compactness step is a theorem (take `h = id`), so `dim:VF:pullback` holds with
`PairWall` alone.  This also shows that `PaperFibreUniform` is satisfied in a real case and is not
a disguised form of the conclusion. -/

theorem fibFun_zero {n m : ℕ} (A : Set (Tup M n m)) (f : Tup M n m → Tup M 0 0) :
    fibFun A f tupZeroZero = A := by
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, Subsingleton.elim _ _⟩⟩

/-- For an `RV^0`-valued `f` the compactness step is provable: `h = id`. -/
theorem paperFibreUniform_zero {n m : ℕ} (A : Set (Tup M n m))
    (f : Tup M n m → Tup M 0 0) : PaperFibreUniform S A f n := by
  intro _
  refine ⟨m, id, definableFun_id S A, fun t => ?_⟩
  have ht : t = tupZeroZero := Subsingleton.elim _ _
  rw [ht, fibFun_zero]
  exact fibreFinite_of_injOn (fun _ _ _ _ h => h)

/-- `dim:VF:pullback` for an `RV^0`-valued `f`, with no compactness hypothesis. -/
theorem dim_VF_pullback_zero {n m : ℕ} {A : Set (Tup M n m)} {f : Tup M n m → Tup M 0 0}
    (hW : PairWall S) (hf : DefinableFun S A f) :
    dimVF S A ≤ n ↔ ∀ t : Tup M 0 0, dimVF S (fibFun A f t) ≤ n :=
  dim_VF_pullback hW hf (paperFibreUniform_zero A f)

end Sec4Fibre

end SpecialTransformations.Milestone0
