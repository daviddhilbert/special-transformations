module

/-
# Section 6 of Yin, *Special transformations in algebraically closed valued fields*
(arXiv:1006.2467), paper.tex line 1419 ff.: the interlude on henselian fields.

This file formalizes the definition of *functionally closed* and Lemma
`cut:to:hensel:substru` (paper.tex:1427-1429) over the frozen encoding of `L_RV` in
`Milestone0/Encoding.lean`, reusing §4's definability layer (`QE/Sec4Dim.lean`) and the frozen §3
vocabulary of `acl`/`dcl` (`QE/Sec3_frozen.lean`), together with the variable/parameter
substitution of `QE/SubstVar.lean` and `QE/SubstParam.lean`.

## What the paper says

* Definition (paper.tex:1423-1424): *"A substructure `M` is **functionally closed** if, for any
  definable subset `A` and any definable function `f` on `A`, `f(A ∩ M) ⊆ M`."*
  Formalized as `FunctionallyClosed`.

* Lemma `cut:to:hensel:substru` (paper.tex:1427-1429): *"Let `M` be a substructure such that
  `(VF(M), O(M))` is a nontrivially valued henselian field and `rv(VF(M)) = RV(M)`. Then `M` is
  functionally closed."*
  Formalized as `cut_to_hensel_substru`.

## What is proved, and what is carried as a hypothesis

`functionallyClosed_of_dclClosed` (the paper's last sentence, *"So `M = dcl(M)` and the lemma
follows"*) is **proved outright**: from `M = dcl(M)` — every tuple definable over parameters in `M`
having its coordinates in `M` (`DclClosed`) — functional closedness follows.  The proof performs the
substitution the paper leaves implicit: the graph formula of `f` is read at the parameters *`S`
together with the coordinates of `a`* (`extendTup`), which uses `SubstParam.wellSorted_substParam`
and `SubstVar.wellSorted_substVar` to keep the formula well-sorted, and `realize_substVar` to see
that its solution set is the singleton `{f a}`.

`dclClosed_of_steps` is also **proved outright**: it assembles `M = dcl(M)` from the two steps of
the paper's proof.

Those two steps are the file's hypotheses, each with the paper's sentence in its docstring:

* `HenselAclStep` — paper.tex:1431, *"By Corollary `aclS:model`, `acl(M) ⊨ ACVF_S(0,0)`. … Since
  the valued field `(VF(M), O(M))` is henselian, it is the fixed field under the valued field
  automorphisms of `(VF(M)^alg, O(acl(M)))` over `(VF(M), O(M))`. … So `VF(dcl(M)) = VF(M)`."*
  Neither Corollary `aclS:model` nor the hypothesis that `(VF(M), O(M))` is a nontrivially valued
  henselian field is formalized here: the encoding is one-sorted (sorts are predicates, the
  operations are total with junk outside their sorts), so it exposes no valued-field structure on a
  substructure's `VF`-sort, and `acl(M)` as a *model* is not available either (`Sec3_frozen.acl` is
  the set of algebraically closed points, not a structure).  The hypothesis is therefore carried at
  the exact place where the paper's proof consumes it, as the sentence the paper derives there.
* `CentersStep` — paper.tex:1431, *"Since `M` is `VF`-generated, by Lemma
  `algebraic:balls:definable:centers`, every `t ∈ RV(dcl(M))` has an `M`-definable point in `VF`."*
  Lemma `algebraic:balls:definable:centers` itself (paper.tex:738, quoted from Yin
  *QE:ACVF:min* Lemma 4.17) is §2-§4 material and is not formalized in this repository; it is
  carried as the hypothesis.

So this file is the paper's Lemma **modulo** those two quoted results, and the statements are the
paper's (paper-level, not weakened): the missing inputs are named, not assumed silently.  In
particular nothing here is vacuous: `FunctionallyClosed` is a genuine closure property of the
carrier, and `functionallyClosed_of_dclClosed` reconstructs `f a` from the graph formula.

## Encoding notes

* `M` is a substructure of the ambient `L_RV`-structure; `Substructure.carrier` is its carrier, `X`
  in the theorems (the paper's `M`), `rv_closed` is closure of `M` under `rv` (a substructure is
  closed under the function symbols) and `rv_generated` is the paper's `rv(VF(M)) = RV(M)`.
* `TupleDefinable S ss x` is `x̄ ∈ dcl(S)` at a tuple of sort pattern `ss`; it matches
  `Sec3_frozen.dcl` at one `VF`-sorted variable, generalized to tuples because the paper's `dcl(M)`
  and the graph of a definable function both speak about tuples.
* `Tup M n m` (`Sec4Dim`) is the paper's `VF^n × RV^m`; `Definable`/`DefinableFun` are §4's.

Compile: `LEAN_PATH=<repo>/.scratch2/sec3:$LEAN_PATH lean Sec6.lean`; no `sorry`, no `axiom`, no
`native_decide`.
-/
public import SubstVar
public import SubstParam

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Milestone0
open LRV
namespace Sec6
open Sec4Dim
open Sec4Compose
open ParamBridge

noncomputable section

variable {M : Type*} [LRV.Structure M]

/-! ## Sorted tuples: the `fSort` bookkeeping of a block `VF^n × RV^m` -/

theorem fSort_castAdd {n m : ℕ} (i : Fin n) : fSort n m (Fin.castAdd m i) = SortTag.vf := by
  simp [fSort, idxSort, finSumFinEquiv]

theorem fSort_natAdd {n m : ℕ} (j : Fin m) : fSort n m (Fin.natAdd n j) = SortTag.rv := by
  simp [fSort, idxSort, finSumFinEquiv]

/-! ## Extending a parameter pair by a tuple -/

def extendTup (S : SP M) {n m : ℕ} (a : Tup M n m) : SP M where
  n := S.n + n
  m := S.m + m
  vf := Fin.append S.vf (fun i => a (Sum.inl i))
  rv := Fin.append S.rv (fun j => a (Sum.inr j))
  vf_sorted := by
    intro i
    induction i using Fin.addCases with
    | left j => rw [Fin.append_left]; exact S.vf_sorted j
    | right j => rw [Fin.append_right]; exact a.2 (Sum.inl j)
  rv_sorted := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact S.rv_sorted i
    | right i => rw [Fin.append_right]; exact a.2 (Sum.inr i)

@[simp]
theorem extendTup_vf_old {S : SP M} {n m : ℕ} (a : Tup M n m) (i : Fin S.n) :
    (extendTup S a).vf (Fin.castAdd n i) = S.vf i := by simp [extendTup]

@[simp]
theorem extendTup_vf_new {S : SP M} {n m : ℕ} (a : Tup M n m) (i : Fin n) :
    (extendTup S a).vf (Fin.natAdd S.n i) = a (Sum.inl i) := by simp [extendTup]

@[simp]
theorem extendTup_rv_old {S : SP M} {n m : ℕ} (a : Tup M n m) (j : Fin S.m) :
    (extendTup S a).rv (Fin.castAdd m j) = S.rv j := by simp [extendTup]

@[simp]
theorem extendTup_rv_new {S : SP M} {n m : ℕ} (a : Tup M n m) (j : Fin m) :
    (extendTup S a).rv (Fin.natAdd S.m j) = a (Sum.inr j) := by simp [extendTup]

@[simp]
theorem extendTup_toFun_old {S : SP M} {n m : ℕ} (a : Tup M n m)
    (p : Fin S.n ⊕ Fin S.m) :
    (extendTup S a).toFun (Sum.map (Fin.castAdd n) (Fin.castAdd m) p) = S.toFun p := by
  rcases p with i | j
  · show (extendTup S a).vf (Fin.castAdd n i) = S.vf i
    rw [extendTup_vf_old]
  · show (extendTup S a).rv (Fin.castAdd m j) = S.rv j
    rw [extendTup_rv_old]
/-! ## Definable closure of tuples, and closure of a set under it -/

/-- `x̄ ∈ dcl(S)`: the tuple `x̄` (with sort pattern `ss`) is the *unique* solution, among sorted
tuples, of a well-sorted `L_RV`-formula over the parameter pair `S`.

This is the tuple-level reading of the paper's `acl(S)`/`dcl(S)` (`QE/Sec3_frozen.lean` reads the
same notion at one `VF`-sorted variable); it is what the paper's `dcl(M) = M` refers to, since
definable closure of a substructure is closure under tuple-definability. -/
def TupleDefinable (S : SP M) {N : ℕ} (ss : Fin N → SortTag) (x : Fin N → M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) N,
    WellSorted S.sortMap ss φ ∧ (∀ i, sortEval (ss i) (x i)) ∧
      ∀ y : Fin N → M, (∀ i, sortEval (ss i) (y i)) → (φ.Realize S.toFun y ↔ y = x)

/-- The parameters of `S` all lie in `X`. -/
def ParamsIn (S : SP M) (X : Set M) : Prop :=
  (∀ i, S.vf i ∈ X) ∧ (∀ j, S.rv j ∈ X)

/-- **`M = dcl(M)`**: every tuple which is tuple-definable over parameters in `X` has all its
coordinates in `X`.  (The paper's proof of Lemma `cut:to:hensel:substru` establishes exactly this
for the carrier of `M`, and then concludes.) -/
def DclClosed (X : Set M) : Prop :=
  ∀ (S : SP M), ParamsIn S X → ∀ {N : ℕ} (ss : Fin N → SortTag) (x : Fin N → M),
    TupleDefinable S ss x → ∀ i, x i ∈ X

/-! ## Functionally closed sets (paper, §6 definition) -/

/-- **Functionally closed** (paper.tex:1424): *"A substructure `M` is functionally closed if, for any
definable subset `A` and any definable function `f` on `A`, `f(A ∩ M) ⊆ M`."*

`A ⊆ VF^n × RV^m` is `S`-definable and `f : A → VF^k × RV^l` is `S`-definable on `A`, for a
parameter pair `S` with parameters in `X` (definability over a substructure means over parameters in
it); `a ∈ A` is written as the tuple `a` lying in `A` with all coordinates in `X`
(`a ∈ A ∩ M`), and the conclusion is that all coordinates of `f a` lie in `X`
(`f a ∈ M`). -/
def FunctionallyClosed (X : Set M) : Prop :=
  ∀ (S : SP M), ParamsIn S X →
    ∀ {n m k l : ℕ} (A : Set (Tup M n m)) (f : Tup M n m → Tup M k l),
      Definable S A → DefinableFun S A f →
        ∀ a : Tup M n m, a ∈ A → (∀ i, a i ∈ X) → ∀ j, f a j ∈ X

/-! ## The descent datum of the paper's proof

The paper's proof of Lemma `cut:to:hensel:substru` (paper.tex:1431) is

> *By Corollary `aclS:model`, `acl(M) ⊨ ACVF_S(0,0)`.  Note that `VF(acl(M)) = VF(M)^alg`.  Since the
> valued field `(VF(M), O(M))` is henselian, it is the fixed field under the valued field
> automorphisms of `(VF(M)^alg, O(acl(M)))` over `(VF(M), O(M))`.  On the other hand, these valued
> field automorphisms are in one-to-one correspondence with the `L_RV`-automorphisms of `acl(M)`
> over `M`.  So `VF(dcl(M)) = VF(M)`.  Since `M` is `VF`-generated, by Lemma
> `algebraic:balls:definable:centers`, every `t ∈ RV(dcl(M))` has an `M`-definable point in `VF`.
> So `M = dcl(M)` and the lemma follows.*

The two steps are carried below as explicit `Prop`-valued hypotheses, with the paper's sentences:
`HenselAclStep` (the first three sentences, i.e. Corollary `aclS:model` together with the henselian
hypothesis) and `CentersStep` (Lemma `algebraic:balls:definable:centers`).  See the file header for
what is and is not formalized. -/

/-- **`VF(dcl(M)) = VF(M)`** — paper.tex:1431, *"So `VF(dcl(M)) = VF(M)`"*: at the `VF` sort,
definable closure over parameters in `M` adds nothing to `M`.

The paper derives this sentence from Corollary `aclS:model` (`acl(M) ⊨ ACVF_S(0,0)`,
paper.tex:742) together with the hypothesis that `(VF(M), O(M))` is a nontrivially valued henselian
field (a henselian valued field is the fixed field of the valued field automorphisms of its algebraic
closure).  Neither of those two statements is formalized here: the encoding has no valued-field
structure on a substructure's `VF`-sort, so the hypothesis is carried at the point where the paper's
proof *uses* it. -/
def HenselAclStep (X : Set M) : Prop :=
  ∀ (S : SP M), ParamsIn S X → ∀ {N : ℕ} (ss : Fin N → SortTag) (x : Fin N → M),
    TupleDefinable S ss x → ∀ i, ss i = SortTag.vf → x i ∈ X

/-- **Lemma `algebraic:balls:definable:centers`**, in the form paper.tex:1431 uses it:
*"Since `M` is `VF`-generated, by Lemma `algebraic:balls:definable:centers`, every
`t ∈ RV(dcl(M))` has an `M`-definable point in `VF`."*

("`M` is `VF`-generated" is the hypothesis of that lemma — `X` is `(VF, Γ)`-generated when
`rv(VF(M)) = RV(M)`, the `Γ`-part coming from `rv`-fibres — and it is a field of `Substructure`
below.) -/
def CentersStep (X : Set M) : Prop :=
  ∀ (S : SP M), ParamsIn S X → ∀ {N : ℕ} (ss : Fin N → SortTag) (x : Fin N → M),
    TupleDefinable S ss x → ∀ i, ss i = SortTag.rv →
      ∃ a : M, iVF a ∧ iRv a = x i ∧
        TupleDefinable S (N := 1) (fun _ => SortTag.vf) (fun _ => a)

/-! ## `M = dcl(M)` from the two steps -/

/-- The carrier of a substructure is closed under tuple-definability: the `VF`-coordinates by the
paper's `VF(dcl(M)) = VF(M)`, the `RV`-coordinates through their definable `VF`-points (centers) and
the closure of a substructure under `rv`. -/
theorem dclClosed_of_steps {X : Set M} (hVF : HenselAclStep X) (hC : CentersStep X)
    (hrv : ∀ x : M, x ∈ X → iVF x → iRv x ∈ X) : DclClosed X := by
  intro S hS N ss x hx i
  rcases hs : ss i with _ | _
  · exact hVF S hS ss x hx i hs
  · obtain ⟨a, haVF, harv, hadef⟩ := hC S hS ss x hx i hs
    have haX : a ∈ X := hVF S hS (N := 1) (fun _ => SortTag.vf) (fun _ => a) hadef 0 rfl
    rw [← harv]
    exact hrv a haX haVF

/-! ## The paper's last step: `M = dcl(M)` implies functional closedness -/

/-! ## The terms of the substitution used in the closing step -/

/-- The term naming the parameter `p` of `S` inside the extended parameter pair `extendTup S a`
(whose parameter type is `Fin (S.n + n) ⊕ Fin (S.m + m)`). -/
def paramTerm (S : SP M) {n m : ℕ} (p : Fin S.n ⊕ Fin S.m) :
    LRV.Term (Fin (S.n + n) ⊕ Fin (S.m + m)) :=
  Term.var (Sum.map (Fin.castAdd n) (Fin.castAdd m) p)

/-- The term naming the `i`-th `VF`-coordinate of `a` as a parameter of `extendTup S a`. -/
def sigmaVF (S : SP M) {n m k l : ℕ} (i : Fin n) :
    LRV.Term ((Fin (S.n + n) ⊕ Fin (S.m + m)) ⊕ Fin (k + l)) :=
  Term.var (Sum.inl ((Sum.inl (Fin.natAdd S.n i)) : Fin (S.n + n) ⊕ Fin (S.m + m)))

/-- The term naming the `j`-th `RV`-coordinate of `a` as a parameter of `extendTup S a`. -/
def sigmaRV (S : SP M) {n m k l : ℕ} (j : Fin m) :
    LRV.Term ((Fin (S.n + n) ⊕ Fin (S.m + m)) ⊕ Fin (k + l)) :=
  Term.var (Sum.inl ((Sum.inr (Fin.natAdd S.m j)) : Fin (S.n + n) ⊕ Fin (S.m + m)))

/-- The `j`-th free variable of the second block, kept free. -/
def sigmaFree (S : SP M) (n m : ℕ) {k l : ℕ} (j : Fin (k + l)) :
    LRV.Term ((Fin (S.n + n) ⊕ Fin (S.m + m)) ⊕ Fin (k + l)) :=
  Term.var (Sum.inr j)

/-- **The paper's closing sentence** — *"So `M = dcl(M)` and the lemma follows."*

If every tuple definable over parameters in `X` has its coordinates in `X`, then `X` is functionally
closed: for `A` and `f` definable over `S ⊆ X` and `a ∈ A` with coordinates in `X`, the graph
formula of `f` read at the parameters `S` together with the coordinates of `a` has the singleton
solution set `{f a}`, so `f a ∈ dcl(X) = X`. -/
theorem functionallyClosed_of_dclClosed {X : Set M} (hX : DclClosed X) :
    FunctionallyClosed X := by
  intro S hS n m k l A f hA hf a ha haX j
  obtain ⟨φ, hφ, hgraph⟩ := hf
  -- the parameter pair `S` extended by the coordinates of `a`
  -- `φ` promoted to the extended parameter pair (parameters moved, variables untouched)
  let φ₁ : LRV.BoundedFormula (Fin (extendTup S a).n ⊕ Fin (extendTup S a).m) ((n + m) + (k + l)) :=
    φ.subst (fun p => paramTerm S p)
  have hsub : ∀ p : Fin S.n ⊕ Fin S.m,
      TmSort (extendTup S a).sortMap (Fin.append (fSort n m) (fSort k l))
        ((paramTerm S p).relabel
          (Sum.inl : (Fin (S.n + n) ⊕ Fin (S.m + m)) →
            (Fin (S.n + n) ⊕ Fin (S.m + m)) ⊕ Fin ((n + m) + (k + l))))
        = some (S.sortMap p) := by
    intro p
    rcases p with i | j
    · show TmSort (extendTup S a).sortMap _ (Term.var (Sum.inl (Sum.inl (Fin.castAdd n i) :
        Fin (S.n + n) ⊕ Fin (S.m + m)))) = some SortTag.vf
      rfl
    · show TmSort (extendTup S a).sortMap _ (Term.var (Sum.inl (Sum.inr (Fin.castAdd m j) :
        Fin (S.n + n) ⊕ Fin (S.m + m)))) = some SortTag.rv
      rfl
  have hφ₁ws : WellSorted (extendTup S a).sortMap (Fin.append (fSort n m) (fSort k l)) φ₁ :=
    wellSorted_substParam S.sortMap (extendTup S a).sortMap ((n + m) + (k + l))
      (Fin.append (fSort n m) (fSort k l)) (fun p => paramTerm S p) hsub φ hφ
  have hφ₁real : ∀ y : Tup M k l, φ₁.Realize (extendTup S a).toFun (pairAssign a y) ↔ f a = y := by
    intro y
    show (φ.subst (fun p => paramTerm S p)).Realize (extendTup S a).toFun (pairAssign a y) ↔ f a = y
    rw [BoundedFormula.realize_subst]
    have hcomp : (fun p : Fin S.n ⊕ Fin S.m => (paramTerm S p).realize (extendTup S a).toFun) = S.toFun := by
      funext p
      exact extendTup_toFun_old a p
    rw [hcomp]
    exact hgraph a ha y
  -- the substitution of the coordinates of `a` for the first block, second block left free
  let σ : Fin ((n + m) + (k + l)) → LRV.Term ((Fin (extendTup S a).n ⊕ Fin (extendTup S a).m) ⊕ Fin (k + l)) :=
    Fin.append
      (Fin.append (fun i : Fin n => sigmaVF S i) (fun j : Fin m => sigmaRV S j))
      (fun j : Fin (k + l) => sigmaFree S n m j)
  have hσ_vf : ∀ i : Fin n, σ (Fin.castAdd (k + l) (Fin.castAdd m i)) = sigmaVF S i := by
    intro i; simp [σ]
  have hσ_rv : ∀ j : Fin m, σ (Fin.castAdd (k + l) (Fin.natAdd n j)) = sigmaRV S j := by
    intro j; simp [σ]
  have hσ_free : ∀ j : Fin (k + l), σ (Fin.natAdd (n + m) j) = sigmaFree S n m j := by
    intro j; simp [σ]
  have hσsort : ∀ i : Fin ((n + m) + (k + l)),
      TmSort (extendTup S a).sortMap (fSort k l) (σ i) = some ((Fin.append (fSort n m) (fSort k l)) i) := by
    intro i
    induction i using Fin.addCases with
    | left i₁ =>
      induction i₁ using Fin.addCases with
      | left i₂ =>
        rw [hσ_vf i₂]
        show some ((extendTup S a).sortMap (@Sum.inl (Fin (extendTup S a).n) (Fin (extendTup S a).m) (Fin.natAdd S.n i₂)))
          = some (Fin.append (fSort n m) (fSort k l) (Fin.castAdd (k + l) (Fin.castAdd m i₂)))
        rw [Fin.append_left, fSort_castAdd]
        rfl
      | right j₂ =>
        rw [hσ_rv j₂]
        show some ((extendTup S a).sortMap (@Sum.inr (Fin (extendTup S a).n) (Fin (extendTup S a).m) (Fin.natAdd S.m j₂)))
          = some (Fin.append (fSort n m) (fSort k l) (Fin.castAdd (k + l) (Fin.natAdd n j₂)))
        rw [Fin.append_left, fSort_natAdd]
        rfl
    | right jj =>
      rw [hσ_free jj]
      show some (fSort k l jj) = some (Fin.append (fSort n m) (fSort k l) (Fin.natAdd (n + m) jj))
      rw [Fin.append_right]
  -- the tuple of values of `f` at `a`, in the flattened index shape of `TupleDefinable`
  have htarget : TupleDefinable (extendTup S a) (fSort k l)
      (fun j : Fin (k + l) => (f a) (finSumFinEquiv.symm j)) := by
    refine ⟨BoundedFormula.substVar σ φ₁, wellSorted_substVar (extendTup S a).sortMap hφ₁ws hσsort, ?_, ?_⟩
    · intro j
      exact (f a).2 (finSumFinEquiv.symm j)
    · intro y hy
      rw [realize_substVar]
      have hfs : ∀ t : Idx k l, fSort k l (finSumFinEquiv t) = idxSort k l t := by
        intro t; rw [fSort, Equiv.symm_apply_apply]
      have hyT : ∀ t : Idx k l, sortEval (idxSort k l t) (y (finSumFinEquiv t)) := by
        intro t
        rw [← hfs t]
        exact hy (finSumFinEquiv t)
      have hval : (fun i : Fin ((n + m) + (k + l)) => Term.realize (Sum.elim (extendTup S a).toFun y) (σ i))
          = pairAssign a ⟨fun t : Idx k l => y (finSumFinEquiv t), hyT⟩ := by
        funext i
        induction i using Fin.addCases with
        | left i₁ =>
          induction i₁ using Fin.addCases with
          | left i₂ =>
            rw [hσ_vf i₂]
            show (Sum.elim (extendTup S a).toFun y) (Sum.inl (Sum.inl (Fin.natAdd S.n i₂)))
              = pairAssign a ⟨fun t : Idx k l => y (finSumFinEquiv t), hyT⟩
                (Fin.castAdd (k + l) (Fin.castAdd m i₂))
            rw [pairAssign_left, finSumFinEquiv_symm_apply_castAdd]
            exact extendTup_vf_new a i₂
          | right j₂ =>
            rw [hσ_rv j₂]
            show (Sum.elim (extendTup S a).toFun y) (Sum.inl (Sum.inr (Fin.natAdd S.m j₂)))
              = pairAssign a ⟨fun t : Idx k l => y (finSumFinEquiv t), hyT⟩
                (Fin.castAdd (k + l) (Fin.natAdd n j₂))
            rw [pairAssign_left, finSumFinEquiv_symm_apply_natAdd]
            exact extendTup_rv_new a j₂
        | right jj =>
          rw [hσ_free jj]
          show (Sum.elim (extendTup S a).toFun y) (Sum.inr jj)
            = pairAssign a ⟨fun t : Idx k l => y (finSumFinEquiv t), hyT⟩
              (Fin.natAdd (n + m) jj)
          rw [pairAssign_right]
          show y jj = y (finSumFinEquiv (finSumFinEquiv.symm jj))
          rw [Equiv.apply_symm_apply]
      rw [hval, hφ₁real]
      constructor
      · intro h
        funext j
        have h2 := congrArg (fun z : Tup M k l => z (finSumFinEquiv.symm j)) h
        simpa using h2.symm
      · intro h
        refine Subtype.ext (funext fun t => ?_)
        have h2 := congrFun h (finSumFinEquiv t)
        simpa using h2.symm
  -- the parameters of `(extendTup S a)` lie in `X`
  have hSext : ParamsIn (extendTup S a) X := by
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.addCases with
      | left i' => rw [extendTup_vf_old a i']; exact hS.1 i'
      | right i' => rw [extendTup_vf_new a i']; exact haX _
    · intro i
      induction i using Fin.addCases with
      | left j' => rw [extendTup_rv_old a j']; exact hS.2 j'
      | right j' => rw [extendTup_rv_new a j']; exact haX _
  have hfin := hX (extendTup S a) hSext (fSort k l)
    (fun j : Fin (k + l) => (f a) (finSumFinEquiv.symm j)) htarget (finSumFinEquiv j)
  simpa using hfin

/-! ## The paper's substructure and Lemma `cut:to:hensel:substru` -/

/-- The paper's `M`: a substructure of the ambient model, described by its carrier.

* `rv_closed` — `M` is closed under `rv`, i.e. under a function symbol of the language (a
  substructure is closed under the function symbols).
* `rv_generated` — the paper's hypothesis `rv(VF(M)) = RV(M)`: every `RV`-element of `M` is `rv` of
  a `VF`-element of `M`.  (The reverse inclusion is automatic in a model of `ACVF`, where `rv` maps
  `VF` into `RV`; the content of the paper's hypothesis is the surjectivity onto `RV(M)`, which is
  what makes `M` `(VF, Γ)`-generated and hence what lets Lemma `algebraic:balls:definable:centers`
  apply — see `CentersStep`.) -/
structure Substructure (M : Type*) [LRV.Structure M] where
  carrier : Set M
  rv_closed : ∀ x, x ∈ carrier → iVF x → iRv x ∈ carrier
  rv_generated : ∀ t, t ∈ carrier → iRV t → ∃ a, a ∈ carrier ∧ iVF a ∧ iRv a = t

/-- **Lemma `cut:to:hensel:substru`** (paper.tex:1427-1429):

> *"Let `M` be a substructure such that `(VF(M), O(M))` is a nontrivially valued henselian field and
> `rv(VF(M)) = RV(M)`.  Then `M` is functionally closed."*

The two hypotheses of the paper enter as follows (see the file header): `(VF(M), O(M))` nontrivially
valued henselian together with Corollary `aclS:model` is `hHensel : HenselAclStep` (its only use in
the proof is the paper's sentence *"So `VF(dcl(M)) = VF(M)`"*), and `rv(VF(M)) = RV(M)` is the field
`Substructure.rv_generated`, under which Lemma `algebraic:balls:definable:centers` applies — stated
as `hCenters : CentersStep`. -/
theorem cut_to_hensel_substru (X : Substructure M)
    (hHensel : HenselAclStep X.carrier) (hCenters : CentersStep X.carrier) :
    FunctionallyClosed X.carrier :=
  functionallyClosed_of_dclClosed (dclClosed_of_steps hHensel hCenters X.rv_closed)

end
end Sec6
end SpecialTransformations.Milestone0
