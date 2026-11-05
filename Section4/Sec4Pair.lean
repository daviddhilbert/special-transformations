/-
**§4 `dim:RV:fibers` proved, with Yin 4.10 + compactness as the only mathematical hypothesis** —
from swarm `smw1jgnht` m6, verified here (compiled: exit 0, 0 errors, no `sorry`; `#print axioms` on
`paperStraightening_of_fibreSeparating`, `dim_RV_fibers_of_fibreSeparating`, `pairForm_realize`,
`wellSorted_pairForm`: all within {propext, Classical.choice, Quot.sound}).

The paper's Lemma (`paper.tex:815`): *`dim_VF A ≤ k` if and only if there is a definable injection
`A → VF^k × RV_Γ^l`* for some `l`.  Here:
`dim_RV_fibers_of_fibreSeparating : dimVF S A ≤ k ↔ ∃ l, ∃ f, DefinableFun S A f ∧ InjOn A f`
(into `VF^k × RV^l`), and `paperStraightening_of_fibreSeparating` gives the uniform form
(`PaperStraightening` of `QE/Sec4Dim.lean`) that the dimension layer consumes — so the hypothesis
`PaperStraightening` there is now dischargeable.

**The method is worth reading before reproving anything like it.**  Instead of composing two definable
functions and eliminating an intermediate tuple (which needs guarded existentials and a composition
lemma — the wall three other directions hit), `pairFun` puts `g`'s `VF` coordinates in the first `k'`
slots, the constant `0` in the remaining `k − k'`, then `g`'s `RV` coordinates, then `h`'s.  Both
values are then *coordinates of the target tuple*, so the graph is one formula

```
pairForm  =  substVar σG φg  ⊓  substVar σH φh  ⊓  padForm
```

with **nothing quantified** and no composition.  Sortedness from `wellSorted_substVar` (cf.
`QE/SubstVar.lean`) with `fSort_castAdd`/`fSort_natAdd`; realisation from `realize_substVar` and
`pairFun_eq_iff`; injectivity because `decG`/`decH` read the pair back and `FibreSeparating` gives
`x = y`.

**Hypotheses, neither silent**: `FibreSeparating` is Yin 4.10 together with the compactness sentence
(a definable `h : A → RV^j` separating `A` modulo `g`'s fibres, uniform in `g`) — §3 material, not the
conclusion; and `sortEval .vf iVFZero` is the sort of the constant `0`, true in every model of `ACVF`
and *not* derivable in an arbitrary `L_RV`-structure, so carrying it is honest.

Build: `.scratch2/sec3/` holds `Enc`, `Sec3Frozen`, `Sec4Dim` and `SubstVar`; copy this file there
and `LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
/-
Section 4 of Yin, "Special transformations in algebraically closed valued fields": the **graph
calculus** for `Sec4Dim.DefinableFun`.

`Sec4Dim.DefinableFun S A f` says that the graph of `f` on `A` is cut out by a well-sorted
`L_RV`-formula.  This file shows that this predicate is closed under the operations the paper's
proof of `dim:RV:fibers` performs on definable functions, and draws the consequence:

* `fSort_castAdd`, `fSort_natAdd`, `fSort_zero` — the sort pattern `fSort k l` of `VF^k × RV^l` on
  its two blocks;
* `padFun`, `pairFun` — the zero-padded pairing `x ↦ (g x padded to VF^k, h x)` of a definable
  `g : A → VF^{k'} × RV^l`, `k' ≤ k`, with a definable `h : A → RV^j`;
* `pairForm` — the *single* well-sorted formula whose graph on `A` is that of the padded pairing,
  obtained by relabelling the graphs of `g` and `h` with `Sec4Compose.BoundedFormula.substVar`;
* `pairFun_definable` — its definability;
* `paperStraightening_of_fibreSeparating` — the paper's proof of `dim:RV:fibers` from the fibre
  separation that Yin's Lemma `finite:VF:project:RV` plus compactness provide;
* `dim_RV_fibers_of_fibreSeparating` — Lemma `dim:RV:fibers` with `FibreSeparating` as the only
  mathematical hypothesis.

No composition of definable functions is needed: the intermediate tuple is never quantified, because
both `g`'s and `h`'s values are coordinates of the target tuple (this is why no `exSortedG`
iteration appears).

No `sorry`, no `axiom`, no `native_decide`.
-/
import SubstVar
set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec4Pair

open Sec4Dim Sec4Compose

variable {M : Type*} [LRV.Structure M]

/-! ## The sort pattern of `VF^k × RV^l` on its two blocks -/

theorem idxSort_inl {k l : ℕ} (p : Fin k) : idxSort k l (Sum.inl p) = SortTag.vf := rfl

theorem idxSort_inr {k l : ℕ} (q : Fin l) : idxSort k l (Sum.inr q) = SortTag.rv := rfl

theorem finSumFinEquiv_symm_castAdd {k l : ℕ} (p : Fin k) :
    (finSumFinEquiv (m := k) (n := l)).symm (Fin.castAdd l p) = Sum.inl p := by
  rw [← finSumFinEquiv_apply_left]
  exact Equiv.symm_apply_apply _ _

theorem finSumFinEquiv_symm_natAdd {k l : ℕ} (q : Fin l) :
    (finSumFinEquiv (m := k) (n := l)).symm (Fin.natAdd k q) = Sum.inr q := by
  rw [← finSumFinEquiv_apply_right]
  exact Equiv.symm_apply_apply _ _

/-- The first `k` coordinates of `VF^k × RV^l` are of sort `VF`. -/
theorem fSort_castAdd {k l : ℕ} (p : Fin k) : fSort k l (Fin.castAdd l p) = SortTag.vf := by
  show idxSort k l ((finSumFinEquiv (m := k) (n := l)).symm (Fin.castAdd l p)) = SortTag.vf
  rw [finSumFinEquiv_symm_castAdd]
  rfl

/-- The last `l` coordinates of `VF^k × RV^l` are of sort `RV`. -/
theorem fSort_natAdd {k l : ℕ} (q : Fin l) : fSort k l (Fin.natAdd k q) = SortTag.rv := by
  show idxSort k l ((finSumFinEquiv (m := k) (n := l)).symm (Fin.natAdd k q)) = SortTag.rv
  rw [finSumFinEquiv_symm_natAdd]
  rfl

/-- `RV^l = VF^0 × RV^l` is all of sort `RV`. -/
theorem fSort_zero {l : ℕ} (q : Fin (0 + l)) : fSort 0 l q = SortTag.rv := by
  show idxSort 0 l ((finSumFinEquiv (m := 0) (n := l)).symm q) = SortTag.rv
  rcases h : (finSumFinEquiv (m := 0) (n := l)).symm q with p | r
  · exact p.elim0
  · rfl

theorem sortEval_vf_of_castAdd {k l : ℕ} {x : Idx k l → M}
    (hx : ∀ i, sortEval (idxSort k l i) (x i)) (p : Fin k) :
    sortEval SortTag.vf (x (Sum.inl p)) := hx (Sum.inl p)

theorem sortEval_rv_of_natAdd {k l : ℕ} {x : Idx k l → M}
    (hx : ∀ i, sortEval (idxSort k l i) (x i)) (q : Fin l) :
    sortEval SortTag.rv (x (Sum.inr q)) := hx (Sum.inr q)


/-! ## The zero-padded pairing -/

/-- The `VF`-zero of the encoding, as an element of the carrier. -/
def iVFZero (M : Type*) [LRV.Structure M] : M :=
  Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

theorem realize_vfZero {α : Type} (n : ℕ) (v : α ⊕ Fin n → M) :
    (((Term.func (L := LRV) Fn.vfZero (fun i => i.elim0)) : LRV.Term (α ⊕ Fin n))).realize v =
      iVFZero M := by
  refine (Term.realize_func (L := LRV) (M := M) v (n := 0) Fn.vfZero
    (fun i => i.elim0)).trans ?_
  congr 1
  funext i
  exact i.elim0

/-- **Forgetting the padded `VF`-coordinates**: the projection `VF^k × RV^{l+j} → VF^{k'} × RV^l`
(`k' ≤ k`) onto `g`'s part of a padded pair. -/
def decG {k' k l j : ℕ} (hkk' : k' ≤ k) (y : Tup (M := M) k (l + j)) : Tup (M := M) k' l :=
  ⟨fun i =>
    match i with
    | Sum.inl a => y (Sum.inl (Fin.castLE hkk' a))
    | Sum.inr q => y (Sum.inr (Fin.castLE (Nat.le_add_right l j) q)),
  by
    intro i
    rcases i with a | q
    · exact y.2 (Sum.inl (Fin.castLE hkk' a))
    · exact y.2 (Sum.inr (Fin.castLE (Nat.le_add_right l j) q))⟩

@[simp]
theorem decG_inl {k' k l j : ℕ} (hkk' : k' ≤ k) (y : Tup (M := M) k (l + j)) (a : Fin k') :
    decG hkk' y (Sum.inl a) = y (Sum.inl (Fin.castLE hkk' a)) := rfl

@[simp]
theorem decG_inr {k' k l j : ℕ} (hkk' : k' ≤ k) (y : Tup (M := M) k (l + j)) (q : Fin l) :
    decG hkk' y (Sum.inr q) = y (Sum.inr (Fin.castLE (Nat.le_add_right l j) q)) := rfl

/-- **Forgetting the padded `VF`-coordinates and `g`'s `RV`-coordinates**: the projection
`VF^k × RV^{l+j} → RV^j` onto `h`'s part of a padded pair. -/
def decH {k l j : ℕ} (y : Tup (M := M) k (l + j)) : Tup (M := M) 0 j :=
  ⟨fun i =>
    match i with
    | Sum.inl a => a.elim0
    | Sum.inr r => y (Sum.inr (Fin.natAdd l r)),
  by
    intro i
    rcases i with a | r
    · exact a.elim0
    · exact y.2 (Sum.inr (Fin.natAdd l r))⟩

@[simp]
theorem decH_inr {k l j : ℕ} (y : Tup (M := M) k (l + j)) (r : Fin j) :
    decH y (Sum.inr r) = y (Sum.inr (Fin.natAdd l r)) := rfl

/-- The position, in the target `Fin (k + (l+j))`, of the `p`-th coordinate of `VF^{k'} × RV^l`
(`p` in the `VF`-block or in the `RV`-block). -/
def gBlock {k' k l j : ℕ} (hkk' : k' ≤ k) (p : Fin (k' + l)) : Fin (k + (l + j)) :=
  Fin.append (fun a : Fin k' => Fin.castAdd (l + j) (Fin.castLE hkk' a))
    (fun q : Fin l => Fin.natAdd k (Fin.castLE (Nat.le_add_right l j) q)) p

/-- The position, in the target, of the `p`-th coordinate of `VF^{k'} × RV^l`, in the `VF`-block. -/
theorem gBlock_vf {k' k l j : ℕ} (hkk' : k' ≤ k) (a : Fin k') :
    gBlock (j := j) hkk' (Fin.castAdd l a) = Fin.castAdd (l + j) (Fin.castLE hkk' a) :=
  Fin.append_left _ _ a

/-- The position, in the target, of the `p`-th coordinate of `VF^{k'} × RV^l`, in the `RV`-block. -/
theorem gBlock_rv {k' k l j : ℕ} (hkk' : k' ≤ k) (q : Fin l) :
    gBlock hkk' (Fin.natAdd k' q) = Fin.natAdd k (Fin.castLE (Nat.le_add_right l j) q) :=
  Fin.append_right _ _ q

/-- The position, in the target `Fin (k + (l+j))`, of the `r`-th `RV`-coordinate of `h`. -/
def hBlock {k l j : ℕ} (r : Fin (0 + j)) : Fin (k + (l + j)) :=
  Fin.natAdd k (Fin.natAdd l (Fin.cast (Nat.zero_add j) r))

/-- The substitution that relabels the graph of `g` (context `(n+m)+(k'+l)`) onto the target
context `(n+m)+(k+(l+j))`: `g`'s `VF`-coordinates onto the first `k'` `VF`-slots of the target,
its `RV`-coordinates onto the first `l` `RV`-slots. -/
def σG {n m k' k l j : ℕ} (hkk' : k' ≤ k) (α : Type) :
    Fin ((n + m) + (k' + l)) → LRV.Term (α ⊕ Fin ((n + m) + (k + (l + j)))) :=
  fun i => Term.var (Sum.inr (Fin.append (fun i' : Fin (n + m) => Fin.castAdd (k + (l + j)) i')
    (fun p : Fin (k' + l) => Fin.natAdd (n + m) (gBlock (j := j) hkk' p)) i))

/-- The substitution that relabels the graph of `h` (context `(n+m)+(0+j)`) onto the target
context `(n+m)+(k+(l+j))`: the same `x`-block, and the `RV`-coordinates of `h` onto the last `j`
`RV`-slots. -/
def σH {n m k l j : ℕ} (α : Type) :
    Fin ((n + m) + (0 + j)) → LRV.Term (α ⊕ Fin ((n + m) + (k + (l + j)))) :=
  fun i => Term.var (Sum.inr (Fin.append (fun i' : Fin (n + m) => Fin.castAdd (k + (l + j)) i')
    (fun r : Fin (0 + j) => Fin.natAdd (n + m) (hBlock (k := k) (l := l) r)) i))

@[simp]
theorem σG_inl {n m k' k l j : ℕ} (hkk' : k' ≤ k) (α : Type) (i' : Fin (n + m)) :
    σG (n := n) (m := m) (l := l) (j := j) hkk' α (Fin.castAdd (k' + l) i') =
      Term.var (Sum.inr (Fin.castAdd (k + (l + j)) i')) := by
  simp only [σG]
  rw [Fin.append_left]

@[simp]
theorem σG_inr {n m k' k l j : ℕ} (hkk' : k' ≤ k) (α : Type) (p : Fin (k' + l)) :
    σG (n := n) (m := m) hkk' α (Fin.natAdd (n + m) p) =
      Term.var (Sum.inr (Fin.natAdd (n + m) (gBlock (j := j) hkk' p))) := by
  simp only [σG]
  rw [Fin.append_right]

@[simp]
theorem σH_inl {n m k l j : ℕ} (α : Type) (i' : Fin (n + m)) :
    σH (n := n) (m := m) (k := k) (l := l) (j := j) α (Fin.castAdd (0 + j) i') =
      Term.var (Sum.inr (Fin.castAdd (k + (l + j)) i')) := by
  simp only [σH]
  rw [Fin.append_left]

@[simp]
theorem σH_inr {n m k l j : ℕ} (α : Type) (r : Fin (0 + j)) :
    σH (n := n) (m := m) (k := k) (l := l) α (Fin.natAdd (n + m) r) =
      Term.var (Sum.inr (Fin.natAdd (n + m) (hBlock (k := k) (l := l) r))) := by
  simp only [σH]
  rw [Fin.append_right]


/-- **`σG` preserves sorts**: it relabels `g`'s variables onto slots of the corresponding sort. -/
theorem tmSort_σG {α : Type} {n m k' k l j : ℕ} (hkk' : k' ≤ k) (sα : α → SortTag) :
    ∀ i : Fin ((n + m) + (k' + l)),
      TmSort sα (Fin.append (fSort n m) (fSort k (l + j)) : Fin ((n + m) + (k + (l + j))) → SortTag)
          (σG (n := n) (m := m) (l := l) (j := j) hkk' α i) =
        some ((Fin.append (fSort n m) (fSort k' l) : Fin ((n + m) + (k' + l)) → SortTag) i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i'
    rw [σG_inl, tmSort_var_inr, Fin.append_left, Fin.append_left]
  · intro p
    rw [σG_inr, tmSort_var_inr, Fin.append_right, Fin.append_right]
    refine Fin.addCases ?_ ?_ p
    · intro a
      rw [gBlock_vf, fSort_castAdd, fSort_castAdd]
    · intro q
      rw [gBlock_rv, fSort_natAdd, fSort_natAdd]

/-- **`σH` preserves sorts**. -/
theorem tmSort_σH {α : Type} {n m k l j : ℕ} (sα : α → SortTag) :
    ∀ i : Fin ((n + m) + (0 + j)),
      TmSort sα (Fin.append (fSort n m) (fSort k (l + j)) : Fin ((n + m) + (k + (l + j))) → SortTag)
          (σH (n := n) (m := m) (k := k) (l := l) (j := j) α i) =
        some ((Fin.append (fSort n m) (fSort 0 j) : Fin ((n + m) + (0 + j)) → SortTag) i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i'
    rw [σH_inl, tmSort_var_inr, Fin.append_left, Fin.append_left]
  · intro r
    rw [σH_inr, tmSort_var_inr, Fin.append_right, Fin.append_right]
    rw [hBlock, fSort_natAdd, fSort_zero]

/-- **The zero-padded pairing**: `x ↦ (g x, h x)`, with `g`'s `VF`-coordinates in the first `k'`
slots of `VF^k`, the remaining `k - k'` slots filled with the constant `0`, then `g`'s
`RV`-coordinates and then `h`'s.  It is injective on `A` as soon as `h` is injective on the fibres
of `g` (`pairFun_injOn`). -/
def pairFun {n m k' k l j : ℕ} (hkk' : k' ≤ k) (hz : sortEval SortTag.vf (iVFZero M))
    (g : Tup (M := M) n m → Tup (M := M) k' l) (h : Tup (M := M) n m → Tup (M := M) 0 j)
    (x : Tup (M := M) n m) : Tup (M := M) k (l + j) :=
  ⟨fun i =>
    match i with
    | Sum.inl p => if hp : (p : ℕ) < k' then g x (Sum.inl ⟨p, hp⟩) else iVFZero M
    | Sum.inr s =>
      match (finSumFinEquiv (m := l) (n := j)).symm s with
      | Sum.inl q => g x (Sum.inr q)
      | Sum.inr r => h x (Sum.inr r),
  by
    intro i
    rcases i with p | s
    · rw [idxSort_inl]
      show sortEval SortTag.vf (if hp : (p : ℕ) < k' then g x (Sum.inl ⟨p, hp⟩) else iVFZero M)
      split
      · exact (g x).2 (Sum.inl ⟨p, _⟩)
      · exact hz
    · rw [idxSort_inr]
      show sortEval SortTag.rv
        (match (finSumFinEquiv (m := l) (n := j)).symm s with
         | Sum.inl q => g x (Sum.inr q)
         | Sum.inr r => h x (Sum.inr r))
      rcases hs : (finSumFinEquiv (m := l) (n := j)).symm s with q | r
      · exact (g x).2 (Sum.inr q)
      · exact (h x).2 (Sum.inr r)⟩


/-! ## The graph formula of the padded pairing -/

/-- The target position of the `i`-th padded `VF`-slot. -/
def padSlot {k' k l j : ℕ} (hkk' : k' ≤ k) (i : Fin (k - k')) : Fin (k + (l + j)) :=
  Fin.castAdd (l + j) ⟨k' + (i : ℕ), by have := i.isLt; omega⟩

theorem fSort_padSlot {k' k l j : ℕ} (hkk' : k' ≤ k) (i : Fin (k - k')) :
    fSort k (l + j) (padSlot (j := j) hkk' i) = SortTag.vf :=
  fSort_castAdd _

/-- The atoms fixing the padded `VF`-slots of the target to the constant `0`. -/
def padForm {α : Type} {n m k' k l j : ℕ} (hkk' : k' ≤ k) :
    LRV.BoundedFormula α ((n + m) + (k + (l + j))) :=
  conjFin (fun i : Fin (k - k') =>
    pEqG (Term.var (Sum.inr (Fin.natAdd (n + m) (padSlot (j := j) hkk' i))))
      (Term.func Fn.vfZero (fun i => i.elim0)))

theorem wellSorted_padForm {α : Type} (sα : α → SortTag) {n m k' k l j : ℕ} (hkk' : k' ≤ k) :
    WellSorted sα
      (Fin.append (fSort n m) (fSort k (l + j)) : Fin ((n + m) + (k + (l + j))) → SortTag)
      (padForm (α := α) (n := n) (m := m) (j := j) hkk') := by
  refine wellSorted_conjFin (fun i => ?_)
  refine wellSorted_pEqG (s := SortTag.vf) sα _ ?_ ?_
  · rw [tmSort_var_inr, Fin.append_right, fSort_padSlot]
  · exact tmSort_vfZero sα _

/-- **The graph of the padded pairing**, as a single well-sorted formula: the graph of `g`,
relabelled by `σG`, conjoined with the graph of `h`, relabelled by `σH`, conjoined with the atoms
fixing the padded `VF`-slots to `0`. -/
def pairForm {α : Type} {n m k' k l j : ℕ} (hkk' : k' ≤ k)
    (φg : LRV.BoundedFormula α ((n + m) + (k' + l)))
    (φh : LRV.BoundedFormula α ((n + m) + (0 + j))) :
    LRV.BoundedFormula α ((n + m) + (k + (l + j))) :=
  (BoundedFormula.substVar (σG (n := n) (m := m) (l := l) (j := j) hkk' α) φg ⊓
      BoundedFormula.substVar (σH (n := n) (m := m) (k := k) (l := l) (j := j) α) φh) ⊓
    padForm (α := α) (n := n) (m := m) (j := j) hkk'

theorem wellSorted_pairForm {α : Type} (sα : α → SortTag) {n m k' k l j : ℕ} (hkk' : k' ≤ k)
    {φg : LRV.BoundedFormula α ((n + m) + (k' + l))}
    {φh : LRV.BoundedFormula α ((n + m) + (0 + j))}
    (hφg : WellSorted sα (Fin.append (fSort n m) (fSort k' l)) φg)
    (hφh : WellSorted sα (Fin.append (fSort n m) (fSort 0 j)) φh) :
    WellSorted sα
      (Fin.append (fSort n m) (fSort k (l + j)) : Fin ((n + m) + (k + (l + j))) → SortTag)
      (pairForm (α := α) hkk' φg φh) :=
  wellSorted_inf sα _ (wellSorted_inf sα _ (wellSorted_substVar sα hφg (tmSort_σG hkk' sα))
    (wellSorted_substVar sα hφh (tmSort_σH sα))) (wellSorted_padForm sα hkk')

/-- The padded pairing, read back: `g x` is the `g`-part of `y` and `h x` is its `h`-part. -/
theorem pairFun_inl {n m k' k l j : ℕ} (hkk' : k' ≤ k) (hz : sortEval SortTag.vf (iVFZero M))
    (g : Tup (M := M) n m → Tup (M := M) k' l) (h : Tup (M := M) n m → Tup (M := M) 0 j)
    (x : Tup (M := M) n m) {p : Fin k} (hp : (p : ℕ) < k') :
    pairFun hkk' hz g h x (Sum.inl p) = g x (Sum.inl ⟨p, hp⟩) := by
  show (if hp' : (p : ℕ) < k' then g x (Sum.inl ⟨p, hp'⟩) else iVFZero M) = g x (Sum.inl ⟨p, hp⟩)
  rw [dif_pos hp]

theorem pairFun_not_inl {n m k' k l j : ℕ} (hkk' : k' ≤ k) (hz : sortEval SortTag.vf (iVFZero M))
    (g : Tup (M := M) n m → Tup (M := M) k' l) (h : Tup (M := M) n m → Tup (M := M) 0 j)
    (x : Tup (M := M) n m) {p : Fin k} (hp : ¬ (p : ℕ) < k') :
    pairFun hkk' hz g h x (Sum.inl p) = iVFZero M := by
  show (if hp' : (p : ℕ) < k' then g x (Sum.inl ⟨p, hp'⟩) else iVFZero M) = iVFZero M
  rw [dif_neg hp]

theorem pairFun_inr_inl {n m k' k l j : ℕ} (hkk' : k' ≤ k)
    (hz : sortEval SortTag.vf (iVFZero M))
    (g : Tup (M := M) n m → Tup (M := M) k' l) (h : Tup (M := M) n m → Tup (M := M) 0 j)
    (x : Tup (M := M) n m) (q : Fin l) :
    pairFun hkk' hz g h x (Sum.inr (Fin.castAdd j q)) = g x (Sum.inr q) := by
  show (match (finSumFinEquiv (m := l) (n := j)).symm (Fin.castAdd j q) with
      | Sum.inl q' => g x (Sum.inr q')
      | Sum.inr r => h x (Sum.inr r)) = g x (Sum.inr q)
  rw [finSumFinEquiv_symm_castAdd]

theorem pairFun_inr_inr {n m k' k l j : ℕ} (hkk' : k' ≤ k)
    (hz : sortEval SortTag.vf (iVFZero M))
    (g : Tup (M := M) n m → Tup (M := M) k' l) (h : Tup (M := M) n m → Tup (M := M) 0 j)
    (x : Tup (M := M) n m) (r : Fin j) :
    pairFun hkk' hz g h x (Sum.inr (Fin.natAdd l r)) = h x (Sum.inr r) := by
  show (match (finSumFinEquiv (m := l) (n := j)).symm (Fin.natAdd l r) with
      | Sum.inl q' => g x (Sum.inr q')
      | Sum.inr r' => h x (Sum.inr r')) = h x (Sum.inr r)
  rw [finSumFinEquiv_symm_natAdd]


/-! ## Reading the padded pairing back -/

/-- The tuple of the **padded `VF`-coordinates** of a target tuple: `k - k'` coordinates. -/
def decPad {k' k l j : ℕ} (hkk' : k' ≤ k) (y : Tup (M := M) k (l + j)) :
    Tup (M := M) (k - k') 0 :=
  ⟨fun i =>
    match i with
    | Sum.inl e => y (Sum.inl (Fin.cast (by rw [Nat.add_sub_of_le hkk']) (Fin.natAdd k' e)))
    | Sum.inr a => a.elim0,
  by
    intro i
    rcases i with e | a
    · exact y.2 (Sum.inl (Fin.cast (by rw [Nat.add_sub_of_le hkk']) (Fin.natAdd k' e)))
    · exact a.elim0⟩

@[simp]
theorem decPad_inl {k' k l j : ℕ} (hkk' : k' ≤ k) (y : Tup (M := M) k (l + j))
    (e : Fin (k - k')) :
    decPad (j := j) hkk' y (Sum.inl e) =
      y (Sum.inl (Fin.cast (by rw [Nat.add_sub_of_le hkk']) (Fin.natAdd k' e))) := rfl

/-- The constant `0`-tuple in `RV^{k-k'}` — the value the padded slots must take. -/
def constZero {k' k : ℕ} (hkk' : k' ≤ k) (hz : sortEval SortTag.vf (iVFZero M)) :
    Tup (M := M) (k - k') 0 :=
  ⟨fun i =>
    match i with
    | Sum.inl _ => iVFZero M
    | Sum.inr a => a.elim0,
  by
    intro i
    rcases i with e | a
    · exact hz
    · exact a.elim0⟩

@[simp]
theorem constZero_inl {k' k : ℕ} (hkk' : k' ≤ k) (hz : sortEval SortTag.vf (iVFZero M))
    (e : Fin (k - k')) : constZero (M := M) hkk' hz (Sum.inl e) = iVFZero M := rfl

/-- **`pairFun` is the paste of `g` and `h`**: it takes exactly the values described by `g`, by `h`
and by the padding. -/
theorem pairFun_eq_iff {n m k' k l j : ℕ} (hkk' : k' ≤ k) (hz : sortEval SortTag.vf (iVFZero M))
    (g : Tup (M := M) n m → Tup (M := M) k' l) (h : Tup (M := M) n m → Tup (M := M) 0 j)
    (x : Tup (M := M) n m) (y : Tup (M := M) k (l + j)) :
    pairFun hkk' hz g h x = y ↔
      (g x = decG hkk' y ∧ h x = decH y ∧ decPad (j := j) hkk' y = constZero hkk' hz) := by
  constructor
  · intro hxy
    refine ⟨?_, ?_, ?_⟩
    · refine Subtype.ext (funext fun i => ?_)
      rcases i with a | q
      · rw [decG_inl, ← hxy, pairFun_inl hkk' hz g h x (by simp)]
        exact congrArg (↑(g x)) (by simp)
      · have hcq : (Fin.castLE (Nat.le_add_right l j) q : Fin (l + j)) = Fin.castAdd j q :=
          Fin.ext rfl
        rw [decG_inr, hcq, ← hxy, pairFun_inr_inl]
    · refine Subtype.ext (funext fun i => ?_)
      rcases i with a | r
      · exact a.elim0
      · rw [decH_inr, ← hxy, pairFun_inr_inr]
    · refine Subtype.ext (funext fun i => ?_)
      rcases i with e | a
      · rw [decPad_inl, ← hxy, constZero_inl,
          pairFun_not_inl hkk' hz g h x (show ¬ ((Fin.cast (by rw [Nat.add_sub_of_le hkk'])
            (Fin.natAdd k' e) : Fin k) : ℕ) < k' by
              simp only [Fin.val_cast, Fin.val_natAdd]; omega)]
      · exact a.elim0
  · rintro ⟨hg, hh, hpad⟩
    refine Subtype.ext (funext fun t => ?_)
    rcases t with p | s
    · by_cases hp : (p : ℕ) < k'
      · rw [pairFun_inl hkk' hz g h x hp, hg, decG_inl]
        exact congrArg (↑y) (by simp)
      · rw [pairFun_not_inl hkk' hz g h x hp]
        have hge : k' ≤ (p : ℕ) := by omega
        have hlt : (p : ℕ) - k' < k - k' := by omega
        have hpad' := congrFun (congrArg Subtype.val hpad) (Sum.inl ⟨(p : ℕ) - k', hlt⟩)
        rw [decPad_inl, constZero_inl] at hpad'
        rw [show (Fin.cast (by rw [Nat.add_sub_of_le hkk']) (Fin.natAdd k' ⟨(p : ℕ) - k', hlt⟩) :
          Fin k) = p from Fin.ext (by
            simp only [Fin.val_cast, Fin.val_natAdd]
            exact Nat.add_sub_of_le hge)] at hpad'
        exact hpad'.symm
    · have hs := Equiv.apply_symm_apply (finSumFinEquiv (m := l) (n := j)) s
      rcases hc : (finSumFinEquiv (m := l) (n := j)).symm s with q | r
      · have hsq : s = Fin.castAdd j q := by
          rw [← hs, hc, finSumFinEquiv_apply_left]
        rw [hsq, pairFun_inr_inl, hg]
        have hcq : (Fin.castLE (Nat.le_add_right l j) q : Fin (l + j)) = Fin.castAdd j q :=
          Fin.ext rfl
        rw [decG_inr, hcq]
      · have hsr : s = Fin.natAdd l r := by
          rw [← hs, hc, finSumFinEquiv_apply_right]
        rw [hsr, pairFun_inr_inr, hh, decH_inr]

/-- The assignment produced by `σG`. -/
theorem σG_assign {α : Type} {n m k' k l j : ℕ} (hkk' : k' ≤ k) (v : α → M)
    (x : Tup (M := M) n m) (y : Tup (M := M) k (l + j)) :
    (fun i => Term.realize (Sum.elim v (pairAssign x y))
        (σG (n := n) (m := m) (l := l) (j := j) hkk' α i)) =
      pairAssign x (decG hkk' y) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i'
    rw [σG_inl, Term.realize_var, Sum.elim_inr, pairAssign_left, pairAssign_left]
  · intro p
    rw [σG_inr, Term.realize_var, Sum.elim_inr, pairAssign_right, pairAssign_right]
    refine Fin.addCases ?_ ?_ p
    · intro a
      rw [gBlock_vf, finSumFinEquiv_symm_castAdd, finSumFinEquiv_symm_castAdd, decG_inl]
    · intro q
      rw [gBlock_rv, finSumFinEquiv_symm_natAdd, finSumFinEquiv_symm_natAdd, decG_inr]

theorem finSumFinEquiv_symm_zero {j : ℕ} (r : Fin (0 + j)) :
    (finSumFinEquiv (m := 0) (n := j)).symm r = Sum.inr (Fin.cast (Nat.zero_add j) r) := by
  rcases h : (finSumFinEquiv (m := 0) (n := j)).symm r with p | r'
  · exact p.elim0
  · have hr : (Fin.natAdd 0 r' : Fin (0 + j)) = r := by
      have h2 := Equiv.apply_symm_apply (finSumFinEquiv (m := 0) (n := j)) r
      rw [h, finSumFinEquiv_apply_right] at h2
      exact h2
    congr 1
    exact Fin.ext (by have := congrArg Fin.val hr; simpa using this)

/-- The assignment produced by `σH`. -/
theorem σH_assign {α : Type} {n m k l j : ℕ} (v : α → M)
    (x : Tup (M := M) n m) (y : Tup (M := M) k (l + j)) :
    (fun i => Term.realize (Sum.elim v (pairAssign x y))
        (σH (n := n) (m := m) (k := k) (l := l) (j := j) α i)) =
      pairAssign x (decH y) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i'
    rw [σH_inl, Term.realize_var, Sum.elim_inr, pairAssign_left, pairAssign_left]
  · intro r
    rw [σH_inr, Term.realize_var, Sum.elim_inr, pairAssign_right, pairAssign_right]
    rw [hBlock, finSumFinEquiv_symm_natAdd, finSumFinEquiv_symm_zero, decH_inr]


/-! ## Realization of the graph formula -/

theorem padAtom_realize {S : SP M} {n m k' k l j : ℕ} (hkk' : k' ≤ k)
    (hz : sortEval SortTag.vf (iVFZero M)) (x : Tup (M := M) n m) (y : Tup (M := M) k (l + j))
    (i : Fin (k - k')) :
    (pEqG (Term.var (Sum.inr (Fin.natAdd (n + m) (padSlot (j := j) hkk' i))))
        (Term.func Fn.vfZero (fun i => i.elim0))).Realize S.toFun (pairAssign x y) ↔
      decPad (j := j) hkk' y (Sum.inl i) = constZero (M := M) hkk' hz (Sum.inl i) := by
  rw [pEqG, BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inr,
    pairAssign_right, padSlot, finSumFinEquiv_symm_castAdd, decPad_inl, constZero_inl]
  rw [show (⟨k' + (i : ℕ), by have := i.isLt; omega⟩ : Fin k) =
      Fin.cast (by rw [Nat.add_sub_of_le hkk']) (Fin.natAdd k' i) from Fin.ext rfl]
  rw [realize_vfZero]

/-- **The realization of the graph of the padded pairing**: on `A` it is the graph of
`pairFun`. -/
theorem pairForm_realize {S : SP M} {n m k' k l j : ℕ} (hkk' : k' ≤ k)
    (hz : sortEval SortTag.vf (iVFZero M))
    {A : Set (Tup (M := M) n m)} {g : Tup (M := M) n m → Tup (M := M) k' l}
    {h : Tup (M := M) n m → Tup (M := M) 0 j}
    {φg : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + m) + (k' + l))}
    {φh : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + m) + (0 + j))}
    (hφg : ∀ x, x ∈ A → ∀ y' : Tup (M := M) k' l,
      (φg.Realize S.toFun (pairAssign x y') ↔ g x = y'))
    (hφh : ∀ x, x ∈ A → ∀ y' : Tup (M := M) 0 j,
      (φh.Realize S.toFun (pairAssign x y') ↔ h x = y'))
    {x : Tup (M := M) n m} (hx : x ∈ A) (y : Tup (M := M) k (l + j)) :
    (pairForm (α := Fin S.n ⊕ Fin S.m) hkk' φg φh).Realize S.toFun (pairAssign x y) ↔
      pairFun hkk' hz g h x = y := by
  have hpadiff : (∀ i : Fin (k - k'),
      (pEqG (Term.var (Sum.inr (Fin.natAdd (n + m) (padSlot (j := j) hkk' i))))
        (Term.func Fn.vfZero (fun i => i.elim0))).Realize S.toFun (pairAssign x y)) ↔
      decPad (j := j) hkk' y = constZero (M := M) hkk' hz := by
    rw [show (∀ i : Fin (k - k'),
        (pEqG (Term.var (Sum.inr (Fin.natAdd (n + m) (padSlot (j := j) hkk' i))))
          (Term.func Fn.vfZero (fun i => i.elim0))).Realize S.toFun (pairAssign x y)) ↔
        ∀ i : Fin (k - k'),
          decPad (j := j) hkk' y (Sum.inl i) = constZero (M := M) hkk' hz (Sum.inl i) from
      forall_congr' (fun i => padAtom_realize hkk' hz x y i)]
    constructor
    · intro hp
      refine Subtype.ext (funext fun t => ?_)
      rcases t with e | a
      · exact hp e
      · exact a.elim0
    · intro hp i
      exact congrFun (congrArg Subtype.val hp) (Sum.inl i)
  rw [pairForm, BoundedFormula.realize_inf, BoundedFormula.realize_inf, padForm, realize_conjFin,
    realize_substVar, realize_substVar, σG_assign, σH_assign, hφg x hx, hφh x hx, hpadiff]
  have hassoc : (((g x = decG hkk' y ∧ h x = decH y) ∧
      decPad (j := j) hkk' y = constZero (M := M) hkk' hz) ↔
      (g x = decG hkk' y ∧ h x = decH y ∧ decPad (j := j) hkk' y = constZero (M := M) hkk' hz)) := by
    tauto
  rw [hassoc]
  exact (pairFun_eq_iff hkk' hz g h x y).symm

/-! ## The paper's hypothesis: fibre separation -/

/-- **Fibre separation** — exactly what Yin's Lemma `finite:VF:project:RV` plus compactness give in
the paper's proof of `dim:RV:fibers`: a definable `RV`-valued function on `A` that is injective on
every fibre of a definable finite-to-one `g`.  The paper's sentence: *"By compactness, there is a
definable function `h : A → RV_Γ^j` for some `j` such that `h ↾ g⁻¹(ā, t̄)` is injective for every
`(ā, t̄) ∈ g(A)`."* -/
def FibreSeparating (S : SP M) {n m : ℕ} (A : Set (Tup (M := M) n m)) : Prop :=
  ∀ (k l : ℕ) (g : Tup (M := M) n m → Tup (M := M) k l), DefinableFun S A g →
    FibreFinite A g →
      ∃ j : ℕ, ∃ h : Tup (M := M) n m → Tup (M := M) 0 j, DefinableFun S A h ∧
        ∀ x y, x ∈ A → y ∈ A → g x = g y → h x = h y → x = y

/-- **`PaperStraightening` from fibre separation**: the padded pairing of `g` and the separating
`h` is a definable injection `A → VF^k × RV^{l+j}`.  This is the paper's step *"Then the function
`f` on `A` given by `(b̄, s̄) ↦ (g(b̄, s̄), h(b̄, s̄))` is as desired."* -/
theorem paperStraightening_of_fibreSeparating (S : SP M) {n m : ℕ}
    (A : Set (Tup (M := M) n m)) (hz : sortEval SortTag.vf (iVFZero M))
    (hfs : FibreSeparating S A) : PaperStraightening S A := by
  intro k' k l hkk' g hg hfin
  obtain ⟨j, h, hhdef, hhsep⟩ := hfs k' l g hg hfin
  obtain ⟨φg, hφgs, hφg⟩ := hg
  obtain ⟨φh, hφhs, hφh⟩ := hhdef
  refine ⟨l + j, pairFun hkk' hz g h, ⟨pairForm hkk' φg φh,
    wellSorted_pairForm S.sortMap hkk' hφgs hφhs,
    fun x hx y => pairForm_realize hkk' hz hφg hφh hx y⟩, ?_⟩
  intro x hx y hy hxy
  have hdx : g x = decG hkk' (pairFun hkk' hz g h x) :=
    ((pairFun_eq_iff hkk' hz g h x _).1 rfl).1
  have hdy : g y = decG hkk' (pairFun hkk' hz g h y) :=
    ((pairFun_eq_iff hkk' hz g h y _).1 rfl).1
  have hhx : h x = decH (pairFun hkk' hz g h x) :=
    ((pairFun_eq_iff hkk' hz g h x _).1 rfl).2.1
  have hhy : h y = decH (pairFun hkk' hz g h y) :=
    ((pairFun_eq_iff hkk' hz g h y _).1 rfl).2.1
  refine hhsep x y hx hy ?_ ?_
  · rw [hdx, hdy, hxy]
  · rw [hhx, hhy, hxy]


/-- **Lemma `dim:RV:fibers` with the paper's own hypothesis**: *"For any natural number `k`,
`dim_VF(A) ≤ k` if and only if there is a definable injection `f : A → VF^k × RV_Γ^l` for some
`l`."*  Here the only hypotheses are `FibreSeparating` (Yin's `finite:VF:project:RV` plus the
compactness of the paper's proof) and `sortEval .vf iVFZero` (the sort of the constant `0`). -/
theorem dim_RV_fibers_of_fibreSeparating (S : SP M) {n m : ℕ} (A : Set (Tup (M := M) n m))
    (hz : sortEval SortTag.vf (iVFZero M)) (hfs : FibreSeparating S A) (k : ℕ) :
    dimVF S A ≤ k ↔ ∃ l : ℕ, ∃ f : Tup (M := M) n m → Tup (M := M) k l,
      DefinableFun S A f ∧ InjOn A f :=
  dim_RV_fibers S A (paperStraightening_of_fibreSeparating S A hz hfs) k

end Sec4Pair

end SpecialTransformations.Milestone0
