/-
Section 3 of the paper, frozen statements over sorted parameter pairs (`SP`), with `acl`/`dcl`.

**Audited against the source** (`paper.tex` section 3 from line 659, and `qe.tex` for the items the
paper cites from Yin, QE:ACVF:min).  The first transcription of this file was not faithful: five of
its six statements carried a defect that made them unprovable, vacuous, or weaker than the paper.
The corrected statements are below, each with the source sentence it freezes; the inventory of what
was wrong is in `Milestone0/DECISION.md`, section "Section 3 statement audit", and in one line each:

* `acl_const_of_fibres`, `acl:VF:transfer:acl:RV` -- the source's hypothesis is `s ∈ acl(a)` for each
  `a ∈ A`, i.e. algebraic closure over `S` *together with* `a`.  The frozen version wrote `acl S s`,
  which does not mention `a` at all: vacuous at `A = ∅`, and the conclusion does not follow.
* `exchange` -- the source is `a ∈ acl(b) ∖ acl(∅) -> b ∈ acl(a)`.  The frozen version quantified
  three unrelated pairs `S, S1, S2` and concluded `acl S b ∨ dcl S2 a`; that is not exchange, and it
  is false: with `S = S2 = base` and `S1 = singleVF b` it asserts `acl base b ∨ dcl base a` for every
  `a ∈ VF`.
* `function:rv:to:vf:finite:image` -- the source's `f` is a *definable* function.  Definability was
  omitted, and without it any injection of an infinite `RV`-definable set into `VF` refutes it.
* `finite:VF:project:RV` -- the source (Yin 4.10) is the existence of a *definable injection* of a
  finite definable `A ⊆ VF^n` into some `RV^m`.  The frozen version was a finiteness claim about a
  `B ⊆ VF × RV` whose `RV`-projection is definable, and that is false: `B = VF × {t}` is definable
  that way and its `VF`-projection is all of `VF`.

**Not expressible, and recorded rather than fixed.**  `acl` below is stated at the `VF` sort only
(`WellSorted S.sortMap (fun _ => .vf)`), which is all of section 3 that this file needs, but it means
the second half of the paper's exchange (*"for any `t, s ∈ RV`, if `t ∈ acl(s) ∖ acl(0)` then
`s ∈ acl(t)`"*) cannot be stated: an `RV`-sorted `acl` and the paper's `rho`-function (exchange at
the `RV` sort is proved through the `Gamma`-sort) are missing.  Nothing in sections 3-5 consumes that
half.

To check (`.scratch2/sec3/` holds a compiled `Enc`):

    cp Milestone0/Encoding.lean .scratch2/sec3/Enc.lean
    cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean -o Enc.olean Enc.lean
    cp ../../QE/Sec3_frozen.lean Sec3Frozen.lean && LEAN_PATH=$PWD:$LEAN_PATH lean Sec3Frozen.lean

The five `sorry`s are deliberate: these are *frozen targets*, and the paper cites three of the five
(`exchange`, `average:...`, `function:rv:to:vf:finite:image`) from QE:ACVF:min, so they are quoted
theorems unless re-proved here.
-/
import Enc
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Milestone0
open LRV

structure SP (M : Type*) [LRV.Structure M] where
  n : ℕ
  m : ℕ
  vf : Fin n → M
  rv : Fin m → M
  vf_sorted : ∀ i, iVF (vf i)
  rv_sorted : ∀ j, iRV (rv j)

namespace SP

variable {M : Type*} [LRV.Structure M]

def paramSet (S : SP M) : Set M := Set.range S.vf ∪ Set.range S.rv

def toFun (S : SP M) : Fin S.n ⊕ Fin S.m → M := Sum.elim S.vf S.rv

def sortMap (S : SP M) : Fin S.n ⊕ Fin S.m → SortTag
  | Sum.inl _ => .vf
  | Sum.inr _ => .rv

/-- The empty parameter pair. -/
def base : SP M := ⟨0, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun j => j.elim0⟩

/-- Extend a sorted pair by one `VF`-parameter, the sortedness of the extended tuple supplied by
the caller (the `Fin.snoc` transport is left to the use site, where the shape is known). -/
def extendVF (S : SP M) (vs : Fin (S.n + 1) → M) (hvs : ∀ i, iVF (vs i)) : SP M :=
  ⟨S.n + 1, S.m, vs, S.rv, hvs, S.rv_sorted⟩

/-- Extend a sorted pair by one `RV`-parameter, likewise. -/
def extendRV (S : SP M) (ts : Fin (S.m + 1) → M) (hts : ∀ j, iRV (ts j)) : SP M :=
  ⟨S.n, S.m + 1, S.vf, ts, S.vf_sorted, hts⟩

/-- **`S` together with the `VF`-element `a`** -- the paper's `abar, a`, i.e. `acl(S ∪ {a})`.  This is
the parameter pair that the source's `acl(a)` means when the ambient parameters are `S`. -/
def extendVFParam (S : SP M) (a : M) (ha : iVF a) : SP M :=
  ⟨S.n + 1, S.m, Fin.snoc S.vf a, S.rv,
    (fun i => by
      refine Fin.lastCases ?_ ?_ i
      · simpa using ha
      · intro j; simpa using S.vf_sorted j),
    S.rv_sorted⟩

/-- **`S` together with the `RV`-element `t`** -- the paper's `tbar, t`. -/
def extendRVParam (S : SP M) (t : M) (ht : iRV t) : SP M :=
  ⟨S.n, S.m + 1, S.vf, Fin.snoc S.rv t, S.vf_sorted,
    (fun j => by
      refine Fin.lastCases ?_ ?_ j
      · simpa using ht
      · intro i; simpa using S.rv_sorted i)⟩

/-- The parameter pair consisting of one `VF`-element: the paper's `acl(a)`. -/
def singleVF (a : M) (ha : iVF a) : SP M :=
  ⟨1, 0, (fun _ => a), Fin.elim0, (fun _ => ha), (fun j => j.elim0)⟩

/-- The parameter pair consisting of one `RV`-element: the paper's `acl(t)`. -/
def singleRV (t : M) (ht : iRV t) : SP M :=
  ⟨0, 1, Fin.elim0, (fun _ => t), (fun i => i.elim0), (fun _ => ht)⟩

/-- **Algebraic closure over `S`**: `x` satisfies a well-sorted formula in one free variable whose
parameter is `S` and whose solution set is finite.  This is the paper's `x ∈ acl(abar, tbar)`.  It is
stated at the `VF` sort only -- see the file header. -/
def acl (S : SP M) (x : M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.vf) φ ∧
      ({y | iVF y ∧ φ.Realize S.toFun ![y]} : Set M).Finite ∧
        iVF x ∧ φ.Realize S.toFun ![x]

/-- **Definable closure over `S`**. -/
def dcl (S : SP M) (x : M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.vf) φ ∧
      ({y | iVF y ∧ φ.Realize S.toFun ![y]} : Set M) = {x}

/-- `S`-definability of a subset of one sort. -/
def DefinableVF (S : SP M) (s : Set M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.vf) φ ∧ s = {y | iVF y ∧ φ.Realize S.toFun ![y]}

def DefinableRV (S : SP M) (s : Set M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.rv) φ ∧ s = {y | iRV y ∧ φ.Realize S.toFun ![y]}

/-- **`f` is `S`-definable**: its graph is cut out by a well-sorted formula over the parameters `S`,
first variable at sort `VF` and second at sort `RV`.  The source of
`function:rv:to:vf:finite:image` requires `f` to be definable, which the first transcription of that
statement omitted. -/
def DefinableFun (S : SP M) (f : M → M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 2,
    WellSorted S.sortMap (fun i : Fin 2 => if i = 0 then SortTag.vf else SortTag.rv) φ ∧
      ∀ x y : M, φ.Realize S.toFun ![x, y] ↔ y = f x

/-- Definable closure is contained in algebraic closure: a singleton solution set is finite. -/
theorem dcl_subset_acl (S : SP M) {x : M} (h : dcl S x) : acl S x := by
  obtain ⟨φ, hφ, hset⟩ := h
  have hx : x ∈ ({y | iVF y ∧ φ.Realize S.toFun ![y]} : Set M) := by
    rw [hset]; exact rfl
  refine ⟨φ, hφ, ?_, hx.1, hx.2⟩
  rw [hset]; exact Set.finite_singleton x

/-- **Every `VF`-element is algebraic over itself**: the formula `x = a` (with `a` as a parameter)
has the singleton solution set `{a}`.  This is reflexivity of `acl`, and it is why the paper's
exchange is stated with `acl(b)` and `acl(a)` — as opposed to `acl S`, which is not reflexive in
`x` for `x ∉ S`.  (It also shows why the *first* transcription of `swl_exchange`, which quantified
three unrelated parameter pairs, could not be exchange: `acl S b` is free in `a` and in the choice of
parameters.) -/
theorem acl_self (a : M) (ha : iVF a) : acl (singleVF a ha) a := by
  classical
  have hφ : WellSorted (singleVF a ha).sortMap (fun _ => SortTag.vf)
      (pEqG (Term.var (Sum.inr (0 : Fin 1))) (Term.var (Sum.inl (Sum.inl (0 : Fin 1))))) :=
    wellSorted_pEqG _ _ rfl rfl
  have hreal : ∀ y : M,
      (pEqG (Term.var (Sum.inr (0 : Fin 1)))
        (Term.var (Sum.inl (Sum.inl (0 : Fin 1))))).Realize (singleVF a ha).toFun ![y] ↔
        y = a := by
    intro y
    simp [pEqG, singleVF, toFun]
  refine ⟨_, hφ, ?_, ha, (hreal a).2 rfl⟩
  have hset : ({y : M | iVF y ∧ (pEqG (Term.var (Sum.inr (0 : Fin 1)))
      (Term.var (Sum.inl (Sum.inl (0 : Fin 1))))).Realize (singleVF a ha).toFun ![y]} : Set M)
      = {a} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h => (hreal y).1 h.2, fun h => ⟨by rw [h]; exact ha, (hreal y).2 h⟩⟩
  rw [hset]
  exact Set.finite_singleton a

section Frozen

variable [Nonempty M] (hM : M ⊨ Axioms.ACVF)

/-- **No label in the paper** (section 3, first lemma): *"Let `A` be a definable subset and `s` an
element such that `s ∈ acl(a)` for every `a ∈ A`, then `s ∈ acl(0)`."*  The hypothesis is closure
over `S` together with `a`; the conclusion is closure over `S` alone (`S = base` is the paper's
`acl(∅)`).  The paper proves it by compactness, splitting `A` into finitely many pieces on each of
which the defining formula has bounded solution sets. -/
theorem swl_acl_const_of_fibres (S : SP M) (A : Set M) (s : M) (hA : DefinableVF S A)
    (h : ∀ a : M, (ha : iVF a) → a ∈ A → acl (S.extendVFParam a ha) s) :
    acl S s := by
  sorry

/-- **`acl:VF:transfer:acl:RV`**, `VF` half: *"For any `tbar ∈ RV`, any `tbar`-definable subset
`A ⊆ rv^{-1}(tbar)`, and any element `x`, if `x ∈ acl(abar)` for every `abar ∈ A` then
`x ∈ acl(tbar)`."*  The hypothesis is closure over `S` together with the point `a ∈ A`, not over
`S`. -/
theorem swl_acl_VF_transfer_acl_RV (S : SP M) (A : Set M) (hA : DefinableRV S A) (x : M)
    (h : ∀ a : M, (ha : iRV a) → a ∈ A → acl (S.extendRVParam a ha) x) :
    acl S x := by
  sorry

/-! `exchange` is **not** stated here.  It was, at an arbitrary model of `ACVF`, and that is the wrong
setting: exchange is a property of `acl` in a *saturated* model (Marker, the pregeometry of algebraic
closure), not in an arbitrary one, and the paper's §3 is explicitly over the monster model.  It is
restated over `Sat.MonsterACVF` in `QE/Sec3_sat.lean` (`swl_exchange`), where the saturation data
needed for its proof is available.  Recorded in `DECISION.md` §"Section 3 statement audit". -/

/-- **`function:rv:to:vf:finite:image`** (Yin, Lemma 4.12, via `dcl:to:ac`): *"Let `A ⊆ RV^m` and
`f : A -> VF^n` a definable function.  Then `f(A)` is finite."*  Definability of `f` is a
hypothesis here, as in the source. -/
theorem swl_function_rv_to_vf_finite_image (S : SP M) (A : Set M) (hA : DefinableRV S A)
    (f : M → M) (hf : DefinableFun S f) (hfVF : ∀ a : M, a ∈ A → iVF (f a)) :
    (f '' A).Finite := by
  sorry

/-- **`finite:VF:project:RV`** (Yin, Lemma 4.10) at `n = 1`: *"Let `A` be a definable finite subset
of `VF^n`.  Then there is a definable injection `f : A -> RV^m` for some `m`."*  The paper's
conclusion leaves `m` free and its proof produces an `m` fixed by the induction; at `n = 1` this
states the sharpest form, an injection into `RV` itself.  If the paper's induction turns out to need
`m > 1`, this statement is a strengthening and must be weakened to match. -/
theorem swl_finite_VF_project_RV (S : SP M) (A : Set M) (hA : DefinableVF S A) (hfin : A.Finite) :
    ∃ f : M → M, DefinableFun S f ∧ (∀ a : M, a ∈ A → iRV (f a)) ∧ Set.InjOn f A := by
  sorry

end Frozen

end SP

end SpecialTransformations.Milestone0
