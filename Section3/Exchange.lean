module

/-
**`exchange`** — `paper.tex:694`, §3 of Yin, *Special transformations in algebraically closed
valued fields*, and its proof `qe.tex` Lemma 4.3 (line 918, §4 "Minimality in ACVF").

The paper's sentence (`paper.tex`, §3, after `dcl:to:ac`):

> **Lemma `exchange`** `[\cite[Lemma~4.3]{Yin:QE:ACVF:min}]` *The exchange principle holds in both
> sorts:*
> 1. *For any `a`, `b ∈ VF`, if `a ∈ acl(b) ∖ acl(0)` then `b ∈ acl(a)`.*
> 2. *For any `t`, `s ∈ RV`, if `t ∈ acl(s) ∖ acl(0)` then `s ∈ acl(t)`.*

## What this file settles, and what it carries as a hypothesis

`acl` here is `SP.acl` of `QE/Sec3_frozen.lean`: *`x` lies in a finite solution set of a well-sorted
`L_RV`-formula over the parameters*.  Three files in the tree assert that the **`RV` half of the
paper's lemma is "not expressible"** in this encoding (`QE/Sec3_frozen.lean`, header and the
`exchange` note; `QE/Sec3_sat.lean`, `swl_exchange`'s docstring; `QE/AlgIndImag.lean`,
`M5.ExchangeVF`'s docstring): they say `SP.acl` is `VF`-valued, so `t ∈ acl(s)` for `RV`-elements
`t, s` cannot be written.  **That is wrong.**  `SP.acl` is `VF`-sorted only because its output sort
map is the constant `fun _ => SortTag.vf`; changing that constant to `fun _ => SortTag.rv` gives the
`RV`-sorted closure `aclRV` below, with the same encoding, the same `WellSorted` discipline and the
same `Realize`.  Part 1 builds it (`aclRV`, `dclRV`, `dclRV_subset_aclRV`, `aclRV_self`), so the
paper's second half is expressible.

## The claim of §3 that this file *does* prove

Yin's 4.3 is a quoted theorem of the companion paper — like `average:…` (4.9) and
`function:rv:to:vf:finite:image` (4.12) it carries a `\cite` and no proof in `paper.tex`.  What is
provable *here*, and is the whole of `§3`'s use of it, is that **exchange reduces to a single
finiteness statement about definable relations**, with no `acl` in it (Part 3):

> `SwapFinite`.  For every well-sorted `φ(x)` over `S, b` and all `a`, `b` with `a ∉ acl(S)`: if
> `φ(a)` holds and the fibre `{x : φ(x)}` is finite, then the transposed fibre
> `{y : φ(a)}` — `b` read as a variable, `a` read as a parameter — is finite.

The hypothesis `a ∉ acl(S)` is not decoration: without it the transfer is *false* in ACVF (take
`φ(x) := x = 0`, whose fibre is `{0}` and whose transpose at `a = 0` is all of `VF`), which is
exactly why the paper's Lemma 4.3 carries `∖ acl(0)`.  With it, `SwapFinite` is the pure finiteness
statement that the `C`-minimality argument of `qe.tex:918-940` establishes, and it has no `acl` in
its conclusion.

This is the "swap lemma" that `QE-PLAN.md` names as the critical path of §3–§4 ("Mathlib has no
variable substitution … demoting a variable back into a parameter needs variable substitution").
Part 3 builds the swap — that the transposed fibre is `(S, a)`-definable, which is the step Mathlib's
substitution API does not provide — and Part 4 derives:

* `acl_of_swap_finite`: `b ∈ acl(S, a)` from the finiteness of the transposed fibre;
* `exchange_of_swap` : `M5.ExchangeVF` (the paper's half (1), uniformly in `S`) from `SwapFinite`;
* Part 4 repeats the construction at the `RV` sort (`swappedRV`, `SwapFiniteRV`) and gets the
  paper's half (2) the same way, so `exchange_of_swap_both : Exchange 𝕄` from the two transfers;
  the `VF` half is additionally stated in the paper's own at-`acl(0)` shape
  (`exchange_paper_VF`, `exchange_paper_RV`).

So the paper's `exchange` follows from `SwapFinite` together with `SwapFiniteRV`, two statements with
no `acl`/`aclRV` in their conclusions;
the finiteness transfer itself is what Yin's `C`-minimality argument controls (`qe.tex:918-940`: a
quantifier-free formula in disjunctive normal form whose `VF`-equalities must carry a root of a
polynomial in the coefficient `b`, since every other disjunct defines an infinite set because
`rv F(d, b) = rv F(a, b)` for `d` close to `a`).

No `axiom`, no `sorry`, no `native_decide`.
-/
public import Sat
public import Sec3Frozen
public import AlgIndImag
public import SubstVar
public import ParamBridgeRelabel
public import ExSortedG

@[expose] public section

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SpecialTransformations.Milestone0
open LRV

/-! ## 1. The `RV`-sorted closure operators

`SP.acl` (`QE/Sec3_frozen.lean`) restricts `WellSorted`'s output sort map to the constant `VF`.
Nothing else in its definition mentions the sort of the target, so the same definition at the
constant `RV` is the `RV`-sorted algebraic closure the paper's Lemma 4.3(2) speaks about. -/

namespace SP

variable {M : Type*} [LRV.Structure M]

/-- **Algebraic closure at the `RV` sort**: `x ∈ aclRV(S)` when `x` is `RV`-sorted and lies in the
solution set of a well-sorted `L_RV`-formula over the parameters `S` whose solution set (in the
`RV` sort) is finite.  This is `SP.acl` with the output sort map changed from `VF` to `RV`; it is
the closure the paper's `exchange`(2) is stated for, and it makes that half expressible. -/
def aclRV (S : SP M) (x : M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.rv) φ ∧
      ({y | iRV y ∧ φ.Realize S.toFun ![y]} : Set M).Finite ∧
        iRV x ∧ φ.Realize S.toFun ![x]

/-- **Definable closure at the `RV` sort**, the `dcl` companion of `aclRV`. -/
def dclRV (S : SP M) (x : M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.rv) φ ∧
      ({y | iRV y ∧ φ.Realize S.toFun ![y]} : Set M) = {x}

/-- Definable closure is contained in algebraic closure, at the `RV` sort. -/
theorem dclRV_subset_aclRV (S : SP M) {x : M} (h : dclRV S x) : aclRV S x := by
  obtain ⟨φ, hφ, hset⟩ := h
  have hx : x ∈ ({y | iRV y ∧ φ.Realize S.toFun ![y]} : Set M) := by
    rw [hset]; exact rfl
  exact ⟨φ, hφ, hset ▸ Set.finite_singleton x, hx.1, hx.2⟩

/-- **Reflexivity of `aclRV`**: every `RV`-element is algebraic over itself, by the formula
`y = t` with `t` the parameter.  The `RV` analogue of `SP.acl_self`. -/
theorem aclRV_self (t : M) (ht : iRV t) : aclRV (singleRV t ht) t := by
  classical
  have hφ : WellSorted (singleRV t ht).sortMap (fun _ => SortTag.rv)
      (pEqG (Term.var (Sum.inr (0 : Fin 1))) (Term.var (Sum.inl (Sum.inr (0 : Fin 1))))) :=
    wellSorted_pEqG _ _ rfl rfl
  have hreal : ∀ y : M,
      (pEqG (Term.var (Sum.inr (0 : Fin 1)))
        (Term.var (Sum.inl (Sum.inr (0 : Fin 1))))).Realize (singleRV t ht).toFun ![y] ↔
        y = t := by
    intro y
    simp [pEqG, singleRV, toFun]
  refine ⟨_, hφ, ?_, ht, (hreal t).2 rfl⟩
  have hset : ({y : M | iRV y ∧ (pEqG (Term.var (Sum.inr (0 : Fin 1)))
      (Term.var (Sum.inl (Sum.inr (0 : Fin 1))))).Realize (singleRV t ht).toFun ![y]} : Set M)
      = {t} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h => (hreal y).1 h.2, fun h => ⟨by rw [h]; exact ht, (hreal y).2 h⟩⟩
  rw [hset]
  exact Set.finite_singleton t

/-- **The parameter assignment of `S` with `y` in the last `VF` slot**: the paper's `S̄, y`.  This
is what a *swapped* formula is realised against (the parameter `b` of an `acl`-witness playing the
role of a variable). -/
def withLastVF (S : SP M) (y : M) : Fin (S.n + 1) ⊕ Fin S.m → M :=
  Sum.elim (Fin.snoc S.vf y) S.rv

/-- `withLastVF` is the parameter assignment of `S` extended by `y`, definitionally. -/
theorem extendVFParam_toFun (S : SP M) (y : M) (hy : iVF y) :
    (S.extendVFParam y hy).toFun = S.withLastVF y := rfl

/-- The paper's `acl(b)` is the pair `singleVF b`; the uniform statement uses
`base.extendVFParam b`.  The two have the same index type and the same parameter assignment. -/
theorem base_extendVFParam_acl (b : M) (hb : iVF b) (x : M) :
    acl (base.extendVFParam b hb) x ↔ acl (singleVF b hb) x := by
  have hto : (base.extendVFParam b hb).toFun = (singleVF b hb).toFun := by
    funext i
    rcases i with i | i
    · fin_cases i
      rfl
    · exact i.elim0
  constructor
  · rintro ⟨φ, hφ, hfin, hx1, hx2⟩
    exact ⟨φ, hφ, hto ▸ hfin, hx1, hto ▸ hx2⟩
  · rintro ⟨φ, hφ, hfin, hx1, hx2⟩
    exact ⟨φ, hφ, hto.symm ▸ hfin, hx1, hto.symm ▸ hx2⟩

/-- The `RV` companion of `base_extendVFParam_acl`. -/
theorem base_extendRVParam_aclRV (s : M) (hs : iRV s) (x : M) :
    aclRV (base.extendRVParam s hs) x ↔ aclRV (singleRV s hs) x := by
  have hto : (base.extendRVParam s hs).toFun = (singleRV s hs).toFun := by
    funext i
    rcases i with i | i
    · exact i.elim0
    · fin_cases i
      rfl
  constructor
  · rintro ⟨φ, hφ, hfin, hx1, hx2⟩
    exact ⟨φ, hφ, hto ▸ hfin, hx1, hto ▸ hx2⟩
  · rintro ⟨φ, hφ, hfin, hx1, hx2⟩
    exact ⟨φ, hφ, hto.symm ▸ hfin, hx1, hto.symm ▸ hx2⟩

/-! ## 2. `exchange` in both sorts, as the paper states it

Half (1) is `M5.ExchangeVF` (`QE/AlgIndImag.lean`), which is the paper's sentence uniformly in the
ambient parameter pair `S`; half (2) is `ExchangeRV`, stated here for the first time — it needs the
`RV`-sorted closure `aclRV` of Part 1, which is why the tree recorded it as inexpressible. -/

/-- **`exchange`(2) of the paper** (`paper.tex:694`, `\cite[Lemma~4.3]{Yin:QE:ACVF:min}`): *"For
any `t`, `s ∈ RV`, if `t ∈ acl(s) ∖ acl(0)` then `s ∈ acl(t)`."*  Stated uniformly in the ambient
parameter pair `S`, in the same shape as `M5.ExchangeVF` so the two halves sit side by side.

`S.extendRVParam s hs` is `acl(S, s)`, so at `S = base` (`SP.base_extendRVParam_aclRV`) this is
exactly the paper's sentence at `acl(0)`.  Carried as a named `Prop`, as the paper cites it from
`qe.tex` Lemma 4.3; the paper's proof is `qe.tex:930-940` ("Clearly we may assume that `φ(X, s)`
does not contain any `VF`-sort literal … every irredundant disjunct of `φ(X, s)` has an equality
conjunct; since `t ∉ acl(0)`, the claim follows again from the exchange principle in field
theory"), which needs the quantifier-free normal form and is not derivable from `SwapFinite` — the
`RV` sort has no polynomial normal form. -/
def ExchangeRV (𝕄 : Sat.MonsterACVF) : Prop :=
  ∀ (S : SP 𝕄.M) (t s : 𝕄.M) (ht : iRV t) (hs : iRV s),
    aclRV (S.extendRVParam s hs) t → ¬ aclRV S t → aclRV (S.extendRVParam t ht) s

/-- **The paper's `exchange`, both halves**, as one named hypothesis: `paper.tex:694`, with the
citation `\cite[Lemma~4.3]{Yin:QE:ACVF:min}`.  This is the object §3 assumes; `§4` and the rest of
the paper consume it through `alg:ind:imag`. -/
def Exchange (𝕄 : Sat.MonsterACVF) : Prop := M5.ExchangeVF 𝕄 ∧ ExchangeRV 𝕄

/-- **`exchange`(1) at `acl(0)`** — the paper's own sentence, with `acl(b)` written as
`SP.singleVF b` and `acl(0)` as `SP.base`: *"For any `a`, `b ∈ VF`, if `a ∈ acl(b) ∖ acl(0)` then
`b ∈ acl(a)`."* -/
theorem exchange_paper_VF {𝕄 : Sat.MonsterACVF} (h : M5.ExchangeVF 𝕄) (a b : 𝕄.M)
    (ha : iVF a) (hb : iVF b) (h1 : acl (singleVF b hb) a) (h2 : ¬ acl (base (M := 𝕄.M)) a) :
    acl (singleVF a ha) b :=
  (base_extendVFParam_acl a ha b).1
    (h (base (M := 𝕄.M)) a b ha hb ((base_extendVFParam_acl b hb a).2 h1) h2)

/-- **`exchange`(2) at `acl(0)`** — the paper's own sentence in the `RV` sort: *"For any `t`,
`s ∈ RV`, if `t ∈ acl(s) ∖ acl(0)` then `s ∈ acl(t)`."* -/
theorem exchange_paper_RV {𝕄 : Sat.MonsterACVF} (h : ExchangeRV 𝕄) (t s : 𝕄.M)
    (ht : iRV t) (hs : iRV s) (h1 : aclRV (singleRV s hs) t) (h2 : ¬ aclRV (base (M := 𝕄.M)) t) :
    aclRV (singleRV t ht) s :=
  (base_extendRVParam_aclRV t ht s).1
    (h (base (M := 𝕄.M)) t s ht hs ((base_extendRVParam_aclRV s hs t).2 h1) h2)

/-! ## 2. The swap lemma

Yin's proof of `exchange` (`qe.tex:918-940`) starts from a formula `φ(X, b)` over the parameters
`S` and one `VF`-parameter `b`, whose solution set in `X` is finite and contains `a`.  The step that
has to be *constructed* — and that `QE-PLAN.md` records as the critical path of §3–§4, because
Mathlib's `BoundedFormula.subst` substitutes parameters only and `relabel` moves parameters *into*
variables, never the other way — is the **swap**: read `b` as a variable and `a` as the parameter, to
obtain a formula `ψ(Y)` over the parameters `S, a` whose solution set is `{y : φ(a, y)}`.

`swapped` below is that operation: `promoteG` promotes the last `VF` parameter to a free variable,
and `Term.substVar`/`BoundedFormula.substVar` of `QE/SubstVar.lean` demote the free variable to the
last `VF` parameter slot, reading the promoted one as the single remaining variable.  `swapped_realize`
is its semantics; `swapped_wellSorted` is the sort discipline.  The two give `acl_of_swap_finite`:
a finite transposed fibre is an `acl`-witness. -/

variable {M : Type*} [LRV.Structure M]

/-- **Promote the last `VF` parameter to a free variable**: every parameter of `S` stays where it
is, and the last `VF` slot becomes the new free variable `0`.  (`BoundedFormula.relabel` produces a
formula with `1 + k` free variables, the new one at index `0`.) -/
def promoteG (S : SP M) :
    Fin (S.n + 1) ⊕ Fin S.m → (Fin (S.n + 1) ⊕ Fin S.m) ⊕ Fin 1
  | Sum.inl i => Fin.lastCases (Sum.inr 0) (fun j => Sum.inl (Sum.inl (Fin.castSucc j))) i
  | Sum.inr j => Sum.inl (Sum.inr j)

/-- **The swap substitution**: free variable `0` (the promoted parameter `b`) is read as the free
variable `y`, and free variable `1` (the algebraic element `a`) is demoted to the last `VF`
parameter slot. -/
def swapσ (S : SP M) : Fin 2 → LRV.Term ((Fin (S.n + 1) ⊕ Fin S.m) ⊕ Fin 1)
  | ⟨0, _⟩ => Term.var (Sum.inr 0)
  | ⟨1, _⟩ => Term.var (Sum.inl (Sum.inl (Fin.last S.n)))

/-- **The swap of an `acl`-witness**: from `φ(x)` well sorted over `S, b`, the formula
`ψ(y) = φ[x := a, b := y]` well sorted over `S, a`. -/
def swapped (S : SP M) (_a : M)
    (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1) :
    LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1 :=
  Sec4Compose.BoundedFormula.substVar (swapσ S) (φ.relabel (promoteG S))

/-- **The semantics of the swap**: `ψ` holds at `y` exactly when `φ` holds at `x = a` with the
parameter `b` replaced by `y`.  This is `{y : φ(a, y)}` — the transposed fibre of Yin's proof. -/
theorem swapped_realize (S : SP M) (a : M) (ha : iVF a)
    (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1) (y : M) :
    (swapped S a φ).Realize (S.extendVFParam a ha).toFun ![y] ↔
      φ.Realize (S.withLastVF y) ![a] := by
  rw [swapped, Sec4Compose.realize_substVar]
  have hxs : (fun i => Term.realize (Sum.elim (S.extendVFParam a ha).toFun ![y]) (swapσ S i))
      = ![y, a] := by
    funext i
    fin_cases i
    · simp [swapσ]
    · simp [swapσ, extendVFParam, toFun, Fin.snoc]
  rw [hxs, BoundedFormula.realize_relabel]
  have h1 : (![y, a] ∘ Fin.natAdd 1) = ![a] := by
    funext i
    fin_cases i
    rfl
  have h2 : Sum.elim (S.extendVFParam a ha).toFun (![y, a] ∘ Fin.castAdd 1) ∘ promoteG S
      = S.withLastVF y := by
    funext p
    rcases p with i | j
    · refine Fin.lastCases ?_ ?_ i
      · simp [promoteG, withLastVF, extendVFParam, toFun, Fin.snoc]
      · intro k
        simp [promoteG, withLastVF, extendVFParam, toFun, Fin.snoc]
    · simp [promoteG, withLastVF, extendVFParam, toFun]
  rw [h1, h2]

/-- `sortAssem` at a constant sort assignment is the same constant assignment. -/
theorem sortAssem_const {k l : ℕ} (s : SortTag) :
    ParamBridge.sortAssem (fun _ : Fin k => s) (fun _ : Fin l => s) = fun _ => s := by
  funext x
  simp only [ParamBridge.sortAssem]
  split <;> rfl

/-- **The swap preserves well-sortedness**: the output sort map of an `acl`-witness over `S, b` and
over `S, a` is the same function, so `ψ` is well sorted over `S, a`. -/
theorem swapped_wellSorted (S : SP M) (a b : M) (ha : iVF a) (hb : iVF b)
    (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1)
    (hφ : WellSorted (S.extendVFParam b hb).sortMap (fun _ => SortTag.vf) φ) :
    WellSorted (S.extendVFParam a ha).sortMap (fun _ => SortTag.vf) (swapped S a φ) := by
  have hsα : (S.extendVFParam b hb).sortMap = (S.extendVFParam a ha).sortMap := by
    funext i
    rcases i with i | i <;> rfl
  rw [← hsα]
  have hg : ∀ p : Fin (S.n + 1) ⊕ Fin S.m,
      (∀ b', promoteG S p = Sum.inl b' →
        (S.extendVFParam b hb).sortMap b' = (S.extendVFParam b hb).sortMap p) ∧
      (∀ j : Fin 1, promoteG S p = Sum.inr j →
        (fun _ : Fin 1 => SortTag.vf) j = (S.extendVFParam b hb).sortMap p) := by
    intro p
    rcases p with i | j
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · constructor
        · intro b' hp
          simp only [promoteG, Fin.lastCases_last] at hp
          exact absurd hp (by simp)
        · intro j' _
          obtain rfl : j' = (0 : Fin 1) := Subsingleton.elim _ _
          rfl
      · constructor
        · intro b' hp
          simp only [promoteG, Fin.lastCases_castSucc] at hp
          obtain rfl : Sum.inl (Fin.castSucc k) = b' := Sum.inl.inj hp
          rfl
        · intro j' hp
          simp only [promoteG, Fin.lastCases_castSucc] at hp
          exact absurd hp (by simp)
    · constructor
      · intro b' hp
        simp only [promoteG] at hp
        obtain rfl : Sum.inr j = b' := Sum.inl.inj hp
        rfl
      · intro j' hp
        simp only [promoteG] at hp
        exact absurd hp (by simp)
  have h1 : WellSorted (S.extendVFParam b hb).sortMap
      (ParamBridge.sortAssem (fun _ : Fin 1 => SortTag.vf) (fun _ : Fin 1 => SortTag.vf))
      (φ.relabel (promoteG S)) :=
    ParamBridge.wellSorted_relabel (promoteG S) (S.extendVFParam b hb).sortMap
      (S.extendVFParam b hb).sortMap (fun _ : Fin 1 => SortTag.vf) hg hφ
  have h2 : ∀ i : Fin (1 + 1), TmSort (S.extendVFParam b hb).sortMap (fun _ : Fin 1 => SortTag.vf)
      (swapσ S i) = some (ParamBridge.sortAssem (fun _ : Fin 1 => SortTag.vf)
        (fun _ : Fin 1 => SortTag.vf) i) := by
    intro i
    rw [sortAssem_const]
    fin_cases i
    · rfl
    · rfl
  exact Sec4Compose.wellSorted_substVar _ h1 h2

/-- **The swap closes the gap**: if the transposed fibre `{y : φ(a, y)}` is finite, then `b` is
algebraic over `S, a` — `ψ` is a well-sorted formula over `S, a` whose solution set is exactly that
fibre and contains `b`.  This is the paper's conclusion `b ∈ acl(a)`, conditional only on the
finiteness of the transposed fibre. -/
theorem acl_of_swap_finite (S : SP M) (a b : M) (ha : iVF a) (hb : iVF b)
    (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1)
    (hφ : WellSorted (S.extendVFParam b hb).sortMap (fun _ => SortTag.vf) φ)
    (hφb : φ.Realize (S.extendVFParam b hb).toFun ![a])
    (hfin : ({y : M | iVF y ∧ φ.Realize (S.withLastVF y) ![a]} : Set M).Finite) :
    acl (S.extendVFParam a ha) b := by
  refine ⟨swapped S a φ, swapped_wellSorted S a b ha hb φ hφ, ?_, hb, ?_⟩
  · have hset : ({y : M | iVF y ∧
        (swapped S a φ).Realize (S.extendVFParam a ha).toFun ![y]} : Set M)
        = {y : M | iVF y ∧ φ.Realize (S.withLastVF y) ![a]} := by
      ext y
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, swapped_realize]
    rw [hset]
    exact hfin
  · rw [swapped_realize, ← extendVFParam_toFun]
    exact hφb

/-- **`SwapFinite`**: the finiteness transfer Yin's `C`-minimality argument controls
(`qe.tex:918-940`).  *A finite fibre of a well-sorted `L_RV`-definable relation at the parameter
`b` stays finite when the two sides of the relation are transposed* — the transposed fibre being the
set of values of the *parameter* for which the formula holds of `a`.

No `acl` occurs in its conclusion: this is the residue of Yin 4.3 once the `dcl`/`acl` bookkeeping
(the swap) is done, and it is what the paper's proof of `exchange` establishes from the normal form
of quantifier-free `L_RV`-formulas.  The paper's hypothesis `a ∉ acl(0)` is not needed for the
derivation `SwapFinite → exchange` below; it is what makes the transfer *true* in ACVF (it rules out
the case where `a` is itself finitely definable over `S`). -/
def SwapFinite (M : Type*) [LRV.Structure M] : Prop :=
  ∀ (S : SP M) (a b : M) (_ha : iVF a) (hb : iVF b)
    (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1),
    ¬ acl S a →
    WellSorted (S.extendVFParam b hb).sortMap (fun _ => SortTag.vf) φ →
      φ.Realize (S.extendVFParam b hb).toFun ![a] →
        ({x : M | iVF x ∧ φ.Realize (S.extendVFParam b hb).toFun ![x]} : Set M).Finite →
          ({y : M | iVF y ∧ φ.Realize (S.withLastVF y) ![a]} : Set M).Finite

/-- **`exchange`(1) from `SwapFinite`**: the paper's `a ∈ acl(b) ∖ acl(0) → b ∈ acl(a)`, uniformly
in the ambient parameters `S` — this is exactly `M5.ExchangeVF` (`QE/AlgIndImag.lean`), derived here
from the finiteness transfer rather than assumed. -/
theorem exchange_of_swap (h : SwapFinite M) (S : SP M) (a b : M) (ha : iVF a) (hb : iVF b)
    (hacl : acl (S.extendVFParam b hb) a) (hne : ¬ acl S a) :
    acl (S.extendVFParam a ha) b := by
  obtain ⟨φ, hφ, hfin, -, hφb⟩ := hacl
  exact acl_of_swap_finite S a b ha hb φ hφ hφb (h S a b ha hb φ hne hφ hφb hfin)

/-- `M5.ExchangeVF` (the paper's `exchange`(1), the form the tree uses) from `SwapFinite`. -/
theorem exchangeVF_of_swap {𝕄 : Sat.MonsterACVF} (h : SwapFinite 𝕄.M) :
    M5.ExchangeVF 𝕄 :=
  fun S a b ha hb hacl hne => exchange_of_swap h S a b ha hb hacl hne

/-! ## 4. The same swap at the `RV` sort: the second half of the paper's lemma

`exchange`(2) is the same statement one sort up, with `RV`-elements in both roles.  The swap goes
through verbatim: the parameter promoted to a variable is the *last `RV`* slot of `S`, and the sort
of the promoted variable is `RV`.  What comes out is `SwapFiniteRV`, the `RV` analogue of the
finiteness transfer of Part 3, and `exchangeRV_of_swapRV`: the paper's second half from it.

The two transfers together give the paper's whole Lemma 694, in both sorts:
`exchange_of_swap_both` produces `Exchange` (the paper's two halves, `paper.tex:694`) from
`SwapFinite` and `SwapFiniteRV`.  Neither transfer mentions `acl`/`aclRV` in its conclusion, and each
carries the paper's own `∖ acl(0)` hypothesis as `¬ acl S a` / `¬ aclRV S a`. -/

/-- Promote the last `RV` parameter of `S` into a free variable of sort `RV`. -/
def promoteGRV (S : SP M) :
    Fin S.n ⊕ Fin (S.m + 1) → (Fin S.n ⊕ Fin (S.m + 1)) ⊕ Fin 1
  | Sum.inl i => Sum.inl (Sum.inl i)
  | Sum.inr j => Fin.lastCases (Sum.inr 0) (fun k => Sum.inl (Sum.inr (Fin.castSucc k))) j

/-- The `RV` swap substitution. -/
def swapσRV (S : SP M) : Fin 2 → LRV.Term ((Fin S.n ⊕ Fin (S.m + 1)) ⊕ Fin 1)
  | ⟨0, _⟩ => Term.var (Sum.inr 0)
  | ⟨1, _⟩ => Term.var (Sum.inl (Sum.inr (Fin.last S.m)))

/-- **The swap of an `RV`-sorted `acl`-witness**. -/
def swappedRV (S : SP M) (_a : M)
    (φ : LRV.BoundedFormula (Fin S.n ⊕ Fin (S.m + 1)) 1) :
    LRV.BoundedFormula (Fin S.n ⊕ Fin (S.m + 1)) 1 :=
  Sec4Compose.BoundedFormula.substVar (swapσRV S) (φ.relabel (promoteGRV S))

/-- The parameter assignment of `S` with `y` in the last `RV` slot. -/
def withLastRV (S : SP M) (y : M) : Fin S.n ⊕ Fin (S.m + 1) → M :=
  Sum.elim S.vf (Fin.snoc S.rv y)

/-- `withLastRV` is the assignment of `S` extended by an `RV`-parameter. -/
theorem extendRVParam_toFun (S : SP M) (y : M) (hy : iRV y) :
    (S.extendRVParam y hy).toFun = S.withLastRV y := rfl

/-- **The semantics of the `RV` swap**. -/
theorem swappedRV_realize (S : SP M) (a : M) (ha : iRV a)
    (φ : LRV.BoundedFormula (Fin S.n ⊕ Fin (S.m + 1)) 1) (y : M) :
    (swappedRV S a φ).Realize (S.extendRVParam a ha).toFun ![y] ↔
      φ.Realize (S.withLastRV y) ![a] := by
  rw [swappedRV, Sec4Compose.realize_substVar]
  have hxs : (fun i => Term.realize (Sum.elim (S.extendRVParam a ha).toFun ![y]) (swapσRV S i))
      = ![y, a] := by
    funext i
    fin_cases i
    · simp [swapσRV]
    · simp [swapσRV, extendRVParam, toFun, Fin.snoc]
  rw [hxs, BoundedFormula.realize_relabel]
  have h1 : (![y, a] ∘ Fin.natAdd 1) = ![a] := by
    funext i
    fin_cases i
    rfl
  have h2 : Sum.elim (S.extendRVParam a ha).toFun (![y, a] ∘ Fin.castAdd 1) ∘ promoteGRV S
      = S.withLastRV y := by
    funext p
    rcases p with i | j
    · simp [promoteGRV, withLastRV, extendRVParam, toFun]
    · refine Fin.lastCases ?_ ?_ j
      · simp [promoteGRV, withLastRV, extendRVParam, toFun, Fin.snoc]
      · intro k
        simp [promoteGRV, withLastRV, extendRVParam, toFun, Fin.snoc]
  rw [h1, h2]

/-- **The `RV` swap preserves well-sortedness** (output sort `RV`). -/
theorem swappedRV_wellSorted (S : SP M) (a b : M) (ha : iRV a) (hb : iRV b)
    (φ : LRV.BoundedFormula (Fin S.n ⊕ Fin (S.m + 1)) 1)
    (hφ : WellSorted (S.extendRVParam b hb).sortMap (fun _ => SortTag.rv) φ) :
    WellSorted (S.extendRVParam a ha).sortMap (fun _ => SortTag.rv) (swappedRV S a φ) := by
  have hsα : (S.extendRVParam b hb).sortMap = (S.extendRVParam a ha).sortMap := by
    funext i
    rcases i with i | i <;> rfl
  rw [← hsα]
  have hg : ∀ p : Fin S.n ⊕ Fin (S.m + 1),
      (∀ b', promoteGRV S p = Sum.inl b' →
        (S.extendRVParam b hb).sortMap b' = (S.extendRVParam b hb).sortMap p) ∧
      (∀ j : Fin 1, promoteGRV S p = Sum.inr j →
        (fun _ : Fin 1 => SortTag.rv) j = (S.extendRVParam b hb).sortMap p) := by
    intro p
    rcases p with i | j
    · constructor
      · intro b' hp
        simp only [promoteGRV] at hp
        obtain rfl : Sum.inl i = b' := Sum.inl.inj hp
        rfl
      · intro j' hp
        simp only [promoteGRV] at hp
        exact absurd hp (by simp)
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · constructor
        · intro b' hp
          simp only [promoteGRV, Fin.lastCases_last] at hp
          exact absurd hp (by simp)
        · intro j' _
          obtain rfl : j' = (0 : Fin 1) := Subsingleton.elim _ _
          rfl
      · constructor
        · intro b' hp
          simp only [promoteGRV, Fin.lastCases_castSucc] at hp
          obtain rfl : Sum.inr (Fin.castSucc k) = b' := Sum.inl.inj hp
          rfl
        · intro j' hp
          simp only [promoteGRV, Fin.lastCases_castSucc] at hp
          exact absurd hp (by simp)
  have h1 : WellSorted (S.extendRVParam b hb).sortMap
      (ParamBridge.sortAssem (fun _ : Fin 1 => SortTag.rv) (fun _ : Fin 1 => SortTag.rv))
      (φ.relabel (promoteGRV S)) :=
    ParamBridge.wellSorted_relabel (promoteGRV S) (S.extendRVParam b hb).sortMap
      (S.extendRVParam b hb).sortMap (fun _ : Fin 1 => SortTag.rv) hg hφ
  have h2 : ∀ i : Fin (1 + 1), TmSort (S.extendRVParam b hb).sortMap (fun _ : Fin 1 => SortTag.rv)
      (swapσRV S i) = some (ParamBridge.sortAssem (fun _ : Fin 1 => SortTag.rv)
        (fun _ : Fin 1 => SortTag.rv) i) := by
    intro i
    rw [sortAssem_const]
    fin_cases i
    · rfl
    · rfl
  exact Sec4Compose.wellSorted_substVar _ h1 h2

/-- **The `RV` swap closes the gap**: a finite transposed `RV`-fibre is an `aclRV`-witness. -/
theorem aclRV_of_swapRV_finite (S : SP M) (a b : M) (ha : iRV a) (hb : iRV b)
    (φ : LRV.BoundedFormula (Fin S.n ⊕ Fin (S.m + 1)) 1)
    (hφ : WellSorted (S.extendRVParam b hb).sortMap (fun _ => SortTag.rv) φ)
    (hφb : φ.Realize (S.extendRVParam b hb).toFun ![a])
    (hfin : ({y : M | iRV y ∧ φ.Realize (S.withLastRV y) ![a]} : Set M).Finite) :
    aclRV (S.extendRVParam a ha) b := by
  refine ⟨swappedRV S a φ, swappedRV_wellSorted S a b ha hb φ hφ, ?_, hb, ?_⟩
  · have hset : ({y : M | iRV y ∧
        (swappedRV S a φ).Realize (S.extendRVParam a ha).toFun ![y]} : Set M)
        = {y : M | iRV y ∧ φ.Realize (S.withLastRV y) ![a]} := by
      ext y
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, swappedRV_realize]
    rw [hset]
    exact hfin
  · rw [swappedRV_realize, ← extendRVParam_toFun]
    exact hφb

/-- **`SwapFiniteRV`**: the `RV` analogue of `SwapFinite` — the pure finiteness transfer that the
paper's `exchange`(2) reduces to.  Same shape, same hypothesis `a ∉ aclRV(S)` (which is what the
paper's `∖ acl(0)` is), no `aclRV` in the conclusion. -/
def SwapFiniteRV (M : Type*) [LRV.Structure M] : Prop :=
  ∀ (S : SP M) (a b : M) (_ha : iRV a) (hb : iRV b)
    (φ : LRV.BoundedFormula (Fin S.n ⊕ Fin (S.m + 1)) 1),
    ¬ aclRV S a →
    WellSorted (S.extendRVParam b hb).sortMap (fun _ => SortTag.rv) φ →
      φ.Realize (S.extendRVParam b hb).toFun ![a] →
        ({x : M | iRV x ∧ φ.Realize (S.extendRVParam b hb).toFun ![x]} : Set M).Finite →
          ({y : M | iRV y ∧ φ.Realize (S.withLastRV y) ![a]} : Set M).Finite

/-- **`exchange`(2) from `SwapFiniteRV`**: the paper's `t ∈ acl(s) ∖ acl(0) → s ∈ acl(t)`,
uniformly in the ambient parameters. -/
theorem exchangeRV_of_swapRV (h : SwapFiniteRV M) (S : SP M) (t s : M) (ht : iRV t) (hs : iRV s)
    (hacl : aclRV (S.extendRVParam s hs) t) (hne : ¬ aclRV S t) :
    aclRV (S.extendRVParam t ht) s := by
  obtain ⟨φ, hφ, hfin, -, hφb⟩ := hacl
  exact aclRV_of_swapRV_finite S t s ht hs φ hφ hφb (h S t s ht hs φ hne hφ hφb hfin)

/-- `ExchangeRV` (the paper's `exchange`(2) at the monster model) from `SwapFiniteRV`. -/
theorem exchangeRV_of_swapRV_monster {𝕄 : Sat.MonsterACVF} (h : SwapFiniteRV 𝕄.M) :
    ExchangeRV 𝕄 :=
  fun S t s ht hs hacl hne => exchangeRV_of_swapRV h S t s ht hs hacl hne

/-- **The paper's Lemma 694, both halves, from the two finiteness transfers.** -/
theorem exchange_of_swap_both {𝕄 : Sat.MonsterACVF} (h : SwapFinite 𝕄.M) (hRV : SwapFiniteRV 𝕄.M) :
    Exchange 𝕄 :=
  ⟨exchangeVF_of_swap h, exchangeRV_of_swapRV_monster hRV⟩

/-! ## 5. Audit

Every theorem above, with its axiom footprint.  Expectations: only `propext`, `Classical.choice`
and `Quot.sound`. -/

#print axioms SpecialTransformations.Milestone0.SP.dclRV_subset_aclRV
#print axioms SpecialTransformations.Milestone0.SP.aclRV_self
#print axioms SpecialTransformations.Milestone0.SP.base_extendVFParam_acl
#print axioms SpecialTransformations.Milestone0.SP.base_extendRVParam_aclRV
#print axioms SpecialTransformations.Milestone0.SP.exchange_paper_VF
#print axioms SpecialTransformations.Milestone0.SP.exchange_paper_RV
#print axioms SpecialTransformations.Milestone0.SP.swapped_realize
#print axioms SpecialTransformations.Milestone0.SP.sortAssem_const
#print axioms SpecialTransformations.Milestone0.SP.swapped_wellSorted
#print axioms SpecialTransformations.Milestone0.SP.acl_of_swap_finite
#print axioms SpecialTransformations.Milestone0.SP.exchange_of_swap
#print axioms SpecialTransformations.Milestone0.SP.exchangeVF_of_swap
#print axioms SpecialTransformations.Milestone0.SP.swappedRV_realize
#print axioms SpecialTransformations.Milestone0.SP.swappedRV_wellSorted
#print axioms SpecialTransformations.Milestone0.SP.aclRV_of_swapRV_finite
#print axioms SpecialTransformations.Milestone0.SP.exchangeRV_of_swapRV
#print axioms SpecialTransformations.Milestone0.SP.exchangeRV_of_swapRV_monster
#print axioms SpecialTransformations.Milestone0.SP.exchange_of_swap_both

end SP

end SpecialTransformations.Milestone0
