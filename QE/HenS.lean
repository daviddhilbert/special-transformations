/-
# Section 6 of Yin, *Special transformations in algebraically closed valued fields*:
the theory `Hen_S(0,0)` of henselian fields of pure characteristic `0`, in the frozen `L_RV`
encoding.

Paper, §6 (`section:inter`):

> Let `Hen_S(0,0)` be the theory of henselian fields of pure characteristic `0` in a language
> `L_H` that expands `L_RV`, where the expansion happens only in the `RV`-sort.  Such a theory
> may be formulated as in Definition 2.2, with obvious modifications.  Note that `Hen_S(0,0)`
> includes the statement that the function `rv` is surjective.

Formalised here:

* `HenPaper` — Definition 2.2's axioms with the two *algebraic closedness* schemes removed and
  a henselian scheme put in place of the one on the `VF` sort; the divisibility of `RV^×` and
  of the residue field are dropped as well, because a henselian field of pure characteristic
  `0` need not have algebraically closed residue field nor divisible value group (`Q_p` is the
  standard witness).  Each modification is documented at the definition.
* `HenS` — `HenPaper` with the sort discipline of the encoding and pure characteristic `0`.
* `wss_henselScheme` — **every henselian axiom is a well-sorted sentence** of the paper's
  two-sorted `L_RV` in the sense of `LRV.WellSorted`, i.e. an honest `L_RV`-sentence and not
  a formula about junk values of the one-sorted carrier.
* `rvSurj_mem_HenS` — the paper's remark that `Hen_S(0,0)` contains the surjectivity of `rv`
  is realised: `Axioms.rvSurj ∈ HenS`.

The henselian scheme is Hensel's lemma in its standard form:

  for every `k ≥ 1`, for all `a₀,…,a_{k-1}, b ∈ VF` with `b ∈ 𝒪`,
  `v(f(b)) > 0` and `v(f'(b)) = 0`, where `f(X) = X^k + a_{k-1}X^{k-1} + ⋯ + a₀` and `f'`
  is its formal derivative, there is `x ∈ VF` with `f(x) = 0`.

`𝒪` is `rv⁻¹(RV^{≥1})` and the conditions on `v` are written in the paper's order on `RV`
(`t ≤ s ↔ vrv s ≤ vrv t`), so `b ∈ 𝒪` is `1 ≤ rv b`, `v(f(b)) > 0` is `rv (f b) < 1` and
`v(f'(b)) = 0` is `rv (f' b) = 1`.  Monic polynomials suffice for henselianity: an arbitrary
`f ∈ 𝒪[X]` with `f(b) ≡ 0` and `f'(b) ≢ 0 (mod 𝔪)` is replaced by its truncation at the last
unit coefficient, which agrees with `f` on `𝒪` modulo `𝔪` and has the same derivative there,
and then divided by its (unit) leading coefficient.
-/
import Enc
import SubstVar
open FirstOrder FirstOrder.Language

set_option linter.unusedVariables false

namespace SpecialTransformations.Milestone0
open LRV
open Sec4Compose

namespace M8Hen

/-! ## 1. Horner terms: the monic polynomial of degree `k` and its derivative -/

variable {α : Type} {n : ℕ}

/-- `+` of the `VF` sort at an arbitrary parameter type -/
abbrev hAdd (t u : LRV.Term (α ⊕ Fin n)) : LRV.Term (α ⊕ Fin n) := Term.func Fn.vfAdd ![t, u]

/-- `×` of the `VF` sort at an arbitrary parameter type -/
abbrev hMul (t u : LRV.Term (α ⊕ Fin n)) : LRV.Term (α ⊕ Fin n) := Term.func Fn.vfMul ![t, u]

/-- `1` of the `VF` sort at an arbitrary parameter type -/
abbrev hOne : LRV.Term (α ⊕ Fin n) := Term.func Fn.vfOne fun i => i.elim0

/-- Horner evaluation, from a list of coefficients:
`c₀ + c₁x + ⋯ + c_{m-1}x^{m-1} + x^m` for `c = [c₀,…,c_{m-1}]`. -/
def hornerEvalList (c : List (LRV.Term (α ⊕ Fin n))) (x : LRV.Term (α ⊕ Fin n)) :
    LRV.Term (α ⊕ Fin n) :=
  c.foldr (fun t acc => hAdd t (hMul x acc)) hOne

/-- Horner evaluation `c₀ + c₁x + ⋯ + c_{k-1}x^{k-1} + x^k` of the **monic** polynomial of
degree `k` with coefficients `c : Fin k → Tm n`, at the term `x`. -/
def hornerEval {k : ℕ} (c : Fin k → LRV.Term (α ⊕ Fin n)) (x : LRV.Term (α ⊕ Fin n)) :
    LRV.Term (α ⊕ Fin n) :=
  hornerEvalList ((List.finRange k).map c) x

/-- Every step of the Horner fold preserves the `VF` sort. -/
theorem tmSort_foldr_horner (sα : α → SortTag) {sn : Fin n → SortTag}
    {x : LRV.Term (α ⊕ Fin n)} (hx : TmSort sα sn x = some .vf) :
    ∀ (l : List (LRV.Term (α ⊕ Fin n))) (init : LRV.Term (α ⊕ Fin n)),
      TmSort sα sn init = some .vf → (∀ t ∈ l, TmSort sα sn t = some .vf) →
      TmSort sα sn (l.foldr (fun t acc => hAdd t (hMul x acc)) init) = some .vf := by
  intro l
  induction l with
  | nil => intro init h; simpa using h
  | cons a l ih =>
    intro init hinit hcl
    simp only [List.foldr_cons, hAdd, hMul, tmSort_vfAdd, tmSort_vfMul]
    exact ⟨hcl a (List.mem_cons_self ..), hx,
      ih init hinit (fun t ht => hcl t (List.mem_cons_of_mem _ ht))⟩

/-- A list of `VF`-terms gives a `VF`-valued Horner evaluation. -/
theorem tmSort_hornerEvalList (sα : α → SortTag) {sn : Fin n → SortTag}
    {c : List (LRV.Term (α ⊕ Fin n))} {x : LRV.Term (α ⊕ Fin n)}
    (hx : TmSort sα sn x = some .vf) (hc : ∀ t ∈ c, TmSort sα sn t = some .vf) :
    TmSort sα sn (hornerEvalList c x) = some .vf :=
  tmSort_foldr_horner sα hx c hOne (tmSort_vfOne sα sn) hc

/-- The monic polynomial of degree `k` in the coefficient terms `c` is a `VF`-term. -/
theorem tmSort_hornerEval {k : ℕ} (sα : α → SortTag) {sn : Fin n → SortTag}
    {c : Fin k → LRV.Term (α ⊕ Fin n)} {x : LRV.Term (α ⊕ Fin n)}
    (hx : TmSort sα sn x = some .vf) (hc : ∀ i, TmSort sα sn (c i) = some .vf) :
    TmSort sα sn (hornerEval c x) = some .vf :=
  tmSort_hornerEvalList sα hx (fun t ht => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact hc i)

/-! ## 2. The henselian scheme

Everything in this section lives at the empty parameter type, i.e. in the sentences of `L_RV`. -/

/-- The coefficient variables `a₀,…,a_{k-1}` in the context `Fin m`, for `k ≤ m`. -/
def coefVar (k m : ℕ) (h : k ≤ m) : Fin k → LRV.Term (Empty ⊕ Fin m) :=
  fun i => Term.var (Sum.inr ⟨i.val, by omega⟩)

/-- The coefficient `j · a_j` of the formal derivative, for `j = 1, …, k-1`
(the leading term `k · 1` is the initial value of the Horner fold). -/
def derCoef (k m : ℕ) (h : k ≤ m) (j : Fin (k - 1)) : LRV.Term (Empty ⊕ Fin m) :=
  hMul (tVFNumeral (n := m) (j.val + 1)) (coefVar k m h ⟨j.val + 1, by omega⟩)

/-- The formal derivative `f'(x)` of the monic polynomial `f` of degree `k` with coefficients
`a₀,…,a_{k-1}`, evaluated at `x`:
`f'(x) = a₁ + 2a₂x + ⋯ + (k-1)a_{k-1}x^{k-2} + k x^{k-1}`. -/
def hornerDeriv (k m : ℕ) (h : k ≤ m) (x : LRV.Term (Empty ⊕ Fin m)) :
    LRV.Term (Empty ⊕ Fin m) :=
  ((List.finRange (k - 1)).map (derCoef k m h)).foldr
    (fun t acc => hAdd t (hMul x acc)) (tVFNumeral (n := m) k)

/-- `b`, the approximate root, is the variable of index `k` in the context `Fin (k+2)`. -/
def bVar (k : ℕ) : LRV.Term (Empty ⊕ Fin (k + 2)) := Term.var (Sum.inr ⟨k, by omega⟩)

/-- `f(b)`, where `f` is the monic polynomial of degree `k` in the variables `a₀,…,a_{k-1}`. -/
def fVal (k : ℕ) : LRV.Term (Empty ⊕ Fin (k + 2)) :=
  hornerEval (coefVar k (k + 2) (by omega)) (bVar k)

/-- `f'(b)`. -/
def fDerivVal (k : ℕ) : LRV.Term (Empty ⊕ Fin (k + 2)) :=
  hornerDeriv k (k + 2) (by omega) (bVar k)

/-- **The hypothesis of Hensel's lemma**: `b ∈ 𝒪`, `v(f(b)) > 0` and `v(f'(b)) = 0`,
in the paper's order on `RV`. -/
def henselHyp (k : ℕ) : Bf (k + 2) :=
  (pLe tRVOne (tRv (bVar k)) ⊓
      (pLe (tRv (fVal k)) tRVOne ⊓ ∼(pEq (tRv (fVal k)) tRVOne))) ⊓
    pEq (tRv (fDerivVal k)) tRVOne

/-- The conclusion of Hensel's lemma: `f` has a root in `VF`. -/
def henselRoot (k : ℕ) : Bf (k + 3) :=
  pEq (hornerEval (coefVar k (k + 3) (by omega))
    (Term.var (Sum.inr ⟨k + 2, by omega⟩))) tVFZero

/-- **Hensel's lemma**, as a sentence of `L_RV`, for monic polynomials of degree `k ≥ 1`. -/
def henselScheme (k : ℕ) : LRV.Sentence :=
  allSorted (fun _ : Fin (k + 2) => SortTag.vf) (henselHyp k ⟹ exSorted .vf (henselRoot k))

/-! ### 2.1 The henselian axioms are well-sorted sentences of `L_RV` -/

variable {m : ℕ}

theorem tmSort_coefVar (sα : Empty → SortTag) {ss : Fin m → SortTag}
    (hss : ∀ i, ss i = .vf) (k : ℕ) (h : k ≤ m) (i : Fin k) :
    TmSort sα ss (coefVar k m h i) = some .vf := by
  rw [coefVar, tmSort_var_inr, hss]

theorem tmSort_derCoef (sα : Empty → SortTag) {ss : Fin m → SortTag}
    (hss : ∀ i, ss i = .vf) (k : ℕ) (h : k ≤ m) (j : Fin (k - 1)) :
    TmSort sα ss (derCoef k m h j) = some .vf := by
  rw [derCoef, hMul, tmSort_vfMul]
  exact ⟨tmSort_tVFNumeral sα ss _, tmSort_coefVar sα hss k h _⟩

theorem tmSort_bVar (sα : Empty → SortTag) {ss : Fin (k + 2) → SortTag}
    (hss : ∀ i, ss i = .vf) : TmSort sα ss (bVar k) = some .vf := by
  rw [bVar, tmSort_var_inr, hss]

theorem tmSort_fVal (sα : Empty → SortTag) {ss : Fin (k + 2) → SortTag} (hss : ∀ i, ss i = .vf) :
    TmSort sα ss (fVal k) = some .vf :=
  tmSort_hornerEval sα (tmSort_bVar sα hss) (fun i => tmSort_coefVar sα hss k _ i)

theorem tmSort_fDerivVal (sα : Empty → SortTag) {ss : Fin (k + 2) → SortTag}
    (hss : ∀ i, ss i = .vf) : TmSort sα ss (fDerivVal k) = some .vf := by
  rw [fDerivVal, hornerDeriv]
  refine tmSort_foldr_horner sα (tmSort_bVar sα hss) _ _
    (tmSort_tVFNumeral sα ss _) ?_
  intro t ht
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
  exact tmSort_derCoef sα hss k (by omega) j

theorem tmSort_rv_fVal (sα : Empty → SortTag) {ss : Fin (k + 2) → SortTag}
    (hss : ∀ i, ss i = .vf) : TmSort sα ss (tRv (fVal k)) = some .rv := by
  rw [tRv, tmSort_tRv]
  exact tmSort_fVal sα hss

theorem tmSort_rv_fDerivVal (sα : Empty → SortTag) {ss : Fin (k + 2) → SortTag}
    (hss : ∀ i, ss i = .vf) : TmSort sα ss (tRv (fDerivVal k)) = some .rv := by
  rw [tRv, tmSort_tRv]
  exact tmSort_fDerivVal sα hss

theorem tmSort_rv_bVar (sα : Empty → SortTag) {ss : Fin (k + 2) → SortTag}
    (hss : ∀ i, ss i = .vf) : TmSort sα ss (tRv (bVar k)) = some .rv := by
  rw [tRv, tmSort_tRv]
  exact tmSort_bVar sα hss

/-- The hypothesis of Hensel's lemma is a well-sorted formula. -/
theorem wellSorted_henselHyp (k : ℕ) :
    WellSorted (fun i : Empty => Empty.elim i) (fun _ : Fin (k + 2) => SortTag.vf)
      (henselHyp k) := by
  have hss : ∀ i : Fin (k + 2), (fun _ : Fin (k + 2) => SortTag.vf) i = SortTag.vf :=
    fun _ => rfl
  have h1 : ∀ i : Fin (k + 2), (fun _ : Fin (k + 2) => SortTag.vf) i = SortTag.vf := hss
  unfold henselHyp
  refine wellSorted_inf _ _ ?_ ?_
  · refine wellSorted_inf _ _ ?_ ?_
    · exact wellSorted_pLeG _ _ (tmSort_rvOne _ _) (tmSort_rv_bVar _ h1)
    · refine wellSorted_inf _ _ ?_ ?_
      · exact wellSorted_pLeG _ _ (tmSort_rv_fVal _ h1) (tmSort_rvOne _ _)
      · exact wellSorted_not _ _ (wellSorted_pEqG _ _ (tmSort_rv_fVal _ h1) (tmSort_rvOne _ _))
  · exact wellSorted_pEqG _ _ (tmSort_rv_fDerivVal _ h1) (tmSort_rvOne _ _)

/-- The conclusion of Hensel's lemma is a well-sorted formula in the extended context. -/
theorem wellSorted_henselRoot (k : ℕ) :
    WellSorted (fun i : Empty => Empty.elim i)
      (fun _ : Fin (k + 3) => SortTag.vf) (henselRoot k) := by
  have hss : ∀ i : Fin (k + 3), (fun _ : Fin (k + 3) => SortTag.vf) i = SortTag.vf :=
    fun _ => rfl
  unfold henselRoot
  refine wellSorted_pEqG _ _ ?_ (tmSort_vfZero _ _)
  refine tmSort_hornerEval _ ?_ (fun i => tmSort_coefVar _ hss k _ i)
  simp [tmSort_var_inr]

/-- **Every henselian axiom is a well-sorted sentence of the paper's `L_RV`.** -/
theorem wss_henselScheme (k : ℕ) : Audit.WSSent (henselScheme k) := by
  unfold henselScheme
  refine wellSorted_allSorted (fun _ : Fin (k + 2) => SortTag.vf) ?_
  refine WellSorted.imp _ (wellSorted_henselHyp k) ?_
  have hsn : (Fin.snoc (fun _ : Fin (k + 2) => SortTag.vf) SortTag.vf) =
      (fun _ : Fin (k + 3) => SortTag.vf) := Audit.snoc_const_vf (k + 2)
  exact wellSorted_exSorted (sα := fun i : Empty => Empty.elim i)
    (ss := fun _ : Fin (k + 2) => SortTag.vf) (s := SortTag.vf)
    (by rw [hsn]; exact wellSorted_henselRoot k)

/-! ## 3. The theory `Hen_S(0,0)` -/

open Axioms

/-- Definition 2.2 item 2 **without divisibility**: `(RV^×, 1, ×)` is an abelian group,
augmented by the absorbing `0 = ∞ = rv 0`.  Divisibility is dropped for `Hen_S(0,0)`: a
henselian field of pure characteristic `0` may have value group `Z` (e.g. `Q_p`). -/
def rvGroupCore : LRV.Theory :=
  ofList [rvOneMem, rvMulMem, rvMulAssoc, rvMulComm, rvMulOne, rvMulInv, rvMulZeroK, rvMulInfty]

/-- **Henselianity of the valued field**, as an `L_RV`-theory: one sentence
(`henselScheme k`) for each degree `k ≥ 1`. -/
def vfHenselian : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = henselScheme k}

/-- **Definition 2.2 "with obvious modifications"** (paper, §6): the axioms of `ACVF(0,0)`
that are not algebraic closedness, with

* `vfAlgClosed` (algebraic closedness of `VF`) replaced by `vfHenselian`;
* `kAlgClosed` (algebraic closedness of the residue field `K`) dropped — a henselian field of
  pure characteristic `0` has no reason to have algebraically closed residue field;
* the divisibility of `RV^×` / of `Γ` dropped (`rvGroupCore` instead of `rvGroup`) — same
  reason.

Everything else of Definition 2.2 is kept: the field axioms on `VF` (`vfField`), the field
axioms on `K` (`kField`), the preorder on `RV` (`preorderRV`), the axioms of `rv`
(`rvAxioms`, which include `rvSurj`, the surjectivity the paper singles out), and the repair
sentences `repairRV` of the encoding. -/
def HenPaper : LRV.Theory :=
  vfField ∪ vfHenselian ∪ rvGroupCore ∪ kField ∪ preorderRV ∪ rvAxioms ∪ repairRV

/-- **The theory `Hen_S(0,0)`** of the paper, §6: henselian fields of pure characteristic `0`
in `L_RV`, i.e. `HenPaper` together with the sort discipline of the encoding and pure
characteristic `0` (characteristic `0` of `VF` and of its residue field). -/
def HenS : LRV.Theory :=
  sortAxioms ∪ HenPaper ∪ {s | ∃ k, s = charZeroVF k} ∪
    {s | ∃ p, p.Prime ∧ s = residueCharZero p}

/-- Every axiom of `HenPaper` is an axiom of `HenS`. -/
theorem mem_HenS_of_mem_HenPaper {s : LRV.Sentence} (h : s ∈ HenPaper) : s ∈ HenS := by
  unfold HenS
  simp only [Set.mem_union]
  tauto

/-- The henselian scheme is an axiom of `Hen_S(0,0)`. -/
theorem henselScheme_mem_HenS {k : ℕ} (hk : 1 ≤ k) : henselScheme k ∈ HenS :=
  mem_HenS_of_mem_HenPaper
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))))))

/-- **`Hen_S(0,0)` includes the statement that `rv` is surjective** — the paper's own remark
after the definition. -/
theorem rvSurj_mem_HenS : rvSurj ∈ HenS := by
  refine mem_HenS_of_mem_HenPaper (Or.inl (Or.inr ?_))
  unfold rvAxioms ofList
  simp

/-- `Hen_S(0,0)` has pure characteristic `0`: characteristic `0` of `VF`. -/
theorem charZero_mem_HenS (k : ℕ) : charZeroVF k ∈ HenS :=
  Or.inl (Or.inr ⟨k, rfl⟩)

/-- `Hen_S(0,0)` has pure characteristic `0`: characteristic `0` of the residue field. -/
theorem residueCharZero_mem_HenS {p : ℕ} (hp : p.Prime) : residueCharZero p ∈ HenS :=
  Or.inr ⟨p, hp, rfl⟩

/-- The henselian scheme is a subset of `Hen_S(0,0)`, sentence by sentence, and each of its
sentences is well-sorted (`wss_henselScheme`).  (That algebraic closedness of `VF` is *absent*
from `HenS` is not asserted here: it would need injectivity of the sentence constructors.) -/
theorem vfHenselian_subset : vfHenselian ⊆ HenS := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := hs
  exact henselScheme_mem_HenS hk

/-! ## 4. `VF`-quantifier-free formulas

The paper's §6 lemma is about `VF`-quantifier-free `L_H`-formulas: in the encoding,
`WellSorted` records the sort of each quantifier only implicitly (it is the `s` of the
`WellSorted.all` constructor), so the syntactic class "no quantifier over a `VF`-variable"
needs its own predicate.  `VFQF` below is that predicate: it is `WellSorted` with the sort of
every quantifier remembered and required to be `≠ .vf`.

This is what makes "`φ` has no `VF`-quantifier" a statement about the *paper's* two-sorted
language rather than about the encoding's one-sorted carrier: `VFQF` is closed under
sort-preserving substitution of free variables, which is the operation the QE proof performs
when it replaces the terms `rv (F_i(X̄))` by new `RV`-variables. -/

/-- **`VFQF sα sn φ`**: `φ` is a *`VF`-quantifier-free* formula of the paper's two-sorted
`L_RV`, with the free parameters `a : α` of sort `sα a` and the free variables of sort `sn`:
it is well-sorted, and every quantifier in it binds a variable of a sort other than `VF`. -/
inductive VFQF {α : Type} (sα : α → SortTag) : {n : ℕ} → (Fin n → SortTag) →
    LRV.BoundedFormula α n → Prop
  /-- `⊥` -/
  | falsum {n : ℕ} (sn : Fin n → SortTag) : VFQF sα sn .falsum
  /-- `t = u` between terms of one sort -/
  | equal {n : ℕ} (sn : Fin n → SortTag) {t u : LRV.Term (α ⊕ Fin n)} {s : SortTag}
      (ht : TmSort sα sn t = some s) (hu : TmSort sα sn u = some s) :
      VFQF sα sn (.equal t u)
  /-- a relation of `L_RV` applied to terms of its declared sorts -/
  | rel {n l : ℕ} (sn : Fin n → SortTag) (R : Rel l) (ts : Fin l → LRV.Term (α ⊕ Fin n))
      (h : ∀ i, TmSort sα sn (ts i) = some (Rel.argSort R i)) :
      VFQF sα sn (.rel R ts)
  /-- implication -/
  | imp {n : ℕ} (sn : Fin n → SortTag) {a b : LRV.BoundedFormula α n} :
      VFQF sα sn a → VFQF sα sn b → VFQF sα sn (.imp a b)
  /-- a guarded quantifier over a variable **of a sort other than `VF`** -/
  | all {n : ℕ} (sn : Fin n → SortTag) {s : SortTag} (hs : s ≠ .vf)
      {χ : LRV.BoundedFormula α (n + 1)} (hχ : VFQF sα (Fin.snoc sn s) χ)
      (hg : GuardsLast s (Fin.last n) χ) (hj : GuardTrue s (Fin.last n) χ) :
      VFQF sα sn (.all χ)

/-- **`VF`-quantifier-free implies well-sorted.** -/
theorem VFQF.toWellSorted {α : Type} {sα : α → SortTag} :
    ∀ {n : ℕ} {sn : Fin n → SortTag} {φ : LRV.BoundedFormula α n},
      VFQF sα sn φ → WellSorted sα sn φ
  | _, _, _, .falsum sn => WellSorted.falsum sn
  | _, _, _, .equal sn ht hu => WellSorted.equal sn ht hu
  | _, _, _, .rel sn R ts h => WellSorted.rel sn R ts h
  | _, _, _, .imp sn ha hb => WellSorted.imp sn ha.toWellSorted hb.toWellSorted
  | _, _, _, .all sn _ hχ hg hj =>
    WellSorted.all sn hχ.toWellSorted hg hj

/-- **`VF`-quantifier-freeness is preserved by a sort-preserving substitution of free
variables.** -/
theorem VFQF.substVar {α : Type} {sα : α → SortTag} :
    ∀ {n : ℕ} {sn : Fin n → SortTag} {φ : LRV.BoundedFormula α n}, VFQF sα sn φ →
      ∀ {m : ℕ} {sm : Fin m → SortTag} {σ : Fin n → LRV.Term (α ⊕ Fin m)},
        (∀ i, TmSort sα sm (σ i) = some (sn i)) →
        VFQF sα sm (BoundedFormula.substVar σ φ)
  | _, _, _, .falsum sn, _, sm, _, _ => VFQF.falsum sm
  | _, _, _, .equal sn ht hu, _, sm, σ, hσ =>
    VFQF.equal sm (by rw [tmSort_substVar sα hσ]; exact ht)
      (by rw [tmSort_substVar sα hσ]; exact hu)
  | _, _, _, .rel sn R ts hts, _, sm, σ, hσ =>
    VFQF.rel sm R (fun i => Term.substVar σ (ts i))
      (fun i => by rw [tmSort_substVar sα hσ (ts i), hts i])
  | _, _, _, .imp sn ha hb, _, sm, σ, hσ =>
    BoundedFormula.substVar_imp σ _ _ ▸ VFQF.imp sm (ha.substVar hσ) (hb.substVar hσ)
  | _, _, _, .all sn hs hχ hg hj, _, sm, σ, hσ =>
    VFQF.all sm hs (hχ.substVar (tmSort_lift sα hσ _))
      (guardsLast_substVar _ (Subst.lift_last σ) hg)
      (guardTrue_substVar _ (Subst.lift_last σ) hj)

/-- `VF`-quantifier-freeness is closed under conjunction. -/
theorem VFQF.inf {α : Type} {sα : α → SortTag} {n : ℕ} {sn : Fin n → SortTag}
    {a b : LRV.BoundedFormula α n} (ha : VFQF sα sn a) (hb : VFQF sα sn b) :
    VFQF sα sn (a ⊓ b) :=
  VFQF.imp sn (VFQF.imp sn ha (VFQF.imp sn hb (VFQF.falsum sn))) (VFQF.falsum sn)

/-- `VF`-quantifier-freeness is closed under negation (`∼a` is `a ⟹ ⊥`). -/
theorem VFQF.not {α : Type} {sα : α → SortTag} {n : ℕ} {sn : Fin n → SortTag}
    {a : LRV.BoundedFormula α n} (ha : VFQF sα sn a) : VFQF sα sn (∼a) :=
  VFQF.imp sn ha (VFQF.falsum sn)

/-- `VF`-quantifier-freeness is closed under disjunction (`a ⊔ b` is `∼a ⟹ b`). -/
theorem VFQF.sup {α : Type} {sα : α → SortTag} {n : ℕ} {sn : Fin n → SortTag}
    {a b : LRV.BoundedFormula α n} (ha : VFQF sα sn a) (hb : VFQF sα sn b) :
    VFQF sα sn (a ⊔ b) :=
  VFQF.imp sn (VFQF.not ha) hb

/-! ## 5. Axiom audit -/

#print axioms VFQF.toWellSorted
#print axioms VFQF.substVar
#print axioms wellSorted_henselHyp
#print axioms wss_henselScheme
#print axioms henselScheme_mem_HenS
#print axioms rvSurj_mem_HenS


/-! ## 6. The shape of the §6 quantifier-elimination lemma

The paper's lemma (§6, the unlabelled lemma after `cut:to:hensel:substru`):

> Let `φ(X̄)` be a `VF`-quantifier-free `L_H`-formula, where `X̄ = (X₁, …, Xₙ)` are the free
> `VF`-sort variables.  Then `Hen_S(0,0)` proves that `∃X̄ φ(X̄)` is equivalent to a
> `VF`-quantifier-free `L_H`-formula.

`Hen_S(0,0)` is `HenS` above, and "`VF`-quantifier-free" is `VFQF` above; the `L_H`-expansion
is *not* modelled here (this file stays in `L_RV`), which is the honest restriction: any
expansion by relation symbols on the `RV` sort only adds formulas whose atoms are
`RV`-sorted, and `VFQF` is already closed under those as atoms (they are `VFQF.rel` at a
relation with `Rel.argSort ≡ .rv`).  The statement below is the paper's lemma for `L_RV`. -/

/-- `∃X̄ φ`: the `VF`-variables of the context, bound one after the other. -/
def exVFAll : (n : ℕ) → Bf n → LRV.Sentence
  | 0, φ => φ
  | (k + 1), φ => exVFAll k (exSorted .vf φ)

/-- **The conclusion of the §6 lemma**, as a property of a theory: every `VF`-quantifier-free
formula `φ(X̄)` whose free variables are all of the `VF` sort has `∃X̄ φ` equivalent, modulo
`T`, to a `VF`-quantifier-free sentence.

This is a `def`, not a theorem: the paper's proof needs Theorem 5.5
(`special:bi:polynomial:constant`) and Lemma `cut:to:hensel:substru`, neither of which is
available in this file.  What is available is everything the *statement* is made of: the
theory `HenS`, the syntactic class `VFQF` with `VFQF.toWellSorted` and closure under
sort-preserving substitution `VFQF.substVar`, and the iterated guarded existential `exVFAll`.
The paper's lemma is `HasVFElimination HenS`. -/
def HasVFElimination (T : LRV.Theory) : Prop :=
  ∀ (n : ℕ) (φ : Bf n),
    VFQF (fun i : Empty => Empty.elim i) (fun _ : Fin n => SortTag.vf) φ →
      ∃ ψ : LRV.Sentence,
        VFQF (fun i : Empty => Empty.elim i) (fun i : Fin 0 => i.elim0) ψ ∧
          ∀ (M : Type) [LRV.Structure M], M ⊨ T → ((M ⊨ exVFAll n φ) ↔ (M ⊨ ψ))

end M8Hen
end SpecialTransformations.Milestone0
