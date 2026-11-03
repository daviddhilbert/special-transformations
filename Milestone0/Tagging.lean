import Mathlib

set_option linter.checkUnivs false
set_option warn.classDefReducibility false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# A many-sorted first-order syntax, and its faithful encoding in Mathlib's one-sorted
framework

Reference for the application: Yimu Yin, *Special transformations in algebraically closed
valued fields*, arXiv:1006.2467, Definition 2.1 (the two-sorted language `L_RV`).

Stage 1: many-sorted syntax and Tarski semantics.
Stage 2: the *tagged* one-sorted language and structure.
Stage 3: term faithfulness.
Stage 4: formula faithfulness.
-/

universe u u1 v w

namespace ManySorted

/-! ## Stage 1: many-sorted syntax and semantics -/

/-- A many-sorted (first-order) signature: a type of sorts, function symbols with an
arity (a finite set of argument sorts) and a value sort, and relation symbols with an
arity. -/
structure MSig where
  Srt : Type u
  Func : (k : ℕ) → (Fin k → Srt) → Srt → Type u1
  Rel : (k : ℕ) → (Fin k → Srt) → Type u1

/-- A structure for a many-sorted signature: a carrier for each sort, and an
interpretation of every function and relation symbol. -/
structure MStruct (L : MSig.{u, u1}) where
  Carrier : L.Srt → Type v
  funMap : ∀ {k : ℕ} {σ : Fin k → L.Srt} {s : L.Srt}, L.Func k σ s →
    ((i : Fin k) → Carrier (σ i)) → Carrier s
  relMap : ∀ {k : ℕ} {σ : Fin k → L.Srt}, L.Rel k σ →
    ((i : Fin k) → Carrier (σ i)) → Prop

variable (L : MSig.{u, u1})

/-- The context obtained by adding a fresh variable of sort `s` at the end of `τ`, the
de Bruijn convention of `FirstOrder.Language.BoundedFormula`. -/
def ctxSnoc {n : ℕ} (τ : Fin n → L.Srt) (s : L.Srt) : Fin (n + 1) → L.Srt :=
  Fin.snoc (α := fun _ => L.Srt) τ s

@[simp] theorem ctxSnoc_castSucc {n : ℕ} (τ : Fin n → L.Srt) (s : L.Srt) (j : Fin n) :
    ctxSnoc L τ s j.castSucc = τ j := by
  simp [ctxSnoc]

@[simp] theorem ctxSnoc_last {n : ℕ} (τ : Fin n → L.Srt) (s : L.Srt) :
    ctxSnoc L τ s (Fin.last n) = s := by
  simp [ctxSnoc]

/-- Many-sorted terms over the sort-indexed free-variable family `V`, with bound
variables from the sort-indexed context `τ : Fin n → L.Srt`.  Each term carries its
sort as an index, so well-sortedness (e.g. `rv` applied to a `VF`-term) is enforced by
the type theory and needs no side conditions. -/
inductive MTerm (V : L.Srt → Type w) {n : ℕ} (τ : Fin n → L.Srt) :
    L.Srt → Type (max (u + 1) u1 w) where
  /-- A free variable of sort `s`. -/
  | var {s : L.Srt} (a : V s) : MTerm V τ s
  /-- The `i`-th bound variable, of the sort that the context assigns to `i`. -/
  | bvar (i : Fin n) : MTerm V τ (τ i)
  /-- A function symbol applied to terms of the correct argument sorts. -/
  | func {k : ℕ} {σ : Fin k → L.Srt} {s : L.Srt} (f : L.Func k σ s)
      (ts : (i : Fin k) → MTerm V τ (σ i)) : MTerm V τ s

namespace MTerm

variable {L : MSig.{u, u1}} {V : L.Srt → Type w} {M : MStruct L}

/-- Evaluation of a many-sorted term.  The types force every application of a function
symbol to be on-sort, so no junk values are needed. -/
def eval (v : (s : L.Srt) → V s → M.Carrier s) {n : ℕ} {τ : Fin n → L.Srt}
    (xs : (i : Fin n) → M.Carrier (τ i)) : {s : L.Srt} → MTerm L V τ s → M.Carrier s
  | _, var a => v _ a
  | _, bvar i => xs i
  | _, func f ts => M.funMap f fun i => eval v xs (ts i)

end MTerm

/-- Many-sorted formulas.  Quantification appends a fresh variable of a prescribed sort
at the end of the context, mirroring the de Bruijn convention of
`FirstOrder.Language.BoundedFormula`. -/
inductive BForm (V : L.Srt → Type w) : (n : ℕ) → (Fin n → L.Srt) → Type (max (u + 1) u1 w) where
  | falsum {n : ℕ} {τ : Fin n → L.Srt} : BForm V n τ
  | equal {n : ℕ} {τ : Fin n → L.Srt} {s : L.Srt} (t₁ t₂ : MTerm L V τ s) : BForm V n τ
  | rel {n : ℕ} {τ : Fin n → L.Srt} {k : ℕ} {σ : Fin k → L.Srt} (R : L.Rel k σ)
      (ts : (i : Fin k) → MTerm L V τ (σ i)) : BForm V n τ
  | imp {n : ℕ} {τ : Fin n → L.Srt} (φ ψ : BForm V n τ) : BForm V n τ
  | all {n : ℕ} {τ : Fin n → L.Srt} {s : L.Srt}
      (φ : BForm V (n + 1) (ctxSnoc L τ s)) : BForm V n τ

namespace BForm

variable {L : MSig.{u, u1}} {V : L.Srt → Type w} {M : MStruct L}

/-- Extend a context assignment by a value of sort `s` for the fresh (last) variable.
The two `Fin.snoc` computation lemmas are propositional, not definitional, so the
transport has to be written out. -/
def snocA {n : ℕ} {τ : Fin n → L.Srt} {s : L.Srt}
    (xs : (i : Fin n) → M.Carrier (τ i)) (x : M.Carrier s) :
    (i : Fin (n + 1)) → M.Carrier (ctxSnoc L τ s i) :=
  Fin.snoc (α := fun i => M.Carrier (ctxSnoc L τ s i))
    (fun j => (ctxSnoc_castSucc L τ s j).symm ▸ xs j)
    ((ctxSnoc_last L τ s).symm ▸ x)

@[simp] theorem snocA_castSucc {n : ℕ} {τ : Fin n → L.Srt} {s : L.Srt}
    (xs : (i : Fin n) → M.Carrier (τ i)) (x : M.Carrier s) (j : Fin n) :
    snocA xs x j.castSucc = (ctxSnoc_castSucc L τ s j).symm ▸ xs j := by
  simp [snocA]

@[simp] theorem snocA_last {n : ℕ} {τ : Fin n → L.Srt} {s : L.Srt}
    (xs : (i : Fin n) → M.Carrier (τ i)) (x : M.Carrier s) :
    snocA xs x (Fin.last n) = (ctxSnoc_last L τ s).symm ▸ x := by
  simp [snocA]

/-- Tarski satisfaction for many-sorted formulas. -/
def Realize (M : MStruct L) (v : (s : L.Srt) → V s → M.Carrier s) :
    {n : ℕ} → {τ : Fin n → L.Srt} → BForm L V n τ → ((i : Fin n) → M.Carrier (τ i)) → Prop
  | _, _, falsum, _ => False
  | _, _, equal t₁ t₂, xs => MTerm.eval v xs t₁ = MTerm.eval v xs t₂
  | _, _, rel R ts, xs => M.relMap R fun i => MTerm.eval v xs (ts i)
  | _, _, imp φ ψ, xs => Realize M v φ xs → Realize M v ψ xs
  | _, _, all (s := s) φ, xs => ∀ x : M.Carrier s, Realize M v φ (snocA xs x)

end BForm

/-! ## Stage 2: the tagged one-sorted language and structure -/

open FirstOrder

/-- The unary sort predicates of the tagged language. -/
inductive SortRel (L : MSig.{u, u1}) : ℕ → Type (max u u1) where
  | mk (s : L.Srt) {n : ℕ} (h : n = 1) : SortRel L n

/-- The one-sorted language obtained by collapsing all sorts of `L` into a single
carrier `Σ s, M s`: one `n`-ary function symbol per many-sorted `n`-ary function
symbol, one `n`-ary relation symbol per many-sorted `n`-ary relation symbol, and one
unary *sort predicate* per sort. -/
def toLang (L : MSig.{u, u1}) : FirstOrder.Language.{max u u1, max u u1} where
  Functions n := Σ (σ : Fin n → L.Srt) (s : L.Srt), L.Func n σ s
  Relations n := (Σ (σ : Fin n → L.Srt), L.Rel n σ) ⊕ SortRel L n

variable {L : MSig.{u, u1}} {V : L.Srt → Type w} {M : MStruct L}

/-- Interpretation of a tagged function symbol, as a plain function (so that its
computation rule is an ordinary `dif_pos` rewrite). -/
noncomputable def tagFun (hne : ∀ s, Nonempty (M.Carrier s)) {k : ℕ} {σ : Fin k → L.Srt}
    {s : L.Srt} (g : L.Func k σ s) (xs : Fin k → Σ t, M.Carrier t) : Σ t, M.Carrier t := by
  classical
  exact if h : ∀ i : Fin k, (xs i).1 = σ i then ⟨s, M.funMap g fun i => (h i) ▸ (xs i).2⟩
    else ⟨s, Classical.choice (hne s)⟩

/-- Interpretation of a tagged relation symbol. -/
noncomputable def tagRel {k : ℕ} {σ : Fin k → L.Srt} (r : L.Rel k σ)
    (xs : Fin k → Σ t, M.Carrier t) : Prop := by
  classical
  exact if h : ∀ i : Fin k, (xs i).1 = σ i then M.relMap r fun i => (h i) ▸ (xs i).2 else False

/-- The tagged structure on the disjoint union `Σ s, M s` of the carriers.  A function
symbol applied to a tuple that is *not* on-sort returns a junk value (the paper's sorts
are all inhabited: `0 ∈ VF`, `0, ∞ ∈ RV`, `0 ∈ Γ`); a relation symbol applied to an
off-sort tuple is false. -/
noncomputable def tagStruct (M : MStruct L) (hne : ∀ s, Nonempty (M.Carrier s)) :
    (toLang L).Structure (Σ s, M.Carrier s) where
  funMap := fun {n} f xs =>
    match f with
    | ⟨σ, s, g⟩ => tagFun hne g xs
  RelMap := fun {n} R xs =>
    match R with
    | Sum.inl ⟨σ, r⟩ => tagRel r xs
    | Sum.inr (SortRel.mk s h) => (xs (Fin.cast h.symm 0)).1 = s

/-- The tagged structure as a global instance, so that Mathlib's `Term.realize` and
`BoundedFormula.Realize` can be used without instance plumbing. -/
noncomputable instance instTagStruct (M : MStruct L) [hne : ∀ s, Nonempty (M.Carrier s)] :
    (toLang L).Structure (Σ s, M.Carrier s) :=
  tagStruct M hne

/-- On an on-sort tuple the tagged interpretation of a function symbol is the
many-sorted one; the junk case is never taken. -/
theorem tagFun_apply (hne : ∀ s, Nonempty (M.Carrier s)) {k : ℕ} {σ : Fin k → L.Srt}
    {s : L.Srt} (g : L.Func k σ s) (z : (i : Fin k) → M.Carrier (σ i)) :
    tagFun (M := M) hne g (fun i => ⟨σ i, z i⟩) = ⟨s, M.funMap g z⟩ := by
  unfold tagFun
  rw [dif_pos (fun i => rfl)]

theorem tagRel_apply {k : ℕ} {σ : Fin k → L.Srt} (r : L.Rel k σ)
    (z : (i : Fin k) → M.Carrier (σ i)) :
    tagRel (M := M) r (fun i => ⟨σ i, z i⟩) = M.relMap r z := by
  unfold tagRel
  rw [dif_pos (fun i => rfl)]

theorem tagStruct_funMap (hne : ∀ s, Nonempty (M.Carrier s)) {k : ℕ} {σ : Fin k → L.Srt}
    {s : L.Srt} (g : L.Func k σ s) (z : (i : Fin k) → M.Carrier (σ i)) :
    (tagStruct M hne).funMap ⟨σ, s, g⟩ (fun i => ⟨σ i, z i⟩) = ⟨s, M.funMap g z⟩ :=
  tagFun_apply hne g z

theorem tagStruct_relMap (hne : ∀ s, Nonempty (M.Carrier s)) {k : ℕ} {σ : Fin k → L.Srt}
    (r : L.Rel k σ) (z : (i : Fin k) → M.Carrier (σ i)) :
    (tagStruct M hne).RelMap (Sum.inl ⟨σ, r⟩) (fun i => ⟨σ i, z i⟩) = M.relMap r z :=
  tagRel_apply r z

theorem tagStruct_sortRel (hne : ∀ s, Nonempty (M.Carrier s)) {s t : L.Srt}
    (x : M.Carrier s) :
    (tagStruct M hne).RelMap (Sum.inr (SortRel.mk t rfl)) (fun _ : Fin 1 => ⟨s, x⟩) = (s = t) :=
  rfl

/-! ## Stage 3: term faithfulness -/

namespace MTerm

open FirstOrder

variable {L : MSig.{u, u1}} {V : L.Srt → Type w}

/-- The free-variable type of the tagged language: the disjoint union of the
many-sorted free-variable families. -/
abbrev TVar (V : L.Srt → Type w) := (Σ s : L.Srt, V s)

/-- Translation of a many-sorted term into the tagged one-sorted language: free
variables go to the injected variable, bound variables keep their de Bruijn index. -/
def translate {n : ℕ} {τ : Fin n → L.Srt} :
    {s : L.Srt} → MTerm L V τ s → (toLang L).Term (TVar V ⊕ Fin n)
  | _, var a => FirstOrder.Language.Term.var (Sum.inl ⟨_, a⟩)
  | _, bvar i => FirstOrder.Language.Term.var (Sum.inr i)
  | _, func f ts => FirstOrder.Language.Term.func ⟨_, _, f⟩ fun i => translate (ts i)

variable {M : MStruct L}

/-- The tagged assignment corresponding to a many-sorted free-variable assignment `v`
and a many-sorted context assignment `xs`. -/
abbrev tagAssign (v : (s : L.Srt) → V s → M.Carrier s) {n : ℕ} {τ : Fin n → L.Srt}
    (xs : (i : Fin n) → M.Carrier (τ i)) : TVar V ⊕ Fin n → (Σ s, M.Carrier s) :=
  Sum.elim (fun a => ⟨a.1, v a.1 a.2⟩) (fun i => ⟨τ i, xs i⟩)

/-- **Term faithfulness.**  A many-sorted term and its translation have the same value,
tagged with the term's sort.  The many-sorted side needs no junk values: well-sortedness
is enforced by the types. -/
theorem realize_translate [hne : ∀ s, Nonempty (M.Carrier s)]
    (v : (s : L.Srt) → V s → M.Carrier s) {n : ℕ} {τ : Fin n → L.Srt}
    (xs : (i : Fin n) → M.Carrier (τ i)) :
    ∀ {s : L.Srt} (t : MTerm L V τ s),
      FirstOrder.Language.Term.realize (tagAssign v xs) (translate t)
      = ⟨s, MTerm.eval v xs t⟩
  | _, var a => rfl
  | _, bvar i => rfl
  | _, func (σ := σ) (s := s) f ts => by
      simp only [translate, MTerm.eval, FirstOrder.Language.Term.realize,
        realize_translate v xs]
      simpa using tagStruct_funMap (hne := hne) f (fun i => MTerm.eval v xs (ts i))

end MTerm

/-! ## Stage 4: formula faithfulness -/

namespace BForm

open FirstOrder FirstOrder.Language

section Faithful

variable {L : MSig.{u, u1}} {V : L.Srt → Type w} {M : MStruct L}

/-- The free-variable tagging map of the one-sorted language. -/
abbrev tagFree (v : (s : L.Srt) → V s → M.Carrier s) : MTerm.TVar V → (Σ s, M.Carrier s) :=
  fun a => ⟨a.1, v a.1 a.2⟩

/-- A many-sorted context assignment, viewed as an assignment in the tagged language. -/
abbrev sigA {n : ℕ} {τ : Fin n → L.Srt} (xs : (i : Fin n) → M.Carrier (τ i)) :
    Fin n → (Σ s, M.Carrier s) :=
  fun i => ⟨τ i, xs i⟩

/-- A universal quantification over a disjoint union, restricted to one summand by its
tag, is a universal quantification over that summand.  This is the semantic content of
the guarded quantifier that the tagging forces. -/
theorem forall_sigma_eq (C : L.Srt → Type v) (s : L.Srt) (P : (Σ t, C t) → Prop) :
    (∀ x : Σ t, C t, x.1 = s → P x) ↔ ∀ y : C s, P ⟨s, y⟩ := by
  constructor
  · intro h y; exact h ⟨s, y⟩ rfl
  · rintro h ⟨t, y⟩ rfl; exact h y

theorem sigma_mk_inj {s : L.Srt} (a b : M.Carrier s) :
    (⟨s, a⟩ : Σ t, M.Carrier t) = ⟨s, b⟩ ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; rfl

theorem sigma_mk_cast {a b : L.Srt} (h : a = b) (x : M.Carrier a) :
    (⟨a, x⟩ : Σ t, M.Carrier t) = ⟨b, h ▸ x⟩ := by
  cases h; rfl

theorem snoc_sigA {n : ℕ} {τ : Fin n → L.Srt} {s : L.Srt}
    (xs : (i : Fin n) → M.Carrier (τ i)) (y : M.Carrier s) :
    Fin.snoc (sigA xs) ⟨s, y⟩
      = fun i => (⟨ctxSnoc L τ s i, snocA xs y i⟩ : Σ t, M.Carrier t) := by
  funext i
  revert i
  refine Fin.lastCases ?_ ?_
  · rw [snocA_last, Fin.snoc_last]
    exact sigma_mk_cast (ctxSnoc_last L τ s).symm y
  · intro j
    rw [snocA_castSucc, Fin.snoc_castSucc]
    exact sigma_mk_cast (ctxSnoc_castSucc L τ s j).symm (xs j)

/-- Translation of many-sorted formulas into the tagged one-sorted language.  The
quantifier case is where the cost of the encoding is paid: quantification over sort `s`
becomes quantification over the whole disjoint union, guarded by the unary sort
predicate `s`. -/
def translate : {n : ℕ} → {τ : Fin n → L.Srt} → BForm L V n τ →
    (toLang L).BoundedFormula (MTerm.TVar V) n
  | _, _, falsum => BoundedFormula.falsum
  | _, _, equal t₁ t₂ =>
      BoundedFormula.equal (MTerm.translate t₁) (MTerm.translate t₂)
  | _, _, rel (σ := σ) R ts =>
      BoundedFormula.rel (Sum.inl ⟨σ, R⟩) (fun i => MTerm.translate (ts i))
  | _, _, imp φ ψ => BoundedFormula.imp (translate φ) (translate ψ)
  | _, _, all (s := s) φ =>
      BoundedFormula.all
        (BoundedFormula.imp
          (BoundedFormula.rel (Sum.inr (SortRel.mk s rfl) : (toLang L).Relations 1)
            (fun _ : Fin 1 => Term.var (Sum.inr (Fin.last _))))
          (translate φ))

/-- The instance form of the sort-predicate computation rule, for rewriting. -/
theorem RelMap_sortRel [hne : ∀ s, Nonempty (M.Carrier s)] {t : L.Srt}
    (z : Σ s, M.Carrier s) :
    Structure.RelMap (L := toLang L) (M := Σ s, M.Carrier s)
      (Sum.inr (SortRel.mk t rfl) : (toLang L).Relations 1) (fun _ : Fin 1 => z) = (z.1 = t) := by
  obtain ⟨u, x⟩ := z
  exact tagStruct_sortRel hne x

/-- The instance form of the relation-symbol computation rule, for rewriting. -/
theorem RelMap_inl [hne : ∀ s, Nonempty (M.Carrier s)] {k : ℕ} {σ : Fin k → L.Srt}
    (R : L.Rel k σ) (z : (i : Fin k) → M.Carrier (σ i)) :
    Structure.RelMap (L := toLang L) (M := Σ s, M.Carrier s)
      (Sum.inl (⟨σ, R⟩ : Σ σ : Fin k → L.Srt, L.Rel k σ))
      (fun i => (⟨σ i, z i⟩ : Σ s, M.Carrier s)) = M.relMap R z :=
  tagRel_apply R z

theorem tagAssign_eq (v : (s : L.Srt) → V s → M.Carrier s) {n : ℕ} {τ : Fin n → L.Srt}
    (xs : (i : Fin n) → M.Carrier (τ i)) :
    MTerm.tagAssign v xs = Sum.elim (tagFree v) (sigA xs) := rfl

/-- **Formula faithfulness.**  A many-sorted formula and its translation into the
tagged one-sorted language have the same truth value under corresponding assignments.
Consequently the tagging neither creates nor destroys definable sets: it is a faithful
encoding of the many-sorted language, not merely a syntactic hack. -/
theorem realize_translate [hne : ∀ s, Nonempty (M.Carrier s)]
    (v : (s : L.Srt) → V s → M.Carrier s) :
    {n : ℕ} → {τ : Fin n → L.Srt} → (φ : BForm L V n τ) →
      (xs : (i : Fin n) → M.Carrier (τ i)) →
      (translate φ).Realize (tagFree v) (sigA xs) ↔ Realize M v φ xs
  | _, _, falsum, xs => Iff.rfl
  | _, _, equal t₁ t₂, xs => by
      simp only [translate, Realize, BoundedFormula.Realize, tagAssign_eq, MTerm.realize_translate,
        sigma_mk_inj]
  | _, _, rel (σ := σ) R ts, xs => by
      simp only [translate, Realize, BoundedFormula.Realize, tagAssign_eq, MTerm.realize_translate,
        RelMap_inl]
  | _, _, imp φ ψ, xs => by
      simp only [translate, Realize, BoundedFormula.Realize, realize_translate v φ xs,
        realize_translate v ψ xs]
  | _, _, all (s := s) φ, xs => by
      simp only [translate, Realize, BoundedFormula.Realize, Term.realize_var, Sum.elim_inr,
        Fin.snoc_last, RelMap_sortRel]
      rw [forall_sigma_eq]
      refine forall_congr' fun y => ?_
      rw [snoc_sigA]
      exact realize_translate v φ (snocA xs y)

/-! ### Quantifier-free formulas and the transfer of quantifier elimination -/

/-- Quantifier-free many-sorted formulas. -/
def QF : {n : ℕ} → {τ : Fin n → L.Srt} → BForm L V n τ → Prop
  | _, _, falsum => True
  | _, _, equal _ _ => True
  | _, _, rel _ _ => True
  | _, _, imp φ ψ => φ.QF ∧ ψ.QF
  | _, _, all _ => False

/-- The translation of a quantifier-free many-sorted formula is quantifier-free. -/
@[simp] theorem translate_falsum {n : ℕ} {τ : Fin n → L.Srt} :
    translate (V := V) (BForm.falsum (n := n) (τ := τ)) = BoundedFormula.falsum := rfl

@[simp] theorem translate_equal {n : ℕ} {τ : Fin n → L.Srt} {s : L.Srt}
    (t₁ t₂ : MTerm L V τ s) :
    translate (BForm.equal t₁ t₂) = BoundedFormula.equal (MTerm.translate t₁) (MTerm.translate t₂) :=
  rfl

@[simp] theorem translate_rel {n : ℕ} {τ : Fin n → L.Srt} {k : ℕ} {σ : Fin k → L.Srt}
    (R : L.Rel k σ) (ts : (i : Fin k) → MTerm L V τ (σ i)) :
    translate (BForm.rel R ts) = BoundedFormula.rel (Sum.inl ⟨σ, R⟩) (fun i => MTerm.translate (ts i)) :=
  rfl

@[simp] theorem translate_imp {n : ℕ} {τ : Fin n → L.Srt} (φ ψ : BForm L V n τ) :
    translate (BForm.imp φ ψ) = BoundedFormula.imp (translate φ) (translate ψ) := rfl

theorem isQF_translate {n : ℕ} {τ : Fin n → L.Srt} (φ : BForm L V n τ) (h : φ.QF) :
    (translate φ).IsQF := by
  match φ with
  | falsum => exact BoundedFormula.IsQF.falsum
  | equal t₁ t₂ =>
      rw [translate_equal]
      exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.equal _ _)
  | rel R ts =>
      rw [translate_rel]
      exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  | imp φ ψ => exact BoundedFormula.IsQF.imp (isQF_translate φ h.1) (isQF_translate ψ h.2)
  | all φ => simp only [QF] at h

/-- Semantic quantifier elimination for a class of many-sorted structures: every
formula is equivalent, in every structure of the class and under every assignment, to a
quantifier-free formula with the same free variables. -/
def HasQE (T : MStruct L → Prop) (W : L.Srt → Type w) : Prop :=
  ∀ {n : ℕ} {τ : Fin n → L.Srt} (φ : BForm L W n τ),
    ∃ ψ : BForm L W n τ, ψ.QF ∧
      ∀ (M : MStruct L) [hne : ∀ s, Nonempty (M.Carrier s)], T M →
        ∀ (v : (s : L.Srt) → W s → M.Carrier s) (xs : (i : Fin n) → M.Carrier (τ i)),
          Realize M v φ xs ↔ Realize M v ψ xs

/-- **Quantifier elimination transfers to the tagged language.**  If every many-sorted
formula is equivalent to a quantifier-free one in every structure of a class, then the
same holds, under the same assignment correspondence, for the translated formulas in
the tagged one-sorted language.  This is the precise sense in which stating Theorem 2.3
in the tagged encoding is not weaker than stating it for `L_RV`. -/
theorem hasQE_transfer {T : MStruct L → Prop} {W : L.Srt → Type w} (h : HasQE T W) :
    ∀ {n : ℕ} {τ : Fin n → L.Srt} (φ : BForm L W n τ),
      ∃ ψ : BForm L W n τ, ψ.QF ∧ ∀ (M : MStruct L) [hne : ∀ s, Nonempty (M.Carrier s)],
        T M → ∀ (v : (s : L.Srt) → W s → M.Carrier s) (xs : (i : Fin n) → M.Carrier (τ i)),
          (translate φ).Realize (tagFree v) (sigA xs) ↔
            (translate ψ).Realize (tagFree v) (sigA xs) := by
  intro n τ φ
  obtain ⟨ψ, hQF, hψ⟩ := h φ
  exact ⟨ψ, hQF, fun M hne hT v xs => by
    rw [realize_translate v φ xs, realize_translate v ψ xs, @hψ M hne hT v xs]⟩

/-- A subset of one sort of a many-sorted structure is definable with parameters from
`W` if it is the set of values of one variable in a formula. -/
def Definable (M : MStruct L) (v : (t : L.Srt) → V t → M.Carrier t) {s : L.Srt}
    (A : Set (M.Carrier s)) : Prop :=
  ∃ (n : ℕ) (τ : Fin n → L.Srt) (φ : BForm L V (n + 1) (ctxSnoc L τ s))
    (xs : (i : Fin n) → M.Carrier (τ i)), A = {y | Realize M v φ (snocA xs y)}

/-- The same notion in the tagged one-sorted language: definable subsets of the
`s`-summand of the tagged carrier.  The guard `⟨s, y⟩` is where the sort predicate of the
tagging is used. -/
def DefinableTagged (M : MStruct L) [hne : ∀ s, Nonempty (M.Carrier s)]
    (v : (t : L.Srt) → V t → M.Carrier t) {s : L.Srt} (A : Set (M.Carrier s)) : Prop :=
  ∃ (n : ℕ) (τ : Fin n → L.Srt) (φ : BForm L V (n + 1) (ctxSnoc L τ s))
    (xs : (i : Fin n) → M.Carrier (τ i)),
    A = {y | (translate φ).Realize (tagFree v) (Fin.snoc (sigA xs) ⟨s, y⟩)}

/-- **Definability is invariant under the encoding.**  A subset of one sort is definable
in the many-sorted language if and only if its tagged version is definable in the
one-sorted tagged language.  This is the lemma on which later statements about
definable subsets of `VF^n × RV^m` rest. -/
theorem definable_iff (M : MStruct L) [hne : ∀ s, Nonempty (M.Carrier s)]
    (v : (t : L.Srt) → V t → M.Carrier t) {s : L.Srt} (A : Set (M.Carrier s)) :
    Definable M v A ↔ DefinableTagged M v A := by
  constructor
  · rintro ⟨n, τ, φ, xs, rfl⟩
    exact ⟨n, τ, φ, xs, Set.ext fun y => by
      simp only [Set.mem_ofPred_eq, snoc_sigA, realize_translate v φ (snocA xs y)]⟩
  · rintro ⟨n, τ, φ, xs, rfl⟩
    exact ⟨n, τ, φ, xs, Set.ext fun y => by
      simp only [Set.mem_ofPred_eq, snoc_sigA, realize_translate v φ (snocA xs y)]⟩

/-- Many-sorted sentences (empty context). -/
abbrev MSentence (L : MSig.{u, u1}) (V : L.Srt → Type w) := BForm L V 0 (Fin.elim0)

/-- **Sentence faithfulness.**  For sentences, truth in a many-sorted structure is
equivalent to truth of the translated sentence in the tagged one-sorted structure. -/
theorem realize_translate_sentence [hne : ∀ s, Nonempty (M.Carrier s)]
    (v : (s : L.Srt) → V s → M.Carrier s) (σ : MSentence L V) :
    (translate σ).Realize (tagFree v) (sigA (τ := Fin.elim0) (fun i : Fin 0 => Fin.elim0 i)) ↔
      Realize M v σ (fun i : Fin 0 => Fin.elim0 i) :=
  realize_translate v σ (fun i : Fin 0 => Fin.elim0 i)

end Faithful

end BForm

/-! ## The paper's language `L_RV` as an instance of the framework -/

/-- Definition 2.1: the sorts.  `VF` and `RV` are the two *syntactic* sorts of `L_RV`;
`G` is the value group, which the paper treats as an imaginary sort ("Semantically we
shall treat `Γ` as an imaginary sort and write `RV_Γ` for `RV ∪ Γ`.  However,
syntactically any reference to `Γ` may be eliminated"), but which is needed because `S`
is required to be `(VF, Γ)`-generated. -/
inductive LRVSort where
  | VF
  | RV
  | G
  deriving DecidableEq

/-- Definition 2.1: the function symbols of `L_RV`.
* `VF` sort: the language of rings `{0, 1, +, −, ×}`.
* `RV` sort: the group language `{1, ×}`, the constants `0` and `∞`, and the operations
  `+ : K × K → K`, `− : K → K` (total on `RV`, meaningful on `K = K^× ∪ {0}`).
* the projection `rv : VF → RV`. -/
inductive LRVFunc : (k : ℕ) → (Fin k → LRVSort) → LRVSort → Type where
  | zero : LRVFunc 0 Fin.elim0 LRVSort.VF
  | one : LRVFunc 0 Fin.elim0 LRVSort.VF
  | add : LRVFunc 2 (fun _ => LRVSort.VF) LRVSort.VF
  | neg : LRVFunc 1 (fun _ => LRVSort.VF) LRVSort.VF
  | mul : LRVFunc 2 (fun _ => LRVSort.VF) LRVSort.VF
  | rvOne : LRVFunc 0 Fin.elim0 LRVSort.RV
  | rvMul : LRVFunc 2 (fun _ => LRVSort.RV) LRVSort.RV
  | rvZero : LRVFunc 0 Fin.elim0 LRVSort.RV
  | rvInf : LRVFunc 0 Fin.elim0 LRVSort.RV
  | rvAdd : LRVFunc 2 (fun _ => LRVSort.RV) LRVSort.RV
  | rvNeg : LRVFunc 1 (fun _ => LRVSort.RV) LRVSort.RV
  | rv : LRVFunc 1 (fun _ => LRVSort.VF) LRVSort.RV

/-- Definition 2.1: the relation symbols of `L_RV`: the unary predicate `K^×` and the
binary preorder `≤` on `RV`. -/
inductive LRVRel : (k : ℕ) → (Fin k → LRVSort) → Type where
  | isKx : LRVRel 1 (fun _ => LRVSort.RV)
  | le : LRVRel 2 (fun _ => LRVSort.RV)

/-- Definition 2.1: the language `L_RV` as a many-sorted signature. -/
def LRV : MSig where
  Srt := LRVSort
  Func := LRVFunc
  Rel := LRVRel

/-- The one-sorted tagged language of `L_RV`: `V F ⊕ RV ⊕ Γ` with a unary predicate for
each of the three sorts.  This is what Mathlib's single-sorted model theory sees. -/
def LRVTagged : FirstOrder.Language.{0, 0} := toLang LRV

/-- `rv(X + Y)`, a term of `L_RV` of `RV`-sort in the context `(VF, VF)`. -/
def rvAddTerm : MTerm LRV (fun _ => Unit) (fun _ : Fin 2 => LRVSort.VF) LRVSort.RV :=
  MTerm.func LRVFunc.rv
    (fun _ => MTerm.func LRVFunc.add (fun i : Fin 2 => MTerm.bvar i))

/-- The tagged translation of `rv(X + Y)`: a term of the one-sorted language
`LRVTagged` over the carrier `VF ⊕ RV ⊕ Γ`. -/
def rvAddTermTagged : LRVTagged.Term (MTerm.TVar (L := LRV) (fun _ => Unit) ⊕ Fin 2) :=
  MTerm.translate rvAddTerm

/-- `rv(X + Y) ≐ rv(X · Y)` is a quantifier-free `L_RV`-formula in the context
`(VF, VF)`; its translation is quantifier-free in the tagged language. -/
theorem rvAddTerm_qf :
    (BForm.equal rvAddTerm
      (MTerm.func LRVFunc.rv
        (fun _ => MTerm.func LRVFunc.mul (fun i : Fin 2 => MTerm.bvar i)))).QF :=
  trivial

theorem rvAddTerm_tagged_qf :
    (BForm.translate
      (BForm.equal rvAddTerm
        (MTerm.func LRVFunc.rv
          (fun _ => MTerm.func LRVFunc.mul (fun i : Fin 2 => MTerm.bvar i))))).IsQF :=
  BForm.isQF_translate _ rvAddTerm_qf

/-- Quantifier elimination for a class `ACVF` of many-sorted `L_RV`-structures, stated
semantically: every formula is equivalent, in every structure of the class, to a
quantifier-free formula with the same free variables and sorts.  Theorem 2.3 is the
instance `QE_target IsACVF W`, where `IsACVF` is Definition 2.2 (Milestone 1). -/
def QE_target (ACVF : MStruct LRV → Prop) (W : LRVSort → Type w) : Prop :=
  BForm.HasQE ACVF W

/-- The same statement in the tagged one-sorted encoding. -/
def QE_target_tagged (ACVF : MStruct LRV → Prop) (W : LRVSort → Type w) : Prop :=
  ∀ {n : ℕ} {τ : Fin n → LRVSort}, ∀ φ : BForm LRV W n τ,
    ∃ ψ : BForm LRV W n τ, ψ.QF ∧
      ∀ (M : MStruct LRV) [hne : ∀ s, Nonempty (M.Carrier s)], ACVF M →
        ∀ (v : (s : LRVSort) → W s → M.Carrier s)
          (xs : (i : Fin n) → M.Carrier (τ i)),
          (BForm.translate φ).Realize (BForm.tagFree v) (BForm.sigA xs) ↔
            (BForm.translate ψ).Realize (BForm.tagFree v) (BForm.sigA xs)

/-- **Quantifier elimination is invariant under the encoding.**  The many-sorted and the
tagged one-sorted statements of quantifier elimination for `L_RV` are *provably
equivalent*: the tagging loses nothing at the level of what Theorem 2.3 asserts. -/
theorem QE_target_iff (ACVF : MStruct LRV → Prop) (W : LRVSort → Type w) :
    QE_target ACVF W ↔ QE_target_tagged ACVF W := by
  constructor
  · intro h
    exact BForm.hasQE_transfer h
  · intro h n τ φ
    obtain ⟨ψ, hQF, hψ⟩ := h φ
    refine ⟨ψ, hQF, fun M hne hT v xs => ?_⟩
    rw [← BForm.realize_translate v φ xs, ← BForm.realize_translate v ψ xs]
    exact @hψ M hne hT v xs

/-! ## What an `L_RV` axiom costs in the framework

The two-variable ring axiom `∀x ∀y, x + y = y + x` is written out in full.  The point is
to measure, not to axiomatize `ACVF` (that is Milestone 1): every occurrence of a bound
variable needs a transport `by simp` from `ctxSnoc τ s i` to the sort `s`, because the
de Bruijn context extension is `Fin.snoc` and its computation rules are propositional. -/

/-- The context of two `VF`-variables. -/
def ctx2VF : Fin 2 → LRVSort :=
  ctxSnoc LRV (ctxSnoc LRV (Fin.elim0 : Fin 0 → LRVSort) LRVSort.VF) LRVSort.VF

theorem ctx2VF_apply (i : Fin 2) : ctx2VF i = LRVSort.VF := by
  fin_cases i <;> decide

/-- The `i`-th bound variable of the context `(VF, VF)`, at sort `VF`. -/
def bv2VF (i : Fin 2) : MTerm LRV (fun _ => Unit) ctx2VF LRVSort.VF :=
  (ctx2VF_apply i) ▸ MTerm.bvar i

/-- `∀x^VF ∀y^VF, x + y = y + x`, an `L_RV`-sentence. -/
def ax_add_comm : BForm LRV (fun _ => Unit) 0 (Fin.elim0 : Fin 0 → LRVSort) :=
  BForm.all (BForm.all
    (BForm.equal
      (MTerm.func LRVFunc.add bv2VF)
      (MTerm.func LRVFunc.add fun i => bv2VF (Fin.rev i))))

/-- The tagged translation of `ax_add_comm`: a sentence of the one-sorted language on
`VF ⊕ RV ⊕ Γ`, in which the two quantifiers are guarded by the `VF` sort predicate. -/
def ax_add_comm_tagged : LRVTagged.BoundedFormula (MTerm.TVar (L := LRV) (fun _ => Unit)) 0 :=
  BForm.translate ax_add_comm

end ManySorted
