/-
# The well-sorted Shoenfield test for the frozen `HasQE` (Gap 2 of Theorem 2.3)

`Milestone0/Encoding.lean`'s `HasQE` is **well-sorted guarded**:

```
def HasQE (T : LRV.Theory) : Prop :=
  ∀ (α) (sα : α → SortTag) (n) (sn : Fin n → SortTag) (φ : LRV.BoundedFormula α n),
    WellSorted sα sn φ →
    ∃ ψ, ψ.IsQF ∧ WellSorted sα sn ψ ∧
      ∀ (M) [LRV.Structure M], M ⊨ T → ∀ (v : α → M) (x : Fin n → M),
        (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (x i)) →
        (φ.Realize v x ↔ ψ.Realize v x)
```

whereas the criterion family in the tree (`QE/QF_type_bridge.lean`, `QE/Merged_end_to_end.lean`, ...)
is about the **unrestricted** `HasQE` (`∀ α φ, ∃ ψ, ψ.IsQF ∧ T ⊨ᵇ (φ ⇔ ψ)`), a different statement (it
quantifies over ill-sorted formulas and asks for no well-sorted witness).  This file closes that
interface gap on the criterion side: it proves the well-sorted **quantifier-free-type criterion** for
the frozen `HasQE`,

    QFTypeDetWS T → HasQE T ,

and its converse `HasQE T → QFTypeDetWS T`, so the criterion is an exact restatement at the frozen
interface (with no reference to `ShoenfieldQE.HasQE`).  `QFTypeDetWS T` says: on *sorted* tuples, the
quantifier-free well-sorted formulas determine the truth value of every well-sorted formula.

Consequently `Assembly.ShoenfieldTestFS` (`QE/Assembly_frozen.lean`: `Prop39FS → HasQE Axioms.ACVF`)
is equivalent to the single purely model-theoretic statement

    Assembly.Prop39FS → QFTypeDetWS Axioms.ACVF ,

which is the exact reduced goal of Gap 2: the extension property for finitely-saturated targets must
determine the type of a sorted tuple from its quantifier-free well-sorted type.  Everything on the
`HasQE` side of that reduction is proved here; the saturation step is what remains.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Assembly_frozen

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace M1Shoenfield

/-! ## Sorted tuples -/

/-- A parameter tuple all of whose entries have their declared sort. -/
def SortedVec {M : Type*} [LRV.Structure M] {α : Type} (sα : α → SortTag) (v : α → M) : Prop :=
  ∀ a, sortEval (sα a) (v a)

/-- A tuple of free variables all of whose entries have their declared sort. -/
def SortedTup {M : Type*} [LRV.Structure M] {n : ℕ} (sn : Fin n → SortTag) (x : Fin n → M) :
    Prop :=
  ∀ i, sortEval (sn i) (x i)

/-! ## The sorted hypotheses, as formulas with parameters

`LRV.sortPredG s t` is the atom `t ∈ s`.  To state a well-sorted formula of the context `(sα, sn)` as
a *sentence* in the expanded parameter type `α ⊕ Fin n` (which is what compactness needs), each free
variable becomes a parameter and each sort condition becomes an atom. -/

/-- the sort condition on the parameter `a`, as a formula in the parameter type `α ⊕ Fin n` -/
def paramHyp {α : Type} {n : ℕ} (sα : α → SortTag) (a : α) : LRV.Formula (α ⊕ Fin n) :=
  LRV.sortPredG (n := 0) (sα a) (Term.var (Sum.inl (Sum.inl a)))

/-- the sort condition on the free variable `i`, as a formula in the parameter type `α ⊕ Fin n` -/
def varHyp {α : Type} {n : ℕ} (sn : Fin n → SortTag) (i : Fin n) : LRV.Formula (α ⊕ Fin n) :=
  LRV.sortPredG (n := 0) (sn i) (Term.var (Sum.inl (Sum.inr i)))

/-- the set of all sort conditions of the context `(sα, sn)` -/
def sortedHypsF {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag) :
    Set (LRV.Formula (α ⊕ Fin n)) :=
  Set.range (paramHyp (n := n) sα) ∪ Set.range (varHyp (α := α) sn)

section Basic
variable {M : Type*} [LRV.Structure M]

/-- Realization of a unary relation atom. -/
theorem realize_boundedFormula₁ {β : Type} {l : ℕ} (R : LRV.Relations 1)
    (t : LRV.Term (β ⊕ Fin l)) (ν : β → M) (xs : Fin l → M) :
    BoundedFormula.Realize (FirstOrder.Language.Relations.boundedFormula₁ R t) ν xs ↔
      Structure.RelMap R ![Term.realize (Sum.elim ν xs) t] := by
  simp only [FirstOrder.Language.Relations.boundedFormula₁, BoundedFormula.realize_rel]
  have h : (fun i => Term.realize (Sum.elim ν xs) (![t] i)) =
      ![Term.realize (Sum.elim ν xs) t] := by
    funext i
    fin_cases i
    rfl
  rw [h]

theorem realize_sortPredG_var {β : Type} (s : SortTag) (b : β) (ν : β → M) :
    Formula.Realize (LRV.sortPredG (n := 0) s (Term.var (Sum.inl b))) ν ↔ sortEval s (ν b) := by
  cases s with
  | vf => exact realize_boundedFormula₁ Rel.memVF (Term.var (Sum.inl b)) ν default
  | rv => exact realize_boundedFormula₁ Rel.memRV (Term.var (Sum.inl b)) ν default

theorem realize_paramHyp {α : Type} {n : ℕ} (sα : α → SortTag) (a : α) (ν : α ⊕ Fin n → M) :
    Formula.Realize (paramHyp (n := n) sα a) ν ↔ sortEval (sα a) (ν (Sum.inl a)) :=
  realize_sortPredG_var (sα a) (Sum.inl a) ν

theorem realize_varHyp {α : Type} {n : ℕ} (sn : Fin n → SortTag) (i : Fin n)
    (ν : α ⊕ Fin n → M) :
    Formula.Realize (varHyp (α := α) sn i) ν ↔ sortEval (sn i) (ν (Sum.inr i)) :=
  realize_sortPredG_var (sn i) (Sum.inr i) ν

/-- A well-sorted formula is realized at a tuple iff its `toFormula` encoding (a sentence in the
parameter type `α ⊕ Fin n`) is realized there. -/
theorem realize_toFormula_elim {α : Type} {n : ℕ} (ψ : LRV.BoundedFormula α n)
    (v : α → M) (x : Fin n → M) :
    Formula.Realize ψ.toFormula (Sum.elim v x) ↔ ψ.Realize v x := by
  rw [FirstOrder.Language.BoundedFormula.realize_toFormula]
  simp

theorem realize_toFormula_comp {α : Type} {n : ℕ} (ψ : LRV.BoundedFormula α n)
    (ν : α ⊕ Fin n → M) :
    Formula.Realize ψ.toFormula ν ↔ ψ.Realize (ν ∘ Sum.inl) (ν ∘ Sum.inr) :=
  FirstOrder.Language.BoundedFormula.realize_toFormula ψ ν

theorem formula_realize_not {β : Type} (ψ : LRV.Formula β) (ν : β → M) :
    Formula.Realize (∼ψ) ν ↔ ¬ Formula.Realize ψ ν := by
  rw [Formula.Realize, Formula.Realize, BoundedFormula.realize_not]

end Basic

/-! ## Finite conjunctions and disjunctions of well-sorted formulas -/

section Finite
variable {α : Type} {n : ℕ}

theorem wellSorted_listFoldr_inf {β : Type*} (l : List β) (sα : α → SortTag)
    (sn : Fin n → SortTag) (f : β → LRV.BoundedFormula α n)
    (h : ∀ b, LRV.WellSorted sα sn (f b)) :
    LRV.WellSorted sα sn ((l.map f).foldr (· ⊓ ·) ⊤) := by
  induction l with
  | nil => simpa using LRV.wellSorted_top sα sn
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact LRV.wellSorted_inf sα sn (h a) ih

theorem wellSorted_listFoldr_sup {β : Type*} (l : List β) (sα : α → SortTag)
    (sn : Fin n → SortTag) (f : β → LRV.BoundedFormula α n)
    (h : ∀ b, LRV.WellSorted sα sn (f b)) :
    LRV.WellSorted sα sn ((l.map f).foldr (· ⊔ ·) ⊥) := by
  induction l with
  | nil => exact LRV.WellSorted.falsum (sα := sα) sn
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact LRV.wellSorted_sup sα sn (h a) ih

theorem wellSorted_iInf {β : Type*} [Finite β] (sα : α → SortTag) (sn : Fin n → SortTag)
    (f : β → LRV.BoundedFormula α n) (h : ∀ b, LRV.WellSorted sα sn (f b)) :
    LRV.WellSorted sα sn (FirstOrder.Language.BoundedFormula.iInf f) := by
  classical
  rw [FirstOrder.Language.BoundedFormula.iInf]
  exact wellSorted_listFoldr_inf _ sα sn f h

theorem wellSorted_iSup {β : Type*} [Finite β] (sα : α → SortTag) (sn : Fin n → SortTag)
    (f : β → LRV.BoundedFormula α n) (h : ∀ b, LRV.WellSorted sα sn (f b)) :
    LRV.WellSorted sα sn (FirstOrder.Language.BoundedFormula.iSup f) := by
  classical
  rw [FirstOrder.Language.BoundedFormula.iSup]
  exact wellSorted_listFoldr_sup _ sα sn f h

end Finite

/-! ## The criterion -/

/-- **The quantifier-free-type determination hypothesis, at the frozen interface.**  On sorted
tuples of models of `T`, quantifier-free *well-sorted* formulas determine the truth value of every
well-sorted formula.  (Ill-sorted formulas are not mentioned: the frozen `HasQE` is not about them,
which is exactly the difference from `ShoenfieldQE.HasQE`.) -/
def QFTypeDetWS (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n), LRV.WellSorted sα sn φ →
    ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ (N : Type) [LRV.Structure N], N ⊨ T →
      ∀ (v : α → M) (x : Fin n → M) (w : α → N) (y : Fin n → N),
        SortedVec sα v → SortedTup sn x → SortedVec sα w → SortedTup sn y →
        (∀ ψ : LRV.BoundedFormula α n, ψ.IsQF → LRV.WellSorted sα sn ψ →
          (ψ.Realize v x ↔ ψ.Realize w y)) →
        (φ.Realize v x ↔ φ.Realize w y)

/-! ## Compactness, in the form the two steps below need

The compactness theorem is inlined below (credited to `QE/QF_type_bridge.lean`'s
`ShoenfieldQE.exists_model_realize_of_finset`) so that this file depends only on
`Milestone0/Encoding.lean` and on the assembly `QE/Assembly_frozen.lean` — nothing else, and in
particular no pre-repair copy of the encoding.  It is phrased without `Theory.ModelType` so that the
models it produces can be fed to `QFTypeDetWS` directly. -/

/-- **Compactness, realization form** (specialised to `LRV`).  If every finite set of formulas
taken from `Γ` can be realised together with `φ` in a model of `T`, then `Γ` itself can be.  This is
`ShoenfieldQE.exists_model_realize_of_finset` (`QE/QF_type_bridge.lean`) at `L := LRV`; it is
inlined here so that this file needs nothing but `Milestone0/Encoding.lean` and the assembly. -/
theorem exists_model_realize_of_finset_core {T : LRV.Theory} {β : Type}
    {Γ : Set (LRV.Formula β)} {φ : LRV.Formula β}
    (h : ∀ Γ₀ : Finset (LRV.Formula β), (∀ ψ ∈ Γ₀, ψ ∈ Γ) →
      ∃ (N : Theory.ModelType.{0, 0, 0} (L := LRV) T) (ν : β → N.Carrier),
        (∀ ψ ∈ Γ₀, Formula.Realize ψ ν) ∧ Formula.Realize φ ν) :
    ∃ (N : Theory.ModelType.{0, 0, 0} (L := LRV) T) (ν : β → N.Carrier),
      (∀ ψ ∈ Γ, Formula.Realize ψ ν) ∧ Formula.Realize φ ν := by
  classical
  set U : (LRV[[β]]).Theory :=
    (LRV.lhomWithConstants β).onTheory T ∪ Formula.equivSentence '' Γ ∪
      {Formula.equivSentence φ} with hUdef
  have hfin : U.IsFinitelySatisfiable := by
    intro U0 hU0
    set Γ0 : Finset (LRV.Formula β) :=
      (U0.filter (fun s => s ∈ Formula.equivSentence '' Γ)).image
        (fun s => Formula.equivSentence.symm s) with hΓ0def
    have hΓ0 : ∀ ψ ∈ Γ0, ψ ∈ Γ := by
      intro ψ hψ
      obtain ⟨s, hs, hseq⟩ := Finset.mem_image.mp hψ
      obtain ⟨-, hs2⟩ := Finset.mem_filter.mp hs
      obtain ⟨ψ', hψ', hψ'eq⟩ := (Set.mem_image _ _ _).mp hs2
      rw [← hseq, ← hψ'eq, Equiv.symm_apply_apply]
      exact hψ'
    obtain ⟨M, ν, hν, hφν⟩ := h Γ0 hΓ0
    letI : (constantsOn β).Structure M.Carrier := constantsOn.structure ν
    have hmem : ∀ s ∈ U0, M.Carrier ⊨ s := by
      intro s hs
      have hsU : s ∈ U := hU0 hs
      simp only [hUdef, Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hsU
      rcases hsU with (hsT | ⟨ψ, hψ, hψs⟩) | hφs
      · exact ((LHom.onTheory_model (LRV.lhomWithConstants β) T).2 M.is_model).realize_of_mem s hsT
      · rw [← hψs] at hs ⊢
        refine (Formula.realize_equivSentence M.Carrier ψ).2 (hν ψ ?_)
        rw [hΓ0def]
        exact Finset.mem_image.mpr
          ⟨Formula.equivSentence ψ, Finset.mem_filter.mpr ⟨hs, ⟨ψ, hψ, rfl⟩⟩, by simp⟩
      · rw [hφs]
        exact (Formula.realize_equivSentence M.Carrier φ).2 hφν
    haveI : M.Carrier ⊨ (U0 : (LRV[[β]]).Theory) := ⟨fun s hs => hmem s hs⟩
    exact Theory.Model.isSatisfiable M.Carrier
  obtain ⟨N⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.2 hfin
  have hNU : ∀ s ∈ U, N.Carrier ⊨ s := fun s hs => N.is_model.realize_of_mem s hs
  letI : LRV.Structure N.Carrier := (LRV.lhomWithConstants β).reduct N.Carrier
  have hNT : N.Carrier ⊨ T :=
    (LHom.onTheory_model (LRV.lhomWithConstants β) T).1
      ⟨fun s hs => hNU s (by rw [hUdef]; exact Or.inl (Or.inl hs))⟩
  refine ⟨Theory.ModelType.of T N.Carrier, fun a => (LRV.con a : N.Carrier), ?_, ?_⟩
  · intro ψ hψ
    refine (Formula.realize_equivSentence N.Carrier ψ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inl (Or.inr ⟨ψ, hψ, rfl⟩)
  · refine (Formula.realize_equivSentence N.Carrier φ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inr rfl

section Compactness
variable {T : LRV.Theory} {β : Type}

theorem exists_model_realize_of_finset_ws
    (hne : ∀ (N : Type) [LRV.Structure N], N ⊨ T → Nonempty N)
    {Γ : Set (LRV.Formula β)} {φ₀ : LRV.Formula β}
    (h : ∀ Γ₀ : Finset (LRV.Formula β), (∀ ψ ∈ Γ₀, ψ ∈ Γ) →
      ∃ (N : Type) (i : LRV.Structure N) (hN : N ⊨ T) (ν : β → N),
        (∀ ψ ∈ Γ₀, Formula.Realize ψ ν) ∧ Formula.Realize φ₀ ν) :
    ∃ (N : Type) (i : LRV.Structure N) (hN : N ⊨ T) (ν : β → N),
      (∀ ψ ∈ Γ, Formula.Realize ψ ν) ∧ Formula.Realize φ₀ ν := by
  classical
  have h' : ∀ Γ₀ : Finset (LRV.Formula β), (∀ ψ ∈ Γ₀, ψ ∈ Γ) →
      ∃ (N : Theory.ModelType (L := LRV) T) (ν : β → N.Carrier),
        (∀ ψ ∈ Γ₀, Formula.Realize ψ ν) ∧ Formula.Realize φ₀ ν := by
    intro Γ₀ hΓ₀
    obtain ⟨N, i, hN, ν, h1, h2⟩ := h Γ₀ hΓ₀
    letI := i
    haveI := hne N hN
    exact ⟨Theory.ModelType.of T N, ν, h1, h2⟩
  obtain ⟨N, ν, h1, h2⟩ := exists_model_realize_of_finset_core h'
  exact ⟨N.Carrier, N.struc, N.is_model, ν, h1, h2⟩

end Compactness


/-! ## Quantifier-free finite conjunctions -/

section QFFinite
variable {α : Type} {n : ℕ}

theorem isQF_listFoldr_inf {β : Type*} (l : List β) (f : β → LRV.BoundedFormula α n)
    (h : ∀ b, (f b).IsQF) : ((l.map f).foldr (· ⊓ ·) ⊤).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a).inf ih

theorem isQF_listFoldr_sup {β : Type*} (l : List β) (f : β → LRV.BoundedFormula α n)
    (h : ∀ b, (f b).IsQF) : ((l.map f).foldr (· ⊔ ·) ⊥).IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a).sup ih

theorem isQF_iInf {β : Type*} [Finite β] (f : β → LRV.BoundedFormula α n)
    (h : ∀ b, (f b).IsQF) : (BoundedFormula.iInf f).IsQF := by
  classical
  rw [BoundedFormula.iInf]
  exact isQF_listFoldr_inf _ f h

theorem isQF_iSup {β : Type*} [Finite β] (f : β → LRV.BoundedFormula α n)
    (h : ∀ b, (f b).IsQF) : (BoundedFormula.iSup f).IsQF := by
  classical
  rw [BoundedFormula.iSup]
  exact isQF_listFoldr_sup _ f h

theorem realize_top_bd {M : Type*} [LRV.Structure M] {α : Type} {n : ℕ}
    (v : α → M) (x : Fin n → M) : (⊤ : LRV.BoundedFormula α n).Realize v x := by
  simp

end QFFinite

/-! ## The isolation step

At a sorted tuple satisfying a well-sorted formula `φ`, some quantifier-free well-sorted formula
holds and implies `φ` at every sorted tuple of every model of `T`.  This is the "cover by
quantifier-free formulas" step of Shoenfield's test, at the frozen interface: `QFTypeDetWS` is used
exactly once, to rule out a model whose sorted tuple has the same quantifier-free well-sorted type
but does not satisfy `φ`. -/


section Isolate
variable {T : LRV.Theory} {α : Type} {n : ℕ} {sα : α → SortTag} {sn : Fin n → SortTag}

theorem exists_qf_imp (hne : ∀ (N : Type) [LRV.Structure N], N ⊨ T → Nonempty N)
    (H : QFTypeDetWS T) {φ : LRV.BoundedFormula α n} (hφ : LRV.WellSorted sα sn φ)
    {M : Type} [LRV.Structure M] (hM : M ⊨ T) {v : α → M} {x : Fin n → M}
    (hv : SortedVec sα v) (hx : SortedTup sn x) (hr : φ.Realize v x) :
    ∃ ψ : LRV.BoundedFormula α n, ψ.IsQF ∧ LRV.WellSorted sα sn ψ ∧ ψ.Realize v x ∧
      ∀ (N : Type) [LRV.Structure N], N ⊨ T → ∀ (w : α → N) (y : Fin n → N),
        SortedVec sα w → SortedTup sn y → ψ.Realize w y → φ.Realize w y := by
  classical
  by_contra hcon
  -- one formula at a time: a quantifier-free well-sorted `θ` true at `(v, x)` does not force `φ`
  have hstep : ∀ (θ : LRV.BoundedFormula α n), θ.IsQF → LRV.WellSorted sα sn θ →
      θ.Realize v x → ∃ (N : Type) (_ : LRV.Structure N) (_ : N ⊨ T)
        (w : α → N) (y : Fin n → N),
        SortedVec sα w ∧ SortedTup sn y ∧ θ.Realize w y ∧ ¬ φ.Realize w y := by
    intro θ h1 h2 h3
    by_contra hno
    refine hcon ⟨θ, h1, h2, h3, fun N _ hN w y hw hy hθ => ?_⟩
    by_contra hφw
    exact hno ⟨N, ‹LRV.Structure N›, hN, w, y, hw, hy, hθ, hφw⟩
  -- the type whose finite satisfiability compactness has to check
  set Γ : Set (LRV.Formula (α ⊕ Fin n)) :=
    {θ | ∃ ψ : LRV.BoundedFormula α n,
        ψ.IsQF ∧ LRV.WellSorted sα sn ψ ∧ ψ.Realize v x ∧ θ = ψ.toFormula}
      ∪ sortedHypsF sα sn with hΓ
  have hfin : ∀ Γ₀ : Finset (LRV.Formula (α ⊕ Fin n)), (∀ θ ∈ Γ₀, θ ∈ Γ) →
      ∃ (N : Type) (i : LRV.Structure N) (hN : N ⊨ T) (ν : (α ⊕ Fin n) → N),
        (∀ θ ∈ Γ₀, Formula.Realize θ ν) ∧
          Formula.Realize (BoundedFormula.not φ).toFormula ν := by
    intro Γ₀ hΓ₀
    -- the quantifier-free formulas that occur in `Γ₀`
    set g : ↥Γ₀ → LRV.BoundedFormula α n := fun θ =>
      if h : ∃ ψ : LRV.BoundedFormula α n,
          ψ.IsQF ∧ LRV.WellSorted sα sn ψ ∧ ψ.Realize v x ∧
            (θ : LRV.Formula (α ⊕ Fin n)) = ψ.toFormula
        then h.choose else ⊤ with hg
    set Ψ₀ : Finset (LRV.BoundedFormula α n) := Γ₀.attach.image g with hΨ₀
    have hΨ₀prop : ∀ ψ ∈ Ψ₀, ψ.IsQF ∧ LRV.WellSorted sα sn ψ ∧ ψ.Realize v x := by
      intro ψ hψ
      obtain ⟨θ, _, rfl⟩ := Finset.mem_image.mp hψ
      by_cases h : ∃ ψ : LRV.BoundedFormula α n,
          ψ.IsQF ∧ LRV.WellSorted sα sn ψ ∧ ψ.Realize v x ∧
            (θ : LRV.Formula (α ⊕ Fin n)) = ψ.toFormula
      · rw [hg]
        simp only [dif_pos h]
        exact ⟨h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1⟩
      · rw [hg]
        simp only [dif_neg h]
        exact ⟨BoundedFormula.IsQF.top, LRV.wellSorted_top sα sn, realize_top_bd v x⟩
    -- their conjunction
    set θc : LRV.BoundedFormula α n :=
      BoundedFormula.iInf (fun ψ : ↥Ψ₀ => (ψ : LRV.BoundedFormula α n)) with hθc
    have hθcQF : θc.IsQF := isQF_iInf _ (fun ψ => (hΨ₀prop ψ.1 ψ.2).1)
    have hθcWS : LRV.WellSorted sα sn θc :=
      wellSorted_iInf sα sn _ (fun ψ => (hΨ₀prop ψ.1 ψ.2).2.1)
    have hθcr : θc.Realize v x := by
      rw [hθc, BoundedFormula.realize_iInf]
      exact fun ψ => (hΨ₀prop ψ.1 ψ.2).2.2
    obtain ⟨N, i, hN, w, y, hw, hy, hθc', hφ'⟩ := hstep θc hθcQF hθcWS hθcr
    letI := i
    have hΨ₀' : ∀ ψ ∈ Ψ₀, ψ.Realize w y := by
      intro ψ hψ
      exact (BoundedFormula.realize_iInf).1 hθc' ⟨ψ, hψ⟩
    refine ⟨N, i, hN, Sum.elim w y, ?_, ?_⟩
    · intro θ hθ
      have hθΓ : θ ∈ Γ := hΓ₀ θ hθ
      rw [hΓ, Set.mem_union] at hθΓ
      rcases hθΓ with hA | hB
      · obtain ⟨ψ, h1, h2, h3, hθψ⟩ := hA
        -- the chosen witness for `θ` is in `Ψ₀`
        have hwit : ∃ ψ : LRV.BoundedFormula α n,
            ψ.IsQF ∧ LRV.WellSorted sα sn ψ ∧ ψ.Realize v x ∧
              (θ : LRV.Formula (α ⊕ Fin n)) = ψ.toFormula := ⟨ψ, h1, h2, h3, hθψ⟩
        have hgθ : g ⟨θ, hθ⟩ = hwit.choose := by
          rw [hg]
          exact dif_pos hwit
        have hmem : hwit.choose ∈ Ψ₀ := by
          rw [hΨ₀]
          exact Finset.mem_image.mpr ⟨⟨θ, hθ⟩, Finset.mem_univ _, hgθ⟩
        have hreal : hwit.choose.Realize w y := hΨ₀' _ hmem
        rw [hwit.choose_spec.2.2.2]
        exact (realize_toFormula_comp hwit.choose (Sum.elim w y)).mpr hreal
      · rw [sortedHypsF, Set.mem_union] at hB
        rcases hB with hP | hV
        · obtain ⟨a, rfl⟩ := hP
          exact (realize_paramHyp sα a (Sum.elim w y)).mpr (hw a)
        · obtain ⟨j, rfl⟩ := hV
          exact (realize_varHyp sn j (Sum.elim w y)).mpr (hy j)
    · exact (realize_toFormula_comp (BoundedFormula.not φ) (Sum.elim w y)).mpr hφ'
  -- compactness
  obtain ⟨N, i, hN, ν, hΓall, hnotφ⟩ := exists_model_realize_of_finset_ws hne hfin
  letI := i
  -- sortedness of the tuple produced
  have hw : SortedVec sα (ν ∘ Sum.inl) := by
    intro a
    refine (realize_paramHyp sα a ν).mp (hΓall _ ?_)
    refine Set.mem_union_right _ ?_
    rw [sortedHypsF, Set.mem_union]
    exact Or.inl ⟨a, rfl⟩
  have hy : SortedTup sn (ν ∘ Sum.inr) := by
    intro j
    refine (realize_varHyp sn j ν).mp (hΓall _ ?_)
    refine Set.mem_union_right _ ?_
    rw [sortedHypsF, Set.mem_union]
    exact Or.inr ⟨j, rfl⟩
  -- the quantifier-free well-sorted types agree
  have hQF : ∀ ψ : LRV.BoundedFormula α n, ψ.IsQF → LRV.WellSorted sα sn ψ →
      (ψ.Realize v x ↔ ψ.Realize (ν ∘ Sum.inl) (ν ∘ Sum.inr)) := by
    intro ψ h1 h2
    constructor
    · intro hψ
      refine (realize_toFormula_comp ψ ν).mp (hΓall _ ?_)
      refine Set.mem_union_left _ ?_
      exact ⟨ψ, h1, h2, hψ, rfl⟩
    · intro hψ
      by_contra hψ'
      have hnot : (BoundedFormula.not ψ).Realize v x := by
        rw [BoundedFormula.realize_not]
        exact hψ'
      have hmem : (BoundedFormula.not ψ).toFormula ∈ Γ := by
        refine Set.mem_union_left _ ?_
        exact ⟨BoundedFormula.not ψ, h1.not, LRV.wellSorted_not sα sn h2, hnot, rfl⟩
      have hreal := (realize_toFormula_comp (BoundedFormula.not ψ) ν).mp (hΓall _ hmem)
      rw [BoundedFormula.realize_not] at hreal
      exact hreal hψ
  have hH := H α sα n sn φ hφ M hM N hN v x (ν ∘ Sum.inl) (ν ∘ Sum.inr)
    hv hx hw hy hQF
  have hnotφ' : ¬ φ.Realize (ν ∘ Sum.inl) (ν ∘ Sum.inr) := by
    intro h
    have h2 : (BoundedFormula.not φ).Realize (ν ∘ Sum.inl) (ν ∘ Sum.inr) :=
      (realize_toFormula_comp (BoundedFormula.not φ) ν).mp hnotφ
    exact (BoundedFormula.realize_not).mp h2 h
  exact hnotφ' (hH.mp hr)

end Isolate


/-! ## The finite cover step

If every sorted tuple satisfying `φ` is isolated by a quantifier-free well-sorted formula whose
truth forces `φ`, then finitely many such formulas cover `φ`.  (Compactness on the dual type: the
negations of the isolating formulas together with `φ` and the sort hypotheses.) -/

section Cover
variable {T : LRV.Theory} {α : Type} {n : ℕ} {sα : α → SortTag} {sn : Fin n → SortTag}

/-- the family of quantifier-free well-sorted formulas which force `φ` at every sorted tuple -/
def Forces (T : LRV.Theory) (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag)
    (φ ψ : LRV.BoundedFormula α n) : Prop :=
  ψ.IsQF ∧ LRV.WellSorted sα sn ψ ∧
    ∀ (N : Type) [LRV.Structure N], N ⊨ T → ∀ (w : α → N) (y : Fin n → N),
      SortedVec sα w → SortedTup sn y → ψ.Realize w y → φ.Realize w y

theorem exists_finset_cover (hne : ∀ (N : Type) [LRV.Structure N], N ⊨ T → Nonempty N)
    (H : QFTypeDetWS T) {φ : LRV.BoundedFormula α n} (hφ : LRV.WellSorted sα sn φ) :
    ∃ Ψ₀ : Finset (LRV.BoundedFormula α n),
      (∀ ψ ∈ Ψ₀, Forces T sα sn φ ψ) ∧
      ∀ (N : Type) [LRV.Structure N], N ⊨ T → ∀ (w : α → N) (y : Fin n → N),
        SortedVec sα w → SortedTup sn y → φ.Realize w y → ∃ ψ ∈ Ψ₀, ψ.Realize w y := by
  classical
  by_contra hno
  push Not at hno
  -- for every finite `Ψ₀ ⊆ Forces`, a sorted tuple satisfies `φ` and none of `Ψ₀`
  set Ψ : Set (LRV.BoundedFormula α n) := {ψ | Forces T sα sn φ ψ} with hΨ
  set Γ : Set (LRV.Formula (α ⊕ Fin n)) :=
    {θ | ∃ ψ : LRV.BoundedFormula α n, ψ ∈ Ψ ∧ θ = (BoundedFormula.not ψ).toFormula}
      ∪ sortedHypsF sα sn with hΓ
  have hfin : ∀ Γ₀ : Finset (LRV.Formula (α ⊕ Fin n)), (∀ θ ∈ Γ₀, θ ∈ Γ) →
      ∃ (N : Type) (i : LRV.Structure N) (hN : N ⊨ T) (ν : (α ⊕ Fin n) → N),
        (∀ θ ∈ Γ₀, Formula.Realize θ ν) ∧ Formula.Realize φ.toFormula ν := by
    intro Γ₀ hΓ₀
    set g : ↥Γ₀ → LRV.BoundedFormula α n := fun θ =>
      if h : ∃ ψ : LRV.BoundedFormula α n, ψ ∈ Ψ ∧
          (θ : LRV.Formula (α ⊕ Fin n)) = (BoundedFormula.not ψ).toFormula
        then h.choose else ⊥ with hg
    set Ψ₀ : Finset (LRV.BoundedFormula α n) := Γ₀.attach.image g with hΨ₀
    have hΨ₀mem : ∀ ψ ∈ Ψ₀, ψ ∈ Ψ := by
      intro ψ hψ
      obtain ⟨θ, _, rfl⟩ := Finset.mem_image.mp hψ
      by_cases h : ∃ ψ : LRV.BoundedFormula α n, ψ ∈ Ψ ∧
          (θ : LRV.Formula (α ⊕ Fin n)) = (BoundedFormula.not ψ).toFormula
      · rw [hg]
        simp only [dif_pos h]
        exact h.choose_spec.1
      · rw [hg]
        simp only [dif_neg h]
        exact ⟨BoundedFormula.isQF_bot, LRV.WellSorted.falsum (sα := sα) sn,
          fun N _ hN w y hw hy hbot => ((BoundedFormula.realize_bot).mp hbot).elim⟩
    obtain ⟨N, i, hN, w, y, hw, hy, hφ', hnone⟩ := hno Ψ₀ hΨ₀mem
    letI := i
    refine ⟨N, i, hN, Sum.elim w y, ?_, ?_⟩
    · intro θ hθ
      have hθΓ : θ ∈ Γ := hΓ₀ θ hθ
      rw [hΓ, Set.mem_union] at hθΓ
      rcases hθΓ with hA | hB
      · obtain ⟨ψ, hψΨ, hθψ⟩ := hA
        have hwit : ∃ ψ : LRV.BoundedFormula α n, ψ ∈ Ψ ∧
            (θ : LRV.Formula (α ⊕ Fin n)) = (BoundedFormula.not ψ).toFormula := ⟨ψ, hψΨ, hθψ⟩
        have hgθ : g ⟨θ, hθ⟩ = hwit.choose := by
          rw [hg]
          exact dif_pos hwit
        have hmem : hwit.choose ∈ Ψ₀ := by
          rw [hΨ₀]
          exact Finset.mem_image.mpr ⟨⟨θ, hθ⟩, Finset.mem_univ _, hgθ⟩
        have hnot : ¬ hwit.choose.Realize w y := hnone _ hmem
        have hreal : (BoundedFormula.not hwit.choose).Realize w y :=
          (BoundedFormula.realize_not).mpr hnot
        rw [hwit.choose_spec.2]
        exact (realize_toFormula_comp (BoundedFormula.not hwit.choose) (Sum.elim w y)).mpr hreal
      · rw [sortedHypsF, Set.mem_union] at hB
        rcases hB with hP | hV
        · obtain ⟨a, rfl⟩ := hP
          exact (realize_paramHyp sα a (Sum.elim w y)).mpr (hw a)
        · obtain ⟨j, rfl⟩ := hV
          exact (realize_varHyp sn j (Sum.elim w y)).mpr (hy j)
    · exact (realize_toFormula_comp φ (Sum.elim w y)).mpr hφ'
  -- compactness
  obtain ⟨N, i, hN, ν, hΓall, hφν⟩ := exists_model_realize_of_finset_ws hne hfin
  letI := i
  have hw : SortedVec sα (ν ∘ Sum.inl) := by
    intro a
    refine (realize_paramHyp sα a ν).mp (hΓall _ ?_)
    refine Set.mem_union_right _ ?_
    rw [sortedHypsF, Set.mem_union]
    exact Or.inl ⟨a, rfl⟩
  have hy : SortedTup sn (ν ∘ Sum.inr) := by
    intro j
    refine (realize_varHyp sn j ν).mp (hΓall _ ?_)
    refine Set.mem_union_right _ ?_
    rw [sortedHypsF, Set.mem_union]
    exact Or.inr ⟨j, rfl⟩
  have hφ' : φ.Realize (ν ∘ Sum.inl) (ν ∘ Sum.inr) :=
    (realize_toFormula_comp φ ν).mp hφν
  -- the isolation step at this tuple gives a member of `Forces` which is false there
  obtain ⟨ψ, hψQF, hψWS, hψreal, hψforce⟩ := exists_qf_imp hne H hφ hN hw hy hφ'
  have hψΨ : ψ ∈ Ψ := ⟨hψQF, hψWS, hψforce⟩
  have hmem : (BoundedFormula.not ψ).toFormula ∈ Γ := by
    refine Set.mem_union_left _ ?_
    exact ⟨ψ, hψΨ, rfl⟩
  have hreal := (realize_toFormula_comp (BoundedFormula.not ψ) ν).mp (hΓall _ hmem)
  rw [BoundedFormula.realize_not] at hreal
  exact hreal hψreal

end Cover

/-! ## The criterion, and its converse -/

section Criterion
variable {T : LRV.Theory}

theorem hasQE_of_qfTypeDetWS (hne : ∀ (N : Type) [LRV.Structure N], N ⊨ T → Nonempty N)
    (H : QFTypeDetWS T) : HasQE T := by
  intro α sα n sn φ hφ
  classical
  obtain ⟨Ψ₀, hΨ₀, hcover⟩ := exists_finset_cover (T := T) hne H hφ
  refine ⟨BoundedFormula.iSup (fun ψ : ↥Ψ₀ => (ψ : LRV.BoundedFormula α n)), ?_, ?_, ?_⟩
  · exact isQF_iSup _ (fun ψ => (hΨ₀ ψ.1 ψ.2).1)
  · exact wellSorted_iSup sα sn _ (fun ψ => (hΨ₀ ψ.1 ψ.2).2.1)
  · intro N _ hN w y hw hy
    constructor
    · intro hφw
      obtain ⟨ψ, hψ, hreal⟩ := hcover N hN w y hw hy hφw
      exact (BoundedFormula.realize_iSup).mpr ⟨⟨ψ, hψ⟩, hreal⟩
    · intro hsup
      obtain ⟨⟨ψ, hψ⟩, hreal⟩ := (BoundedFormula.realize_iSup).1 hsup
      exact (hΨ₀ ψ hψ).2.2 N hN w y hw hy hreal

theorem qfTypeDetWS_of_hasQE (h : HasQE T) : QFTypeDetWS T := by
  intro α sα n sn φ hφ M _ hM N _ hN v x w y hv hx hw hy hQF
  obtain ⟨ψ, hψQF, hψWS, hagree⟩ := h α sα n sn φ hφ
  exact (hagree M hM v x hv hx).trans ((hQF ψ hψQF hψWS).trans
    (hagree N hN w y hw hy).symm)

/-- The criterion is an exact restatement of quantifier elimination at the frozen interface. -/
theorem hasQE_iff_qfTypeDetWS (hne : ∀ (N : Type) [LRV.Structure N], N ⊨ T → Nonempty N) :
    HasQE T ↔ QFTypeDetWS T :=
  ⟨qfTypeDetWS_of_hasQE, hasQE_of_qfTypeDetWS hne⟩

end Criterion

/-! ## `ACVF` models are nonempty (`0` of the `VF` sort is a closed term) -/

theorem nonempty_of_model_ACVF {N : Type} [LRV.Structure N] (h : N ⊨ Axioms.ACVF) :
    Nonempty N :=
  ⟨Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0⟩


/-! ## The exact reduction of `Assembly.ShoenfieldTestFS`

`Assembly.ShoenfieldTestFS` is `Assembly.Prop39FS → HasQE Axioms.ACVF`.  By the criterion above it is
*equivalent* to `Assembly.Prop39FS → QFTypeDetWS Axioms.ACVF`: everything on the `HasQE` side is
proved, and the only remaining input is the model-theoretic statement that the extension property for
finitely-saturated targets determines the type of a sorted tuple from its quantifier-free well-sorted
type. -/

theorem shoenfieldTestFS_of_qfTypeDet
    (h : Assembly.Prop39FS → QFTypeDetWS Axioms.ACVF) : Assembly.ShoenfieldTestFS :=
  fun h39 => hasQE_of_qfTypeDetWS (fun _ _ hN => nonempty_of_model_ACVF hN) (h h39)

theorem qfTypeDet_of_shoenfieldTestFS (h : Assembly.ShoenfieldTestFS) :
    Assembly.Prop39FS → QFTypeDetWS Axioms.ACVF :=
  fun h39 => qfTypeDetWS_of_hasQE (h h39)

/-- **Gap 2, exactly reduced**: the frozen Shoenfield test is equivalent to well-sorted
quantifier-free-type determination for models of `ACVF`, given the extension property of
Proposition 3.9 at `Assembly.SaturatedFS`. -/
theorem shoenfieldTestFS_iff :
    Assembly.ShoenfieldTestFS ↔ (Assembly.Prop39FS → QFTypeDetWS Axioms.ACVF) :=
  ⟨qfTypeDet_of_shoenfieldTestFS, shoenfieldTestFS_of_qfTypeDet⟩

/-- The frozen target from the two remaining gaps: Proposition 3.9 at `SaturatedFS`, and the
criterion's model-theoretic input.  (`Assembly.theorem_2_3_of_fs` is the assembly's own composite.) -/
theorem theorem_2_3_of_prop39_and_criterion
    (h : Assembly.Prop39FS → QFTypeDetWS Axioms.ACVF) (h39 : Assembly.Prop39FS) :
    HasQE Axioms.ACVF :=
  Assembly.theorem_2_3_of_fs (shoenfieldTestFS_of_qfTypeDet h) h39


/-! ## Convenience forms at `Axioms.ACVF` -/

theorem qfTypeDetWS_ACVF_iff : HasQE Axioms.ACVF ↔ QFTypeDetWS Axioms.ACVF :=
  hasQE_iff_qfTypeDetWS (fun _ _ hN => nonempty_of_model_ACVF hN)

theorem hasQE_ACVF_of_qfTypeDet (H : QFTypeDetWS Axioms.ACVF) : HasQE Axioms.ACVF :=
  hasQE_of_qfTypeDetWS (fun _ _ hN => nonempty_of_model_ACVF hN) H

/-! ## What `Prop39FS` does give: atomic types over a substructure are realised

`Assembly.Saturated` was strong enough to realise the *complete* type of an element outright
(`Assembly.realizesAtomic_of_saturated`), which is why the old reduction was vacuous.  At
`Assembly.SaturatedFS` the type has to be shown finitely satisfiable, and that is what
`Assembly.Prop39FS` supplies: it extends `f : S ↪ N` to a monomorphism `M ↪ N`, whose value at `m`
realises the atomic type of `m` over `S`.  This is the one-element step of the paper's Lemmas
3.2-3.8 in the form the assembly's back-and-forth machinery
(`Realize.exists_oneStep` / `exists_total_embedding_of_realizesAtomic`) consumes. -/

theorem realizesAtomic_of_prop39FS (h39 : Assembly.Prop39FS)
    {N : Type} [LRV.Structure N] [hN : N ⊨ Axioms.ACVF] (hSat : Assembly.SaturatedFS N)
    {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) :
    ∃ b : N, Realize.RealizesAtomic S f m b := by
  obtain ⟨g, hg⟩ := h39 M N hSat S f
  -- the composition `g ∘ mv S m` is `wv f (g m)`
  have hmv : (g : M → N) ∘ Realize.mv S m = Realize.wv f (g m) := by
    funext x
    rcases x with s | u
    · exact hg s
    · cases u
      rfl
  -- hence `g` commutes with the value of every term of the expanded language
  have hkey : ∀ (t : LRV.Term (S ⊕ Unit)),
      g (t.realize (Realize.mv S m)) = t.realize (Realize.wv f (g m)) := by
    intro t
    rw [← HomClass.realize_term, hmv]
  have hrel : ∀ {n : ℕ} (r : LRV.Relations n) (ts : Fin n → LRV.Term (S ⊕ Unit)),
      Structure.RelMap r (fun i => (ts i).realize (Realize.wv f (g m))) ↔
        Structure.RelMap r (fun i => (ts i).realize (Realize.mv S m)) := by
    intro n r ts
    have hmap : Structure.RelMap r (g ∘ (fun i => (ts i).realize (Realize.mv S m))) ↔
        Structure.RelMap r (fun i => (ts i).realize (Realize.mv S m)) :=
      g.map_rel' r _
    rw [show (g ∘ (fun i => (ts i).realize (Realize.mv S m))) =
        (fun i => (ts i).realize (Realize.wv f (g m))) from funext (fun i => hkey (ts i))] at hmap
    exact hmap
  refine ⟨g m, ?_, ?_⟩
  · intro u v
    constructor
    · intro h
      rw [← hkey u, ← hkey v, h]
    · intro h
      refine g.injective ?_
      rw [hkey u, hkey v, h]
  · intro n r ts
    exact (hrel r ts).symm

end M1Shoenfield

#print axioms M1Shoenfield.realize_paramHyp
#print axioms M1Shoenfield.exists_qf_imp
#print axioms M1Shoenfield.exists_finset_cover
#print axioms M1Shoenfield.hasQE_of_qfTypeDetWS
#print axioms M1Shoenfield.qfTypeDetWS_of_hasQE
#print axioms M1Shoenfield.hasQE_iff_qfTypeDetWS
#print axioms M1Shoenfield.nonempty_of_model_ACVF
#print axioms M1Shoenfield.shoenfieldTestFS_of_qfTypeDet
#print axioms M1Shoenfield.qfTypeDet_of_shoenfieldTestFS
#print axioms M1Shoenfield.shoenfieldTestFS_iff
#print axioms M1Shoenfield.theorem_2_3_of_prop39_and_criterion
#print axioms M1Shoenfield.qfTypeDetWS_ACVF_iff
#print axioms M1Shoenfield.hasQE_ACVF_of_qfTypeDet
#print axioms M1Shoenfield.realizesAtomic_of_prop39FS
