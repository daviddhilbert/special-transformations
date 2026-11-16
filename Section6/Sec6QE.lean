module

/-
Section 6 of Yin, "Special transformations in algebraically closed valued fields"
(arXiv:1006.2467): the interlude on quantifier elimination for henselian fields
(paper lines 1419–1520).

This file formalises, on top of the frozen encoding of `L_RV` in
`Milestone0/Encoding.lean`,

* the two semantic facts about the encoding's sort guards that the elimination needs
  (`InAntecedent` is false, and `GuardTrue` is true, off the sort of the guarded variable);
* the syntactic class of `VF`-quantifier-free formulas (`IsVFQF`);
* the notion "the theory `T` eliminates `VF`-quantifiers" (`HasVFQE`), the paper's one-step
  form of it (`VFQE_step`, the Lemma at l.1444), and the derivation
  **`hasVFQE_of_step`** of the first from the second — the paper's "By elementary logic this
  lemma yields:" before Proposition `qe:hensel`;
* the theory `Hen_S(0,0)` of henselian fields of pure characteristic `0` in `L_RV`, with the
  henselian scheme left as an explicit parameter;
* Proposition `qe:hensel` (paper, l.1517), derived from the paper's Lemma.

The paper's Lemma is *not* proved here: its proof uses Theorem 5.5
(`special:bi:polynomial:constant`, §5) and Lemma `cut:to:hensel:substru`, through the descent
along an `RV`-pullback bijection `T`, which needs the `T`-image of a `VF`-quantifier-free formula
computed by term replacement.  It is carried as the hypothesis `hensel_qe_lemma_statement`, with
the paper's sentence in its docstring.  No `sorry`, no `axiom`: every theorem below is proved
from the frozen encoding alone, except those that take that Lemma as a hypothesis.

Conventions follow `Milestone0/DECISION.md`: `rv 0 = ∞` is one absorbing element, `≤` is the
paper's value-group order, and a formula is a formula of the paper's two-sorted language only if
it is `WellSorted`.
-/
public import Enc

@[expose] public section

set_option linter.unusedSimpArgs false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0
namespace Sec6

variable {M : Type*} [LRV.Structure M]

/-! ## 1. The sort guard, semantically

The encoding is one-sorted and its quantifiers range over the whole tagged carrier, so a sorted
quantifier `∃ x ∈ VF, ψ` is written `BoundedFormula.ex (x ∈ VF ⊓ ψ)`.  `WellSorted` therefore
requires (`GuardsLast`) that the sort atom of the bound variable be a top-level conjunct of the
body's antecedent, and (`GuardTrue`) that the body be *true* at elements outside the sort.  The
two lemmas below are the semantic content of those syntactic conditions; they are what makes the
`VF`-elimination steps of §3 sound.
-/

/-- The guard atom `xᵢ ∈ s` holds exactly at the tuples whose `i`-th entry is of sort `s`. -/
theorem sortPredG_var_realize {α : Type} {n : ℕ} (s : SortTag) (i : Fin n)
    (v : α → M) (xs : Fin n → M) :
    (sortPredG s (Term.var (Sum.inr i) : LRV.Term (α ⊕ Fin n))).Realize v xs ↔
      sortEval s (xs i) := by
  cases s
  · show (Structure.RelMap (L := LRV) Rel.memVF
        (fun j : Fin 1 => Term.realize (Sum.elim v xs)
          ((![Term.var (Sum.inr i)] : Fin 1 → LRV.Term (α ⊕ Fin n)) j)))
      ↔ Structure.RelMap (L := LRV) Rel.memVF ![xs i]
    have h : (fun j : Fin 1 => Term.realize (Sum.elim v xs)
          ((![Term.var (Sum.inr i)] : Fin 1 → LRV.Term (α ⊕ Fin n)) j)) = ![xs i] := by
      funext j
      fin_cases j
      rfl
    rw [h]
  · show (Structure.RelMap (L := LRV) Rel.memRV
        (fun j : Fin 1 => Term.realize (Sum.elim v xs)
          ((![Term.var (Sum.inr i)] : Fin 1 → LRV.Term (α ⊕ Fin n)) j)))
      ↔ Structure.RelMap (L := LRV) Rel.memRV ![xs i]
    have h : (fun j : Fin 1 => Term.realize (Sum.elim v xs)
          ((![Term.var (Sum.inr i)] : Fin 1 → LRV.Term (α ⊕ Fin n)) j)) = ![xs i] := by
      funext j
      fin_cases j
      rfl
    rw [h]

/-- Appending an element of sort `s` to a tuple of the declared sorts gives a tuple of the
declared sorts `Fin.snoc sn s`. -/
theorem sorted_snoc {n : ℕ} {sn : Fin n → SortTag} {s : SortTag}
    {x : Fin n → M} {y : M} (hx : ∀ i, sortEval (sn i) (x i)) (hy : sortEval s y) :
    ∀ i, sortEval (Fin.snoc (α := fun _ => SortTag) sn s i)
      (Fin.snoc (α := fun _ => M) x y i) := by
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact hx j
  · rw [Fin.snoc_last, Fin.snoc_last]
    exact hy

/-- **`InAntecedent` is false off the sort of the guarded variable**: a formula with the atom
`xᵢ ∈ s` as a top-level conjunct is false at any tuple whose `i`-th entry is not of sort `s`. -/
theorem inAntecedent_false {α : Type} {m : ℕ} {s : SortTag} {i : Fin m}
    {η : LRV.BoundedFormula α m} (h : InAntecedent s i η) :
    ∀ (v : α → M) (xs : Fin m → M), ¬ sortEval s (xs i) → ¬ η.Realize v xs := by
  induction h with
  | atom =>
      intro v xs hx hcon
      exact hx ((sortPredG_var_realize s i v xs).mp hcon)
  | and_left _ ih =>
      intro v xs hx hcon
      exact ih v xs hx (BoundedFormula.realize_inf.mp hcon).1
  | and_right _ ih =>
      intro v xs hx hcon
      exact ih v xs hx (BoundedFormula.realize_inf.mp hcon).2

/-- **`GuardTrue` is true off the sort of the guarded variable** — the semantic reading of the
`GuardTrue` field of `WellSorted`.  The value of the formula off the sort does not depend on the
other entries of the tuple, which is what makes the raw one-sorted quantifier `∀ x, χ` agree with
the guarded `∀ x ∈ s, χ` at tuples of the declared sorts. -/
theorem guardTrue_true {α : Type} {s : SortTag} {n : ℕ} {i : Fin n}
    {χ : LRV.BoundedFormula α n} (h : GuardTrue s i χ) :
    ∀ (v : α → M) (xs : Fin n → M), ¬ sortEval s (xs i) → χ.Realize v xs := by
  induction h with
  | imp hη =>
      intro v xs hx hcon
      exact absurd hcon (inAntecedent_false hη v xs hx)
  | all _ ih =>
      intro v xs hx
      rw [BoundedFormula.realize_all]
      intro a
      refine ih v (Fin.snoc (α := fun _ => M) xs a) ?_
      rwa [Fin.snoc_castSucc]

/-! ## 2. `VF`-quantifier-free formulas

The paper's `L_H` expands `L_RV` only on the `RV` sort, so `VF`-quantifier-free means: every
quantifier of the formula is a quantifier over the `RV` sort.  In the encoding the only quantifier
is `BoundedFormula.all`, and every sorted quantifier is guarded (`GuardsLast`), so the class is
Mathlib's `BoundedFormula.IsQF` relaxed by allowing `all` nodes whose body carries the `RV`-sort
guard.  This is `Mathlib/ModelTheory/Complexity.lean`'s `IsQF` with one constructor added,
exactly as the paper's notion relaxes quantifier-freeness. -/
inductive IsVFQF {α : Type} : {n : ℕ} → LRV.BoundedFormula α n → Prop
  /-- `⊥` -/
  | falsum {n : ℕ} : IsVFQF (⊥ : LRV.BoundedFormula α n)
  /-- an atomic formula -/
  | of_isAtomic {n : ℕ} {φ : LRV.BoundedFormula α n} (h : φ.IsAtomic) : IsVFQF φ
  /-- implication -/
  | imp {n : ℕ} {φ ψ : LRV.BoundedFormula α n} (h₁ : IsVFQF φ) (h₂ : IsVFQF ψ) :
      IsVFQF (φ.imp ψ)
  /-- the quantifier `∀ x ∈ RV, χ`, written in the encoding's guarded form -/
  | all_rv {n : ℕ} {χ : LRV.BoundedFormula α (n + 1)} (h : IsVFQF χ)
      (hg : GuardsLast .rv (Fin.last n) χ) : IsVFQF (BoundedFormula.all χ)

/-- The encoding's guarded existential `∃ x ∈ s, ψ`, for an arbitrary parameter type `α`
(`LRV.exSorted` is the case `α = Empty`). -/
def exSortedG {α : Type} {k : ℕ} (s : SortTag) (ψ : LRV.BoundedFormula α (k + 1)) :
    LRV.BoundedFormula α k :=
  BoundedFormula.ex (sortPredG s (Term.var (Sum.inr (Fin.last k))) ⊓ ψ)

namespace IsVFQF

variable {α : Type} {n : ℕ}

theorem not {φ : LRV.BoundedFormula α n} (h : IsVFQF φ) : IsVFQF φ.not :=
  IsVFQF.imp h (IsVFQF.falsum (α := α))

theorem top : IsVFQF (⊤ : LRV.BoundedFormula α n) :=
  IsVFQF.falsum.not

theorem inf {φ ψ : LRV.BoundedFormula α n} (h₁ : IsVFQF φ) (h₂ : IsVFQF ψ) :
    IsVFQF (φ ⊓ ψ) :=
  IsVFQF.imp (IsVFQF.imp h₁ h₂.not) IsVFQF.falsum

theorem sup {φ ψ : LRV.BoundedFormula α n} (h₁ : IsVFQF φ) (h₂ : IsVFQF ψ) :
    IsVFQF (φ ⊔ ψ) :=
  IsVFQF.imp h₁.not h₂

theorem iff {φ ψ : LRV.BoundedFormula α n} (h₁ : IsVFQF φ) (h₂ : IsVFQF ψ) :
    IsVFQF (φ ⇔ ψ) :=
  IsVFQF.inf (IsVFQF.imp h₁ h₂) (IsVFQF.imp h₂ h₁)

/-- A relation of `L_RV` applied to a term is `VF`-quantifier-free (here: `t ∈ RV`). -/
theorem rvSort_atom {t : LRV.Term (α ⊕ Fin n)} : IsVFQF (pRVG t : LRV.BoundedFormula α n) :=
  IsVFQF.of_isAtomic (BoundedFormula.IsAtomic.rel (L := LRV) (l := 1) Rel.memRV ![t])

/-- The guard atom `xᵢ ∈ RV` is `VF`-quantifier-free. -/
theorem guardAtom_rv (i : Fin n) : IsVFQF (guardAtom .rv i : LRV.BoundedFormula α n) :=
  rvSort_atom (t := Term.var (Sum.inr i))

/-- An existential quantifier over the `RV` sort preserves `VF`-quantifier-freeness: this is the
encoding's `∃ x ∈ RV, ψ`, whose body `x ∈ RV ⊓ ψ` carries the guard. -/
theorem ex_rv {ψ : LRV.BoundedFormula α (n + 1)} (h : IsVFQF ψ) :
    IsVFQF (exSortedG .rv ψ) := by
  have hb : IsVFQF (guardAtom .rv (Fin.last n) ⊓ ψ) :=
    IsVFQF.inf (guardAtom_rv (Fin.last n)) h
  have hgl : GuardsLast .rv (Fin.last n) ((guardAtom .rv (Fin.last n) ⊓ ψ).imp ⊥) :=
    Or.inl (InAntecedent.and_left InAntecedent.atom)
  exact (IsVFQF.all_rv hb.not hgl).not

end IsVFQF

/-! ## 3. Elimination of `VF`-quantifiers -/

/-- **`T` admits elimination of `VF`-quantifiers** — the paper's Proposition `qe:hensel`
(§6, l.1517) in the form the frozen encoding uses for `HasQE` (Theorem 2.3): every formula of the
paper's two-sorted language (`WellSorted`) is `T`-equivalent, at tuples respecting the declared
sorts, to a `VF`-quantifier-free formula of the same fragment. -/
def HasVFQE (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n), WellSorted sα sn φ →
    ∃ ψ : LRV.BoundedFormula α n, IsVFQF ψ ∧ WellSorted sα sn ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ (v : α → M) (x : Fin n → M),
        (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (x i)) →
        (φ.Realize v x ↔ ψ.Realize v x)

/-- **The paper's Lemma at l.1444, in the one-step parametric form in which it is used.**

Paper, verbatim: *"Let `φ(X̄)` be a `VF`-quantifier-free `L_H`-formula, where `X̄ = (X₁, …, Xₙ)`
are the free `VF`-sort variables. Then `Hen_S(0,0)` proves that `∃X̄ φ(X̄)` is equivalent to a
`VF`-quantifier-free `L_H`-formula."*

The free `RV`-sort variables `Ȳ` of `φ(X̄, Ȳ)` — the paper writes them as free, cf. its own proof,
"Let `F_i(X̄)` be the occurring polynomials of `φ(X̄, Ȳ)`" — are the parameter type `α` here, and
`sn` sorts the remaining free variables; the formula `χ` is `φ` with the free `VF`-sort variables
other than the quantified `y` collected in `sn`.  Nothing in the paper's proof uses that `X̄`
exhausts the free `VF`-sort variables, so this is the form in which the Lemma gives Proposition
`qe:hensel` by iteration (see `hasVFQE_of_step`). -/
def VFQE_step (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (χ : LRV.BoundedFormula α (n + 1)),
    WellSorted sα (Fin.snoc sn .vf) χ → IsVFQF χ →
    ∃ ψ : LRV.BoundedFormula α n, IsVFQF ψ ∧ WellSorted sα sn ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ (v : α → M) (x : Fin n → M),
        (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (x i)) →
        ((∃ y : M, sortEval .vf y ∧ χ.Realize v (Fin.snoc (α := fun _ => M) x y)) ↔
          ψ.Realize v x)

/-- The `∀`-case of `hasVFQE_of_step`, with the sort `s` of the quantified variable an explicit
variable so that it can be decided (the sort is otherwise hidden in the type of the
well-sortedness hypothesis). -/
private theorem all_case (T : LRV.Theory) (hstep : VFQE_step T) {α : Type} {sα : α → SortTag}
    {n : ℕ} {sn : Fin n → SortTag} {s : SortTag} {χ : LRV.BoundedFormula α (n + 1)}
    (hχ : WellSorted sα (Fin.snoc sn s) χ) (hg : GuardsLast s (Fin.last n) χ)
    (hj : GuardTrue s (Fin.last n) χ)
    (ih : ∃ ψ : LRV.BoundedFormula α (n + 1), IsVFQF ψ ∧ WellSorted sα (Fin.snoc sn s) ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ (v : α → M) (x : Fin (n + 1) → M),
        (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (Fin.snoc (α := fun _ => SortTag) sn s i) (x i)) →
        (χ.Realize v x ↔ ψ.Realize v x)) :
    ∃ ψ : LRV.BoundedFormula α n, IsVFQF ψ ∧ WellSorted sα sn ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ (v : α → M) (x : Fin n → M),
        (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (x i)) →
        ((BoundedFormula.all χ).Realize v x ↔ ψ.Realize v x) := by
  obtain ⟨ψ, hq, hw, he⟩ := ih
  cases s with
  | vf =>
      -- `∀ x ∈ VF, χ` is `¬∃ x ∈ VF, ¬χ`; the step hypothesis removes the existential
      obtain ⟨θ, hqθ, hwθ, heθ⟩ :=
        hstep α sα n sn (BoundedFormula.not ψ) (wellSorted_not sα (Fin.snoc sn .vf) hw)
          hq.not
      refine ⟨BoundedFormula.not θ, hqθ.not, wellSorted_not sα sn hwθ, ?_⟩
      intro M _ hM v x hv hx
      rw [BoundedFormula.realize_all, BoundedFormula.realize_not]
      have heψ := he M hM v
      have heθ' := heθ M hM v x hv hx
      rw [← heθ']
      constructor
      · rintro hall ⟨y, hy, hny⟩
        exact hny ((heψ (Fin.snoc (α := fun _ => M) x y) hv (sorted_snoc hx hy)).mp
          (hall y))
      · intro hno a
        by_cases ha : sortEval .vf a
        · refine (heψ (Fin.snoc (α := fun _ => M) x a) hv (sorted_snoc hx ha)).mpr ?_
          by_contra hna
          exact hno ⟨a, ha, hna⟩
        · exact guardTrue_true hj v (Fin.snoc (α := fun _ => M) x a) (by rwa [Fin.snoc_last])
  | rv =>
      -- the guarded universal over `RV` is `VF`-quantifier-free: re-attach the guard
      have hbody : IsVFQF (guardAtom .rv (Fin.last n) ⟹ ψ) :=
        IsVFQF.imp (IsVFQF.guardAtom_rv (Fin.last n)) hq
      have hgl : GuardsLast .rv (Fin.last n) (guardAtom .rv (Fin.last n) ⟹ ψ) :=
        Or.inl InAntecedent.atom
      have hwguard : WellSorted sα (Fin.snoc sn .rv)
          (guardAtom .rv (Fin.last n) : LRV.BoundedFormula α (n + 1)) :=
        WellSorted.rel (Fin.snoc sn .rv) Rel.memRV
          ![Term.var (Sum.inr (Fin.last n))]
          (fun i => by
            fin_cases i
            rw [rel_argSort_memRV]
            simpa using tmSort_var_inr sα (Fin.snoc sn .rv) (Fin.last n))
      have hwb : WellSorted sα (Fin.snoc sn .rv) (guardAtom .rv (Fin.last n) ⟹ ψ) :=
        WellSorted.imp _ hwguard hw
      have hgb : GuardTrue .rv (Fin.last n) (guardAtom .rv (Fin.last n) ⟹ ψ) :=
        GuardTrue.imp InAntecedent.atom
      refine ⟨BoundedFormula.all (guardAtom .rv (Fin.last n) ⟹ ψ),
        IsVFQF.all_rv hbody hgl, WellSorted.all (sα := sα) sn hwb hgl hgb, ?_⟩
      intro M _ hM v x hv hx
      rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
      have heψ := he M hM v
      constructor
      · intro hall a ha
        have ha' : sortEval .rv a := by
          have hg' := (sortPredG_var_realize (M := M) .rv (Fin.last n) v
            (Fin.snoc (α := fun _ => M) x a)).mp ha
          rwa [Fin.snoc_last] at hg'
        exact (heψ (Fin.snoc (α := fun _ => M) x a) hv (sorted_snoc hx ha')).mp (hall a)
      · intro hall a
        by_cases ha : sortEval .rv a
        · have hga : (guardAtom .rv (Fin.last n) : LRV.BoundedFormula α (n + 1)).Realize v
              (Fin.snoc (α := fun _ => M) x a) :=
            (sortPredG_var_realize (M := M) .rv (Fin.last n) v
              (Fin.snoc (α := fun _ => M) x a)).mpr (by rwa [Fin.snoc_last])
          exact (heψ (Fin.snoc (α := fun _ => M) x a) hv (sorted_snoc hx ha)).mpr (hall a hga)
        · exact guardTrue_true hj v (Fin.snoc (α := fun _ => M) x a) (by rwa [Fin.snoc_last])

/-- **"By elementary logic this lemma yields:" (paper, §6, after the Lemma at l.1444)** —
elimination of `VF`-quantifiers from the one-step elimination of an existential `VF`-quantifier.

Induction on the well-sortedness derivation.  Atoms are `VF`-quantifier-free; connectives are
componentwise; a quantifier over the `RV` sort stays `VF`-quantifier-free once the guard is
re-attached, and it *is* equivalent to its guarded form because the body is junk-true off the `RV`
sort (`guardTrue_true`); a quantifier over the `VF` sort is removed by the step hypothesis, after
converting `∀ x ∈ VF` into `¬∃ x ∈ VF, ¬`. -/
theorem hasVFQE_of_step (T : LRV.Theory) (hstep : VFQE_step T) : HasVFQE T := by
  intro α sα n sn φ hφ
  induction hφ with
  | falsum sn =>
      exact ⟨⊥, IsVFQF.falsum, WellSorted.falsum (sα := sα) sn, fun M _ _ v x _ _ => Iff.rfl⟩
  | equal sn ht hu =>
      exact ⟨_, IsVFQF.of_isAtomic (BoundedFormula.IsAtomic.equal _ _),
        WellSorted.equal (sα := sα) sn ht hu, fun M _ _ v x _ _ => Iff.rfl⟩
  | rel sn R ts h =>
      have his := BoundedFormula.IsAtomic.rel R ts
      simp only [Relations.boundedFormula] at his
      exact ⟨BoundedFormula.rel R ts, IsVFQF.of_isAtomic his,
        WellSorted.rel (sα := sα) sn R ts h, fun M _ _ v x _ _ => Iff.rfl⟩
  | imp sn ha hb iha ihb =>
      obtain ⟨ψa, hqa, hwa, hea⟩ := iha
      obtain ⟨ψb, hqb, hwb, heb⟩ := ihb
      refine ⟨ψa.imp ψb, IsVFQF.imp hqa hqb, WellSorted.imp (sα := sα) sn hwa hwb, ?_⟩
      intro M _ hM v x hv hx
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, hea M hM v x hv hx,
        heb M hM v x hv hx]
  | all sn hχ hg hj ih =>
      exact all_case T hstep hχ hg hj ih

/-- **Proposition `qe:hensel`** (paper, §6, l.1517), verbatim: *"The theory `Hen_S(0,0)` admits
elimination of `VF`-quantifiers."*  Derived here from the paper's Lemma (l.1444) in its one-step
form; the theory is otherwise arbitrary, so this is the paper's "by elementary logic" step and
nothing else. -/
theorem qe_hensel (T : LRV.Theory) (h : VFQE_step T) : HasVFQE T :=
  hasVFQE_of_step T h

/-! ## 4. The theory `Hen_S(0,0)`

Paper, §6, l.1450: *"Let `Hen_S(0,0)` be the theory of henselian fields of pure characteristic
`0` in a language `L_H` that expands `L_RV`, where the expansion happens only in the `RV`-sort.
Such a theory may be formulated as in Definition 2.2, with obvious modifications.  Note that
`Hen_S(0,0)` includes the statement that the function `rv` is surjective."*

We work in `L_RV` itself: the paper's elimination is of `VF`-quantifiers, on which the `RV`-sort
expansion symbols have no bearing.  The axioms are the frozen ones of Definition 2.2 except the
two algebraic-closedness schemes **and** the divisibility of `K^×`: neither is entailed by
henselianity in pure characteristic `0` (`k((t))` with `k` algebraically closed of
characteristic `0` is henselian of pure characteristic `0` and its value group is `ℤ`, so `K^×`
is not divisible).  The henselian scheme is the parameter `hsel`: any `L_RV` formulation of
henselianity may be substituted, and nothing below inspects it. -/

/-- Definition 2.2 item 2 as it holds in a henselian field of pure characteristic `0`:
`(RV^×, 1, ×)` is an abelian group and `×` is augmented by the absorbing `0 = ∞`; the frozen
`Axioms.repairRV` sentences are added elsewhere.  Divisibility (`Axioms.rvDivisible`) is
dropped. -/
def rvGroupND : LRV.Theory :=
  Axioms.ofList [Axioms.rvOneMem, Axioms.rvMulMem, Axioms.rvMulAssoc, Axioms.rvMulComm,
    Axioms.rvMulOne, Axioms.rvMulInv, Axioms.rvMulZeroK, Axioms.rvMulInfty]

/-- The `L_RV`-axioms of `Hen_S(0,0)` other than the henselian scheme: the encoding's carrier
sentences, Definition 2.2 items 1, 3, 4, 5, 6, and pure characteristic `0`, i.e. characteristic
`0` for `VF` and for the residue field `K = K^× ∪ {0}`. -/
def henSBase : LRV.Theory :=
  Axioms.sortAxioms ∪ Axioms.vfField ∪ Axioms.kField ∪ rvGroupND ∪ Axioms.preorderRV ∪
    Axioms.rvAxioms ∪ Axioms.repairRV ∪ {s | ∃ k, s = Axioms.charZeroVF k} ∪
      {s | ∃ p, p.Prime ∧ s = Axioms.residueCharZero p}

/-- **`Hen_S(0,0)`**: the theory of henselian fields of pure characteristic `0` in `L_RV`
(paper, §6, l.1450).  `hsel` is its henselian scheme. -/
def HenS00 (hsel : LRV.Theory) : LRV.Theory := henSBase ∪ hsel

/-- The paper's Lemma (l.1444) as a hypothesis about `Hen_S(0,0)`: the content the paper derives
there from Theorem 5.5 (`special:bi:polynomial:constant`) and Lemma `cut:to:hensel:substru`. -/
def hensel_qe_lemma_statement (hsel : LRV.Theory) : Prop := VFQE_step (HenS00 hsel)

/-- **Proposition `qe:hensel` for `Hen_S(0,0)`** (paper, §6, l.1517): the theory of henselian
fields of pure characteristic `0` admits elimination of `VF`-quantifiers, given the paper's Lemma
at l.1444. -/
theorem qe_hensel_HenS00 (hsel : LRV.Theory) (h : hensel_qe_lemma_statement hsel) :
    HasVFQE (HenS00 hsel) :=
  hasVFQE_of_step (HenS00 hsel) h

end Sec6
end SpecialTransformations.Milestone0

#print axioms SpecialTransformations.Milestone0.Sec6.sortPredG_var_realize
#print axioms SpecialTransformations.Milestone0.Sec6.guardTrue_true
#print axioms SpecialTransformations.Milestone0.Sec6.IsVFQF.ex_rv
#print axioms SpecialTransformations.Milestone0.Sec6.hasVFQE_of_step
#print axioms SpecialTransformations.Milestone0.Sec6.qe_hensel_HenS00
