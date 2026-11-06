import Enc
import Mathlib.Data.Finite.Sum

/-! Generic logical reduction from one-step VF elimination. Adapted from the local
legacy Section6/Sec6QE.lean; this proves no henselian elimination step. -/

set_option linter.unusedSimpArgs false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6

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

/-- Uniform parametric one-step elimination, sufficient for the logical
induction below. Establishing this hypothesis for the henselian theory is
part of the remaining syntactic assembly of Lemma 6.3. In particular the
output formula is chosen before the model and the free assignment. This
LRV interface does not yet cover arbitrary RV expansions. -/
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


end SpecialTransformations.Section6
