module

/-
**Parameter substitution on `L_RV`: `TmSort`/`WellSorted` are preserved.**

Mathlib's `BoundedFormula.subst (f : α → Term β)` replaces *parameters* by terms (the direction that
`relabel` cannot do: `relabel` maps parameters into parameters-or-*new* variables).  It has
`realize_subst` but no sort preservation, which is what this file supplies — the companion of
`QE/SubstVar.lean` (variables ↦ terms) in the other direction.

`subst` is `mapTermRel` with the term map `t ↦ t.subst (Sum.elim (relabel Sum.inl ∘ f) (var ∘ inr))`
at every depth, so bound variables are untouched and the substitution is uniform; the guard atoms
`guardAtom s i` are parameter-free, hence fixed by it, which is why `InAntecedent`/`GuardTrue`
transport without any shift.

**Proved, no `sorry`**: `tmSort_substParam` (term level), `tmSort_relabel_inl_indep` (`TmSort` of a
parameter-only term does not depend on the variable context — the ingredient the `.all` case needs),
`subst_guardAtom`, `inAntecedent_substParam`, `guardTrue_substParam`, and `wellSorted_substParam`;
`#print axioms` within {propext, Classical.choice, Quot.sound}.

Build: `.scratch2/sec3/` holds a compiled `Enc`; copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
public import Enc
public import ParamBridgeRelabel

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0

variable {α β : Type} {n : ℕ}

/-- The assignment used by `BoundedFormula.subst`: parameters go through `f` (relabelled into the
ambient variable context), variables stay. -/
def substAssign (f : α → LRV.Term β) (n : ℕ) : α ⊕ Fin n → LRV.Term (β ⊕ Fin n) :=
  Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)

/-- `subst` is `mapTermRel` at that assignment (definitional, but stated for rewriting). -/
theorem subst_eq_mapTermRel (φ : LRV.BoundedFormula α n) (f : α → LRV.Term β) :
    φ.subst f = φ.mapTermRel (fun n t => t.subst (substAssign f n)) (fun _ => id) (fun _ => id) :=
  rfl

/-- **The sort of a term is preserved by a sort-preserving parameter substitution.** -/
theorem tmSort_substParam (sα : α → SortTag) (sβ : β → SortTag) (sn : Fin n → SortTag)
    {f : α → LRV.Term β}
    (hf : ∀ a : α, TmSort sβ sn ((f a).relabel (Sum.inl : β → β ⊕ Fin n)) = some (sα a))
    (t : LRV.Term (α ⊕ Fin n)) :
    TmSort sβ sn (t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)))
      = TmSort sα sn t := by
  induction t with
  | var a =>
    rcases a with a | i
    · exact hf a
    · rfl
  | func g ts ih =>
    have key : ∀ i, TmSort sβ sn
        ((ts i).subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)))
          = TmSort sα sn (ts i) := ih
    simp only [Term.subst, TmSort]
    by_cases h : ∀ i, TmSort sα sn (ts i) = some (Fn.argSort g i)
    · rw [if_pos (fun i => by rw [key i]; exact h i), if_pos h]
    · rw [if_neg (fun hc => h (fun i => by rw [← key i]; exact hc i)), if_neg h]

/-- The guard atom is parameter-free, so a parameter substitution fixes it. -/
theorem subst_guardAtom (s : SortTag) (i : Fin n) (g : α → LRV.Term β) :
    (guardAtom s i : LRV.BoundedFormula α n).subst g =
      (guardAtom s i : LRV.BoundedFormula β n) := by
  cases s with
  | vf =>
    show (BoundedFormula.rel (L := LRV) Rel.memVF ![Term.var (Sum.inr i)]).subst g
      = BoundedFormula.rel (L := LRV) Rel.memVF ![Term.var (Sum.inr i)]
    simp only [BoundedFormula.subst, BoundedFormula.mapTermRel]
    congr 1
    funext j
    fin_cases j
    simp [substAssign]
  | rv =>
    show (BoundedFormula.rel (L := LRV) Rel.memRV ![Term.var (Sum.inr i)]).subst g
      = BoundedFormula.rel (L := LRV) Rel.memRV ![Term.var (Sum.inr i)]
    simp only [BoundedFormula.subst, BoundedFormula.mapTermRel]
    congr 1
    funext j
    fin_cases j
    simp [substAssign]

/-- `InAntecedent` is carried by a parameter substitution. -/
theorem inAntecedent_substParam {s : SortTag} {i : Fin n} {η : LRV.BoundedFormula α n}
    (h : InAntecedent s i η) (g : α → LRV.Term β) :
    InAntecedent s i (η.subst g) := by
  induction h with
  | atom => rw [subst_guardAtom]; exact InAntecedent.atom
  | and_left _ ih => exact InAntecedent.and_left ih
  | and_right _ ih => exact InAntecedent.and_right ih

/-- `GuardTrue` is carried by a parameter substitution. -/
theorem guardTrue_substParam {s : SortTag} {i : Fin n} {χ : LRV.BoundedFormula α n}
    (h : GuardTrue s i χ) (g : α → LRV.Term β) :
    GuardTrue s i (χ.subst g) := by
  induction h with
  | imp hin => exact GuardTrue.imp (inAntecedent_substParam hin g)
  | @all k iB χB hgt ih =>
    show GuardTrue s iB (BoundedFormula.all (χB.subst g))
    exact GuardTrue.all ih

/-- **`TmSort` of a parameter-only term does not depend on the variable context.**  Needed to
transport the substitution's sort hypothesis from `sn` to `Fin.snoc sn s` when passing under a
quantifier: `(f a)` is a term over `β` alone, so it has no `Sum.inr` variables. -/
theorem tmSort_relabel_inl_indep (sβ : β → SortTag) :
    ∀ (t : LRV.Term β) {n m : ℕ} (sn : Fin n → SortTag) (sm : Fin m → SortTag),
      TmSort sβ sn (t.relabel (Sum.inl : β → β ⊕ Fin n)) =
        TmSort sβ sm (t.relabel (Sum.inl : β → β ⊕ Fin m))
  | .var b, _, _, _, _ => rfl
  | .func g ts, n, m, sn, sm => by
    have key : ∀ i, TmSort sβ sn ((ts i).relabel (Sum.inl : β → β ⊕ Fin n))
        = TmSort sβ sm ((ts i).relabel (Sum.inl : β → β ⊕ Fin m)) :=
      fun i => tmSort_relabel_inl_indep sβ (ts i) sn sm
    have e1 : (∀ i, TmSort sβ sn ((ts i).relabel (Sum.inl : β → β ⊕ Fin n))
          = some (Fn.argSort g i)) ↔
        (∀ i, TmSort sβ sm ((ts i).relabel (Sum.inl : β → β ⊕ Fin m))
          = some (Fn.argSort g i)) := by
      constructor
      · intro h i; rw [← key i]; exact h i
      · intro h i; rw [key i]; exact h i
    simp only [Term.relabel, TmSort]
    by_cases h : ∀ i, TmSort sβ sn ((ts i).relabel (Sum.inl : β → β ⊕ Fin n))
        = some (Fn.argSort g i)
    · rw [if_pos h, if_pos (e1.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (e1.mpr hc))]

/-- **`WellSorted` is preserved by a sort-preserving parameter substitution.**

The proof goes by `BoundedFormula.rec` with the sort assignment quantified *inside* the motive: a
`WellSorted` derivation cannot be inducted on directly, because its index contains `sn` and every
case would come back with a fresh sort assignment. -/
theorem wellSorted_substParam (sα : α → SortTag) (sβ : β → SortTag) :
    ∀ (n : ℕ) (sn : Fin n → SortTag) (f : α → LRV.Term β),
      (∀ a : α, TmSort sβ sn ((f a).relabel (Sum.inl : β → β ⊕ Fin n)) = some (sα a)) →
      ∀ (φ : LRV.BoundedFormula α n), WellSorted sα sn φ → WellSorted sβ sn (φ.subst f) := by
  intro n sn f hf φ
  refine BoundedFormula.rec (motive := fun m (ψ : LRV.BoundedFormula α m) =>
      ∀ (sn : Fin m → SortTag) (f : α → LRV.Term β),
        (∀ a : α, TmSort sβ sn ((f a).relabel (Sum.inl : β → β ⊕ Fin m)) = some (sα a)) →
        WellSorted sα sn ψ → WellSorted sβ sn (ψ.subst f)) ?_ ?_ ?_ ?_ ?_ φ sn f hf
  · -- `falsum`
    intro m sn f hf _
    exact WellSorted.falsum (sα := sβ) sn
  · -- `equal`
    intro m t₁ t₂ sn f hf h
    cases h with
    | equal sn' ht hu =>
      exact WellSorted.equal sn (by rw [tmSort_substParam sα sβ sn hf]; exact ht)
        (by rw [tmSort_substParam sα sβ sn hf]; exact hu)
  · -- `rel`
    intro m l R ts sn f hf h
    cases h with
    | rel sn' R' ts' harg =>
      exact WellSorted.rel sn R _ (fun i => by rw [tmSort_substParam sα sβ sn hf]; exact harg i)
  · -- `imp`
    intro m a b iha ihb sn f hf h
    cases h with
    | imp sn' ha hb => exact WellSorted.imp sn (iha sn f hf ha) (ihb sn f hf hb)
  · -- `all`
    intro m χ ih sn f hf h
    cases h with
    | @all m' sn' s χ' hχ hg hj =>
      have hf' : ∀ a : α,
          TmSort sβ (Fin.snoc sn s) ((f a).relabel (Sum.inl : β → β ⊕ Fin (m + 1)))
            = some (sα a) := by
        intro a
        rw [tmSort_relabel_inl_indep sβ (f a) (Fin.snoc sn s) sn]
        exact hf a
      have hj' : GuardTrue s (Fin.last m) (χ.subst f) := guardTrue_substParam hj f
      exact WellSorted.all (s := s) sn (ih (Fin.snoc sn s) f hf' hχ)
        (ParamBridge.guardsLast_of_guardTrue hj') hj'

end Milestone0
end SpecialTransformations
