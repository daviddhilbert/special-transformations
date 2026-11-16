module

/-
**Parameter relabelling of the well-sorted fragment** — from swarm `smw1bwjo2` m2, verified here
(compiled; 0 errors, no `sorry`, axioms within {propext, Classical.choice, Quot.sound}).  The earlier
swarm recorded this transport as *not* delivered; with `Occurs := InAntecedent` it is routine,
because the guard transports by its own constructors, which a compiled match could not do.

`wellSorted_relabel`: for `g : α → β ⊕ Fin m` sending every parameter to a *same-sorted* name —
either a parameter of `β` or one of `m` new leading variables — `WellSorted sα sn ψ` gives
`WellSorted sβ (sortAssem sG sn) (ψ.relabel g)`.  This is the parameter ⇄ variable promotion the
`hasQE_of_hasQE_empty` bridge needs, and (independently) what section 3 needs to move `acl` between
parameter pairs.

`guardsLast_of_GuardTrue` is a fact about the frozen predicate worth knowing: `GuardTrue` implies
`GuardsLast`, so `WellSorted.all`'s `hg` field is redundant given `hj`.  The frozen constructor keeps
both (and that is fine); it means the guard information is carried once, not twice.
-/
/-
Transport of `TmSort`, `InAntecedent`, `GuardTrue` and `WellSorted` along Mathlib's
`BoundedFormula.relabel`, in the direction that turns parameters into leading variables.
This is the piece that the old compiled `Occurs` could not do; with `Occurs := InAntecedent`
an inductive family, the guard transports by its own constructors.
-/
public import ParamBridgeShift

@[expose] public section

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
namespace ParamBridge

open LRV

set_option maxHeartbeats 2000000

variable {α β : Type} {m k : ℕ}

/-! ### The sort assignment of a relabel -/

/-- The sort assignment at the target context `Fin (m+k)`: the first `m` names are the new
"parameter variables", the last `k` are the original variables. -/
noncomputable def sortAssem (sG : Fin m → SortTag) (sn : Fin k → SortTag) :
    Fin (m + k) → SortTag :=
  fun x => if h : (x : ℕ) < m then sG ⟨(x : ℕ), h⟩ else sn ⟨(x : ℕ) - m, by omega⟩

theorem sortAssem_castAdd (sG : Fin m → SortTag) (sn : Fin k → SortTag) (j : Fin m) :
    sortAssem sG sn (Fin.castAdd k j) = sG j := by
  simp only [sortAssem, Fin.val_castAdd, dif_pos j.isLt]

theorem sortAssem_natAdd (sG : Fin m → SortTag) (sn : Fin k → SortTag) (i : Fin k) :
    sortAssem sG sn (Fin.natAdd m i) = sn i := by
  have h : ¬ ((Fin.natAdd m i : Fin (m+k)) : ℕ) < m := by simp only [Fin.val_natAdd]; omega
  rw [sortAssem, dif_neg h]
  exact congrArg sn (Fin.ext (by simp only [Fin.val_mk, Fin.val_natAdd]; omega))

theorem sortAssem_snoc (sG : Fin m → SortTag) (sn : Fin k → SortTag) (s : SortTag) :
    sortAssem sG (Fin.snoc sn s) = Fin.snoc (sortAssem sG sn) s := by
  funext x
  induction x using Fin.addCases with
  | left j =>
      rw [sortAssem_castAdd, Fin.snoc_castAdd, sortAssem_castAdd]
  | right i =>
      rw [sortAssem_natAdd]
      have h3 := congrFun (Fin.snoc_comp_natAdd (f := sortAssem sG sn) (a := s) (n := k) (m := m)) i
      rw [show (sortAssem sG sn) ∘ (Fin.natAdd m) = sn from
        funext (fun i => sortAssem_natAdd sG sn i)] at h3
      exact h3.symm

/-! ### The index map `relabelAux`, by shape -/

theorem relabelAux_inr (g : α → β ⊕ Fin m) (i : Fin k) :
    BoundedFormula.relabelAux g k (Sum.inr i) = Sum.inr (Fin.natAdd m i) := by
  simp [BoundedFormula.relabelAux]

theorem relabelAux_inl (g : α → β ⊕ Fin m) (a : α) :
    BoundedFormula.relabelAux g k (Sum.inl a) =
      Sum.map id (Fin.castAdd k) (g a) := by
  rcases h : g a with b | j
  · simp [BoundedFormula.relabelAux, h]
  · simp [BoundedFormula.relabelAux, h]

/-! ### `TmSort` is preserved by a relabel that maps parameters to sorted names -/

theorem tmSort_relabelAux (g : α → β ⊕ Fin m) (sα : α → SortTag) (sβ : β → SortTag)
    (sG : Fin m → SortTag) (sn : Fin k → SortTag)
    (hg : ∀ b, (∀ b', g b = Sum.inl b' → sβ b' = sα b) ∧
      (∀ j, g b = Sum.inr j → sG j = sα b)) :
    ∀ (t : LRV.Term (α ⊕ Fin k)) (s : SortTag),
      TmSort sα sn t = some s →
      TmSort sβ (sortAssem sG sn) (t.relabel (BoundedFormula.relabelAux g k)) = some s := by
  intro t
  induction t with
  | var x =>
      rintro s h
      rcases x with a | i
      · obtain rfl : sα a = s := by simpa only [TmSort, Option.some.injEq] using h
        simp only [Term.relabel, relabelAux_inl]
        rcases hga : g a with b | j
        · simp only [Sum.map_inl, TmSort]
          exact congrArg some (hg a |>.1 b hga)
        · simp only [Sum.map_inr, TmSort, sortAssem_castAdd]
          exact congrArg some (hg a |>.2 j hga)
      · obtain rfl : sn i = s := by simpa only [TmSort, Option.some.injEq] using h
        simp only [Term.relabel, relabelAux_inr, TmSort, sortAssem_natAdd, Sum.elim_inr]
  | func f ts ih =>
      rintro s h
      obtain ⟨harg, hres⟩ := (tmSort_func_iff sα sn f ts (s := s)).1 h
      rw [← hres]
      exact tmSort_func sβ _ f (fun i => (ts i).relabel (BoundedFormula.relabelAux g k))
        (fun i => ih i (Fn.argSort f i) (harg i))

/-! ### The sort predicate at a relabelled variable -/

theorem relabel_sortPredG (g : α → β ⊕ Fin m) (s : SortTag) (i : Fin k) :
    (sortPredG (α := α) s (Term.var (Sum.inr i))).relabel g =
      sortPredG (α := β) s (Term.var (Sum.inr (Fin.natAdd m i)) : LRV.Term (β ⊕ Fin (m + k))) := by
  have key : ∀ (R : LRV.Relations 1),
      (BoundedFormula.rel R ![Term.var (Sum.inr i)] : LRV.BoundedFormula α k).relabel g
        = BoundedFormula.rel R
            (![Term.var (Sum.inr (Fin.natAdd m i))] : Fin 1 → LRV.Term (β ⊕ Fin (m + k))) := by
    intro R
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel]
    congr 1
    funext j
    fin_cases j
    show Term.relabel (BoundedFormula.relabelAux g k) (Term.var (Sum.inr i))
      = Term.var (Sum.inr (Fin.natAdd m i))
    simp only [Term.relabel, relabelAux_inr]
  rcases s with _ | _ <;> exact key _

/-! ### The guard is preserved by a relabel -/

theorem inAntecedent_relabel (g : α → β ⊕ Fin m) {N : ℕ} {s : SortTag} {i : Fin N}
    {η : LRV.BoundedFormula α N} (h : InAntecedent s i η) :
    InAntecedent s (Fin.natAdd m i) (η.relabel g) := by
  induction h with
  | atom =>
      show InAntecedent s (Fin.natAdd m _)
        ((sortPredG (α := α) s (Term.var (Sum.inr _))).relabel g)
      rw [relabel_sortPredG]
      exact InAntecedent.atom
  | and_left ha ih => exact InAntecedent.and_left ih
  | and_right hb ih => exact InAntecedent.and_right ih

theorem guardTrue_relabel (g : α → β ⊕ Fin m) {N : ℕ} {s : SortTag} {i : Fin N}
    {χ : LRV.BoundedFormula α N} (h : GuardTrue s i χ) :
    GuardTrue s (Fin.natAdd m i) (χ.relabel g) := by
  induction h with
  | imp hin => exact GuardTrue.imp (inAntecedent_relabel g hin)
  | @all N' iB χB hgt ih =>
      rw [BoundedFormula.relabel_all]
      have h2 : Fin.natAdd m (Fin.castSucc iB) = Fin.castSucc (Fin.natAdd m iB) := Fin.ext rfl
      rw [h2] at ih
      exact GuardTrue.all ih

theorem guardsLast_of_guardTrue {s : SortTag} {N : ℕ} {i : Fin N}
    {χ : LRV.BoundedFormula α N} (h : GuardTrue s i χ) : GuardsLast s i χ := by
  induction h with
  | imp hin => exact Or.inl hin
  | all hgt ih => exact ih

/-- **`WellSorted` is preserved by a relabel that maps parameters to sorted names** -/
theorem wellSorted_relabel (g : α → β ⊕ Fin m) (sα : α → SortTag) (sβ : β → SortTag)
    (sG : Fin m → SortTag)
    (hg : ∀ b, (∀ b', g b = Sum.inl b' → sβ b' = sα b) ∧
      (∀ j, g b = Sum.inr j → sG j = sα b))
    {k : ℕ} {sn : Fin k → SortTag} {ψ : LRV.BoundedFormula α k}
    (h : WellSorted sα sn ψ) :
    WellSorted sβ (sortAssem sG sn) (ψ.relabel g) := by
  induction h with
  | falsum => exact WellSorted.falsum _
  | equal snB ht hu =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel]
      exact WellSorted.equal _ (tmSort_relabelAux g sα sβ sG snB hg _ _ ht)
        (tmSort_relabelAux g sα sβ sG snB hg _ _ hu)
  | rel snB R ts harg =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel]
      exact WellSorted.rel _ R _ (fun i => tmSort_relabelAux g sα sβ sG snB hg _ _ (harg i))
  | imp snB ha hb iha ihb =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel]
      exact WellSorted.imp _ iha ihb
  | @all N snB sB χB hχ hgL hj ih =>
      rw [BoundedFormula.relabel_all]
      have hgt : GuardsLast sB (Fin.last (m + N)) (χB.relabel g) := by
        have h1 : Fin.natAdd m (Fin.last N) = (Fin.last (m + N)) := Fin.ext rfl
        rw [← h1]
        exact guardsLast_of_guardTrue (guardTrue_relabel g hj)
      refine WellSorted.all (s := sB) _ ?_ hgt (guardTrue_relabel g hj)
      rw [← sortAssem_snoc]
      exact ih

end ParamBridge
end Milestone0
end SpecialTransformations
