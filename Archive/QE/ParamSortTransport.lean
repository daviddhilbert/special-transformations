/-
**`WellSorted` is preserved by the shrink** — from swarm `smw1bwjo2` m2, verified here (compiled,
0 errors, no `sorry`).  `wellSorted_shrink_of_isQF` is what lets the bridge move a *quantifier-free*
well-sorted formula back across `shrinkAux` with its sort assignment intact.
-/
import ParamShrink

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace W4

variable {α : Type} {m n : ℕ}

/-! ### The index map, by value -/

theorem gVar_of_lt (V : Fin m → α) (k : ℕ) (i : Fin (m + (n + k))) (h : (i : ℕ) < m) :
    gVar V k i = Sum.inl (V ⟨i, h⟩) := by
  have h2 : finSumFinEquiv (Sum.inl (⟨(i:ℕ), h⟩ : Fin m)) = i := by
    rw [finSumFinEquiv_apply_left]
    exact Fin.ext rfl
  have h1 : finSumFinEquiv.symm i = Sum.inl (⟨(i:ℕ), h⟩ : Fin m) :=
    (Equiv.symm_apply_eq _).mpr h2.symm
  simp only [gVar, h1, Sum.elim_inl]

theorem gVar_of_ge (V : Fin m → α) (k : ℕ) (i : Fin (m + (n + k))) (h : m ≤ (i : ℕ)) :
    gVar V k i = Sum.inr (⟨(i:ℕ) - m, by omega⟩ : Fin (n + k)) := by
  have h2 : finSumFinEquiv (Sum.inr (⟨(i:ℕ) - m, by omega⟩ : Fin (n + k))) = i := by
    rw [finSumFinEquiv_apply_right]
    exact Fin.ext (by simp only [Fin.val_natAdd]; omega)
  have h1 : finSumFinEquiv.symm i = Sum.inr (⟨(i:ℕ) - m, by omega⟩ : Fin (n + k)) :=
    (Equiv.symm_apply_eq _).mpr h2.symm
  simp only [gVar, h1, Sum.elim_inr]

/-! ### `TmSort` is preserved by the shrink -/

theorem tmSort_shrink (V : Fin m → α) (sα : α → SortTag) (k : ℕ)
    (snT : Fin (n + k) → SortTag) :
    ∀ (t : LRV.Term (Empty ⊕ Fin (m + (n + k)))) (s : SortTag),
      TmSort (fun e : Empty => e.elim) (fun i => Sum.elim sα snT (gVar V k i)) t = some s →
      TmSort sα snT (t.relabel (gmap V k)) = some s := by
  intro t
  induction t with
  | var i =>
      rcases i with e | i
      · intro s h; exact e.elim
      · intro s h
        have hh : Sum.elim sα snT (gVar V k i) = s := by
          simpa only [TmSort, Option.some.injEq] using h
        have hgg : (Term.var (Sum.inr i) : LRV.Term (Empty ⊕ Fin (m + (n + k)))).relabel
            (gmap V k) = Term.var (gVar V k i) := rfl
        rw [hgg, ← hh]
        rcases gVar V k i with a | r <;> rfl
  | func f ts ih =>
      intro s h
      have hiff := tmSort_func_iff (sα := fun e : Empty => e.elim)
        (sn := fun i => Sum.elim sα snT (gVar V k i)) (s := s) f ts
      obtain ⟨harg, hres⟩ := hiff.1 h
      rw [← hres]
      refine (tmSort_func_iff (sα := sα) (sn := snT) (s := Fn.resSort f) f
        (fun i => (ts i).relabel (gmap V k))).2 ⟨fun i => ?_, rfl⟩
      exact ih i (Fn.argSort f i) (harg i)

/-! ### Atoms: the sort predicate at a shrunk variable -/

theorem shrink_sortPredG (V : Fin m → α) (k : ℕ) (s : SortTag) (i : Fin (m + (n + k)))
    (hi : m ≤ (i : ℕ)) :
    shrinkAux V k (sortPredG s (Term.var (Sum.inr i)))
      = sortPredG s (Term.var (Sum.inr (⟨(i:ℕ) - m, by omega⟩ : Fin (n + k)))) := by
  have hg := gVar_of_ge V k i hi
  have key : ∀ (R : LRV.Relations 1),
      shrinkAux V k (BoundedFormula.rel R ![Term.var (Sum.inr i)])
        = BoundedFormula.rel R
            ![Term.var (Sum.inr (⟨(i:ℕ) - m, by omega⟩ : Fin (n + k)))] := by
    intro R
    simp only [shrinkAux]
    congr 1
    funext j
    fin_cases j
    show Term.relabel (gmap V k) (Term.var (Sum.inr i))
      = Term.var (Sum.inr (⟨(i:ℕ) - m, _⟩ : Fin (n + k)))
    rw [show Term.relabel (gmap V k) (Term.var (Sum.inr i)) = Term.var (gVar V k i) from rfl, hg]
  rcases s with _ | _ <;> exact key _

/-! ### QF formulas: `WellSorted` is preserved by the shrink -/

theorem isQF_imp_iff {φ ψ : LRV.BoundedFormula α n} (h : (φ.imp ψ).IsQF) :
    φ.IsQF ∧ ψ.IsQF := by
  cases h with
  | imp h1 h2 => exact ⟨h1, h2⟩
  | of_isAtomic h => cases h

set_option maxHeartbeats 1000000 in
theorem wellSorted_shrink_of_isQF (V : Fin m → α) (sα : α → SortTag) :
    ∀ (k : ℕ) (snT : Fin (n + k) → SortTag) (χ : LRV.BoundedFormula Empty (m + (n + k))),
      χ.IsQF →
      WellSorted (fun e : Empty => e.elim) (fun i => Sum.elim sα snT (gVar V k i)) χ →
      WellSorted sα snT (shrinkAux V k χ)
  | k, snT, .falsum, _, _ => by simp only [shrinkAux]; exact WellSorted.falsum snT
  | k, snT, .equal t u, _, h => by
      simp only [shrinkAux]
      cases h with
      | equal sn ht hu =>
          exact WellSorted.equal snT (tmSort_shrink V sα k snT t _ ht)
            (tmSort_shrink V sα k snT u _ hu)
  | k, snT, .rel R ts, _, h => by
      simp only [shrinkAux]
      cases h with
      | rel sn R ts harg =>
          exact WellSorted.rel snT R _ (fun i => tmSort_shrink V sα k snT (ts i) _ (harg i))
  | k, snT, .imp a b, hQF, h => by
      simp only [shrinkAux]
      obtain ⟨h1, h2⟩ := isQF_imp_iff hQF
      cases h with
      | imp sn ha hb =>
          exact WellSorted.imp snT (wellSorted_shrink_of_isQF V sα k snT a h1 ha)
            (wellSorted_shrink_of_isQF V sα k snT b h2 hb)
  | k, snT, .all χ, hQF, _ => absurd hQF (BoundedFormula.not_all_isQF χ)

end W4
