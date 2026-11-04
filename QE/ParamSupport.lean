/-
**The support of a formula** — from swarm `smw1bwjo2` m2, verified here (compiled, 0 errors, no
`sorry`).  `paramsOf`/`support` is the finite set of parameters a formula actually mentions, and
`realize_congr` says its truth depends only on that set.  The bridge uses it to shrink the parameter
type to a finite set and then re-expand.
-/
/-
The finite support of a formula: the parameters it actually uses.  Used to turn a formula with
arbitrary parameters into one whose parameters are the free variables of an `Empty`-parameter
formula.
-/
import Enc

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
namespace ParamBridge

open LRV

set_option maxHeartbeats 1000000

/-- the parameters occurring in a term (Mathlib's `varFinsetLeft`, with a classical instance) -/
noncomputable def paramsTerm {α : Type} {k : ℕ} (t : LRV.Term (α ⊕ Fin k)) : Finset α :=
  @Term.varFinsetLeft LRV α (Fin k) (Classical.decEq α) t

/-- the parameters occurring in a formula (with an explicit decidability instance) -/
noncomputable def paramsOf {α : Type} [DecidableEq α] :
    {k : ℕ} → LRV.BoundedFormula α k → Finset α
  | _, .falsum => ∅
  | _, .equal t u => paramsTerm t ∪ paramsTerm u
  | _, .rel _ ts => Finset.univ.biUnion (fun i => paramsTerm (ts i))
  | _, .imp a b => paramsOf a ∪ paramsOf b
  | _, .all χ => paramsOf χ

/-- the finite support of a term -/
noncomputable def supportTerm {α : Type} {k : ℕ} (t : LRV.Term (α ⊕ Fin k)) : Finset α :=
  paramsTerm t

/-- the finite support of a formula -/
noncomputable def support {α : Type} {k : ℕ} (φ : LRV.BoundedFormula α k) : Finset α :=
  @paramsOf α (Classical.decEq α) k φ

section Congruence
variable {α : Type} {M : Type} [LRV.Structure M]

theorem realize_congr_term {k : ℕ} (t : LRV.Term (α ⊕ Fin k)) {v v' : α → M} (x : Fin k → M)
    (h : ∀ a ∈ supportTerm t, v' a = v a) :
    t.realize (Sum.elim v x) = t.realize (Sum.elim v' x) := by
  induction t with
  | var y =>
      rcases y with a | i
      · classical
        show Sum.elim v x (Sum.inl a) = Sum.elim v' x (Sum.inl a)
        exact (h a (by simp [paramsTerm, supportTerm])).symm
      · rfl
  | func f ts ih =>
      simp only [Term.realize]
      congr 1
      funext i
      refine ih i (fun a ha => h a ?_)
      classical
      exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, ha⟩

theorem realize_congr {k : ℕ} (φ : LRV.BoundedFormula α k) {v v' : α → M} (x : Fin k → M)
    (h : ∀ a ∈ support φ, v' a = v a) :
    (φ.Realize v x ↔ φ.Realize v' x) := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t u =>
      show (t.realize (Sum.elim v x) = u.realize (Sum.elim v x)) ↔
        (t.realize (Sum.elim v' x) = u.realize (Sum.elim v' x))
      rw [realize_congr_term t x (fun a ha => h a ?_),
        realize_congr_term u x (fun a ha => h a ?_)]
      · classical
        exact Finset.mem_union.2 (Or.inr ha)
      · classical
        exact Finset.mem_union.2 (Or.inl ha)
  | rel R ts =>
      show _root_.FirstOrder.Language.Structure.RelMap R
          (fun i => (ts i).realize (Sum.elim v x)) ↔
        _root_.FirstOrder.Language.Structure.RelMap R
          (fun i => (ts i).realize (Sum.elim v' x))
      have hfun : (fun i => (ts i).realize (Sum.elim v x))
          = (fun i => (ts i).realize (Sum.elim v' x)) := by
        funext i
        refine realize_congr_term (ts i) x (fun a ha => h a ?_)
        classical
        exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, ha⟩
      rw [hfun]
  | imp a b iha ihb =>
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp,
        iha x (fun a ha => h a (by classical exact Finset.mem_union.2 (Or.inl ha))),
        ihb x (fun a ha => h a (by classical exact Finset.mem_union.2 (Or.inr ha)))]
  | all χ ih =>
      rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
      refine forall_congr' fun a => ih (Fin.snoc x a) h

end Congruence

end ParamBridge
end Milestone0
end SpecialTransformations
