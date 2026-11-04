/-
**The `t = rv 0` case of §3's `alg:ind:imag`.**

`alg:ind:imag` (`QE/AlgIndImag.lean`) is proved for `t` whose `rv`-fibre is not small.  At
`t = rv 0 = ∞` the fibre is `{0}`, so that hypothesis fails — but then the single `RV` parameter is the
*value of a closed term*, so `acl (rv 0) ⊆ acl (∅)`, and the claim of `alg:ind:imag` at `t = rv 0`
reduces to its own hypothesis `a ∉ acl(∅)`.

The reduction substitutes the closed term `rv 0` for the one `RV` parameter, which is what
`QE/SubstParam.lean` supplies (parameter substitution with `WellSorted` preservation).

One Lean wrinkle, which is why the statement below restates the `acl` hypothesis once: the parameter
type of `SP.singleRV t ht` is written with the record's projections
(`Fin (SP.singleRV t ht).n ⊕ Fin (SP.singleRV t ht).m`), and those do not reduce under implicit
transparency, so a term of that type cannot be fed to a map whose domain is the literal
`Fin 0 ⊕ Fin 1`.  Restating the hypothesis at the literal type (a single definitional type ascription)
fixes it; `backward.isDefEq.respectTransparency false` does not.
-/
import AlgIndImag
import SubstParam

/- The `acl` predicate is stated at the parameter type `Fin S.n ⊕ Fin S.m`, and `SP.base` /
`SP.singleRV` are `def`s, so `SP.base.n` does not unfold at the transparency that elaboration uses
for `isDefEq`.  That is the whole obstruction: mark the two parameter pairs reducible *locally* and
the projection type-checks against the literal `Fin 0 ⊕ Fin 0` / `Fin 0 ⊕ Fin 1`.  This is why no
restatement of the theorem is needed. -/
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
attribute [local reducible] SpecialTransformations.Milestone0.SP.base
attribute [local reducible] SpecialTransformations.Milestone0.SP.singleRV

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace M5

variable {M : Type*} [LRV.Structure M]

/-- `rv 0` as a closed term over the parameter type of `SP.base` (`Fin 0 ⊕ Fin 0`). -/
def rvZeroTm : LRV.Term (Fin 0 ⊕ Fin 0) := Term.func Fn.rvZero (fun i => i.elim0)

/-- The parameter map `singleRV t → base` sending the one `RV` parameter to the closed term `rv 0`. -/
def zeroMap : Fin 0 ⊕ Fin 1 → LRV.Term (Fin 0 ⊕ Fin 0) :=
  Sum.elim (fun e => Fin.elim0 e) (fun _ => rvZeroTm)

theorem zeroMap_inr (i : Fin 1) : zeroMap (Sum.inr i) = rvZeroTm := rfl

/-- `Term.relabel` of the arity-`0` constant is that constant again (the arity-`0` argument function
is `Fin.elim0`, and it is not syntactically the same after relabelling). -/
theorem relabel_rvZeroTm {k : ℕ} (g : (Fin 0 ⊕ Fin 0) → (Fin 0 ⊕ Fin 0) ⊕ Fin k) :
    Term.relabel g rvZeroTm
      = (Term.func Fn.rvZero (fun i => i.elim0) : LRV.Term ((Fin 0 ⊕ Fin 0) ⊕ Fin k)) := by
  simp only [rvZeroTm, Term.relabel]
  congr 1
  funext i
  exact i.elim0

/-- Realising the closed term `rv 0` gives the interpretation of `rv 0`. -/
theorem realize_rvZeroTm (v : (Fin 0 ⊕ Fin 0) → M) :
    Term.realize v rvZeroTm = iRVZero (M := M) := by
  simp only [rvZeroTm, iRVZero, Term.realize]
  congr 1
  funext i
  exact i.elim0

/-- **A formula over the single `RV` parameter `rv 0` is, at `SP.base`'s parameters, itself with
`rv 0` substituted for that parameter.** -/
theorem wellSorted_subst_zero (hvz : iRV (iRVZero (M := M)))
    {φ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) 1}
    (h : WellSorted (SP.singleRV (iRVZero (M := M)) hvz).sortMap (fun _ => SortTag.vf) φ) :
    WellSorted (SP.base (M := M)).sortMap (fun _ => SortTag.vf) (φ.subst zeroMap) := by
  refine wellSorted_substParam (SP.singleRV (iRVZero (M := M)) hvz).sortMap
    (SP.base (M := M)).sortMap (n := 1) _ zeroMap ?_ φ h
  intro a
  rcases a with e | i
  · exact Fin.elim0 e
  · rw [zeroMap_inr, SP.sortMap_singleRV]
    show TmSort (SP.base (M := M)).sortMap (fun _ => SortTag.vf)
      (Term.relabel (Sum.inl : (Fin 0 ⊕ Fin 0) → (Fin 0 ⊕ Fin 0) ⊕ Fin 0) rvZeroTm)
        = some SortTag.rv
    rw [relabel_rvZeroTm]
    exact tmSort_rvZero _ _

/-- **The `rv`-zero case**: `acl` over the single parameter `rv 0` is contained in `acl` over `∅`. -/
theorem acl_singleRV_zero (hvz : iRV (iRVZero (M := M))) {x : M}
    (h : SP.acl (SP.singleRV (iRVZero (M := M)) hvz) x) : SP.acl (SP.base (M := M)) x := by
  -- restate the hypothesis at the literal parameter type `Fin 0 ⊕ Fin 1`
  have h' : ∃ φ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) 1,
      WellSorted (SP.singleRV (iRVZero (M := M)) hvz).sortMap (fun _ => SortTag.vf) φ ∧
      ({y : M | iVF y ∧ φ.Realize (SP.singleRV (iRVZero (M := M)) hvz).toFun ![y]}).Finite ∧
      iVF x ∧ φ.Realize (SP.singleRV (iRVZero (M := M)) hvz).toFun ![x] := h
  obtain ⟨φ, hws, hfin, hxVF, hxφ⟩ := h'
  have hpt : (fun a => Term.realize (SP.base (M := M)).toFun (zeroMap a))
      = valRV (iRVZero (M := M)) := by
    funext a
    rcases a with e | i
    · exact Fin.elim0 e
    · simp only [zeroMap_inr]
      exact realize_rvZeroTm _
  refine ⟨φ.subst zeroMap, wellSorted_subst_zero hvz hws, ?_, hxVF, ?_⟩
  · have hiff : ∀ y : M, (φ.subst zeroMap).Realize (SP.base (M := M)).toFun ![y]
        ↔ φ.Realize (valRV (iRVZero (M := M))) ![y] := by
      intro y
      rw [BoundedFormula.realize_subst, hpt]
    have hset : {y : M | iVF y ∧ (φ.subst zeroMap).Realize (SP.base (M := M)).toFun ![y]}
        = {y : M | iVF y ∧ φ.Realize (valRV (iRVZero (M := M))) ![y]} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      rw [hiff y]
    rw [hset, ← SP.toFun_singleRV]
    exact hfin
  · rw [BoundedFormula.realize_subst, hpt, ← SP.toFun_singleRV]
    exact hxφ

/-- **`alg:ind:imag` for every `t ∈ RV`.**  The paper (`paper.tex` §3, after `exchange`): *"If
`a ∈ VF` is such that `a ∉ acl(0)`, then for any `t ∈ RV` we have `a ∉ acl(t)`."*

Both cases are now proved and neither needs the fibre to be a ball at `t = rv 0`:

* `t ≠ rv 0`: `alg_ind_imag`, whose counting hypothesis `hfib` is the geometric input (the fibre of
  `rv` over `t ≠ ∞` is a coset of the unit ball, hence is not small) — this is the one input that is
  not built yet, and it is stated here as a single hypothesis about cardinalities, not about `acl`.
* `t = rv 0`: `acl_singleRV_zero`, i.e. the closed term `rv 0` is substituted for the single `RV`
  parameter, because a term of the language is not an `acl`-generator. -/
theorem alg_ind_imag_all {𝕄 : Sat.MonsterACVF} (hex : M5.ExchangeVF 𝕄) (a : 𝕄.M)
    (ha : iVF a)
    (hacl : 𝕄.Small ↥{y : 𝕄.M | SP.acl (SP.singleVF a ha) y})
    (h : ¬ SP.acl (SP.base (M := 𝕄.M)) a)
    (hfib : ∀ (t : 𝕄.M) (_ht : iRV t), t ≠ iRVZero →
      ¬ 𝕄.Small ↥{x : 𝕄.M | iVF x ∧ iRv x = t}) :
    ∀ (t : 𝕄.M) (ht : iRV t), ¬ SP.acl (SP.singleRV t ht) a := by
  intro t ht
  by_cases hz : t = iRVZero
  · subst hz
    intro hcon
    exact h (acl_singleRV_zero ht hcon)
  · exact M5.alg_ind_imag hex a t ha ht (hfib t ht hz) hacl h

end M5
end Milestone0
end SpecialTransformations
