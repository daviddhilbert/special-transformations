/-
# p2 — the separated slot from its structural residual

Member `m2`, swarm `smw2mluv7`, direction p2.  Companion to `Bookkeeping.lean`.

`Bookkeeping.bookkeeping_half` proves that at the paper's hypotheses — minus henselianity, the
irreducible polynomial, the root `d` and the embedding — the `Γ`/`RV` bookkeeping of one step goes
through, *provided* the extension `T` is handed over together with the two structural facts about
it (`Assembly.IsVFGen T` = Remark 3.1, `M5L.QuotExpansions S T m` = `qe.tex:645`) and with
`M5L.VFInvClosedOn S` (the encoding's `Ŝ = ⟨VF(S)⟩` is a field).  This file composes that with
`M4Cases.CaseSeparated` (`QE/OneStepCases.lean`), so that the *exact* content of the separated slot
beyond the bookkeeping half is machine-checked to be nothing but the realization of the extension
with those three properties.

The zero case (`m = 0`) is handled separately: `0` is a constant symbol, so it is already in `S`
(`M5.OneStepRVOld`'s own case split does the same in `M5L.oneStepRVOld_of_separated_and_rest`).
-/
import Bookkeeping
import OneStepCases

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Milestone0.Bookkeeping

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The separated slot from its structural residual.**  If at every separated step the paper's
hypotheses produce an extension `T` with the two structural facts about it (`Assembly.IsVFGen T`,
`M5L.QuotExpansions S T m`) and the `VF`-closure `M5L.VFInvClosedOn S`, then
`M4Cases.CaseSeparated` holds — because `bookkeeping_half` turns those into
`Assembly.Standing T`.

So the separated slot owes exactly: realization of the extension plus `IsVFGen`/`QuotExpansions`
(the field-theoretic shape of `VF(⟨Ŝ,e⟩)`) plus `VFInvClosedOn S` — and nothing about `Γ` or `RV`,
which are discharged here. -/
theorem caseSeparated_of_structuralResidual
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ M5L.VFInvClosedOn S ∧
          Assembly.IsVFGen T ∧ M5L.QuotExpansions S T m) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  obtain ⟨T, g, hST, hagree, hmT, hfinv, hgen, hquot⟩ := h S f hS m hmVF hmrv hsep
  by_cases hm0 : m = iVFZero
  · refine ⟨S, f, le_rfl, fun _ => rfl, ?_, hS⟩
    rw [hm0]
    exact S.fun_mem Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)
  · exact ⟨T, g, hST, hagree, hmT,
      (bookkeeping_half hST hS hfinv hmVF hm0 hmrv hsep hgen hquot).1⟩

/-- **The `Γ`/`RV` content of the separated slot, from the same residual**: the extra conclusions of
`bookkeeping_half` (the `Γ`-equality as a subgroup equality, and the named-generator form of
Claim (⋆)) hold at every separated step. -/
theorem caseSeparated_bookkeeping (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
      Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S → M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ M5L.VFInvClosedOn S ∧
          Assembly.IsVFGen T ∧ M5L.QuotExpansions S T m) :
    ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → M5L.Separated S m → m ≠ iVFZero →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
          GammaDiv.GammaEqQ S T ∧
          HullAudit.gammaSub (M := M) T = HullAudit.gammaSub (M := M) S ∧
          RVGenCover S T (iRv m) ∧ M5L.ResidualClasses S T := by
  intro S f hS m hmVF hmrv hsep hm0
  obtain ⟨T, g, hST, hagree, hmT, hfinv, hgen, hquot⟩ := h S f hS m hmVF hmrv hsep
  obtain ⟨-, hgamma, hsub, hcov, hres⟩ :=
    bookkeeping_half hST hS hfinv hmVF hm0 hmrv hsep hgen hquot
  exact ⟨T, g, hST, hagree, hmT, hgamma, hsub, hcov, hres⟩

end SpecialTransformations.Milestone0.Bookkeeping

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Bookkeeping.caseSeparated_of_structuralResidual
#print axioms SpecialTransformations.Milestone0.Bookkeeping.caseSeparated_bookkeeping
