/-
**`qf2_cover`**: a well-sorted quantifier-free formula over a sorted context is, at sorted tuples,
equivalent to the image of a `QF2` term of `QE/QF2Fragment.lean`.

Why this is the right target and why it is not the audit's `MixedContextCover`: that statement
(`.ultramath/smw1b0thh/m3/AvAudit.lean:158`) asks for a *parameter-free* formula `φ'` and an all-`VF`
tuple `y` with `φ.Realize v x ↔ φ'.Realize default y`.  Since `y` may depend on `(v, x)` and `φ'` is
fixed, the only thing it can require of `φ'` is that it be neither valid nor unsatisfiable, so it is
essentially true for any `φ'` with a true and a false instance, independently of `φ`.  It is therefore
not the content, and it is not what this file proves.

This file proves the content: with the fragment `RVT2` carrying an `RV`-sorted *variable*
(`RVT2.rvar`), every well-sorted quantifier-free formula over a sorted context is the image of a
`QF2` term, so the atom layer of the elimination can be done inside the fragment.  The term
extraction is where `QE/MulNormalForm.lean` belongs: an `RV`-term built out of `rvMul`/`kAdd` has to
be flattened into `RVT2`, and off `Kˣ` that is cancellation.

Build (`.scratch2/sec3/` holds the oleans):

    LEAN_PATH=$PWD:$LEAN_PATH lean QF2Cover.lean        # with QF2Fragment.olean present
-/
import QF2Fragment
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Transfer
namespace QFRes2

/-- The sort assignment of the empty parameter type. -/
abbrev sE : Empty → SortTag := fun e => e.elim

section Extract

variable {n : ℕ} {sn : Fin n → SortTag}

/-! ## The cover, stated

The extraction is a *proof-free* recursion (`Option`-valued), because the proof-carrying version
(`(t : Tm n) → TmSort sE sn t = some .vf → VFT2 sn`) does not pass Lean's structural-recursion
check when the sort hypothesis is consumed inside a `cases f` block: the offending goal is
`sizeOf (ts 0) < 1 + l`, where `l` is the arity and not a size.  The `Option` version descends on `t`
alone and its soundness is a separate induction on `t`, which is the standard way round.

`vfOpt`/`rvOpt` mirror `TmSort` symbol by symbol.  **Proved here** (no `sorry`, axioms within
{propext, Classical.choice, Quot.sound}): `vfOpt_sound` and `rvOpt_sound` — a term of sort `VF`
(resp. `RV`) is extracted, and the extracted fragment term has the same value at every tuple.  The
computation uses the fragment's own `val_*` lemmas (`QF2Fragment`) plus one point that cost a round:
the encoding writes its atoms as `rel R ts` for a general `ts`, while `pVF`/`pRVsort`/`pUnits`/`pLe`
are the `![…]`-shaped abbreviations, so every atom case needs `ts` rewritten to the matrix
(`hts : ts = ![ts 0, ts 1]`) before the realization lemma applies; and `rvMap`'s argument is a *VF*
term, so the `RV` extraction has to call `vfOpt_sound` rather than its own induction hypothesis.

**Still `sorry`:** `qf2_cover` itself, the formula induction.  Its cases are all in place in the
sketch recorded in `QE-PLAN.md` — atoms via the extraction, `imp` via `IsQF.imp`, `all` excluded by
`BoundedFormula.not_all_isQF` — and the two technical hazards are that `QF2.Eval` is a
pattern-matching `def` (so its constructor equations must be stated separately, each by `rfl`) and
that the atom realization lemmas must be stated at general `ts`. -/

/-- Extract a fragment `VF`-term, undoing `TmSort` symbol by symbol.  Proof-free, so that the
recursion is structural on the term; the sort hypothesis is used only in `vfOpt_sound`. -/
noncomputable def vfOpt (sn : Fin n → SortTag) : Tm n → Option (VFT2 sn)
  | .var (Sum.inl e) => Empty.elim e
  | .var (Sum.inr i) => if h : sn i = .vf then some (.var i h) else none
  | .func f ts => match f with
      | .vfZero => some .zero
      | .vfOne => some .one
      | .vfAdd => (vfOpt sn (ts 0)).bind (fun a => (vfOpt sn (ts 1)).map (fun b => .add a b))
      | .vfNeg => (vfOpt sn (ts 0)).map (fun a => .neg a)
      | .vfMul => (vfOpt sn (ts 0)).bind (fun a => (vfOpt sn (ts 1)).map (fun b => .mul a b))
      | .rvOne => none
      | .rvZero => none
      | .rvMul => none
      | .kAdd => none
      | .kNeg => none
      | .rvMap => none

/-- Extract a fragment `RV`-term, dually. -/
noncomputable def rvOpt (sn : Fin n → SortTag) : Tm n → Option (RVT2 sn)
  | .var (Sum.inl e) => Empty.elim e
  | .var (Sum.inr i) => if h : sn i = .rv then some (.rvar i h) else none
  | .func f ts => match f with
      | .rvOne => some .one
      | .rvZero => some .zero
      | .rvMul => (rvOpt sn (ts 0)).bind (fun a => (rvOpt sn (ts 1)).map (fun b => .mul a b))
      | .kAdd => (rvOpt sn (ts 0)).bind (fun a => (rvOpt sn (ts 1)).map (fun b => .kAdd a b))
      | .kNeg => (rvOpt sn (ts 0)).map (fun a => .kNeg a)
      | .rvMap => (vfOpt sn (ts 0)).map (fun s => .rv s)
      | .vfZero => none
      | .vfOne => none
      | .vfAdd => none
      | .vfNeg => none
      | .vfMul => none

/-- **Soundness of the `VF` extraction**: a term of `VF` sort is extracted, and the extracted
fragment term has the same value. -/
theorem vfOpt_sound {M : Type} [LRV.Structure M] :
    ∀ (t : Tm n), TmSort sE sn t = some .vf →
      ∃ s : VFT2 sn, vfOpt sn t = some s ∧
        ∀ x : Fin n → M, s.Val x = t.realize (Sum.elim (default : Empty → M) x) := by
  intro t
  induction t with
  | var a =>
    rcases a with e | i
    · intro h; exact Empty.elim e
    · intro h
      simp only [TmSort, Option.some.injEq] at h
      exact ⟨.var i h, by simp only [vfOpt, h, dif_pos], fun x => rfl⟩
  | @func l f ts ih =>
    intro h
    obtain ⟨hargs, hres⟩ := (tmSort_func_iff sE sn f ts).1 h
    cases f with
    | vfZero =>
      refine ⟨.zero, rfl, fun x => ?_⟩
      rw [VFT2.val_zero]
      have hts : ts = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      rw [hts]
      exact (realize_tVFZero (M := M) (n := n) (Sum.elim (default : Empty → M) x)).symm
    | vfOne =>
      refine ⟨.one, rfl, fun x => ?_⟩
      rw [VFT2.val_one]
      have hts : ts = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      rw [hts]
      exact (realize_tVFOne (M := M) (n := n) (Sum.elim (default : Empty → M) x)).symm
    | vfAdd =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      obtain ⟨b, hb, hvb⟩ := ih 1 (hargs 1)
      refine ⟨.add a b, by simp only [vfOpt, ha, hb, Option.bind_some, Option.map_some], fun x => ?_⟩
      rw [VFT2.val_add, hva, hvb]
      have hts : ts = ![ts 0, ts 1] := funext (fun i => by fin_cases i <;> rfl)
      rw [hts]
      exact (realize_tVFAdd _ _ _).symm
    | vfNeg =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      refine ⟨.neg a, by simp only [vfOpt, ha, Option.map_some], fun x => ?_⟩
      rw [VFT2.val_neg, hva]
      have hts : ts = ![ts 0] := funext (fun i => by fin_cases i; rfl)
      rw [hts]
      exact (realize_tVFNeg _ _).symm
    | vfMul =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      obtain ⟨b, hb, hvb⟩ := ih 1 (hargs 1)
      refine ⟨.mul a b, by simp only [vfOpt, ha, hb, Option.bind_some, Option.map_some], fun x => ?_⟩
      rw [VFT2.val_mul, hva, hvb]
      have hts : ts = ![ts 0, ts 1] := funext (fun i => by fin_cases i <;> rfl)
      rw [hts]
      exact (realize_tVFMul _ _ _).symm
    | rvOne => exact absurd hres (by decide)
    | rvZero => exact absurd hres (by decide)
    | rvMul => exact absurd hres (by decide)
    | kAdd => exact absurd hres (by decide)
    | kNeg => exact absurd hres (by decide)
    | rvMap => exact absurd hres (by decide)

/-- **Soundness of the `RV` extraction**. -/
theorem rvOpt_sound {M : Type} [LRV.Structure M] :
    ∀ (t : Tm n), TmSort sE sn t = some .rv →
      ∃ u : RVT2 sn, rvOpt sn t = some u ∧
        ∀ x : Fin n → M, u.Val x = t.realize (Sum.elim (default : Empty → M) x) := by
  intro t
  induction t with
  | var a =>
    rcases a with e | i
    · intro h; exact Empty.elim e
    · intro h
      simp only [TmSort, Option.some.injEq] at h
      exact ⟨.rvar i h, by simp only [rvOpt, h, dif_pos], fun x => rfl⟩
  | @func l f ts ih =>
    intro h
    obtain ⟨hargs, hres⟩ := (tmSort_func_iff sE sn f ts).1 h
    cases f with
    | rvOne =>
      refine ⟨.one, rfl, fun x => ?_⟩
      rw [RVT2.val_one]
      have hts : ts = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      rw [hts]
      exact (TrivCase.realize_tRVOne (M := M) (n := n) (Sum.elim (default : Empty → M) x)).symm
    | rvZero =>
      refine ⟨.zero, rfl, fun x => ?_⟩
      rw [RVT2.val_zero]
      have hts : ts = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      rw [hts]
      exact (realize_tRVZero (M := M) (k := n) (Sum.elim (default : Empty → M) x)).symm
    | rvMul =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      obtain ⟨b, hb, hvb⟩ := ih 1 (hargs 1)
      refine ⟨.mul a b, by simp only [rvOpt, ha, hb, Option.bind_some, Option.map_some], fun x => ?_⟩
      rw [RVT2.val_mul, hva, hvb]
      have hts : ts = ![ts 0, ts 1] := funext (fun i => by fin_cases i <;> rfl)
      rw [hts]
      exact (realize_tRVMul _ _ _).symm
    | kAdd =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      obtain ⟨b, hb, hvb⟩ := ih 1 (hargs 1)
      refine ⟨.kAdd a b, by simp only [rvOpt, ha, hb, Option.bind_some, Option.map_some], fun x => ?_⟩
      rw [RVT2.val_kAdd, hva, hvb]
      have hts : ts = ![ts 0, ts 1] := funext (fun i => by fin_cases i <;> rfl)
      rw [hts]
      exact (TrivCase.realize_tKAdd _ _ _).symm
    | kNeg =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      refine ⟨.kNeg a, by simp only [rvOpt, ha, Option.map_some], fun x => ?_⟩
      rw [RVT2.val_kNeg, hva]
      have hts : ts = ![ts 0] := funext (fun i => by fin_cases i; rfl)
      rw [hts]
      exact (TrivCase.realize_tKNeg _ _).symm
    | rvMap =>
      -- `rvMap`'s argument is a *VF* term, so this branch calls `vfOpt_sound`, not the `RV` IH
      obtain ⟨s, hs, hvs⟩ := vfOpt_sound (M := M) (sn := sn) (ts 0) (hargs 0)
      refine ⟨.rv s, by simp only [rvOpt, hs, Option.map_some], fun x => ?_⟩
      rw [RVT2.val_rv, hvs]
      have hts : ts = ![ts 0] := funext (fun i => by fin_cases i; rfl)
      rw [hts]
      exact (realize_tRv _ _).symm
    | vfZero => exact absurd hres (by decide)
    | vfOne => exact absurd hres (by decide)
    | vfAdd => exact absurd hres (by decide)
    | vfNeg => exact absurd hres (by decide)
    | vfMul => exact absurd hres (by decide)

/-! ## `qf2_cover`

The target: a well-sorted quantifier-free formula over a sorted context is, at sorted tuples, the
image of a `QF2` term.  The atom cases are the extraction above; the connectives are `QF2.imp` and
`QF2.falsum`, and `pVF`/`pRV`/`pUnits`/`pLe`/`pEq` map to `inVF`/`inRV`/`unitRV`/`leRV`/`eqVF`
(resp. `eqRV` when both terms are `RV`). -/
theorem qf2_cover {n : ℕ} (sn : Fin n → SortTag) (φ : Bf n) (hws : WellSorted sE sn φ)
    (hqf : φ.IsQF) :
    ∃ q : QF2 sn, ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF → ∀ x : Fin n → M,
      (∀ i, sortEval (sn i) (x i)) →
      (φ.Realize (fun e : Empty => e.elim) x ↔
        (q.toRV).Realize (fun e : Empty => e.elim) x) := by
  sorry

end Extract

end QFRes2
end SpecialTransformations.Milestone0.Transfer
